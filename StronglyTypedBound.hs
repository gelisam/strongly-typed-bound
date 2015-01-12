-- |
-- A reimplementation of Edward Kmett's
-- <http://lpaste.net/79582 strongly-typed bound>, except:
-- 
-- 1. with comments
-- 2. optimized for clarity, not performance
-- 3. updated for GHC 7.8.3

{-# LANGUAGE GADTs, KindSignatures, InstanceSigs, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module StronglyTypedBound (
  -- * Strongly-typed Lambda Calculus
  
  -- |
  -- The <http://hackage.haskell.org/package/bound bound> library is used to
  -- represent languages in a scope-safe way, meaning that terms which attempt
  -- to use unbounded variables are ill-typed.
  
  -- |
  -- This file is a strongly-typed version of the bound library, meaning that
  -- variables are not only guaranteed to be well-scoped, but also well-typed.
  
  Exp(..),
  
  -- * AST manipulations
  
  eval, hasUnusedBoundVars,
  
  -- * Sets of variables
  
  -- |
  -- Used by 'hasUnusedBoundVars' to track which variables have been used.
  
  Subset(..), empty, singleton, union,
  
  -- * Finite contexts
  
  -- |
  -- In the typing judgement "Γ ⊢ e : τ", the "Γ" on the left of the turnstile
  -- is a "context", describing which variables are in scope.
  
  Comma(..),
  Empty1, absurd1,
  
  -- * Infinite contexts
  
  NumericVar(..),
  bindVar,
  
  -- * HOAS syntax for lambdas
  
  -- |
  -- For convenience, we construct a small DSL for describing terms using HOAS
  -- instead of De Bruijn variables.
  
  HoasExp, runHoasExp,
  var, unit, (<@>), lam,
  
  -- * Heterogeneous equality
  
  -- |
  -- If two variables are the same, then they also have equal types.
  -- We need a notion of equality which reflects this.
  
  Eq1(..), eqProxy,
  
  -- * Indexed version of common constructs
  
  -- |
  -- 'Functor1' is a version of 'Functor' with @->@ replaced with ':->:',
  -- and similarly for the other indexed constructs. The suffix @1@ represents
  -- the fact that the construct takes one more type argument than usual.
  
  (:->:),
  Functor1(..), Monad1(..), Show1(..)
  ) where

import Control.Applicative (liftA2)
import Control.Monad.State
import Data.Maybe
import Data.Typeable
import GHC.Conc.Sync (pseq)
import Text.Printf


-- * Strongly-typed Lambda Calculus

-- |
-- Values of type @Exp Γ τ@ represent expressions 'e' such that
-- the typing judgement "Γ ⊢ e : τ" holds.
data Exp (g :: * -> *) a where
    Var :: g a -> Exp g a
    Unit :: Exp g ()
    App :: Exp g (a -> b) -> Exp g a -> Exp g b
    Lam :: Exp (g `Comma` a) b -> Exp g (a -> b)


-- * AST manipulations

-- |
-- An interpreter is equally easy with 'Exp' as with a more typical HOAS
-- representation...
-- 
-- >>> :{
--   eval $ runHoasExp $ lam (\f -> f <@> unit)
--                   <@> lam (\x -> x)
-- :}
-- ()
eval :: Exp Empty1 a -> a
eval = go absurd1
  where
    go :: forall g a. (forall b. g b -> b) -> Exp g a -> a
    go env (Var gx)    = env gx
    go _   Unit        = ()
    go env (App e1 e2) = (go env e1) (go env e2)
    go env (Lam e)     = \x1 -> go (env' x1) e
      where
        env' :: forall a1. a1 -> (forall b. Comma g a1 b -> b)
        env' x1 Here       = x1
        env' _  (There gy) = env gy

-- |
-- ...but some operations are much easier using a representation which, like 'Exp',
-- use concrete representations for variables.
-- 
-- >>> :{
--   hasUnusedBoundVars $ runHoasExp $ lam (\f -> f <@> unit)
--                                 <@> lam (\x -> x)
-- :}
-- False
-- 
-- >>> :{
--   hasUnusedBoundVars $ runHoasExp $ lam (\f -> f <@> unit)
--                                 <@> lam (\x -> unit)
-- :}
-- True
hasUnusedBoundVars :: Exp Empty1 a -> Bool
hasUnusedBoundVars = isNothing . go
  where
    -- abort once an unused variable is found,
    -- otherwise return which variables were used so far.
    go :: forall g a. Eq1 g
       => Exp g a -> Maybe (Subset g)
    go (Var gx)    = return (singleton gx)
    go Unit        = return empty
    go (App e1 e2) = liftA2 union (go e1) (go e2)
    go (Lam e)     = do
        Subset isVarUsed <- go e
        guard (isVarUsed Here)
        return $ Subset (isVarUsed . There)


-- * Sets of variables

-- |
-- The subset of the variables for which a predicate is 'True'.
data Subset (g :: * -> *) = Subset
  { runSubset :: forall a. g a -> Bool
  }

empty :: Subset g
empty = Subset (const False)

singleton :: Eq1 g => g a -> Subset g
singleton gx = Subset $ \gy -> isJust (gx ==? gy)

union :: Subset g -> Subset g -> Subset g
union (Subset p1) (Subset p2) = Subset $ \x -> p1 x || p2 x


-- * Finite contexts

-- |
-- @Comma Γ a@ represents the context @Γ@ extended with an extra
-- variable of type @a@, typically written "Γ, x:a".
data Comma g a b where
    Here  ::        Comma g a a
    There :: g b -> Comma g a b

-- |
-- 'Empty1' represents the empty context, with no variables.
data Empty1 a

-- |
-- @'absurd1' empty1@ forces the evaluation of 'empty1', which can only be ⊥.
absurd1 :: Empty1 a -> b
absurd1 empty1 = empty1 `pseq` error "never happens"


-- * Infinite contexts

-- |
-- Unlike a fixed context such as @'Empty1' \`Comma\` 'Unit' \`Comma\` ('Unit' -> 'Unit')@,
-- which contains only one variable of type 'Unit' and one variable of type
-- @'Unit' -> 'Unit'@, the context 'NumericVar' contains infinitely-many
-- variables of every type.
-- 
-- This allows fresh variables to be generated without changing the context,
-- which in turn allows existing variables to be used without prefixing them with 'There'.
data NumericVar a where
    NumericVar :: Typeable a => Int -> Proxy a -> NumericVar a

instance Eq1 NumericVar where
    NumericVar n p ==? NumericVar n' p' = case (n == n', p `eqProxy` p') of
        (True, Just Refl) -> Just Refl
        _                 -> Nothing

-- |
-- @'bindVar' v e@ shadows 'v', replacing its occurences in 'e' with a fresh
-- bound variable.
bindVar :: forall g a b. Eq1 g
     => g a -> Exp g b -> Exp (g `Comma` a) b
bindVar gx = fmap1 s
  where
    s :: g c -> (g `Comma` a) c
    s gz = case gz ==? gx of
        Just Refl -> Here
        Nothing   -> There gz


-- * Locally-unique variable names

-- |
-- A pure alternative to open type witnesses.
-- 
-- In the original strongly-typed bound implementation, Edward Kmett uses
-- @'unsafePerformIO' 'newUnique'@ to generate new variable names and
-- @unsafeCoerce@ to generate the @a :~: b@ proofs.
-- 
-- Since the variables will be converted to De Bruijn indices immediately after
-- the expression is built, we don't really need the names to be globally unique.
-- So we can simply thread the next available 'Int' throughout the expression,
-- thereby ensuring that the variables are locally unique.
type HoasExp a = State Int (Exp NumericVar a)

-- |
-- Fails if 'var' was used to create variables which haven't been bound by 'lam'.
runHoasExp :: HoasExp a -> Exp Empty1 a
runHoasExp = fmap1 s . flip evalState 0
  where
    s :: NumericVar a -> Empty1 a
    s _ = error "unbound variable, var must have been used improperly."


-- |
-- For internal use by 'lam' only.
var :: NumericVar a -> HoasExp a
var = return . Var

-- |
-- DSL representation for 'Unit'.
unit :: HoasExp ()
unit = return Unit

-- |
-- DSL representation for 'App'.
infixl 4 <@>
(<@>) :: HoasExp (a -> b) -> HoasExp a -> HoasExp b
(<@>) = liftA2 App

-- |
-- DSL representation for 'Lam'. The DSL exists to provide this more convenient
-- HOAS-style syntax.
lam :: Typeable a
    => (HoasExp a -> HoasExp b) -> HoasExp (a -> b)
lam body = do
    n <- get
    modify (+1)
    let numericVar = NumericVar n Proxy
    e <- body (var numericVar)
    return $ Lam (bindVar numericVar e)


-- * Heterogeneous equality

-- |
-- Note that even if 'a' and 'a'' are the same type, '==?' may still
-- return 'Nothing' if the values are unequal.
class Eq1 (f :: * -> *) where
    (==?) :: f a -> f a' -> Maybe (a :~: a')

-- |
-- Due to the 'Typeable' constraints, this isn't quite the right type
-- for an @'Eq1' 'Proxy'@ instance.
eqProxy :: (Typeable a, Typeable a')
        => Proxy a -> Proxy a' -> Maybe (a :~: a')
eqProxy _ _ = eqT

instance Eq1 Empty1 where
    empty1 ==? _ = absurd1 empty1

instance Eq1 g => Eq1 (Comma g a) where
    Here ==? Here = Just Refl
    There gy ==? There gy' = case gy ==? gy' of
        Just Refl -> Just Refl
        Nothing   -> Nothing
    _ ==? _ = Nothing


-- * Indexed version of common constructs

type (:->:) f g = forall a. f a -> g a

-- |
-- > fmap1 :: (a1 :->: a2) -> (m a1 :->: m a2)
class Functor1 (m :: (* -> *) -> * -> *) where
    fmap1 :: (forall b. f b -> g b) -> m f a -> m g a

instance Functor1 Exp where
    fmap1 :: forall f a g. (forall b. f b -> g b) -> Exp f a -> Exp g a
    fmap1 s (Var fx)    = Var (s fx)
    fmap1 _ Unit        = Unit
    fmap1 s (App e1 e2) = App (fmap1 s e1) (fmap1 s e2)
    fmap1 s (Lam e)     = Lam (fmap1 s' e)
      where
        s' :: forall a1 b1. (f `Comma` a1) b1 -> (g `Comma` a1) b1
        s' Here        = Here
        s' (There fy1) = There (s fy1)

-- |
-- > return1 :: a1 :->: m a1
-- > (=<<<) :: (a1 :->: m b1) -> m a1 :->: m b1
class Monad1 (m :: (* -> *) -> * -> *) where
    return1 :: g a -> m g a
    (>>>=) :: m f a -> (forall b. f b -> m g b) -> m g a

instance Monad1 Exp where
    return1 = Var
    
    (>>>=) :: forall f a g. Exp f a -> (forall b. f b -> Exp g b) -> Exp g a
    Var fx    >>>= s = s fx
    Unit      >>>= _ = Unit
    App e1 e2 >>>= s = App (e1 >>>= s) (e2 >>>= s)
    Lam e     >>>= s = Lam (e >>>= s')
      where
        s' :: forall a1 b1. (f `Comma` a1) b1 -> Exp (g `Comma` a1) b1
        s' Here        = Var Here
        s' (There fy1) = fmap1 There (s fy1)

class Show1 (f :: * -> *) where
    show1 :: f a -> String

instance Show1 Empty1 where
    show1 = absurd1

instance Show1 g => Show1 (Comma g a) where
    show1 Here       = "Here"
    show1 (There gx) = printf "There (%s)" (show1 gx)

instance Show1 NumericVar where
    show1 (NumericVar n Proxy) = show n

instance Show1 g => Show1 (Exp g) where
    show1 (Var gx)    = show1 gx
    show1 Unit        = "Unit"
    show1 (App e1 e2) = printf "(%s) `App` (%s)" (show1 e1) (show1 e2)
    show1 (Lam e)     = printf "Lam (%s)" (show1 e)

instance Show1 g => Show (Exp g a) where
    show = show1


