-- |
-- A reimplementation of Edward Kmett's
-- <http://lpaste.net/79582 strongly-typed bound>, except:
-- 
-- 1. With comments.
-- 2. Optimized for clarity, not performance.
-- 3. Specialized to only work on 'Exp', the simply-typed lambda calculus.
--    In particular, simultaneous binding of multiple variables is omited.
-- 4. Specialized to support the 'hasUnusedBoundVars' example.
--    In particular, monadic substitution is omited.
-- 5. Updated for GHC 7.8.
-- 
-- Many constructs in this file have the suffix @1@, meaning that the
-- construct takes one more type argument than usual.

{-# LANGUAGE GADTs, KindSignatures, InstanceSigs, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module StronglyTypedBound (
  -- * Simply-typed Lambda Calculus
  
  -- |
  -- The <http://hackage.haskell.org/package/bound bound> library is used to
  -- represent languages in a scope-safe way, meaning that terms which attempt
  -- to use unbounded variables are ill-typed.
  -- 
  -- The following language representation goes further: terms which satisfy
  -- Haskell's type-checker are also guaranteed to be well-typed (according to
  -- the rules of the language, not Haskell's).
  
  Exp(..),
  mapContext,
  
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
  
  Eq1(..), eqProxy
  ) where

import Control.Applicative (liftA2)
import Control.Monad.State
import Data.Maybe
import Data.Typeable
import GHC.Conc.Sync (pseq)


-- * Simply-typed Lambda Calculus

-- |
-- Values of type @Exp Γ τ@ represent expressions 'e' such that
-- the typing judgement "Γ ⊢ e : τ" holds.
data Exp (g :: * -> *) a where
    Var :: g a -> Exp g a
    Unit :: Exp g ()
    App :: Exp g (a' -> a) -> Exp g a' -> Exp g a
    Lam :: Exp (g `Comma` a') a -> Exp g (a' -> a)

-- |
-- Change the context by changing all the variables.
mapContext :: forall g h a
            . (forall b. g b -> h b)
           -> Exp g a -> Exp h a
mapContext s (Var gx)   = Var (s gx)
mapContext _ Unit       = Unit
mapContext s (App e e') = App (mapContext s e) (mapContext s e')
mapContext s (Lam e)    = Lam (mapContext s' e)
  where
    s' :: forall a' b. (g `Comma` a') b -> (h `Comma` a') b
    s' Here        = Here
    s' (There gy) = There (s gy)


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
    go env (Var gx)   = env gx
    go _   Unit       = ()
    go env (App e e') = (go env e) (go env e')
    go env (Lam e)    = \x' -> go (env' x') e
      where
        env' :: forall a'. a' -> (forall b. (g `Comma` a') b -> b)
        env' x' Here       = x'
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
    go (Var gx)   = return (singleton gx)
    go Unit       = return empty
    go (App e e') = liftA2 union (go e) (go e')
    go (Lam e)    = do
        Subset isVarUsed <- go e
        guard (isVarUsed Here)
        return $ Subset (isVarUsed . There)


-- * Sets of variables

-- |
-- The subset of the variables for which a predicate is 'True'.
data Subset (g :: * -> *) = Subset
  { runSubset :: forall b. g b -> Bool
  }

empty :: Subset g
empty = Subset (const False)

singleton :: Eq1 g => g a -> Subset g
singleton gx = Subset $ \gy -> isJust (gx ==? gy)

union :: Subset g -> Subset g -> Subset g
union (Subset p1) (Subset p2) = Subset $ \y -> p1 y || p2 y


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
bindVar :: forall g a. Eq1 g
        => g a
        -> (forall b. Exp g b -> Exp (g `Comma` a) b)
bindVar gx = mapContext s
  where
    s :: forall b. g b -> (g `Comma` a) b
    s gy = case gx ==? gy of
        Just Refl -> Here
        Nothing   -> There gy


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
runHoasExp = mapContext s . flip evalState 0
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
(<@>) :: HoasExp (a' -> a) -> HoasExp a' -> HoasExp a
(<@>) = liftA2 App

-- |
-- DSL representation for 'Lam'. The DSL exists to provide this more convenient
-- HOAS-style syntax.
lam :: Typeable a'
    => (HoasExp a' -> HoasExp a) -> HoasExp (a' -> a)
lam body = do
    n <- get
    modify (+1)
    let numericVar = NumericVar n Proxy
    e <- body (var numericVar)
    return $ Lam (bindVar numericVar e)


-- * Heterogeneous equality

-- |
-- Note that even if 'b' and 'b'' are the same type, '==?' may still
-- return 'Nothing' if the values are unequal.
class Eq1 (g :: * -> *) where
    (==?) :: g b -> g b' -> Maybe (b :~: b')

-- |
-- Due to the 'Typeable' constraints, this isn't quite the right type
-- for an @'Eq1' 'Proxy'@ instance.
eqProxy :: (Typeable b, Typeable b')
        => Proxy b -> Proxy b' -> Maybe (b :~: b')
eqProxy _ _ = eqT

instance Eq1 Empty1 where
    empty1 ==? _ = absurd1 empty1

instance Eq1 g => Eq1 (Comma g a) where
    Here ==? Here = Just Refl
    There gy ==? There gy' = case gy ==? gy' of
        Just Refl -> Just Refl
        Nothing   -> Nothing
    _ ==? _ = Nothing
