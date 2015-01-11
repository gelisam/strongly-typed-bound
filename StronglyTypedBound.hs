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
  
  -- * Finite contexts
  
  -- |
  -- In the typing judgement "Γ ⊢ e : τ", the "Γ" on the left of the turnstile
  -- is a "context", describing which variables are in scope.
  
  Comma(..),
  Empty1, absurd1,
  
  -- * Indexed version of common constructs
  
  -- |
  -- 'Functor1' is a version of 'Functor' with @->@ replaced with ':->:',
  -- and similarly for the other indexed constructs. The suffix @1@ represents
  -- the fact that the construct takes one more type argument than usual.
  
  (:->:),
  Functor1(..), Monad1(..),
  
  -- * Heterogeneous equality
  
  -- |
  -- If two variables are the same, then they also have equal types.
  -- We need a notion of equality which reflects this.
  
  Eq1(..), eqProxy,
  
  -- * Infinite contexts
  
  NumericVar(..)
  ) where

import Data.Typeable
import GHC.Conc.Sync (pseq)


-- * Strongly-typed Lambda Calculus

-- |
-- Values of type @Exp Γ τ@ represent expressions 'e' such that
-- the typing judgement "Γ ⊢ e : τ" holds.
data Exp (g :: * -> *) a where
    Var :: g a -> Exp g a
    Unit :: Exp g ()
    App :: Exp g (a -> b) -> Exp g a -> Exp g b
    Lam :: Exp (g `Comma` a) b -> Exp g (a -> b)



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

instance (Eq1 g, Eq a) => Eq1 (Comma g a) where
    Here ==? Here = Just Refl
    There gy ==? There gy' = case gy ==? gy' of
        Just Refl -> Just Refl
        Nothing   -> Nothing
    _ ==? _ = Nothing


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
