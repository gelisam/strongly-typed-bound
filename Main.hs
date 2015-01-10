-- A reimplementation of Edward Kmett's strongly-typed bound
-- (http://lpaste.net/79582), except
-- 1) with comments
-- 2) optimized for clarity, not performance 
-- 3) updated for GHC 7.8.3

{-# LANGUAGE GADTs, KindSignatures, InstanceSigs, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Main where

import Control.Applicative


-- Values of type `Exp Γ τ` represent expressions `e` such that
-- the typing judgement "Γ ⊢ e : τ" holds.
data Exp (g :: * -> *) a where
    Var :: g a -> Exp g a
    Unit :: Exp g ()
    App :: Exp g (a -> b) -> Exp g a -> Exp g b
    Lam :: Exp (g `Comma` a) b -> Exp g (a -> b)

-- `Comma Γ a` represents the context `Γ` extended with an extra
-- variable of type `a`, typically written "Γ, x:a".
type Comma f a = Either1 f (Const a)


type (:->:) f g = forall a. f a -> g a

data Either1 (f :: * -> *) (g :: * -> *) a where
    -- Left1  :: a1 :->: Either1 a1 b1
    -- Right1 :: b1 :->: Either1 a1 b1
    Left1  :: f a -> Either1 f g a
    Right1 :: g a -> Either1 f g a


class Functor1 (m :: (* -> *) -> * -> *) where
    -- fmap1 :: (a1 :->: a2) -> (m a1 :-> m a2)
    fmap1 :: (forall b. f b -> g b) -> m f a -> m g a

instance Functor1 Exp where
    fmap1 :: forall f a g. (forall b. f b -> g b) -> Exp f a -> Exp g a
    fmap1 s (Var fx)    = Var (s fx)
    fmap1 _ Unit        = Unit
    fmap1 s (App e1 e2) = App (fmap1 s e1) (fmap1 s e2)
    fmap1 s (Lam e)     = Lam (fmap1 s' e)
      where
        s' :: forall a1 b1. (f `Comma` a1) b1 -> (g `Comma` a1) b1
        s' (Left1 fy1)         = Left1 (s fy1)
        s' (Right1 (Const x1)) = Right1 (Const x1)

class Monad1 (m :: (* -> *) -> * -> *) where
    -- return1 :: a1 :->: m a1
    -- (=<<<) :: (a1 :->: m b1) -> m a1 :->: m b1
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
        s' (Left1 fy1)         = fmap1 Left1 (s fy1)
        s' (Right1 (Const x1)) = Var (Right1 (Const x1))


main :: IO ()
main = putStrLn "typechecks."
