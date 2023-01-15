{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 810
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
#endif
module ElimNat where

#if __GLASGOW_HASKELL__ >= 810
import Data.Kind

-- | A type-level eliminator for 'Nat's.
type ElimNat :: forall (p :: Nat ~> Type) (s :: Nat)
             -> p @@ Z
             -> (forall (n :: Nat) -> p @@ n ~> p @@ S n)
             -> p @@ s
type family ElimNat p s pZ pS where
  forall (p :: Nat ~> Type)
         (pZ :: p @@ Z) (pS :: forall (n :: Nat) -> p @@ n ~> p @@ S n).
    ElimNat p Z pZ pS = pZ
  forall (p :: Nat ~> Type)
         (pZ :: p @@ Z) (pS :: forall (n :: Nat) -> p @@ n ~> p @@ S n)
         (n :: Nat).
    ElimNat p (S n) pZ pS = pS n @@ ElimNat p n pZ pS

-- | Multiply a 'Nat' by two.
type TimesTwo :: Nat -> Nat
type family TimesTwo n where
  TimesTwo n = ElimNat (ConstSym1 Nat) n Z Doubler

type Doubler :: forall (n :: Nat) -> Const Nat n ~> Nat
data Doubler (n :: Nat) :: Const Nat n ~> Nat
type instance Doubler _ @@ x = S (S x)

type TyFun :: Type -> Type -> Type
data TyFun a b

type (~>) :: Type -> Type -> Type
type a ~> b = TyFun a b -> Type
infixr 0 ~>

type (@@) :: (a ~> b) -> a -> b
type family f @@ x

type KindOf :: k -> Type
type KindOf (a :: k) = k

type Sing :: k -> Type
data family Sing

type Nat :: Type
data Nat = Z | S Nat

data instance Sing :: Nat -> Type where
  SZ :: Sing Z
  SS :: Sing n -> Sing (S n)

type ConstSym1 :: a -> b ~> a
data ConstSym1 a f
type instance ConstSym1 x @@ y = Const x y

type Const :: a -> b -> a
type family Const x y where
  Const x _ = x
#endif
