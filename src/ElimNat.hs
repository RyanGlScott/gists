{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module ElimNat where

import Data.Kind

-- | A type-level eliminator for 'Nat's.
type family ElimNat (p :: Nat ~> Type)
                    (s :: Nat)
                    (pZ :: p @@ Z)
                    (pS :: KindOf (PS p)) -- (pS :: forall (n :: Nat) -> (p @@ n ~> p @@ S n))
                 :: p @@ s where
  ElimNat _ Z     pZ _  = pZ
  ElimNat p (S n) pZ pS = pS n @@ ElimNat p n pZ pS
data PS (p :: Nat ~> Type) (n :: Nat) :: p @@ n ~> p @@ S n

-- | Multiply a 'Nat' by two.
type family TimesTwo (n :: Nat) :: Nat where
  TimesTwo n = ElimNat (ConstSym1 Nat) n Z Doubler
data Doubler (n :: Nat) :: Const Nat n ~> Nat
type instance Doubler _ @@ x = S (S x)

data TyFun :: Type -> Type -> Type
type a ~> b = TyFun a b -> Type
infixr 0 ~>
type family (f :: a ~> b) @@ (x :: a) :: b
type KindOf (a :: k) = k

data family Sing (z :: k)

data Nat = Z | S Nat
data instance Sing (z :: Nat) where
  SZ :: Sing Z
  SS :: Sing n -> Sing (S n)

data ConstSym1 :: forall a b. a -> b ~> a
type instance ConstSym1 x @@ y = Const x y
type family Const (x :: a) (y :: b) :: a where
  Const x _ = x
