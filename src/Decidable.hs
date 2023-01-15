{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
-- | A translation of <https://github.com/idris-lang/Idris-dev/blob/0d3d2d66796b172e9933360aee51993a4abc624d/libs/contrib/Decidable/Decidable.idr>
-- from Idris to Haskell.
module Decidable where

import Data.Kind
import Data.Type.Equality
import Data.Void

data family Sing (z :: k)

data Dec a = Yes a | No (a -> Void)

class DecEq t where
  decEq :: Sing (x :: t) -> Sing (y :: t) -> Dec (x :~: y)

instance DecEq Nat where
  decEq SZ   SZ   = Yes Refl
  decEq SZ   SS{} = No $ \case
  decEq SS{} SZ   = No $ \case
  decEq (SS n) (SS m)
    = case decEq n m of
      Yes Refl  -> Yes Refl
      No contra -> No $ \Refl -> contra Refl

data Nat = Z | S Nat

data instance Sing (z :: Nat) where
  SZ :: Sing Z
  SS :: Sing n -> Sing (S n)

data Vect :: Nat -> Type -> Type where
  VNil  ::                  Vect Z a
  (:&:) :: a -> Vect n a -> Vect (S n) a
infixr 5 :&:

type family Fun (ts :: Vect n Type) (r :: Type) :: Type where
  Fun VNil       r = r
  Fun (t :&: ts) r = t -> Fun ts r

type Rel (ts :: Vect n Type) = Fun ts Type

newtype WrappedLiftRel (t :: Type) (ts :: Vect n Type)
                       (p :: t -> Fun ts Type) (f :: Type -> Type)
  = WrapLiftRel { unwrapLiftRel :: forall (x :: t). Sing x -> LiftRel ts (p x) f }

type family LiftRel (ts :: Vect n Type) (p :: Rel ts) (f :: Type -> Type) :: Type where
  LiftRel VNil       p f = f p
  LiftRel (t :&: ts) p f = WrappedLiftRel t ts p f

class Decidable (ts :: Vect k Type) (p :: Rel ts) where
  decide :: LiftRel ts p Dec

data LTE :: Nat -> Nat -> Type where
  LTEZero :: LTE Z right
  LTESucc :: LTE left right -> LTE (S left) (S right)

lteIsReflexive :: Sing (n :: Nat) -> LTE n n
lteIsReflexive SZ     = LTEZero
lteIsReflexive (SS n) = LTESucc (lteIsReflexive n)

ltesuccinjective :: Sing (n :: Nat) -> Sing (m :: Nat)
                 -> (LTE n m -> Void) -> LTE (S n) (S m) -> Void
ltesuccinjective _ _ disprf (LTESucc nLTEm) = absurd (disprf nLTEm)

decideLTE :: Sing (n :: Nat) -> Sing (m :: Nat) -> Dec (LTE n m)
decideLTE SZ     _  = Yes LTEZero
decideLTE (SS _) SZ = No $ \case
decideLTE sx@(SS x) sy@(SS y)
  = case decEq sx sy of
      Yes Refl -> Yes $ lteIsReflexive sy
      No _ -> case decideLTE x y of
                Yes nLTEm -> Yes $ LTESucc nLTEm
                No nGTm   -> No $ ltesuccinjective x y nGTm

instance Decidable (Nat :&: Nat :&: VNil) LTE where
  decide = WrapLiftRel $ \sn -> WrapLiftRel $ decideLTE sn

data Fin :: Nat -> Type where
  FZ :: Fin (S k)
  FS :: Fin k -> Fin (S k)

data instance Sing (z :: Fin n) where
  SFZ :: Sing FZ
  SFS :: Sing k -> Sing (FS k)

finToNat :: Fin n -> Nat
finToNat FZ     = Z
finToNat (FS k) = S (finToNat k)

type family FinToNat (f :: Fin n) :: Nat where
  FinToNat FZ     = Z
  FinToNat (FS k) = S (FinToNat k)

sFinToNat :: Sing a -> Sing (FinToNat a)
sFinToNat SFZ      = SZ
sFinToNat (SFS sk) = SS (sFinToNat sk)

newtype FinLTE :: forall (k :: Nat). Fin k -> Fin k -> Type where
  FromNatPrf :: forall (k :: Nat) (m :: Fin k) (n :: Fin k).
                { runFromNatPrf :: LTE (FinToNat m) (FinToNat n) } -> FinLTE m n

instance Decidable (Fin k :&: Fin k :&: VNil) FinLTE where
  decide
    = WrapLiftRel $ \m ->
      WrapLiftRel $ \n ->
      case decideLTE (sFinToNat m) (sFinToNat n) of
        Yes prf   -> Yes $ FromNatPrf prf
        No disprf -> No $ disprf . runFromNatPrf
