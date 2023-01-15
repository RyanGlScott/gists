{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- | A generic implementation of 'SingKind'.
module SGenericSingKind where

import Data.Kind
import Data.Type.Equality

-----
-- singletons machinery
-----

data family Sing :: forall k. k -> Type
data SomeSing :: Type -> Type where
  SomeSing :: Sing (a :: k) -> SomeSing k

data instance Sing :: () -> Type where
  STuple0 :: Sing '()
data instance Sing :: Bool -> Type where
  SFalse :: Sing False
  STrue  :: Sing True
data instance Sing :: forall a. [a] -> Type where
  SNil  :: Sing '[]
  SCons :: Sing x -> Sing xs -> Sing (x:xs)

-----
-- A stripped down version of GHC.Generics
-----

data U1 = MkU1
data instance Sing (z :: U1) where
  SMkU1 :: Sing MkU1

newtype K1 (c :: Type) = MkK1 { runK1 :: c }
data instance Sing (z :: K1 c) where
  SMkK1 :: { sRunK1 :: Sing c } -> Sing (MkK1 c)

data Sum (a :: Type) (b :: Type) = L1 a | R1 b
data instance Sing (z :: Sum a b) where
  SL1 :: Sing a -> Sing (L1 a)
  SR1 :: Sing b -> Sing (R1 b)

data Product (a :: Type) (b :: Type) = MkProduct a b
data instance Sing (z :: Product a b) where
  SMkProduct :: Sing a -> Sing b -> Sing (MkProduct a b)

-----

class Generic (a :: Type) where
    type Rep a :: Type
    from :: a -> Rep a
    to   :: Rep a -> a

class PGeneric (a :: Type) where
  type PFrom (x :: a)     :: Rep a
  type PTo   (x :: Rep a) :: a

class SGeneric k where
  sFrom :: forall (a :: k).     Sing a -> Sing (PFrom a)
  sTo   :: forall (a :: Rep k). Sing a -> Sing (PTo a :: k)
  sTof  :: forall (a :: k).     Sing a -> PTo (PFrom a) :~: a
  sFot  :: forall (a :: Rep k). Sing a -> PFrom (PTo a :: k) :~: a

-----

instance Generic () where
  type Rep () = U1
  from () = MkU1
  to MkU1 = ()

instance PGeneric () where
  type PFrom '()   = MkU1
  type PTo   'MkU1 = '()

instance SGeneric () where
  sFrom STuple0 = SMkU1
  sTo   SMkU1   = STuple0
  sTof  STuple0 = Refl
  sFot  SMkU1   = Refl

-----

instance Generic Bool where
  type Rep Bool = Sum U1 U1
  from False = L1 MkU1
  from True  = R1 MkU1
  to (L1 MkU1) = False
  to (R1 MkU1) = True

instance PGeneric Bool where
  type PFrom False = L1 MkU1
  type PFrom True  = R1 MkU1
  type PTo (L1 MkU1) = False
  type PTo (R1 MkU1) = True

instance SGeneric Bool where
  sFrom SFalse = SL1 SMkU1
  sFrom STrue  = SR1 SMkU1
  sTo (SL1 SMkU1) = SFalse
  sTo (SR1 SMkU1) = STrue
  sTof SFalse = Refl
  sTof STrue  = Refl
  sFot (SL1 SMkU1) = Refl
  sFot (SR1 SMkU1) = Refl

-----

instance Generic [a] where
  type Rep [a] = Sum U1 (Product (K1 a) (K1 [a]))
  from []     = L1 MkU1
  from (x:xs) = R1 (MkProduct (MkK1 x) (MkK1 xs))
  to (L1 MkU1)                           = []
  to (R1 (MkProduct (MkK1 x) (MkK1 xs))) = x:xs

instance PGeneric [a] where
  type PFrom '[]    = L1 MkU1
  type PFrom (x:xs) = R1 (MkProduct (MkK1 x) (MkK1 xs))
  type PTo (L1 MkU1)                           = '[]
  type PTo (R1 (MkProduct (MkK1 x) (MkK1 xs))) = x:xs

instance SGeneric [a] where
  sFrom SNil         = SL1 SMkU1
  sFrom (SCons x xs) = SR1 (SMkProduct (SMkK1 x) (SMkK1 xs))
  sTo (SL1 SMkU1)                             = SNil
  sTo (SR1 (SMkProduct (SMkK1 x) (SMkK1 xs))) = SCons x xs
  sTof SNil    = Refl
  sTof SCons{} = Refl
  sFot (SL1 SMkU1)                        = Refl
  sFot (SR1 (SMkProduct SMkK1{} SMkK1{})) = Refl

-----

class SingKind k where
  type Demote k = (r :: Type) | r -> k

  fromSing         :: forall (a :: k).
                      Sing a -> Demote k
  default fromSing :: forall (a :: k).
                      ( SGeneric k, SingKind (Rep k)
                      , Generic (Demote k), Demote (Rep k) ~ Rep (Demote k) )
                   => Sing a -> Demote k
  fromSing = to . fromSing . sFrom

  toSing         :: Demote k -> SomeSing k
  default toSing :: ( SGeneric k, SingKind (Rep k)
                    , Generic (Demote k), Rep (Demote k) ~ Demote (Rep k) )
                 => Demote k -> SomeSing k
  toSing d = withSomeSing (from d) $ SomeSing . sTo

withSomeSing :: forall k r
              . SingKind k
             => Demote k
             -> (forall (a :: k). Sing a -> r)
             -> r
withSomeSing x f =
  case toSing x of
    SomeSing x' -> f x'

-----
-- Instances for representation types
-----

instance SingKind U1 where
  type Demote U1 = U1
  fromSing SMkU1 = MkU1
  toSing MkU1 = SomeSing SMkU1

instance SingKind c => SingKind (K1 c) where
  type Demote (K1 c) = K1 (Demote c)
  fromSing (SMkK1 sc) = MkK1 (fromSing sc)
  toSing (MkK1 c) = withSomeSing c $ SomeSing . SMkK1

instance (SingKind a, SingKind b) => SingKind (Sum a b) where
  type Demote (Sum a b) = Sum (Demote a) (Demote b)
  fromSing (SL1 sa) = L1 (fromSing sa)
  fromSing (SR1 sb) = R1 (fromSing sb)
  toSing (L1 a) = withSomeSing a $ SomeSing . SL1
  toSing (R1 b) = withSomeSing b $ SomeSing . SR1

instance (SingKind a, SingKind b) => SingKind (Product a b) where
  type Demote (Product a b) = Product (Demote a) (Demote b)
  fromSing (SMkProduct sa sb) = MkProduct (fromSing sa) (fromSing sb)
  toSing (MkProduct a b) = withSomeSing a $ \sA ->
                           withSomeSing b $ \sB ->
                           SomeSing (SMkProduct sA sB)

-----
-- The fruits of our labor
-----

instance SingKind () where
  type Demote () = ()

instance SingKind Bool where
  type Demote Bool = Bool

instance SingKind a => SingKind [a] where
  type Demote [a] = [Demote a]
