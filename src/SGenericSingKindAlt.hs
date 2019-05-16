{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
#endif
-- | A generic implementation of 'SingKind' (alternative presentation).
module SGenericSingKindAlt where

#if __GLASGOW_HASKELL__ >= 806
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
-- GHC.Generics?
-----

data Univ = U1 | K1 Type | Sum Univ Univ | Product Univ Univ

data instance Sing :: Univ -> Type where
  SU1      ::                     Sing U1
  SK1      :: Sing c           -> Sing (K1 c)
  SSum     :: Sing a -> Sing b -> Sing (Sum a b)
  SProduct :: Sing a -> Sing b -> Sing (Product a b)

data In :: Univ -> Type where
  MkU1      ::                 In U1
  MkK1      :: c            -> In (K1 c)
  L1        :: In a         -> In (Sum a b)
  R1        ::         In b -> In (Sum a b)
  MkProduct :: In a -> In b -> In (Product a b)

data instance Sing :: forall u. In u -> Type where
  SMkU1      ::                     Sing MkU1
  SMkK1      :: Sing c           -> Sing (MkK1 c)
  SL1        :: Sing a           -> Sing (L1 a)
  SR1        ::           Sing b -> Sing (R1 b)
  SMkProduct :: Sing a -> Sing b -> Sing (MkProduct a b)

-----

class Generic (a :: Type) where
    type Rep a :: Univ
    from :: a -> In (Rep a)
    to   :: In (Rep a) -> a

class PGeneric (a :: Type) where
  type PFrom (x :: a)          :: In (Rep a)
  type PTo   (x :: In (Rep a)) :: a

class SGeneric k where
  sFrom :: forall (a :: k).          Sing a -> Sing (PFrom a)
  sTo   :: forall (a :: In (Rep k)). Sing a -> Sing (PTo a :: k)
  sTof  :: forall (a :: k).          Sing a -> PTo (PFrom a) :~: a
  sFot  :: forall (a :: In (Rep k)). Sing a -> PFrom (PTo a :: k) :~: a

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
-- Machinery from https://gist.github.com/RyanGlScott/63480e23f49fc686950dbd46b776a759
-----

type family Promote (k :: Type) :: Type
type family PromoteX (a :: k) :: Promote k

type family Demote (k :: Type) :: Type
type family DemoteX (a :: k) :: Demote k

type SingKindX (a :: k) = (PromoteX (DemoteX a) ~~ a)
type family SingC (a :: k) :: Constraint
type SingCX (a :: k) = (SingC a, SingKindX a)

class SingKind k where
  fromSing         :: forall (a :: k).
                      Sing a -> Demote k
  default fromSing :: forall (a :: k).
                      ( SGeneric k, SingKind (In (Rep k))
                      , Generic (Demote k), Demote (In (Rep k)) ~ In (Rep (Demote k)) )
                   => Sing a -> Demote k
  fromSing = to . fromSing . sFrom

  toSing         :: Demote k -> SomeSing k
  default toSing :: ( SGeneric k, SingKind (In (Rep k))
                    , Generic (Demote k), In (Rep (Demote k)) ~ Demote (In (Rep k)) )
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
-- Instances
-----

type instance Demote  Type = Type
type instance Promote Type = Type

instance SingKind Type where
  fromSing = error "fromSing Type"
  toSing   = error "toSing Type"

type instance DemoteX (a :: Type) = Demote a
type instance PromoteX (a :: Type) = Promote a

type instance SingC (a :: Type) = SingKind a

type instance Demote  Univ = Univ
type instance Promote Univ = Univ

instance SingKind Univ where
  fromSing SU1              = U1
  fromSing (SK1 sc)         = K1 (fromSing sc)
  fromSing (SSum sa sb)     = Sum (fromSing sa) (fromSing sb)
  fromSing (SProduct sa sb) = Product (fromSing sa) (fromSing sb)

  toSing U1            = SomeSing SU1
  toSing (K1 c)        = withSomeSing c $ SomeSing . SK1
  toSing (Sum a b)     = withSomeSing a $ \sA ->
                         withSomeSing b $ \sB ->
                         SomeSing $ SSum sA sB
  toSing (Product a b) = withSomeSing a $ \sA ->
                         withSomeSing b $ \sB ->
                         SomeSing $ SProduct sA sB

type instance DemoteX U1            = U1
type instance DemoteX (K1 c)        = K1 (DemoteX c)
type instance DemoteX (Sum a b)     = Sum (DemoteX a) (DemoteX b)
type instance DemoteX (Product a b) = Product (DemoteX a) (DemoteX b)

type instance PromoteX U1            = U1
type instance PromoteX (K1 c)        = K1 (PromoteX c)
type instance PromoteX (Sum a b)     = Sum (PromoteX a) (PromoteX b)
type instance PromoteX (Product a b) = Product (PromoteX a) (PromoteX b)

type instance SingC (z :: Univ) = SUnivC z
type family SUnivC (z :: Univ) :: Constraint where
  SUnivC U1            = ()
  SUnivC (K1 c)        = SingC c
  SUnivC (Sum a b)     = (SingC a, SingC b)
  SUnivC (Product a b) = (SingC a, SingC b)

type instance Demote  (In u) = In (DemoteX  u)
type instance Promote (In u) = In (PromoteX u)

instance SingCX u => SingKind (In u) where
  fromSing SMkU1              = MkU1
  fromSing (SMkK1 sc)         = MkK1 (fromSing sc)
  fromSing (SL1 sa)           = L1 (fromSing sa)
  fromSing (SR1 sb)           = R1 (fromSing sb)
  fromSing (SMkProduct sa sb) = MkProduct (fromSing sa) (fromSing sb)

  toSing MkU1            = SomeSing SMkU1
  toSing (MkK1 c)        = withSomeSing c $ SomeSing . SMkK1
  toSing (L1 a)          = withSomeSing a $ SomeSing . SL1
  toSing (R1 b)          = withSomeSing b $ SomeSing . SR1
  toSing (MkProduct a b) = withSomeSing a $ \sA ->
                           withSomeSing b $ \sB ->
                           SomeSing $ SMkProduct sA sB

$(return [])
type instance DemoteX MkU1          = MkU1
type instance DemoteX (MkK1 c)      = MkK1 (DemoteX c)
type instance DemoteX (L1 a)        = L1 (DemoteX a)
type instance DemoteX (R1 b)        = R1 (DemoteX b)
type instance DemoteX (Product a b) = Product (DemoteX a) (DemoteX b)

type instance PromoteX MkU1          = MkU1
type instance PromoteX (MkK1 c)      = MkK1 (PromoteX c)
type instance PromoteX (L1 a)        = L1 (PromoteX a)
type instance PromoteX (R1 b)        = R1 (PromoteX b)
type instance PromoteX (Product a b) = Product (PromoteX a) (PromoteX b)

type instance SingC (z :: In u) = SInC z
type family SInC (z :: In u) :: Constraint where
  SInC MkU1            = ()
  SInC (MkK1 c)        = SingC c
  SInC (L1 a)          = SingC a
  SInC (R1 b)          = SingC b
  SInC (MkProduct a b) = (SingC a, SingC b)

-----
-- The fruits of our labor
-----

type instance Demote  () = ()
type instance Promote () = ()
instance SingKind ()

type instance Demote  Bool = Bool
type instance Promote Bool = Bool
instance SingKind Bool

type instance Demote  [a] = [Demote a]
type instance Promote [a] = [Promote a]
instance SingCX a => SingKind [a]
#endif
