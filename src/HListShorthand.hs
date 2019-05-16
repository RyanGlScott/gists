{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module HListShorthand where

import Data.Kind

-----
-- singletons machinery
-----

data TyFun :: Type -> Type -> Type
type a ~> b = TyFun a b -> Type
infixr 0 ~>
type family Apply (f :: k1 ~> k2) (x :: k1) :: k2

type family Map (f :: a ~> b) (l :: [a]) :: [b] where
  Map _ '[]    = '[]
  Map f (x:xs) = Apply f x : Map f xs

data family Sing (a :: k)

data SomeSing :: Type -> Type where
  SomeSing :: Sing (a :: k) -> SomeSing k

class SingKind k where
  type Demote k = (r :: Type) | r -> k
  fromSing :: Sing (a :: k) -> Demote k
  toSing   :: Demote k -> SomeSing k

withSomeSing :: forall k r
              . SingKind k
             => Demote k
             -> (forall (a :: k). Sing a -> r)
             -> r
withSomeSing x f =
  case toSing x of
    SomeSing x' -> f x'

class SingI (a :: k) where
  sing :: Sing a

data instance Sing (z :: Bool) where
  SFalse :: Sing False
  STrue  :: Sing True

instance SingKind Bool where
  type Demote Bool = Bool
  fromSing SFalse = False
  fromSing STrue  = True
  toSing False = SomeSing SFalse
  toSing True  = SomeSing STrue

instance SingI False where
  sing = SFalse
instance SingI True where
  sing = STrue

data instance Sing (z :: Ordering) where
  SLT :: Sing LT
  SEQ :: Sing EQ
  SGT :: Sing GT

instance SingKind Ordering where
  type Demote Ordering = Ordering
  fromSing SLT = LT
  fromSing SEQ = EQ
  fromSing SGT = GT
  toSing LT = SomeSing SLT
  toSing EQ = SomeSing SEQ
  toSing GT = SomeSing SGT

instance SingI LT where
  sing = SLT
instance SingI EQ where
  sing = SEQ
instance SingI GT where
  sing = SGT

-----

data HList :: [Type] -> Type where
  HNil :: HList '[]
  (:#) :: x -> HList xs -> HList (x:xs)
infixr 5 :#

deriving instance AllC Show xs => Show (HList xs)

data instance Sing (z :: HList xs) where
  SHNil :: Sing HNil
  (:%#) :: Sing x -> Sing xs -> Sing (x :# xs)
infixr 5 :%#

type family AllC (f :: k -> Constraint) (l :: [k]) :: Constraint where
  AllC _ '[]    = ()
  AllC f (x:xs) = (f x, AllC f xs)

type family DemoteList (l :: [Type]) = (r :: [Type]) | r -> l where
  DemoteList '[]    = '[]
  DemoteList (x:xs) = Demote x : DemoteList xs

instance AllC SingKind xs => SingKind (HList xs) where
  type Demote (HList xs) = HList (DemoteList xs)
  fromSing SHNil        = HNil
  fromSing (sx :%# sxs) = fromSing sx :# fromSing sxs
  toSing = error $ unlines
            [ "Won't typecheck."
            , "See GADTSingletons for an approach which does typecheck."
            ]

instance SingI HNil where
  sing = SHNil

instance (SingI x, SingI xs) => SingI (x :# xs) where
  sing = sing :%# sing

data Obj :: Type where
  O :: x -> Obj

type family OKind (o :: Obj) :: Type where
  OKind (O (_ :: x)) = x

data OKindSym0 :: Obj ~> Type
type instance Apply OKindSym0 o = OKind o

type family ToHList (l :: [Obj]) = (r :: HList (Map OKindSym0 l)) | r -> l where
  ToHList '[]             = HNil
  ToHList (O (o :: x):os) = o :# ToHList os

sLit :: forall (l :: [Obj]).
        (SingI (ToHList l), AllC SingKind (Map OKindSym0 l))
     => HList (DemoteList (Map OKindSym0 l))
sLit = fromSing (sing @(HList (Map OKindSym0 l)) @(ToHList l))

example :: HList '[Ordering, Bool]
example = sLit @'[O LT, O False]
