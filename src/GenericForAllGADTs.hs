{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- | An old attempt at defining 'Generic' instances for GADTs.
module GenericForAllGADTs where

import Data.Kind
import GHC.Generics

-----
-- Extra machinery
-----

data TyFun :: Type -> Type -> Type
type a ~> b = TyFun a b -> Type
infixr 0 ~>
type family Apply (f :: k1 ~> k2) (x :: k1) :: k2

data ExQuant (a :: Type) :: forall k. (a ~> (k -> Type)) -> (k -> Type) where
  ExQuant :: forall a k (x :: a) (f :: a ~> (k -> Type)) (p :: k).
             { unExQuant :: WrappedApply f x p }
          -> ExQuant a f p

newtype WrappedApply (f :: a ~> (k -> Type)) (x :: a) (p :: k)
  = WrapApply { unwrapApply :: Apply f x p }

data ExConstr :: forall k. Constraint -> (k -> Type) -> (k -> Type) where
  ExConstr :: c => { unExConstr :: f a } -> ExConstr c f a

-----
-- Generic Functor
-----

genericFmap :: (Generic1 f, Functor (Rep1 f)) => (a -> b) -> f a -> f b
genericFmap f = to1 . fmap f . from1

instance (forall x. Functor (WrappedApply f x)) => Functor (ExQuant a f) where
  fmap f (ExQuant x) = ExQuant (fmap f x)

instance (Functor (Apply f x)) => Functor (WrappedApply f x) where
  fmap f (WrapApply x) = WrapApply (fmap f x)

instance (c => Functor f) => Functor (ExConstr c f) where
  fmap f (ExConstr x) = ExConstr (fmap f x)

-----
-- Example
-----

data Foo :: Type -> Type where
  MkFoo :: Eq b => a -> b -> Foo a

type Aux (b :: Type) =
  ExConstr (Eq b)
    (   S1 (MetaSel Nothing NoSourceUnpackedness NoSourceStrictness DecidedLazy) Par1
    :*: S1 (MetaSel Nothing NoSourceUnpackedness NoSourceStrictness DecidedLazy) (Rec0 b))
data AuxSym :: forall k. Type ~> (k -> Type)
type instance Apply AuxSym b = Aux b

instance Generic1 Foo where
  type Rep1 Foo =
    D1 (MetaData "Foo" "GenericForAllGADTs" "future-haskell" False)
      (C1 (MetaCons "MkFoo" PrefixI False)
        (ExQuant Type AuxSym))
  from1 (MkFoo x y) = M1 (M1 (ExQuant (WrapApply (ExConstr (M1 (Par1 x) :*: M1 (K1 y))))))
  to1 (M1 (M1 (ExQuant (WrapApply (ExConstr (M1 (Par1 x) :*: M1 (K1 y))))))) = MkFoo x y

instance Functor Foo where
  fmap = genericFmap
