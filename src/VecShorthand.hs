{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module VecShorthand where

import Data.Kind

-----
-- singletons machinery
-----

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

data Nat = Z | S Nat

data instance Sing (z :: Nat) where
  SZ :: Sing Z
  SS :: Sing n -> Sing (S n)

-----

len :: [a] -> Nat
len []     = Z
len (_:xs) = S (len xs)

type family Len (l :: [a]) :: Nat where
  Len '[]    = Z
  Len (_:xs) = S (Len xs)

data Vec :: Nat -> Type -> Type where
  VNil :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a
infixr 5 :>
deriving instance Show a => Show (Vec n a)

data instance Sing (z :: Vec n a) where
  SVNil :: Sing VNil
  (:%>) :: Sing x -> Sing xs -> Sing (x :> xs)
infixr 5 :%>

instance SingKind a => SingKind (Vec n a) where
  type Demote (Vec n a) = Vec n (Demote a)
  fromSing SVNil        = VNil
  fromSing (sx :%> sxs) = fromSing sx :> fromSing sxs
  toSing VNil = SomeSing SVNil
  toSing (x :> xs) = withSomeSing x  $ \sx ->
                     withSomeSing xs $ \sxs ->
                     SomeSing (sx :%> sxs)

instance SingI VNil where
  sing = SVNil

instance (SingI x, SingI xs) => SingI (x :> xs) where
  sing = sing :%> sing

type family Lit (l :: [a]) = (r :: Vec (Len l) a) | r -> l a where
  Lit '[]    = VNil
  Lit (x:xs) = x :> Lit xs

sLit :: forall a (l :: [a]).
        (SingI (Lit l), SingKind a)
     => Vec (Len l) (Demote a)
sLit = fromSing (sing @(Vec (Len l) a) @(Lit l))

-----

example :: Vec (S (S Z)) Bool
example = sLit @_ @'[True, False]
