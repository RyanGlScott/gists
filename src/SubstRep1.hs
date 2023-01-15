{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- | How to derive a 'Generic' instance using nothing but 'Generic1'.
module SubstRep1 where

import Data.Kind
import GHC.Generics

fromRep1 :: (Generic1 f, SubstRep1' (Rep1 f))
         => f p -> SubstRep1 (Rep1 f) p x
fromRep1 = substRep1 . from1

toRep1 :: (Generic1 f, SubstRep1' (Rep1 f))
       => SubstRep1 (Rep1 f) p x -> f p
toRep1 = to1 . unsubstRep1

newtype FromGeneric1 f p = FromGeneric1 (f p)

instance (Generic1 f, SubstRep1' (Rep1 f)) => Generic (FromGeneric1 f p) where
  type Rep (FromGeneric1 f p) = SubstRep1 (Rep1 f) p
  from (FromGeneric1 x) = fromRep1 x
  to x = FromGeneric1 (toRep1 x)

data Example a = MkExample1 Int a [a] [[a]] [[[a]]]
               | MkExample2
  deriving stock (Generic1, Show)
  deriving Generic via FromGeneric1 Example a

class SubstRep1' (f :: k -> Type) where
  type SubstRep1 f (p :: k) :: Type -> Type
  substRep1   :: f p -> SubstRep1 f p x
  unsubstRep1 :: SubstRep1 f p x -> f p

instance SubstRep1' V1 where
  type SubstRep1 V1 p = V1
  substRep1 x = case x of {}
  unsubstRep1 x = case x of {}

instance SubstRep1' U1 where
  type SubstRep1 U1 p = U1
  substRep1 _ = U1
  unsubstRep1 _ = U1

instance SubstRep1' (K1 i c) where
  type SubstRep1 (K1 i c) p = K1 i c
  substRep1 (K1 x) = K1 x
  unsubstRep1 (K1 x) = K1 x

instance SubstRep1' f => SubstRep1' (M1 i c f) where
  type SubstRep1 (M1 i c f) p = M1 i c (SubstRep1 f p)
  substRep1 (M1 x) = M1 (substRep1 x)
  unsubstRep1 (M1 x) = M1 (unsubstRep1 x)

instance (SubstRep1' f, SubstRep1' g) => SubstRep1' (f :*: g) where
  type SubstRep1 (f :*: g) p = SubstRep1 f p :*: SubstRep1 g p
  substRep1 (x :*: y) = substRep1 x :*: substRep1 y
  unsubstRep1 (x :*: y) = unsubstRep1 x :*: unsubstRep1 y

instance (SubstRep1' f, SubstRep1' g) => SubstRep1' (f :+: g) where
  type SubstRep1 (f :+: g) p = SubstRep1 f p :+: SubstRep1 g p
  substRep1 (L1 x) = L1 (substRep1 x)
  substRep1 (R1 y) = R1 (substRep1 y)
  unsubstRep1 (L1 x) = L1 (unsubstRep1 x)
  unsubstRep1 (R1 y) = R1 (unsubstRep1 y)

instance SubstRep1' Par1 where
  type SubstRep1 Par1 p = Rec0 p
  substRep1 (Par1 x) = K1 x
  unsubstRep1 (K1 x) = Par1 x

instance SubstRep1' (Rec1 f) where
  type SubstRep1 (Rec1 f) p = Rec0 (f p)
  substRep1 (Rec1 x) = K1 x
  unsubstRep1 (K1 x) = Rec1 x

instance (Functor f, SubstRep1Par' g) => SubstRep1' (f :.: g) where
  type SubstRep1 (f :.: g) p = Rec0 (f (SubstRep1Par g p))
  substRep1 (Comp1 x) = K1 (fmap substRep1Par x)
  unsubstRep1 (K1 x) = Comp1 (fmap unsubstRep1Par x)

class SubstRep1Par' (f :: k -> Type) where
  type SubstRep1Par f (p :: k) :: Type
  substRep1Par   :: f p -> SubstRep1Par f p
  unsubstRep1Par :: SubstRep1Par f p -> f p

instance SubstRep1Par' (Rec1 f) where
  type SubstRep1Par (Rec1 f) p = f p
  substRep1Par (Rec1 x) = x
  unsubstRep1Par x = Rec1 x

instance (Functor f, SubstRep1Par' g) => SubstRep1Par' (f :.: g) where
  type SubstRep1Par (f :.: g) p = f (SubstRep1Par g p)
  substRep1Par (Comp1 x) = fmap substRep1Par x
  unsubstRep1Par x = Comp1 (fmap unsubstRep1Par x)
