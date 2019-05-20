{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 808
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
#endif

-- | A somewhat convincing facsimile of dependent composition functions...
-- at the /term level/.
--
-- Brace yourself: I'm about to 'Sing' the song of my people.
module DependentComposition where

#if __GLASGOW_HASKELL__ >= 808
import Data.Kind

type family Sing :: k -> Type
newtype WrappedSing :: forall k. k -> Type where
  WrapSing :: { unwrapSing :: Sing a } -> WrappedSing a
newtype SWrappedSing :: forall k (a :: k). WrappedSing a -> Type where
  SWrapSing :: forall k (a :: k) (ws :: WrappedSing a).
               { sUnwrapSing :: Sing a } -> SWrappedSing ws
type instance Sing = SWrappedSing

data TyFun :: Type -> Type -> Type
type a ~> b = TyFun a b -> Type
infixr 0 ~>
type family (f :: k1 ~> k2) @@ (x :: k1) :: k2

newtype SLambda (f :: k1 ~> k2) =
  SLambda { (@@) :: forall t. Sing t -> Sing (f @@ t) }
type instance Sing = SLambda

-- | Dependent composition.
(.) :: forall a
              (b :: a ~> Type)
              (c :: forall (x :: a). b @@ x ~> Type)
              (g :: forall (x :: a). WrappedSing x ~> b @@ x)
              (x :: a) (sx :: Sing x).
       (forall (xx :: a) (y :: b @@ xx). Sing y -> c @xx @@ y)
    -> (forall (xx :: a). Sing (g @xx))
    -> Sing (WrapSing sx) -> c @x @@ (g @@ WrapSing sx)
(f . g) x = f @x (g @@ x)

-- | Conor McBride's combinator.
s :: forall a (b :: a ~> Type) (c :: forall (x :: a). Sing x ~> b @@ x ~> Type).
     (forall (x :: a) (sx :: Sing x) (y :: b @@ x). Sing (WrapSing sx) -> Sing y -> c @@ sx @@ y)
  -> forall (g :: forall (x :: a). WrappedSing x ~> b @@ x). (forall (x :: a). Sing (g @x))
  -> (forall (x :: a) (sx :: Sing x). Sing (WrapSing sx) -> c @@ sx @@ (g @@ WrapSing sx))
s f g x = f x (g @@ x)
#endif
