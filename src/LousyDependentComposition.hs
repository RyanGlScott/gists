{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Horrific attempts at defining dependent composition functions in GHC.
module LousyDependentComposition where

import Data.Kind
import Data.Proxy

data family Sing (a :: k)
data SomeSing :: Type -> Type where
  SomeSing :: Sing (a :: k) -> SomeSing k

class SingKind k where
  type Demote k = (r :: Type) | r -> k
  fromSing :: Sing (a :: k) -> Demote k
  toSing :: Demote k -> SomeSing k

withSomeSing :: forall k r
              . SingKind k
             => Demote k
             -> (forall (a :: k). Sing a -> r)
             -> r
withSomeSing x f =
  case toSing x of
    SomeSing x' -> f x'

newtype instance Sing (f :: k1 ~> k2) =
  SLambda { applySing :: forall t. Sing t -> Sing (f @@ t) }

instance (SingKind k1, SingKind k2) => SingKind (k1 ~> k2) where
  type Demote (k1 ~> k2) = Demote k1 -> Demote k2
  fromSing sFun x = withSomeSing x (fromSing . applySing sFun)
  toSing = undefined

data TyFun :: Type -> Type -> Type
type a ~> b = TyFun a b -> Type
infixr 0 ~>

type family Apply (f :: k1 ~> k2) (x :: k1) :: k2
type f @@ x = Apply f x
infixl 9 @@

dapply1 :: forall (a :: Type)
                  (b :: a ~> Type)
                  (x :: a).
           (forall (xx :: a). b @@ xx)
        -> Sing x
        -> b @@ x
dapply1 f _ = f @x

dapply2 :: forall (a :: Type)
                  (b :: a ~> Type)
                  (f :: forall (x :: a). Proxy x ~> b @@ x)
                  (x :: a).
           SingKind (b @@ x)
        => (forall (xx :: a). Sing (f @@ ('Proxy :: Proxy xx)))
        -> Sing x
        -> Demote (b @@ x)
dapply2 sf _ = fromSing $ sf @x

dcomp1 :: forall (a :: Type)
                 (b :: a ~> Type)
                 (c :: forall (x :: a). Proxy x ~> b @@ x ~> Type)
                 (g :: forall (x :: a). Proxy x ~> b @@ x)
                 (x :: a).
          (forall (xx :: a) (yy :: b @@ xx). c @@ ('Proxy :: Proxy xx) @@ yy)
       -> (forall (xx :: a). Sing (g @@ ('Proxy :: Proxy xx)))
       -> Sing x
       -> c @@ ('Proxy :: Proxy x) @@ (g @@ ('Proxy :: Proxy x))
dcomp1 f _ _ = f @x @(g @@ ('Proxy :: Proxy x))

#if __GLASGOW_HASKELL__ >= 805
dcomp2 :: forall (a :: Type)
                 (b :: a ~> Type)
                 (c :: forall (x :: a). Proxy x ~> b @@ x ~> Type)
                 (f :: forall (x :: a) (y :: b @@ x). Proxy x ~> Proxy y ~> c @@ ('Proxy :: Proxy x) @@ y)
                 (g :: forall (x :: a). Proxy x ~> b @@ x)
                 (x :: a).
          SingKind (c @@ ('Proxy :: Proxy x) @@ (g @@ ('Proxy :: Proxy x)))
       => (forall (xx :: a) (yy :: b @@ xx). Sing (f @@ ('Proxy :: Proxy xx) @@ ('Proxy :: Proxy yy)))
       -> (forall (xx :: a). Sing (g @@ ('Proxy :: Proxy xx)))
       -> Sing x
       -> Demote (c @@ ('Proxy :: Proxy x) @@ (g @@ ('Proxy :: Proxy x)))
dcomp2 sf _ _ = fromSing $ sf @x @(g @@ ('Proxy :: Proxy x))
#endif
