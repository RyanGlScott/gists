{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 810
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
#endif
-- | Conor McBride's S combinator in GHC
module S where

#if __GLASGOW_HASKELL__ >= 810
import Data.Kind

type TyFun :: Type -> Type -> Type
data TyFun a b

type (~>) :: Type -> Type -> Type
type a ~> b = TyFun a b -> Type
infixr 0 ~>

type (@@) :: (a ~> b) -> a -> b
type family f @@ x

type KindOf :: k -> Type
type KindOf (a :: k) = k

-- | Warm-up.
type DApply :: forall a
                      (b :: a ~> Type)
            -> (forall (x :: a) -> b @@ x)
            -> forall (x :: a)
            -> b @@ x
type DApply a b f x = f x

-- | Conor McBride's S combinator.
type S :: forall a
                 (b :: a ~> Type)
                 (c :: forall (x :: a) -> (b @@ x ~> Type))
       -> (forall (x :: a) (y :: b @@ x) -> c x @@ y)
       -> forall (g :: forall (x :: a) -> b @@ x)
                 (x :: a)
       -> c x @@ g x
type S a b c f g x = f x (g x)

-- | Depedent function composition (in limited form).
type DComp :: forall a
                     (b :: a -> Type)
                     (c :: forall (x :: a). b x -> Type)
           -> (forall (x :: a). forall (y :: b x) -> c y)
           -> forall (g :: forall (x :: a) -> b x)
                     (x :: a)
           -> c (g x)
type DComp a b c f g x = f (g x)
#endif
