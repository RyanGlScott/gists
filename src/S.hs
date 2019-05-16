{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
-- | Conor McBride's S combinator in GHC
module S where

import Data.Kind

data TyFun :: Type -> Type -> Type
type a ~> b = TyFun a b -> Type
infixr 0 ~>
type family (f :: a ~> b) @@ (x :: a) :: b
type KindOf (a :: k) = k

-- | Warm-up.
type DApply a
            (b :: a ~> Type)
            (f :: KindOf (DApplyAux a b))
              -- (f :: forall (x :: a) -> b @@ x)
            (x :: a)
  = (f x :: b @@ x)
type family DApplyAux a (b :: a ~> Type) (x :: a) :: b @@ x where {}

-- | Conor McBride's S combinator.
type S a
       (b :: a ~> Type)
       (c :: KindOf (SAux1 a b))
         -- (c :: forall (x :: a) -> (b @@ x ~> Type))
       (f :: KindOf (SAux2 a b c))
         -- (f :: forall (x :: a) (y :: b @@ x) -> c x @@ y)
       (g :: KindOf (SAux3 a b))
         -- (g :: forall (x :: a) -> b @@ x)
       (x :: a)
  = (f x (g x) :: c x @@ g x)
type family SAux1 a (b :: a ~> Type)
                  (x :: a) :: b @@ x ~> Type
type family SAux2 a (b :: a ~> Type) (c :: KindOf (SAux1 a b))
                  (x :: a) (y :: b @@ x) :: c x @@ y
type SAux3 a (b :: a ~> Type) (x :: a) = (DApplyAux a b x :: b @@ x)

-- | Depedent function composition (in limited form).
type DComp a
           (b :: a -> Type)
           (c :: forall (x :: a). KindOf (DCompAux1 a b x))
             -- (c :: forall (x :: a). b x -> Type)
           (f :: forall (x :: a). KindOf (DCompAux2 a b c x))
             -- (f :: forall (x :: a). forall (y :: b x) -> c y)
           (g :: KindOf (DCompAux3 a b))
             -- (g :: forall (x :: a) -> b x)
           (x :: a)
  = (f (g x) :: c (g x))
type family DCompAux1 a (b :: a -> Type)
                      (x :: a) :: b x -> Type
type family DCompAux2 a (b :: a -> Type) (c :: forall (x :: a). KindOf (DCompAux1 a b x))
                      (x :: a) (y :: b x) :: c y
type family DCompAux3 a (b :: a -> Type) (x :: a) :: b x
