{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module WorkingAroundT12564 where

import Data.Kind
import Data.Type.Equality

data Nat = Z | S Nat

type family Len (xs :: [a]) :: Nat where
  Len '[]    = Z
  Len (_:xs) = S (Len xs)

data Fin :: Nat -> Type where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

-----
-- Attempt 1 (failed)
-----

{-
type family At (xs :: [a]) (i :: Fin (Len xs)) :: a where
  At (x:_)  FZ     = x
  At (_:xs) (FS i) = At xs i
-}
{-
    • Illegal type synonym family application ‘Len @a _1’ in instance:
        At @a ((':) @a x _1) ('FZ @(Len @a _1))
    • In the equations for closed type family ‘At’
      In the type family declaration for ‘At’
   |
   |   At (x:_)  FZ     = x
   |   ^^^^^^^^^^^^^^^^^^^^
-}

-----
-- Attempt 2
-----

data LenProp :: forall a. [a] -> Nat -> Type where
  LenNil  :: LenProp '[] Z
  LenCons :: LenProp xs n -> LenProp (x:xs) (S n)

type family At' (xs :: [a]) (lp :: LenProp xs n) (i :: Fin n) :: a where
  At' (x:_)  (LenCons _)  FZ     = x
  At' (_:xs) (LenCons lp) (FS i) = At' xs lp i

type family EncodeLenProp (xs :: [a]) :: LenProp xs (Len xs) where
  EncodeLenProp '[]    = LenNil
  EncodeLenProp (_:xs) = LenCons (EncodeLenProp xs)

type family At (xs :: [a]) (i :: Fin (Len xs)) :: a where
  At xs i = At' xs (EncodeLenProp xs) i

-- Unit tests
test1 :: At '[True] FZ :~: True
test1 = Refl

test2 :: At [True, False] FZ :~: True
test2 = Refl

test3 :: At [True, False] (FS FZ) :~: False
test3 = Refl

-----
-- Attempt 2 (alternative approach)
-----

data Vec :: Nat -> Type -> Type where
  VNil :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a

type family ListToVec (l :: [a]) :: Vec (Len l) a where
  ListToVec '[]    = VNil
  ListToVec (x:xs) = x :> ListToVec xs

type family AtAlternative' (xs :: Vec n a) (i :: Fin n) :: a where
  AtAlternative' (x :> _)  FZ     = x
  AtAlternative' (_ :> xs) (FS i) = AtAlternative' xs i

type family AtAlternative (xs :: [a]) (i :: Fin (Len xs)) :: a where
  AtAlternative xs i = AtAlternative' (ListToVec xs) i

-- Unit tests
test1Alternative :: AtAlternative '[True] FZ :~: True
test1Alternative = Refl

test2Alternative :: AtAlternative [True, False] FZ :~: True
test2Alternative = Refl

test3Alternative :: AtAlternative [True, False] (FS FZ) :~: False
test3Alternative = Refl
