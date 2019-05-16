{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
#endif
-- | A way to generically derive instances and special-case behavior for certain types.
module ExcludingEq where

#if __GLASGOW_HASKELL__ >= 806
import Data.Kind
import GHC.Generics

-----
-- Taken from the singleton-bool package
-----

-- | The singleton version of 'Bool'.
data SBool :: Bool -> Type where
  SFalse :: SBool False
  STrue  :: SBool True

-- | An 'SBoolI' constraint is an implicitly-passed 'SBool'.
class SBoolI (b :: Bool) where
  sbool :: SBool b

instance SBoolI False where
  sbool = SFalse

instance SBoolI True where
  sbool = STrue

-----
-- Type-level voodoo
-----

type family Unless (a :: Bool) (b :: Constraint) :: Constraint where
  Unless True  _ = ()
  Unless False b = b

type family Elem (x :: a) (xs :: [a]) :: Bool where
  Elem _ '[]    = False
  Elem x (x:_)  = True
  Elem x (y:xs) = Elem x xs

-----
-- The Excluding newtype
-----

newtype Excluding :: [Type] -> Type -> Type where
  Excluding :: a -> Excluding excluded a

instance (Generic a, GEq excluded (Rep a)) => Eq (Excluding excluded a) where
  Excluding x == Excluding y = geq @excluded (from x) (from y)

-----
-- Generics machinery
-----

class GEq (excluded :: [Type]) f where
  geq :: f a -> f a -> Bool

instance GEq e U1 where
  geq _ _ = True

instance GEq e a => GEq e (M1 i c a) where
  geq (M1 a) (M1 b) = geq @e a b

instance (GEq e a, GEq e b) => GEq e (a :+: b) where
  geq (L1 a) (L1 b) = geq @e a b
  geq (R1 a) (R1 b) = geq @e a b
  geq _      _      = False

instance (GEq e a, GEq e b) => GEq e (a :*: b) where
  geq (a1 :*: b1) (a2 :*: b2) = geq @e a1 a2 && geq @e b1 b2

-- This is the important instance.
instance ( Unless (Elem a excluded) (Eq a)
         , SBoolI (Elem a excluded) )
    => GEq excluded (K1 i a) where
  geq (K1 a) (K1 b)
    = case sbool @(Elem a excluded) of
        SFalse -> a == b
        STrue  -> True

-----
-- Example
-----

data MyBigType
  = MyBigType {
      f1 :: Int
    , f2 :: Double
    , f3 :: (Int -> Char)
    , f4 :: Char
    } deriving stock Generic
      deriving Eq via (Excluding '[Int -> Char] MyBigType)

main :: IO ()
main = do
  let mbt = MyBigType 1 2.0 (const 'a') '3'
  print $ mbt == mbt
#endif
