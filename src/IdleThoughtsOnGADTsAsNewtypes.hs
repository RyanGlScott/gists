{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 804
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
#endif
-- | How some GADTs can (almost) be represented as newtypes
module IdleThoughtsOnGADTsAsNewtypes where

#if __GLASGOW_HASKELL__ >= 804
import Data.Coerce
import Data.Functor.Identity
import Data.Kind

{-
Can't do this:

newtype T :: Type -> Type where
  MkT :: Bool -> T Bool
-}

newtype T :: Type -> Type where
  MkT :: forall a. ((a ~ Bool) => Bool) -> T a

fromT1 :: forall a. T a -> ((a ~ Bool) => Bool)
fromT1 = coerce @(T a) @((a ~ Bool) => Bool)

fromT2 :: forall a. (a ~ Bool) => T a -> Bool
fromT2 = coerce @(T a) @((a ~ Bool) => Bool)

fromT3 :: T Bool -> Bool
fromT3 = coerce @(T Bool) @((Bool ~ Bool) => Bool)

toT1 :: forall a. ((a ~ Bool) => Bool) -> T a
toT1 = coerce @((a ~ Bool) => Bool) @(T a)

toT2 :: forall a. (a ~ Bool) => Bool -> T a
toT2 = coerce @((a ~ Bool) => Bool) @(T a)

toT3 :: Bool -> T Bool
toT3 = coerce @((Bool ~ Bool) => Bool) @(T Bool)

instance (a ~ Bool) => Eq (T a) where
  (==) = coerce @(((a ~ Bool) => Bool) -> ((a ~ Bool) => Bool) -> Bool)
                @(T a                  -> T a                  -> Bool)
                (==)

{-
Can't do this:

newtype S :: Type -> Type where
  MkS :: forall a. a -> S (Identity a)
-}

newtype S :: Type -> Type where
  MkS :: forall a. (forall a'. (a ~ Identity a') => a') -> S a

fromS1 :: forall a. S a -> (forall a'. (a ~ Identity a') => a')
fromS1 = coerce @(S a) @(forall a'. (a ~ Identity a') => a')

fromS2 :: forall a a'. (a ~ Identity a') => S a -> a'
fromS2 = coerce @(S a) @(forall a''. (a ~ Identity a'') => a'')

fromS3 :: forall a. S (Identity a) -> a
fromS3 = coerce @(S (Identity a)) @(forall a'. (Identity a ~ Identity a') => a')

toS1 :: forall a. (forall a'. (a ~ Identity a') => a') -> S a
toS1 = coerce @(forall a'. (a ~ Identity a') => a') @(S a)

toS2 :: forall a a'. (a ~ Identity a') => a' -> S a
toS2 = coerce @(forall a''. (a ~ Identity a'') => a'') @(S a)

toS3 :: forall a. a -> S (Identity a)
toS3 = coerce @(forall a'. (Identity a ~ Identity a') => a') @(S (Identity a))

{-
Can we do this?

newtype O :: Type where
  MkO :: forall a. a -> O
-}

newtype O :: Type where
  MkO :: (forall a. a) -> O

fromO1 :: O -> (forall a. a)
fromO1 = coerce @O @(forall a. a)

fromO2 :: forall a. O -> a
fromO2 = coerce @O @(forall a'. a')

toO1 :: (forall a. a) -> O
toO1 = coerce @(forall a. a) @O

{-
Can't write this, though:

toO2 :: forall a. a -> O
toO2 = coerce @(forall a. a) @O

So it seems that arbitrary existential quantification is beyond our reach.
-}

data family Sing :: forall k. k -> Type

{-
Can't write this:

newtype instance Sing :: forall a. Identity a -> Type where
  SMkIdentity :: forall a (x :: a).
                 Sing x
              -> Sing ('Identity x)
-}

newtype instance Sing :: forall a. Identity a -> Type where
  SMkIdentity :: forall a (i :: Identity a).
                 (forall (x :: a). (i ~ 'Identity x) => Sing x)
              -> Sing i

fromSI1 :: forall a (i :: Identity a).
           Sing i -> (forall (x :: a). (i ~ 'Identity x) => Sing x)
fromSI1 = coerce @(Sing i)
                 @(forall (x' :: a). (i ~ 'Identity x') => Sing x')

fromSI2 :: forall a (i :: Identity a) (x :: a). (i ~ 'Identity x)
        => Sing i -> Sing x
fromSI2 = coerce @(Sing i)
                 @(forall (x' :: a). (i ~ 'Identity x') => Sing x')

fromSI3 :: forall a (x :: a).
           Sing ('Identity x) -> Sing x
fromSI3 = coerce @(Sing ('Identity x))
                 @(forall (x' :: a). ('Identity x ~ 'Identity x') => Sing x')

toSI1 :: forall a (i :: Identity a).
         (forall (x :: a). (i ~ 'Identity x) => Sing x) -> Sing i
toSI1 = coerce @(forall (x' :: a). (i ~ 'Identity x') => Sing x')
               @(Sing i)

toSI2 :: forall a (i :: Identity a) (x :: a). (i ~ 'Identity x)
      => Sing x -> Sing i
toSI2 = coerce @(forall (x' :: a). (i ~ 'Identity x') => Sing x')
               @(Sing i)

toSI3 :: forall a (x :: a).
         Sing x -> Sing ('Identity x)
toSI3 = coerce @(forall (x' :: a). ('Identity x ~ 'Identity x') => Sing x')
               @(Sing ('Identity x))
#endif