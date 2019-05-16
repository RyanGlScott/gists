{-# LANGUAGE CPP #-}

-- This does not typecheck on GHC 8.4 due to
-- https://gitlab.haskell.org/ghc/ghc/issues/14720
#if __GLASGOW_HASKELL__ < 804 || __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
#endif
module SGenericDecide where

#if __GLASGOW_HASKELL__ < 804 || __GLASGOW_HASKELL__ >= 806
import Data.Kind
import Data.Type.Equality
import Data.Void

-----
-- singletons machinery
-----

data family Sing (z :: k)

data instance Sing (z :: ()) where
  STuple0 :: Sing '()
data instance Sing (z :: Bool) where
  SFalse :: Sing False
  STrue  :: Sing True
data instance Sing (z :: [a]) where
  SNil  :: Sing '[]
  SCons :: Sing x -> Sing xs -> Sing (x:xs)

type Refuted a = a -> Void
data Decision a = Proved a | Disproved (Refuted a)

-----
-- A stripped down version of GHC.Generics
-----

data U1 = MkU1
data instance Sing (z :: U1) where
  SMkU1 :: Sing MkU1

newtype K1 (c :: Type) = MkK1 { runK1 :: c }
data instance Sing (z :: K1 c) where
  SMkK1 :: { sRunK1 :: Sing c } -> Sing (MkK1 c)

data Sum (a :: Type) (b :: Type) = L1 a | R1 b
data instance Sing (z :: Sum a b) where
  SL1 :: Sing a -> Sing (L1 a)
  SR1 :: Sing b -> Sing (R1 b)

data Product (a :: Type) (b :: Type) = MkProduct a b
data instance Sing (z :: Product a b) where
  SMkProduct :: Sing a -> Sing b -> Sing (MkProduct a b)

-----

class Generic (a :: Type) where
    type Rep a :: Type
    from :: a -> Rep a
    to :: Rep a -> a

class PGeneric (a :: Type) where
  type PFrom (x :: a)     :: Rep a
  type PTo   (x :: Rep a) :: a

class SGeneric k where
  sFrom :: forall (a :: k).     Sing a -> Sing (PFrom a)
  sTo   :: forall (a :: Rep k). Sing a -> Sing (PTo a :: k)
  sTof  :: forall (a :: k).     Sing a -> PTo (PFrom a) :~: a
  sFot  :: forall (a :: Rep k). Sing a -> PFrom (PTo a :: k) :~: a

-----

instance Generic () where
  type Rep () = U1
  from () = MkU1
  to MkU1 = ()

instance PGeneric () where
  type PFrom '()   = MkU1
  type PTo   'MkU1 = '()

instance SGeneric () where
  sFrom STuple0 = SMkU1
  sTo   SMkU1   = STuple0
  sTof  STuple0 = Refl
  sFot  SMkU1   = Refl

-----

instance Generic Bool where
  type Rep Bool = Sum U1 U1
  from False = L1 MkU1
  from True  = R1 MkU1
  to (L1 MkU1) = False
  to (R1 MkU1) = True

instance PGeneric Bool where
  type PFrom False = L1 MkU1
  type PFrom True  = R1 MkU1
  type PTo (L1 MkU1) = False
  type PTo (R1 MkU1) = True

instance SGeneric Bool where
  sFrom SFalse = SL1 SMkU1
  sFrom STrue  = SR1 SMkU1
  sTo (SL1 SMkU1) = SFalse
  sTo (SR1 SMkU1) = STrue
  sTof SFalse = Refl
  sTof STrue  = Refl
  sFot (SL1 SMkU1) = Refl
  sFot (SR1 SMkU1) = Refl

-----

instance Generic [a] where
  type Rep [a] = Sum U1 (Product (K1 a) (K1 [a]))
  from []     = L1 MkU1
  from (x:xs) = R1 (MkProduct (MkK1 x) (MkK1 xs))
  to (L1 MkU1)                           = []
  to (R1 (MkProduct (MkK1 x) (MkK1 xs))) = x:xs

instance PGeneric [a] where
  type PFrom '[]    = L1 MkU1
  type PFrom (x:xs) = R1 (MkProduct (MkK1 x) (MkK1 xs))
  type PTo (L1 MkU1)                           = '[]
  type PTo (R1 (MkProduct (MkK1 x) (MkK1 xs))) = x:xs

instance SGeneric [a] where
  sFrom SNil         = SL1 SMkU1
  sFrom (SCons x xs) = SR1 (SMkProduct (SMkK1 x) (SMkK1 xs))
  sTo (SL1 SMkU1)                             = SNil
  sTo (SR1 (SMkProduct (SMkK1 x) (SMkK1 xs))) = SCons x xs
  sTof SNil    = Refl
  sTof SCons{} = Refl
  sFot (SL1 SMkU1)                        = Refl
  sFot (SR1 (SMkProduct SMkK1{} SMkK1{})) = Refl

-----

class SDecide k where
  -- | Compute a proof or disproof of equality, given two singletons.
  (%~) :: forall (a :: k) (b :: k). Sing a -> Sing b -> Decision (a :~: b)
  default (%~) :: forall (a :: k) (b :: k). (SGeneric k, SDecide (Rep k))
               => Sing a -> Sing b -> Decision (a :~: b)
  s1 %~ s2 =
    case sFrom s1 %~ sFrom s2 of
      Proved Refl
        |  Refl <- sTof s1
        ,  Refl <- sTof s2
        -> Proved Refl
      Disproved contra -> Disproved $ \Refl -> contra Refl

instance Show a => Show (Decision a) where
  showsPrec p (Proved a) =
    showParen (p > 10) $ showString "Proved " . showsPrec 11 a
  showsPrec p (Disproved _) =
    showParen (p > 10) $ showString "Disproved <void>"

instance SDecide U1 where
  SMkU1 %~ SMkU1 = Proved Refl

instance SDecide c => SDecide (K1 c) where
  SMkK1 c1 %~ SMkK1 c2 =
    case c1 %~ c2 of
      Proved Refl -> Proved Refl
      Disproved contra -> Disproved $ \Refl -> contra Refl

instance (SDecide a, SDecide b) => SDecide (Product a b) where
  SMkProduct a1 b1 %~ SMkProduct a2 b2 =
    case (a1 %~ a2, b1 %~ b2) of
      (Proved Refl, Proved Refl) -> Proved Refl
      (Disproved contra, _) -> Disproved $ \Refl -> contra Refl
      (_, Disproved contra) -> Disproved $ \Refl -> contra Refl

instance (SDecide a, SDecide b) => SDecide (Sum a b) where
  SL1 a %~ SL1 b =
    case a %~ b of
      Proved Refl -> Proved Refl
      Disproved contra -> Disproved $ \Refl -> contra Refl
  SR1 a %~ SR1 b =
    case a %~ b of
      Proved Refl -> Proved Refl
      Disproved contra -> Disproved $ \Refl -> contra Refl
  SL1 _ %~ SR1 _ = Disproved $ \case
  SR1 _ %~ SL1 _ = Disproved $ \case

-----
-- The fruits of our labor
-----

instance SDecide ()
instance SDecide Bool
instance SDecide a => SDecide [a]
#endif
