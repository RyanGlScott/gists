{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Generic 'SingI' instances for 'TyCon's, using @QuantifiedConstraints@.
module SingIForTyCons where

import Data.Kind
import Unsafe.Coerce (unsafeCoerce)

data family Sing :: k -> Type
data TyFun :: Type -> Type -> Type
type a ~> b = TyFun a b -> Type
infixr 0 ~>
type family Apply (f :: k1 ~> k2) (x :: k1) :: k2
type a @@ b = Apply a b
infixl 9 @@
type ShowSing k = forall a. Show (Sing (a :: k))

newtype instance Sing (f :: k1 ~> k2) =
  SLambda { applySing :: forall t. Sing t -> Sing (f @@ t) }

data instance Sing :: () -> Type where
  STuple0 :: Sing '()
deriving instance Show (Sing (z :: ()))

data instance Sing :: forall a b. (a, b) -> Type where
  STuple2 :: Sing a -> Sing b -> Sing '(a, b)
deriving instance (ShowSing a, ShowSing b) => Show (Sing (z :: (a, b)))

data TyCon1 :: (k1 -> k2)       -> (k1 ~> k2)
data TyCon2 :: (k1 -> k2 -> k3) -> (k1 ~> k2 ~> k3)
-- etc.
type instance Apply (TyCon1 f) x = f x
type instance Apply (TyCon2 f) x = TyCon1 (f x)
-- etc.

class SingI (a :: k) where
  sing :: Sing a

withSingI :: Sing n -> (SingI n => r) -> r
withSingI sn r =
  case singInstance sn of
    SingInstance -> r

data SingInstance (a :: k) where
  SingInstance :: SingI a => SingInstance a

newtype DI a = Don'tInstantiate (SingI a => SingInstance a)

singInstance :: forall k (a :: k). Sing a -> SingInstance a
singInstance s = with_sing_i SingInstance
  where
    with_sing_i :: (SingI a => SingInstance a) -> SingInstance a
    with_sing_i si = unsafeCoerce (Don'tInstantiate si) s

instance (SingI a, SingI b) => SingI '(a, b) where
  sing = STuple2 sing sing

instance (forall a. SingI a => SingI (f a)) => SingI (TyCon1 f) where
  sing = SLambda $ \(x :: Sing a) -> withSingI x $ sing @_ @(f a)

instance (forall a b. (SingI a, SingI b) => SingI (f a b)) => SingI (TyCon2 f) where
  sing = SLambda $ \(x :: Sing a) -> withSingI x $ sing @_ @(TyCon1 (f a))

-- etc.

test :: Sing '( '(), '() )
test = sing @_ @(TyCon2 '(,)) `applySing` STuple0 `applySing` STuple0
