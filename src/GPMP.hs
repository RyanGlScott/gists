{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- | An implementation of /Generic Programming with Multiple Parameters/ by
-- José Pedro Magalhães.
module GPMP where

import Data.Kind

data Univ
  = U
  | F Field
  | Univ :+: Univ
  | Univ :*: Univ
infixr 5 :+:
infixr 6 :*:

data Nat = Ze | Su Nat

data Field :: Type where
  K     ::                     Type         -> Field
  P     ::                     Nat          -> Field
  (:@:) :: forall (k :: Type). k -> [Field] -> Field
infixr 7 :@:

data In :: Univ -> [Type] -> Type where
  U' :: forall                         (p :: [Type]).                     In U p
  F' :: forall (v :: Field)            (p :: [Type]). InField v p      -> In (F v) p
  L' :: forall (a :: Univ) (b :: Univ) (p :: [Type]). In a p           -> In (a :+: b) p
  R' :: forall (a :: Univ) (b :: Univ) (p :: [Type]). In b p           -> In (a :+: b) p
  X' :: forall (a :: Univ) (b :: Univ) (p :: [Type]). In a p -> In b p -> In (a :*: b) p
infixr 6 `X'`

data InField :: Field -> [Type] -> Type where
  K' :: forall (a :: Type)                (p :: [Type]). a                -> InField (K a) p
  P' :: forall (v :: Nat)                 (p :: [Type]). p !! v           -> InField (P v) p
  A' :: forall k (s :: k) (xs :: [Field]) (p :: [Type]). AppFields s xs p -> InField (s :@: xs) p

infixl 9 !!
type family (l :: [Type]) !! (n :: Nat) :: Type where
  (x:_)  !! Ze     = x
  (_:xs) !! (Su n) = xs !! n

type AppFields (s :: k) (xs :: [Field]) (p :: [Type]) = s $$ ExpandField xs p

type family (s :: k) $$ (p :: [Type]) :: Type where
  (s :: Type)      $$ '[]   = s
  (s :: Type -> k) $$ (a:b) = s a $$ b

type family ExpandField (x :: [Field]) (p :: [Type]) :: [Type] where
  ExpandField '[]                   _ = '[]
  ExpandField (K a:xs)              p = a                      : ExpandField xs p
  ExpandField (P v:xs)              p = (p !! v)               : ExpandField xs p
  ExpandField (((s :: k) :@: w):xs) p = (s $$ ExpandField w p) : ExpandField xs p

data HList :: [Type] -> Type where
  HNil  ::                                                     HList '[]
  HCons :: forall (x :: Type) (xs :: [Type]). x -> HList xs -> HList (x:xs)
infixr 5 `HCons`

class Generic (a :: Type) where
  type Rep  a :: Univ
  type Pars a :: [Type]

  from :: a -> In (Rep a) (Pars a)
  to   :: In (Rep a) (Pars a) -> a

instance Generic [a] where
  type Rep  [a] = U :+: F (P Ze) :*: F ([] :@: '[P Ze])
  type Pars [a] = '[a]

  from []    = L' U'
  from (h:t) = R' (F' (P' h) `X'` F' (A' t))

  to (L' U') = []
  to (R' (F' (P' h) `X'` F' (A' t))) = h:t

data RTree a = RTree a [RTree a]
  deriving Show

instance Generic (RTree a) where
  type Rep  (RTree a) = F (P Ze) :*: F ([] :@: '[RTree :@: '[P Ze]])
  type Pars (RTree a) = '[a]

  from (RTree x xs) = F' (P' x) `X'` F' (A' xs)
  to (F' (P' x) `X'` F' (A' xs)) = RTree x xs

instance Generic (a, b) where
  type Rep  (a, b) = F (P Ze) :*: F (P (Su Ze))
  type Pars (a, b) = '[a, b]

  from (a, b) = F' (P' a) `X'` F' (P' b)
  to (F' (P' a) `X'` F' (P' b)) = (a, b)

data D a b c = D b [(a, Int)] (RTree [c])
  deriving Show

instance Generic (D a b c) where
  type Rep  (D a b c) = F (P (Su Ze)) :*: F ([] :@: '[(,) :@: '[P Ze, K Int]])
                                      :*: F (RTree :@: '[[] :@: '[P (Su (Su Ze))]])
  type Pars (D a b c) = '[a, b, c]

  from (D a b c) = F' (P' a) `X'` F' (A' b) `X'` F' (A' c)
  to (F' (P' a) `X'` F' (A' b) `X'` F' (A' c)) = D a b c

data Perfect a = Perfect (Perfect (a, a)) | End a

instance Generic (Perfect a) where
  type Rep  (Perfect a) = F (Perfect :@: '[(,) :@: '[P Ze, P Ze]]) :+: F (P Ze)
  type Pars (Perfect a) = '[a]

  from (Perfect x) = L' (F' (A' x))
  from (End x)     = R' (F' (P' x))

  to (L' (F' (A' x))) = Perfect x
  to (R' (F' (P' x))) = End x

class HLookup (p :: [Type]) (n :: Nat) where
  hlookup :: HList p -> p !! n

instance HLookup (x:xs) Ze where
  hlookup (HCons x _) = x

instance HLookup xs n => HLookup (x:xs) (Su n) where
  hlookup (HCons _ xs) = hlookup @xs @n xs

class GMap (s :: k) (t :: [Type]) | t -> k where
  gmap :: HList t -> s $$ Doms t -> s $$ Codoms t
  default gmap :: ( s $$ Doms   t ~ a
                  , s $$ Codoms t ~ b
                  , Generic a, Generic b
                  , Rep a ~ Rep b
                  , Pars a ~ Doms t
                  , Pars b ~ Codoms t
                  , GMapR (Rep a) t
                  )
               => HList t -> s $$ Doms t -> s $$ Codoms t
  gmap fs = to . gmapR fs . from

instance GMap []      '[a -> a']
instance GMap RTree   '[a -> a']
instance GMap (,)     '[a -> a', b -> b']
instance GMap D       '[a -> a', b -> b', c -> c']
instance GMap Perfect '[a -> a']

d1 :: D Int Float Char
d1 = D 0.2 [(0,0), (1,1)] (RTree "p" [])

d2 :: D Int String Char
d2 = gmap ((+1) `HCons` show `HCons` const 'q' `HCons` HNil) d1

type family Doms (t :: [Type]) :: [Type] where
  Doms '[]            = '[]
  Doms ((a -> b) : t) = a : Doms t

type family Codoms (t :: [Type]) :: [Type] where
  Codoms '[]            = '[]
  Codoms ((a -> b) : t) = b : Codoms t

class GMapR (v :: Univ) (t :: [Type]) where
  gmapR :: HList t -> In v (Doms t) -> In v (Codoms t)

instance GMapR U t where
  gmapR _ U' = U'

instance (GMapR a t, GMapR b t) => GMapR (a :+: b) t where
  gmapR fs (L' x) = L' (gmapR fs x)
  gmapR fs (R' x) = R' (gmapR fs x)

instance (GMapR a t, GMapR b t) => GMapR (a :*: b) t where
  gmapR fs (x `X'` y) = gmapR fs x `X'` gmapR fs y

instance GMapRF v t => GMapR (F v) t where
  gmapR fs (F' x) = F' (gmapRF fs x)

class GMapRF (v :: Field) (t :: [Type]) where
  gmapRF :: HList t -> InField v (Doms t) -> InField v (Codoms t)

instance GMapRF (K a) t where
  gmapRF _ (K' x) = (K' x)

instance GMapRP n t => GMapRF (P n) t where
  gmapRF fs (P' x) = P' (gmapRP @n fs x)

class GMapRP (n :: Nat) (t :: [Type]) where
  gmapRP :: HList t -> Doms t !! n -> Codoms t !! n

instance GMapRP Ze ((a -> b) : t) where
  gmapRP (HCons f _) x = f x

instance GMapRP n t => GMapRP (Su n) ((a -> b) : t) where
  gmapRP (HCons _ fs) p = gmapRP @n fs p

type family MakeFs (p :: [Field]) (t :: [Type]) :: [Type] where
  MakeFs '[]     t = '[]
  MakeFs (K a:p) t = (a -> a) : MakeFs p t
  MakeFs (P n:p) t = (t !! n) : MakeFs p t
  MakeFs (((s :: k) :@: w) : p) t =
    (AppFields s w (Doms t) -> AppFields s w (Codoms t)) : MakeFs p t

instance ( GMap s (MakeFs p t)
         , AdaptFs p t
         , ExpandField p (Doms   t) ~ Doms   (MakeFs p t)
         , ExpandField p (Codoms t) ~ Codoms (MakeFs p t)
         ) => GMapRF ((s :: k) :@: p) t where
  gmapRF fs (A' x) = A' (gmap @k @s (adaptFs @p fs) x)

class AdaptFs (p :: [Field]) (t :: [Type]) where
  adaptFs :: HList t -> HList (MakeFs p t)

instance AdaptFs '[] t where
  adaptFs _ = HNil

instance AdaptFs p t => AdaptFs (K a:p) t where
  adaptFs fs = HCons id (adaptFs @p fs)

instance (AdaptFs p t, HLookup t n) => AdaptFs (P n:p) t where
  adaptFs fs = HCons (hlookup @t @n fs) (adaptFs @p fs)

instance ( GMap s (MakeFs w t)
         , AdaptFs w t
         , AdaptFs p t
         , ExpandField w (Doms   t) ~ Doms   (MakeFs w t)
         , ExpandField w (Codoms t) ~ Codoms (MakeFs w t)
         ) => AdaptFs (((s :: k) :@: w) : p) t where
  adaptFs fs = HCons (gmap @k @s (adaptFs @w fs)) (adaptFs @p fs)
