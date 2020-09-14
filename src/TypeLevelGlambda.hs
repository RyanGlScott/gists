{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 810
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
#endif
module TypeLevelGlambda where

#if __GLASGOW_HASKELL__ >= 810
import Data.Kind

type ArithOp :: Type -> Type
data ArithOp x where
  Plus, Minus, Times, Divide, Mod        :: ArithOp Int
  Less, LessE, Greater, GreaterE, Equals :: ArithOp Bool

type Elem :: [a] -> a -> Type
data Elem xs x where
  EZ :: Elem (x:xs) x
  ES :: Elem xs x -> Elem (y:xs) x

type Exp :: [Type] -> Type -> Type
data Exp ctx ty where
  Var   :: Elem ctx ty -> Exp ctx ty
  Lam   :: Exp (arg:ctx) res -> Exp ctx (arg -> res)
  App   :: Exp ctx (arg -> res) -> Exp ctx arg -> Exp ctx res
  Arith :: Exp ctx Int -> ArithOp ty -> Exp ctx Int -> Exp ctx ty
  Cond  :: Exp ctx Bool -> Exp ctx ty -> Exp ctx ty -> Exp ctx ty
  Fix   :: Exp ctx (ty -> ty) -> Exp ctx ty
  IntE  :: Int -> Exp ctx Int
  BoolE :: Bool -> Exp ctx Bool

infixr 5 ++, `LenProp`

type (++) :: [a] -> [a] -> [a]
type family xs ++ ys where
  '[]    ++ ys = ys
  (x:xs) ++ ys = x:(xs ++ ys)

type LenProp :: [a] -> [a] -> [a] -> Type
data LenProp xs ys r where
  LenNil  :: ('[] `LenProp` ys) ys
  LenCons :: (xs `LenProp` ys) r -> ((x:xs) `LenProp` ys) (x:r)

type Shift :: Exp ts2 ty -> Exp (t:ts2) ty
type family Shift e where
  Shift e = ShiftGo LenNil e

type ShiftGo :: forall t ts1 ts2 ty r.
                (ts1 `LenProp` ts2) r -> Exp r ty -> Exp (ts1 ++ t:ts2) ty
type family ShiftGo lp e where
  ShiftGo @t lp (Var v)          = Var (ShiftElem @t lp v)
  ShiftGo @t lp (Lam body)       = Lam (ShiftGo @t (LenCons lp) body)
  ShiftGo @t lp (App e1 e2)      = App (ShiftGo @t lp e1) (ShiftGo @t lp e2)
  ShiftGo @t lp (Arith e1 op e2) = Arith (ShiftGo @t lp e1) op (ShiftGo @t lp e2)
  ShiftGo @t lp (Cond e1 e2 e3)  = Cond (ShiftGo @t lp e1) (ShiftGo @t lp e2) (ShiftGo @t lp e3)
  ShiftGo @t lp (Fix e)          = Fix (ShiftGo @t lp e)
  ShiftGo @_ _  (IntE n)         = IntE n
  ShiftGo @_ _  (BoolE b)        = BoolE b

type ShiftElem :: forall t ts1 ts2 x r.
                  (ts1 `LenProp` ts2) r -> Elem r x -> Elem (ts1 ++ t:ts2) x
type family ShiftElem lp e where
  ShiftElem @_ LenNil      e      = ES e
  ShiftElem @_ (LenCons _) EZ     = EZ
  ShiftElem @t (LenCons l) (ES e) = ES (ShiftElem @t l e)

type Subst :: Exp ts2 s -> Exp (s:ts2) t -> Exp ts2 t
type family Subst exp1 exp2 where
  Subst exp1 exp2 = SubstGo exp1 LenNil exp2

type SubstGo :: Exp ts2 s -> (ts1 `LenProp` s:ts2) r -> Exp r t -> Exp (ts1 ++ ts2) t
type family SubstGo exp1 lp exp2 where
  SubstGo e len (Var v)          = SubstVar e len v
  SubstGo e len (Lam body)       = Lam (SubstGo e (LenCons len) body)
  SubstGo e len (App e1 e2)      = App (SubstGo e len e1) (SubstGo e len e2)
  SubstGo e len (Arith e1 op e2) = Arith (SubstGo e len e1) op (SubstGo e len e2)
  SubstGo e len (Cond e1 e2 e3)  = Cond (SubstGo e len e1) (SubstGo e len e2) (SubstGo e len e3)
  SubstGo e len (Fix e')         = Fix (SubstGo e len e')
  SubstGo _ _   (IntE n)         = IntE n
  SubstGo _ _   (BoolE b)        = BoolE b

type SubstVar :: Exp ts2 s -> (ts1 `LenProp` s:ts2) r -> Elem r t -> Exp (ts1 ++ ts2) t
type family SubstVar exp lp el where
  SubstVar e LenNil        EZ     = e
  SubstVar _ LenNil        (ES v) = Var v
  SubstVar _ (LenCons _)   EZ     = Var EZ
  SubstVar e (LenCons len) (ES v) = Shift (SubstVar e len v)
#endif
