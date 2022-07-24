{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Converter (prToLambda) where

import Data.Type.Equality
import GHC.Natural
import Interpreter (evalSafe)
import Lib.Fin
import Lib.HList
import Lib.Nat
import Lib.SNat (SNat (SZ, Sy))
import Lib.Types (Eval)
import Lib.Vector (Curry, Vec (..), len, uncurry')
import Precs
import Syntax
import Test.QuickCheck (Args (maxDiscardRatio, maxSuccess), isSuccess, quickCheckWithResult, stdArgs)
import TypeChecker (ExpTC (..))

type NatToTy :: Nat -> Ty
type family NatToTy (n :: Nat) = ty | ty -> n where
  NatToTy Z = TyNat
  NatToTy (S n) = (TyNat :-> NatToTy n)

type Plus' :: Nat -> Nat -> Nat
type family Plus' (n :: Nat) (m :: Nat) = res where
  Plus' n Z = n
  Plus' m (S n) = S (Plus' m n)

prToLambda :: SNat m -> PR n -> ExpTC (NatContext m) (NatToTy n)
prToLambda _ Succ = SuccTC
prToLambda e (ConstZero sn) = snatToConstZero e sn
prToLambda e (Proj sn f) = convProj' sn f e
prToLambda e (Comp f gs) =
  convComp e f gs
prToLambda e (PRec g h) = convPR e (compArity g) g h

snatToConstZero :: SNat m -> SNat n -> ExpTC (NatContext m) (NatToTy n)
snatToConstZero _ SZ = NatTC 0
snatToConstZero e (Sy n) = LamTC $ snatToConstZero (Sy e) n

convProj :: SNat m -> Fin (Plus' n m) -> SNat n -> ExpTC (NatContext n) (NatToTy m)
convProj SZ f _ = VarTC $ finToDBNat f
convProj (Sy n) f ctx = case eqPlus n ctx of Refl -> LamTC $ convProj n f (Sy ctx)

convProj' :: SNat m -> Fin m -> SNat n -> ExpTC (NatContext n) (NatToTy m)
convProj' sm f ctx = convProj sm (liftF' ctx (minusF sm f)) ctx

liftF' :: SNat n -> Fin m -> Fin (Plus' n m)
liftF' _ FZero = FZero
liftF' sn (FSuc f) = FSuc $ liftF' sn f

eqPlus :: SNat m -> SNat n -> ('S (Plus' n m) :~: Plus' ('S n) m)
eqPlus SZ _ = Refl
eqPlus (Sy n) h = case eqPlus n h of
  Refl -> Refl

convComp :: SNat o -> PR (S n) -> Vec (S n) (PR m) -> ExpTC (NatContext o) (NatToTy m)
convComp ctx f gs@(g_1 :> _) =
  let arityGs = compArity g_1
      ctx' = enlargeContext ctx arityGs
      cF = prToLambda ctx' f
      cGs = fmap (prToLambda ctx') gs
      vars = mkVars ctx arityGs
      appliedGS = fmap (applyFull vars) cGs
      appliedF = applyFull appliedGS cF
      res = prepLambdas ctx arityGs appliedF
   in res

prepLambdas :: SNat o -> SNat m -> ExpTC (NatContext (Plus' o m)) TyNat -> ExpTC (NatContext o) (NatToTy m)
prepLambdas _ SZ e = e
prepLambdas ctx (Sy sn) e = case eqPlus sn ctx of
  Refl -> LamTC $ prepLambdas (Sy ctx) sn e

mkVars' :: SNat n -> SNat m -> Vec m (Index (Repeat (Plus' n m) 'TyNat) 'TyNat)
mkVars' ctx sn = fmap (finToDBNat . liftF' ctx) (smallerFins sn)

mkVars :: SNat n -> SNat m -> Vec m (ExpTC (Repeat (Plus' n m) 'TyNat) 'TyNat)
mkVars ctx sn = fmap VarTC (mkVars' ctx sn)

convPR :: SNat m -> SNat n -> PR n -> PR (S (S n)) -> ExpTC (NatContext m) (NatToTy (S n))
convPR ctx arityG g h = case eqPlus arityG ctx of
  Refl ->
    let ctx' = Sy $ enlargeContext ctx arityG
        cG = prToLambda ctx' g
        cH = prToLambda (Sy $ Sy ctx') h
        varsG = tail' $ mkVars' ctx (Sy arityG)
        cGapplied = applyFull (fmap VarTC varsG) cG
        z = VarTC ZeroI
        o = VarTC (SuccI ZeroI)
        varsH = o :> (z :> fmap (VarTC . SuccI . SuccI) varsG)
        cHapplied = LamTC $ LamTC $ applyFull varsH cH
        cP'' = AppTC (PRecTC cHapplied) cGapplied
        x_1 = VarTC $ finToDBNat $ liftF' ctx $ snatToFin (Sy arityG)
        cP''' = AppTC cP'' x_1
     in prepLambdas ctx (Sy arityG) cP'''

enlargeContext :: SNat n -> SNat m -> SNat (Plus' n m)
enlargeContext ctx SZ = ctx
enlargeContext ctx (Sy n) = Sy $ enlargeContext ctx n

applyFull :: Vec n (ExpTC e TyNat) -> ExpTC e (NatToTy n) -> ExpTC e TyNat
applyFull VNil e = e
applyFull (v :> vs) e = applyFull vs (AppTC e v)

smallerFins :: SNat n -> Vec n (Fin n)
smallerFins SZ = VNil
smallerFins (Sy n) = snatToFin (Sy n) :> fmap liftF (smallerFins n)

snatToFin :: SNat (S n) -> Fin (S n)
snatToFin (Sy SZ) = FZero
snatToFin (Sy (Sy n)) = FSuc $ snatToFin (Sy n)

decF :: Fin n -> Fin n
decF FZero = FZero
decF (FSuc f) = liftF f

minusF :: SNat n -> Fin n -> Fin n
minusF sn FZero = snatToFin sn
minusF sn (FSuc f) = decF $ minusF sn $ liftF f

type Repeat :: Nat -> a -> [a]
type family Repeat (n :: Nat) a where
  Repeat Z _ = '[]
  Repeat (S n) a = a : Repeat n a

type NatContext n = (Repeat n TyNat)

finToDBNat :: Fin n -> Index (NatContext n) TyNat
finToDBNat FZero = ZeroI
finToDBNat (FSuc f) = SuccI $ finToDBNat f

tail' :: Vec (S n) a -> Vec n a
tail' (_ :> vs) = vs

eqCurryEval :: SNat n -> Curry n :~: Eval (NatToTy n)
eqCurryEval SZ = Refl
eqCurryEval (Sy n) = case eqCurryEval n of Refl -> Refl

prop_eq :: Vec n Natural -> PR n -> Bool
prop_eq vec pr = case eqCurryEval (len vec) of
  Refl -> evalSafePr pr vec == uncurry' (evalSafe HNil $ prToLambda SZ pr) vec

prop_eq' :: SNat n -> Vec n Natural -> PR n -> Bool
prop_eq' sn = prop_eq

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

testConverter :: IO Bool
testConverter =
  isSuccess
    <$> quickCheckWithResult
      stdArgs {maxSuccess = 10000, maxDiscardRatio = 1} -- ,maxSize = 3}
      (prop_eq' (Sy $ Sy SZ))

--
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

monus :: PR ('S ('S 'Z))
monus = PRec (Proj (Sy SZ) FZero) (Comp (PRec (ConstZero SZ) (Proj (Sy $ Sy SZ) (FSuc FZero))) ((:>) (Proj (Sy $ Sy $ Sy SZ) FZero) VNil))

monus' :: Natural -> Natural -> Natural
monus' = evalSafe HNil $ prToLambda SZ monus

add :: PR ('S ('S 'Z))
add = PRec (Proj (Sy SZ) FZero) (Comp Succ ((:>) (Proj (Sy $ Sy $ Sy SZ) FZero) VNil))

add' :: Natural -> Natural -> Natural
add' = evalSafe HNil $ prToLambda SZ add
