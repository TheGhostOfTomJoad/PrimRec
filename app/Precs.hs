{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Precs (PR (..), evalSafePr) where

import Control.Lens ((??))
import Data.Kind (Type)
import Lib.Fin
import Lib.Nat
import Lib.Vector

data PR :: Nat -> Type where
  Succ :: PR (S Z)
  ConstZero :: PR n
  Proj :: Fin n -> PR n
  Comp :: PR m -> Vec m (PR n) -> PR n
  PRec :: PR n -> PR (S (S n)) -> PR (S n)
  InBuilt :: ArithFun n -> PR n -> PR n

-- deriving instance Show (PR n)

-- evalSafePr (PRec (Proj FZero) (Comp Succ ((:>) (Proj FZero) VNil))) (x:> (y:> VNil )) =  x +y
-- evalSafePr (PRec ConstZero (Comp (PRec (Proj FZero) (Comp Succ ((:>) (Proj FZero) VNil))) ((:>) (Proj FZero) ((:>) (Proj (FSuc (FSuc FZero))) VNil)))) (x:> (y:> VNil )) =  x *y
-- evalSafePr (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) (x:> (y:> VNil )) = max (y -x) 0
-- evalSafePr (PRec ConstZero (Proj (FSuc FZero)))  ((y:> VNil )) = max (y -1) 0
-- evalSafePr (Comp (PRec (Comp Succ ((:>) ConstZero VNil)) ConstZero) ((:>) (Comp (PRec (Proj FZero) (Comp Succ ((:>) (Proj FZero) VNil))) ((:>) (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) ((:>) (Comp (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) ((:>) (Proj (FSuc FZero)) ((:>) (Proj FZero) VNil))) VNil))) VNil)) ((x:> (y:> VNil )) ) = if x == y then 1 else 0
-- evalSafePr (PRec (Comp Succ ((:>) ConstZero VNil)) ConstZero) ((x:> VNil )) =  if x== 0 then 1 else 0
-- evalSafePr (Comp (Comp (Comp (Comp (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) ((:>) (Proj (FSuc FZero)) ((:>) (Proj FZero) VNil))) ((:>) (Comp Succ ((:>) ConstZero VNil)) ((:>) (Proj FZero) VNil))) ((:>) (PRec (Comp Succ ((:>) ConstZero VNil)) ConstZero) VNil)) ((:>) (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) VNil)) ((x:> (y:> VNil )) ) = if x < y then 1 else 0
-- evalSafePr (Comp (PRec (Comp Succ ((:>) ConstZero VNil)) (Comp (PRec ConstZero (Comp (PRec (Proj FZero) (Comp Succ ((:>) (Proj FZero) VNil))) ((:>) (Proj FZero) ((:>) (Proj (FSuc (FSuc FZero))) VNil)))) ((:>) (Proj FZero) ((:>) (Proj (FSuc (FSuc FZero))) VNil)))) ((:>) (Proj (FSuc FZero)) ((:>) (Proj FZero) VNil))) (x:> (y:> VNil )) = x ^ y

-- wrong if y = 0 evalSafePr (PRec ConstZero (Comp (PRec (Proj FZero) (Comp Succ ((:>) (Proj FZero) VNil))) ((:>) (Comp (PRec ConstZero (Comp (PRec (Proj FZero) (Comp Succ ((:>) (Proj FZero) VNil))) ((:>) (Proj FZero) ((:>) (Proj (FSuc (FSuc FZero))) VNil)))) ((:>) (Comp (Comp (Comp (Comp (Comp (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) ((:>) (Proj (FSuc FZero)) ((:>) (Proj FZero) VNil))) ((:>) (Comp Succ ((:>) ConstZero VNil)) ((:>) (Proj FZero) VNil))) ((:>) (PRec (Comp Succ ((:>) ConstZero VNil)) ConstZero) VNil)) ((:>) (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) VNil)) ((:>) (Comp (PRec (Proj FZero) (Comp Succ ((:>) (Proj FZero) VNil))) ((:>) (Proj FZero) ((:>) (Comp Succ ((:>) ConstZero VNil)) VNil))) ((:>) (Proj (FSuc (FSuc FZero))) VNil))) ((:>) (Comp Succ ((:>) (Proj FZero) VNil)) VNil))) ((:>) (Comp (PRec ConstZero (Comp (PRec (Proj FZero) (Comp Succ ((:>) (Proj FZero) VNil))) ((:>) (Proj FZero) ((:>) (Proj (FSuc (FSuc FZero))) VNil)))) ((:>) (Comp (Comp (Comp (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) ((:>) (Proj (FSuc FZero)) ((:>) (Proj FZero) VNil))) ((:>) (Comp Succ ((:>) ConstZero VNil)) ((:>) (Proj FZero) VNil))) ((:>) (Comp (Comp (Comp (Comp (Comp (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) ((:>) (Proj (FSuc FZero)) ((:>) (Proj FZero) VNil))) ((:>) (Comp Succ ((:>) ConstZero VNil)) ((:>) (Proj FZero) VNil))) ((:>) (PRec (Comp Succ ((:>) ConstZero VNil)) ConstZero) VNil)) ((:>) (PRec (Proj FZero) (Comp (PRec ConstZero (Proj (FSuc FZero))) ((:>) (Proj FZero) VNil))) VNil)) ((:>) (Comp (PRec (Proj FZero) (Comp Succ ((:>) (Proj FZero) VNil))) ((:>) (Proj FZero) ((:>) (Comp Succ ((:>) ConstZero VNil)) VNil))) ((:>) (Proj (FSuc (FSuc FZero))) VNil))) VNil)) ((:>) ConstZero VNil))) VNil)))) ( ((x:> (y:> VNil )) ) ) = rem x y
evalSafePr :: PR n -> ArithFun n
evalSafePr ConstZero = const 0
evalSafePr Succ = (+ 1) . safeHead
evalSafePr (Proj n) = (!!! n)
evalSafePr (Comp h gs) =
  evalSafePr h . (??) (fmap evalSafePr gs)
evalSafePr (PRec g h) =
  -- Order of Arguments like in the English Wikipedia
  paraNat (evalSafePr g) (evalSafePr h)
evalSafePr (InBuilt f _) = f

-- simplify :: PR n -> PR n
-- simplify (Comp f gs) = case simplify f of
--   ConstZero -> ConstZero
--   Proj fin -> simplify $ gs !!! fin
--   p -> Comp p $ fmap simplify gs
-- simplify (PRec g h) = PRec (simplify g) (simplify h)
-- simplify p = p

-- (?!) :: Functor f => f (a -> b) -> a -> f b
-- fab ?! a = fmap ($ a) fab
-- fab ?! a = fmap (\f -> f a) fab
