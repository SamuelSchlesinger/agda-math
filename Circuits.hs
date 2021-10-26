{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Circuits where

import Numeric.Natural
import Unsafe.Coerce (unsafeCoerce)

data N = Z | S N

data Vec n a where
  Cons :: a -> Vec n a -> Vec ('S n) a 
  Nil :: Vec 'Z a

mapVec :: (a -> b) -> Vec n a -> Vec n b
mapVec f (Cons a b) = Cons (f a) (mapVec f b)
mapVec f Nil = Nil

appendVecEither :: Vec n a -> Vec m b -> Vec (n + m) (Either a b)
appendVecEither v v' = appendVec (mapVec Left v) (mapVec Right v')

appendVec :: Vec n a -> Vec m a -> Vec (n + m) a
appendVec v v' = case v of
  Cons a b -> Cons a (appendVec b v')
  Nil -> v'

instance (Eq a, Eq (Vec n a)) => Eq (Vec ('S n) a) where
  Cons a v == Cons a' v' = a == a' && v == v'

instance Eq (Vec 'Z a) where
  Nil == Nil = True

instance Functor (Vec n) where
  fmap f (Cons a v) = Cons (f a) (fmap f v)
  fmap f Nil = Nil

data Example (n :: N) = Example
  { input :: Vec n Bool
  , output :: Bool
  }

type family (n :: N) + (m :: N) where
  S n + m = S (n + m)
  Z + m = m

data Mod n where
  A :: Mod n -> Mod ('S n)
  B :: Mod n

addMod :: Mod n -> Mod m -> Mod (n + m)
addMod x x' = case x of
  A y -> A (addMod y x')
  B -> unsafeCoerce x' -- Beware, ye who tread here
  

index :: Mod n -> Vec n a -> a
index (A m) (Cons _ v) = index m v
index B (Cons x v) = x

modToNat :: Mod n -> Natural
modToNat = go 0 where 
  go :: Natural -> Mod n -> Natural
  go !s (A m) = go (s + 1) m
  go !s B = s

type GateInputs (n :: N) = GateInputs' n n

data Lit a = Pos a | Neg a

sign :: Lit a -> Bool
sign (Pos _) = True
sign (Neg _) = False

unLit :: Lit a -> a
unLit (Pos a) = a
unLit (Neg a) = a

data GateInputs' (n :: N) (m :: N) where
  MoreInput :: Lit (Mod n) -> GateInputs' n m -> GateInputs' n ('S m)
  EndOfInput :: GateInputs' n m

foldGateInputs :: (Lit (Mod n) -> b -> b) -> GateInputs' n m -> b -> b
foldGateInputs f EndOfInput b = b
foldGateInputs f (MoreInput l m) b = foldGateInputs f m (f l b)

data AC (alt :: Bool) (d :: N) (n :: N) (m :: N) where
  And :: Vec m (GateInputs g) -> AC 'False d n g -> AC 'True ('S d) n m
  Or :: Vec m (GateInputs g) -> AC 'True d n g -> AC 'False ('S d) n m
  Inputs :: AC alt 'Z n n

type One = S Z
type Two = S (S Z)

execute :: AC alt d n m -> Vec n Bool -> Vec m Bool
execute Inputs = id
execute ac = case ac of
  And inputs ac -> f (&&) True inputs . execute ac
  Or inputs ac -> f (||) False inputs . execute ac
  where
    f :: (Bool -> Bool -> Bool) -> Bool -> Vec m (GateInputs g) -> Vec g Bool -> Vec m Bool
    f op e v g = fmap (\i -> foldGateInputs (\l -> op (index (unLit l) g)) i e)  v

(&) :: forall alt d n m n' m'. AC alt d n m -> AC alt d n' m' -> AC alt d (n + n') (m + m')
c & c' = case (c, c') of
  (And gates lowerLayers, And gates' lowerLayers') -> And (mergeGates gates gates') (lowerLayers & lowerLayers')
  (Or gates lowerLayers, Or gates' lowerLayers') -> Or (mergeGates gates gates') (lowerLayers & lowerLayers')
  (Inputs, Inputs) -> Inputs
  where
    mergeGates :: forall m m' g g1. Vec m (GateInputs g) -> Vec m' (GateInputs g1) -> Vec (m + m') (GateInputs (g + g1))
    mergeGates v v' = mapVec _correctGateInputs $ appendVecEither v v'
    correctGateInputs :: Either (GateInputs g) (GateInputs g1) -> GateInputs (g + g1)
    correctGateInputs = \case
      Left gs -> goLeft gs
      Right gs -> goRight gs
      where
        goRight = \case
          MoreInput lit gs -> case lit of
            Pos a -> MoreInput (Pos (a `addMod` _)) (goLeft gs)
          EndOfInput -> EndOfInput
        goLeft = \case
          MoreInput lit gs -> case lit of
            Pos a -> MoreInput (Pos (a `addMod` (B :: Mod g'))) (goLeft gs)
            Neg a -> MoreInput (Neg (a `addMod` (B :: Mod g'))) (goLeft gs)
          EndOfInput -> EndOfInput
