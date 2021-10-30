module Circuits where

open import Naturals
open import Basics
open import Agda.Primitive
open import Vectors

data Input : N -> Set where
  MkInput : {n : N} -> (neg : B) -> Fin n -> Input n

data Gate : N -> Set  where
  MkGate : {g : N} -> (dir : B) -> (i : N) -> Vector i (Input g) -> Gate g

data Circuit : N -> N -> N -> N -> Set where
  Layer : {s d n m : N} -> (g : N) -> Vector m (Gate g) -> Circuit s d n g -> Circuit (m + s) (S d) n m
  Inputs : { n : N } -> Circuit n Z n n

executeGate : {g : N} -> Gate g -> Vector g B -> B
executeGate (MkGate dir i vs) inp = foldr (go inp) vs dir where
  op = if dir then and else or
  go : {g : N} -> Vector g B -> Input g -> B -> B
  go vs (MkInput neg u) b = op b (xor neg (index u vs))

executeGates : {m g : N} -> Vector m (Gate g) -> Vector g B -> Vector m B
executeGates Nil v = Nil
executeGates (Cons g gs) v = Cons (executeGate g v) (executeGates gs v)

execute : {s d n m : N} -> Circuit s d n m -> Vector n B -> Vector m B
execute (Layer g gates c) i = executeGates gates (execute c i)
execute Inputs i = i

uncurryVec : {A B : Set} -> (A -> A -> B) -> Vector (S (S Z)) A -> B
uncurryVec f (Cons a (Cons b Nil)) = f a b

executeInputs : {n : N} {i : Vector n B} -> execute (Inputs {n}) i == i
executeInputs = refl

depthZeroAreInputs : {n : N} -> (c : Circuit n Z n n) -> c == Inputs {n}
depthZeroAreInputs Inputs = refl

data SomeCircuit : N -> N -> Set where
  MkSomeCircuit : {s d n m : N} -> Circuit s d n m -> SomeCircuit n m

executeSome : { n m : N } -> SomeCircuit n m -> Vector n B -> Vector m B
executeSome (MkSomeCircuit c) = execute c

xorN : {n : N} -> Vector n B -> B
xorN Nil = false
xorN (Cons b xs) = xor b (xorN xs)

xorNV : {n : N} -> Vector n B -> Vector 1 B
xorNV v = Cons (xorN v) Nil

data False : Set where

openQuestion : Set
openQuestion = {n : N} -> (c : Circuit n 2 n 1) -> ((inp : Vector n B) -> execute c inp == xorNV inp) -> False



