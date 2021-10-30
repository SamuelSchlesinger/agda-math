module Vectors where

open import Basics
open import Naturals

data Vector : N -> Set -> Set where
  Cons : {n : N} {A : Set} -> (a : A) -> Vector n A -> Vector (S n) A
  Nil : {A : Set} -> Vector Z A

mapVec : {n : N} {A B : Set} -> (f : A -> B) -> Vector n A -> Vector n B
mapVec f Nil = Nil
mapVec f (Cons x xs) = Cons (f x) (mapVec f xs)

append : {n m : N} {A : Set} -> Vector n A -> Vector m A -> Vector (n + m) A
append Nil ys = ys
append (Cons a xs) ys = Cons a (append xs ys)

foldr : {n : N} {A B : Set} -> (A -> B -> B) -> Vector n A -> B -> B
foldr f Nil b = b
foldr f (Cons a as) b = f a (foldr f as b)

index : {n : N} {A : Set} -> Fin n -> Vector n A -> A
index UZ (Cons a _) = a
index (US i) (Cons _ as) = index i as
