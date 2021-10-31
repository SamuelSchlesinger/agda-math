module Vectors where

open import Basics
open import Naturals

-- Beautiful, simple functional code :)

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

eqVector : {n : N} {A : Set} -> (A -> A -> B) -> Vector n A -> Vector n A -> B
eqVector eq Nil Nil = true
eqVector eq (Cons a as) (Cons a' as') = and (eq a a') (eqVector eq as as') 

enumerateFin : (n : N) -> Vector n (Fin n)
enumerateFin Z = Nil
enumerateFin (S n) = Cons UZ (mapVec US (enumerateFin n))

mapIndexLemma :
  { A B : Set }
  -> (n : N)
  -> (f : A -> B)
  -> (v : Vector n A)
  -> (i : Fin n)
  -> f (index i v) == index i (mapVec f v)
mapIndexLemma (S n) f (Cons a as) UZ = refl
mapIndexLemma (S n) f (Cons a as) (US i) =
  leftSub f (index i as) (index (US i) (Cons a as)) refl
    (sym
      (leftSub (index (US i)) (Cons (f a) (mapVec f as)) (mapVec f (Cons a as)) refl
        ( lem1
        ∙ sym (mapIndexLemma n f as i)
        )
      )
    )
  where
    lem1 : index (US i) (Cons (f a) (mapVec f as)) == index i (mapVec f as)
    lem1 = refl

-- AGH! Ye best turn back here.

mapMapLemma :
  { A B C : Set }
  -> (n : N)
  -> (f : A -> B)
  -> (g : B -> C)
  -> (v : Vector n A)
  -> mapVec (\x -> g (f x)) v == mapVec g (mapVec f v)
mapMapLemma Z f g Nil = refl
mapMapLemma (S n) f g (Cons a as) =
  lem1
  ∙ fun (Cons (g (f a))) (mapMapLemma n f g as)
  ∙ lem2
  where
    lem1 : mapVec (\x -> g (f x)) (Cons a as) == Cons (g (f a)) (mapVec (\x -> g (f x)) as) 
    lem1 = refl
    lem2 : Cons (g (f a)) (mapVec g (mapVec f as)) == mapVec g (mapVec f (Cons a as))
    lem2 = refl

mapFoldLemma : 
  {A B X : Set}
  -> (n : N)
  -> (g : X -> A)
  -> (f : A -> B -> B)
  -> (v : Vector n X)
  -> (b : B)
  -> foldr f (mapVec g v) b == foldr (\x b -> f (g x) b) v b
mapFoldLemma Z g f Nil b = refl
mapFoldLemma (S n) g f (Cons x xs) b =
  leftSub (\x -> foldr f x b) (Cons (g x) (mapVec g xs)) (mapVec g (Cons x xs)) refl
    ( fun (\y -> f (g x) y) (mapFoldLemma n g f xs b)
    )

mapAppendLemma :
  { A B : Set }
  -> (n m : N)
  -> (v : Vector n A)
  -> (w : Vector m A)
  -> (f : A -> B)
  -> append (mapVec f v) (mapVec f w) == mapVec f (append v w)
mapAppendLemma Z m Nil w f = refl
mapAppendLemma (S n) m (Cons a as) w f =
  leftSub (\x -> append x (mapVec f w)) (Cons (f a) (mapVec f as)) (mapVec f (Cons a as)) refl
    lem1
  ∙ fun (Cons (f a)) (mapAppendLemma n m as w f)
  ∙ sym lem3
  ∙ sym (leftSub (\x -> mapVec f x) (Cons a (append as w)) (append (Cons a as) w) refl refl)
  where
    lem1 : append (Cons (f a) (mapVec f as)) (mapVec f w) == Cons (f a) (append (mapVec f as) (mapVec f w))
    lem1 = refl
    lem2 : append (Cons a as) w == Cons a (append as w)
    lem2 = refl
    lem3 : mapVec f (Cons a (append as w)) == Cons (f a) (mapVec f (append as w))
    lem3 = refl
