module Naturals where

open import Basics

-- Natural Numbers

data N : Set where
  S : N -> N
  Z : N
{-# BUILTIN NATURAL N #-}

_+_ : N -> N -> N
Z + m = m
S n + m = S (n + m)

_==N_ : N -> N -> B
_==N_ Z Z = true
_==N_ (S n) (S m) = n ==N m
_==N_ _ _ = false

infixr 4 _+_

addLeftIdentity : (n : N) -> Z + n == n
addLeftIdentity n = refl

addRightIdentity : (n : N) -> n + Z == n
addRightIdentity Z = refl
addRightIdentity (S x) = fun S (addRightIdentity x)

lemma0 : (n : N) -> (m : N) -> S n + m == n + S m
lemma0 Z m = refl
lemma0 (S n) m = fun S (lemma0 n m)

addCommutative : (n : N) -> (m : N) -> n + m == m + n
addCommutative Z m = sym (addRightIdentity m)
addCommutative (S n) m =
  leftSub S
    (m + n)
    (n + m)
    (addCommutative m n)
    (lemma0 m n)

addAssociative : (a : N) -> (b : N) -> (c : N) -> a + (b + c) == (a + b) + c
addAssociative Z b c = refl
addAssociative (S a) b c = fun S (addAssociative a b c)

_*_ : N -> N -> N
Z * m = Z
S n * m = m + (n * m)

infixr 6 _*_

mulZero : (m : N) -> Z == m * Z
mulZero Z = refl
mulZero (S n) = mulZero n

lemma1 : (n : N) -> (m : N) -> n + n * m == n * S m
lemma1 Z m = refl 
lemma1 (S n) m =
  fun S
    ( addAssociative n m (n * m)
    ∙ fun (\x -> x + n * m) (addCommutative n m)
    ∙ sym (addAssociative m n (n * m))
    ∙ fun (\x -> m + x) (lemma1 n m)
    )

mulCommutative : (n : N) -> (m : N) -> n * m == m * n
mulCommutative Z m = mulZero m
mulCommutative (S n) m = leftSub (\x -> m + x) (m * n)(n * m) (mulCommutative m n) (lemma1 m n)

distributive : (a : N) -> (n : N) -> (m : N) -> a * (n + m) == a * n + a * m
distributive Z n m = refl
distributive (S a) n m =
  leftSub (\x -> (n + m) + x) (a * n + a * m) (a * (n + m)) (sym (distributive a n m))
    ( (sym (addAssociative n m (a * n + a * m)))
    ∙ fun (\x -> n + x)
        ( addAssociative m (a * n) (a * m)
        ∙ fun (\x -> x + a * m) (addCommutative m (a * n))
        ∙ sym (addAssociative (a * n) m (a * m)))
    ∙ (addAssociative n (a * n) (m + a * m))
    )

-- Hyperoperations

hyp : (n : N) -> (a : N) -> (b : N) -> N
hyp Z a b = S b 
hyp (S Z) a Z = a
hyp (S (S Z)) a Z = Z
hyp (S (S (S n))) a Z = S Z
hyp (S n) a (S b) = hyp n a (hyp (S n) a b)

hypAddition : (x : N) -> (y : N) -> hyp (S Z) x y == y + x
hypAddition x Z = refl
hypAddition x (S y) = fun S (hypAddition x y)

hypMultiplication : (x : N) -> (y : N) -> hyp (S (S Z)) x y == y * x
hypMultiplication x Z = refl
hypMultiplication x (S y) =
    hypAddition x (hyp (S (S Z)) x y)
  ∙ addCommutative (hyp (S (S Z)) x y) x
  ∙ fun (\a -> x + a) (hypMultiplication x y)

data Fin : N -> Set where
  US : {n : N} -> Fin n -> Fin (S n)
  UZ : {n : N} -> Fin (S n)

_==Fin_ : {n : N} -> Fin n -> Fin n -> B
_==Fin_ UZ UZ = true
_==Fin_ (US n) (US m) = n ==Fin m
_==Fin_ _ _ = false

finForgetS : (n : N) -> Fin n -> Fin (S n)
finForgetS (S n) UZ = UZ
finForgetS (S n) (US u) = US (finForgetS n u)

maxFin : (n : N) -> Fin (S n)
maxFin Z = UZ
maxFin (S n) = US (maxFin n)

unFin : {n : N} -> Fin n -> N
unFin UZ = Z
unFin (US u) = S (unFin u)

data _<=_ : N -> N -> Set where
  MkLeq : {n m : N} -> (d : N) -> d + m == n -> m <= n

infixr 2 _<=_

subtract : {a b : N} -> a <= b -> N
subtract (MkLeq d _) = d

zeroBottom : (n : N) -> Z <= n
zeroBottom n = MkLeq n (addRightIdentity n)

transLeq : (a b c : N) -> (a <= b) -> (b <= c) -> (a <= c)
transLeq a b c (MkLeq Z refl) pf' = pf'
transLeq a b c pf (MkLeq Z refl) = pf
transLeq a b c (MkLeq (S d) pf) (MkLeq (S d') pf') = MkLeq (S (S (d + d')))
  ( fun S
    (sym
      (leftSub (\x -> d' + x) (S (d + a)) b pf 
       ( sym (lemma0 d' (d + a))
       ∙ fun S
         ( addAssociative d' d a
         ∙ leftSub (\x -> x + a) (d + d') (d' + d) (addCommutative d d') refl
         )
       )
      )
    )
  ∙ pf'
  )

stripS : (n m : N) -> S n <= S m -> n <= m
stripS n m (MkLeq Z refl) = MkLeq Z refl
stripS n m (MkLeq (S d) refl) = MkLeq (S d) (lemma0 d n)

monotoneS : (x : N) -> (y : N) -> x <= y -> S x <= S y
monotoneS x y (MkLeq d refl) = MkLeq d (sym (lemma0 d x))

plusLeq : (a n m : N) -> n <= m -> a + n <= a + m
plusLeq Z n m = id
plusLeq (S a) n m (MkLeq d refl) = monotoneS (a + n) (a + d + n)
  ( MkLeq d
    ( addAssociative d a n
    ∙ leftSub (\x -> x + n) (a + d) (d + a) (addCommutative a d) (sym (addAssociative a d n))
    )
  )

unFinLeq : (n : N) -> (u : Fin n) -> unFin u <= n
unFinLeq n (US {n1} a) = monotoneS (unFin a) n1 (unFinLeq n1 a)
unFinLeq n UZ = zeroBottom n
