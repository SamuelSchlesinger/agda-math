module Basics where

open import Agda.Primitive

-- Equality

data _==_ {l : Level} {A : Set l} (x : A) : A -> Set where
  refl : x == x

infixr 2 _==_

-- Equality Combinators

sym : {A : Set} -> {a : A} -> {b : A} -> (a == b) -> (b == a)
sym refl = refl

trans : {A : Set} -> {a : A} -> {b : A} -> {c : A} -> (a == b) -> (b == c) -> (a == c)
trans refl refl = refl

_∙_ : {A : Set} -> {a : A} -> {b : A} -> {c : A} -> (a == b) -> (b == c) -> (a == c)
_∙_ = trans

infixr 0 _∙_

fun : {A : Set} -> {a : A} -> {b : A} -> (f : A -> A) -> (a == b) -> (f a == f b)
fun f refl = refl

subst : {A : Set} (C : A -> Set) {x y : A} -> x == y -> C x -> C y
subst C refl cx = cx

leftSub :
     {A B : Set}
  -> (f : A -> B)
  -> (a : A)
  -> {b : B}
  -> (a' : A)
  -> (a == a')
  -> (f a == b)
  -> (f a' == b)
leftSub f a a' refl refl = refl

id : {l : Level} -> {A : Set l} -> A -> A
id x = x

-- Booleans

data B : Set where
  true : B
  false : B

set : Set _
set = id B

not : B -> B
not true = false
not false = true

and : B -> B -> B
and true true = true
and _ _ = false

or : B -> B -> B
or false false = false
or _ _ = true

xor : B -> B -> B
xor false true = true
xor true false = true
xor _ _ = false

deMorgan : (a b : B) -> and a b == not (or (not a) (not b))
deMorgan false false = refl
deMorgan true false = refl
deMorgan false true = refl
deMorgan true true = refl

notSwap : (a b : B) -> not a == b -> a == not b
notSwap false true refl = refl
notSwap true false refl = refl

notElim : (a : B) -> not (not a) == a
notElim true = refl
notElim false = refl

-- This is probably a worse proof than just doing it directly, but I found it interesting to
-- do as an exercise.
deMorgan' : (a b : B) -> not (and (not a) (not b)) == or a b
deMorgan' a b = sym
  ( notSwap (or a b) (and (not a) (not b))
    ( sym
      ( leftSub (\x -> not (or x (not (not b)))) a (not (not a)) (sym (notElim a)) 
        ( leftSub (\x -> not (or a x)) b (not (not b)) (sym (notElim b)) refl
        )
      )
    ∙ sym (deMorgan (not a) (not b))
    )
  )

data _SuchThat_ : (A : Set) -> (f : A -> B) -> Set where
  ST : {A : Set} {f : A -> B} -> (a : A) -> f a == true -> A SuchThat f

data _&_ : (A : Set) -> (f : A -> Set) -> Set where
  Pair : {A : Set} {f : A -> Set} -> (a : A) -> (b : f a) -> A & f

uncurry : { A X : Set} {f : A -> Set} -> (g : (a : A) -> (b : f a) -> X) -> (A & f -> X)
uncurry g (Pair a b) = g a b

curry : {A X : Set} {f : A -> Set} -> (A & f -> X) -> (a : A) -> (b : f a) -> X
curry g a b = g (Pair a b)

if_then_else : {A : Set} -> B -> A -> A -> A
if_then_else true a a' = a
if_then_else false a a' = a'

