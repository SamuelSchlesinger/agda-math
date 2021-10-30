module Basics where

open import Agda.Primitive

id : {l : Level} -> {A : Set l} -> A -> A
id x = x

-- Booleans

data B : Set where
  true : B
  false : B

set : Set _
set = id B

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

if_then_else : {A : Set} -> B -> A -> A -> A
if_then_else true a a' = a
if_then_else false a a' = a'

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
