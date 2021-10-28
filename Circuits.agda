-- Booleans

data B : Set where
  true : B
  false : B

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

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

infixr 2 _==_

-- Equality Combinators

sym : {A : Set} -> {a : A} -> {b : A} ->  (a == b) -> (b == a)
sym refl = refl

trans : {A : Set} -> {a : A} -> {b : A} -> {c : A} -> (a == b) -> (b == c) -> (a == c)
trans refl refl = refl

fun : {A : Set} -> {a : A} -> {b : A} -> (f : A -> A) -> (a == b) -> (f a == f b)
fun f refl = refl

subst : {A : Set} (C : A -> Set) {x y : A} -> x == y -> C x -> C y
subst C refl cx = cx

leftSub : {A : Set} -> {B : Set} -> (f : A -> B) -> (a : A) -> {b : B} -> (a' : A) -> (a == a') -> (f a == b) -> (f a' == b)
leftSub f a a' refl refl = refl

-- Natural Numbers

data N : Set where
  S : N -> N
  Z : N

_+_ : N -> N -> N
Z + m = m
S n + m = S (n + m)

infixr 4 _+_

addLeftIdentity : (n : N) -> Z + n == n
addLeftIdentity Z = refl
addLeftIdentity (S x) = refl

addRightIdentity : (n : N) -> n + Z == n
addRightIdentity Z = refl
addRightIdentity (S x) = fun S (addRightIdentity x)

lemma0 : (n : N) -> (m : N) -> S n + m == n + S m
lemma0 Z m = refl
lemma0 (S n) m = fun S (lemma0 n m)

addCommutative : (n : N) -> (m : N) -> n + m == m + n
addCommutative Z m = sym (addRightIdentity m)
addCommutative (S n) m = leftSub {N} {N} S (m + n) (n + m) (addCommutative m n) (lemma0 m n)

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
    (trans
      (trans
        (addAssociative n m (n * m))
          (trans
            (fun (\x -> x + n * m)
            (addCommutative n m))
          (sym (addAssociative m n (n * m))))
      )
      (fun (\x -> m + x) (lemma1 n m))
    )

mulCommutative : (n : N) -> (m : N) -> n * m == m * n
mulCommutative Z m = mulZero m
mulCommutative (S n) m = leftSub (\x -> m + x) (m * n)(n * m) (mulCommutative m n) (lemma1 m n)

distributive : (a : N) -> (n : N) -> (m : N) -> a * (n + m) == a * n + a * m
distributive Z n m = refl
distributive (S a) n m =
  leftSub (\x -> (n + m) + x) (a * n + a * m) (a * (n + m)) (sym (distributive a n m))
    (trans (sym (addAssociative n m (a * n + a * m)))
    (trans
      (fun (\x -> n + x)
        (trans (addAssociative m (a * n) (a * m))
        (trans (fun (\x -> x + a * m) (addCommutative m (a * n)))
        (sym (addAssociative (a * n) m (a * m))))))
    (addAssociative n (a * n) (m + a * m))))

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
hypMultiplication x (S y) = trans (hypAddition x (hyp (S (S Z)) x y)) (trans (addCommutative (hyp (S (S Z)) x y) x) (fun (\a -> x + a) (hypMultiplication x y)))

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

data UpTo : N -> Set where
  US : {n : N} -> UpTo n -> UpTo (S n)
  UZ : {n : N} -> UpTo n

index : {n : N} {A : Set} -> UpTo n -> Vector (S n) A -> A
index UZ (Cons a _) = a
index (US i) (Cons _ as) = index i as

data Input : N -> Set where
  MkInput : {n : N} -> (neg : B) -> UpTo n -> Input (S n)

data Gate : N -> Set  where
  MkGate : {g : N} -> (dir : B) -> (i : N) -> Vector i (Input g) -> Gate g

data Circuit : N -> N -> N -> Set where
  Layer : {d n m : N} -> (g : N) -> Vector m (Gate g) -> Circuit d n g -> Circuit (S d) n m
  Inputs : { n : N } -> Circuit Z n n

executeGate : {g : N} -> Gate g -> Vector g B -> B
executeGate (MkGate dir i vs) inp = foldr (go inp) vs dir where
  op = if dir then and else or
  go : {g : N} -> Vector g B -> Input g -> B -> B
  go vs (MkInput neg u) b = op b (xor neg (index u vs))

executeGates : {m g : N} -> Vector m (Gate g) -> Vector g B -> Vector m B
executeGates Nil v = Nil
executeGates (Cons g gs) v = Cons (executeGate g v) (executeGates gs v)

execute : {d n m : N} -> Circuit d n m -> Vector n B -> Vector m B
execute (Layer g gates c) i = executeGates gates (execute c i)
execute Inputs i = i

