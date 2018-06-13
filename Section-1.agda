module Section-1 where
open import Equality

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

add : Nat -> Nat -> Nat
add Z n = n
add (S m) n = S (add m n)

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

infixr 5 _++_
_++_ : {a : Set} -> List a -> List a -> List a
Nil ++ xs = xs
(Cons a as) ++ xs = Cons a (as ++ xs)

fold : {a p : Set} -> p -> (a -> p -> p) -> List a -> p
fold base step Nil = base
fold base step (Cons x xs) = step x (fold base step xs)

ind : {a : Set} {p : List a -> Set} -> p Nil ->
          ((x : a) -> {xs : List a} -> p xs -> p (Cons x xs)) -> (l : List a) -> p l
ind base step Nil = base
ind base step (Cons x xs) = step x {xs} (ind base step xs)

map : {a b : Set} -> (a -> b) -> List a -> List b
map f l = fold Nil (\ a r -> Cons (f a) r) l

sum : List Nat -> Nat
sum l = fold Z (\ x r -> add x r) l

map' : {a b : Set} -> (a -> b) -> List a -> List b
map' f Nil = Nil
map' f (Cons x xs) = Cons (f x) (map' f xs)

lemma1 : {a b : Set} -> (f : a -> b) -> (l : List a) -> map f l == map' f l 
lemma1 {a} {b} f l =  
   ind {a} {\ y -> map f y == map' f y} refl (\ x {xs} ih -> cong (Cons (f x)) ih) l

--- Bush 

data Bush (a : Set) : Set where
  NilB : Bush a
  ConsB : a -> Bush (Bush a) -> Bush a

-- Agda fails to decide the termination of the following functions

hmapB : {b c : Set} -> (b -> c) -> Bush b -> Bush c
hmapB f NilB = NilB
hmapB f (ConsB x xs) = ConsB (f x) (hmapB (hmapB f) xs)

hfoldB : {a : Set} -> {p : Set -> Set} ->
        ({b : Set} -> p b) -> ({b : Set} -> b -> p (p b) -> p b) -> Bush a -> p a
hfoldB base step NilB = base
hfoldB base step (ConsB x xs) =
  step x (hfoldB base step (hmapB (hfoldB base step) xs))





