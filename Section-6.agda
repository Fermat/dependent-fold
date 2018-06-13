{-# OPTIONS --no-termination --type-in-type --no-positivity #-}
module Section-6 where

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

add : Nat -> Nat -> Nat
add Z n = n
add (S m) n = S (add m n)

data Bush (a : Set) : Set where
  NilB : Bush a
  ConsB : a -> Bush (Bush a) -> Bush a

hmapB : {b c : Set} -> (b -> c) -> Bush b -> Bush c
hmapB f NilB = NilB
hmapB f (ConsB x xs) = ConsB (f x) (hmapB (hmapB f) xs)

-- hfoldB : {a : Set} -> {p : Set -> Set} ->
--          ({b : Set} -> p b) -> ({b : Set} -> b -> p (p b) -> p b) -> Bush a -> p a
-- hfoldB base step NilB = base
-- hfoldB base step (ConsB x xs) =
--   step x (hfoldB base step (hmapB (hfoldB base step) xs))

gfoldB : {a : Set} -> {p q : Set -> Set} ->
        ({b : Set} -> p b) ->
        ({b : Set} -> q b -> p (p b) -> p b) ->
        ({b : Set} -> p b -> q (p b)) ->
        Bush (q a) -> p a
gfoldB base step k NilB = base
gfoldB {a} {p} {q} base step k (ConsB x xs) =
  step x (gfoldB {p a} {p} {q} base step k
      (hmapB (\ y -> k (gfoldB {a} {p} {q} base step k y)) xs))

bush1 : Bush Nat
bush1 = ConsB (S (S Z)) (ConsB (ConsB (S Z) (ConsB (ConsB (S Z) NilB) (ConsB (ConsB (ConsB (S (S Z)) NilB) NilB) NilB))) NilB)

hfoldB : {a : Set} -> {p : Set -> Set} ->
          ({b : Set} -> p b) -> ({b : Set} -> b -> p (p b) -> p b) -> Bush a -> p a
hfoldB {a} {p} base step = gfoldB {a} {p} {\ y -> y} base step (\ y -> y) 

sumB : Bush Nat -> Nat
sumB = gfoldB {Nat} {\ y -> Nat} {\ y -> Nat} Z add (\ x -> x) 

sumAux : {a : Set} -> Bush a -> (a -> Nat) -> Nat
sumAux {a} = hfoldB {a} {\ a -> (a -> Nat) -> Nat} 
               (\ x -> Z) (\ x k f -> add (f x) (k (\ r -> r f)))  

sumB' : Bush Nat -> Nat
sumB' l = sumAux l (\ y -> y)

data Mu (F : (Set -> Set) -> (Set -> Set)) (a : Set) : Set where
  In : F (Mu F) a -> Mu F a

out : {F : (Set -> Set) -> (Set -> Set)} {a : Set} -> Mu F a -> F (Mu F) a
out (In x) = x

infixl 4 _+_
data _+_ : Set -> Set -> Set where
  Inl : {a b : Set} -> a -> a + b
  Inr : {a b : Set} -> b -> a + b

infixl 6 _*_
data _*_ : Set -> Set -> Set where
   Times : {a b : Set} -> a -> b -> a * b

p1 : {a b : Set} -> a * b -> a
p1 (Times x y) = x

p2 : {a b : Set} -> a * b -> b
p2 (Times x y) = y


data Unit : Set where
   unit : Unit
   
mon : (Set -> Set) -> (Set -> Set) -> (Set -> Set) -> Set
mon F H G = {a b : Set} -> (a -> H b) -> F a -> G b

gIt : {F : (Set -> Set) -> (Set -> Set)} {H G : Set -> Set} ->
      ({X : Set -> Set} -> mon X H G -> mon (F X) H G) ->
      {a b : Set} -> (a -> H b) -> Mu F a -> G b
gIt {F} {H} {G} s {a} {b} f (In t) = s (gIt s) f t

BushF : (Set -> Set) -> (Set -> Set)
BushF B a = Unit + a * (B (B a))

Bush' : Set -> Set
Bush' = Mu BushF

BNil : {a : Set} -> Bush' a
BNil = In (Inl unit)

BCons : {a : Set} -> a -> Bush' (Bush' a) -> Bush' a
BCons x xs = In (Inr (Times x xs))

match : {a b t : Set} -> (a + b) -> (a -> t) -> (b -> t) -> t
match (Inl x) f1 f2 = f1 x
match (Inr x) f1 f2 = f2 x

sumAux' : {a : Set} -> (a -> Nat) -> Bush' a -> Nat
sumAux' {a} = gIt {BushF} {\ x -> Nat} {\ x -> Nat}
            (\ {X} r {a} {b} f t ->
                   match t (\ x -> Z)
                           (\ p -> add (f (p1 p))
                                   (r {X a} {b} (r {a} {b} f) (p2 p))))
            {a} {a} 

sumB'' : Bush' Nat -> Nat
sumB'' = sumAux' (\ y -> y)

bush2 : Bush' Nat
bush2 = BCons (S (S Z)) (BCons (BCons (S Z) (BCons (BCons (S Z) BNil)
         (BCons (BCons (BCons (S (S Z)) BNil) BNil) BNil))) BNil)

mfold : {F : (Set -> Set) -> (Set -> Set) } -> {G : Set -> Set} ->
         (m : {X Y : Set -> Set} -> mon X (\ y -> y) Y -> mon (F X) (\ y -> y) (F Y)) ->
         (s : {X : Set} -> F G X -> G X) ->
         mon (Mu F) (\ y -> y) G
mfold {F} {G} m s {a} {b} = gIt {F} {\ y -> y } {G} (\ i f t -> s (m i f t)) {a} {b}          

lift :  {F : (Set -> Set) -> (Set -> Set) } ->
         (m : {X Y : Set -> Set} -> mon X (\ y -> y) Y -> mon (F X) (\ y -> y) (F Y)) ->
         ({X Y : Set} -> (X -> Y) -> (Mu F X -> Mu F Y))
lift m = mfold m In         

fork : {a b c d : Set} -> (a -> c) -> (b -> d) -> (a * b) -> (c * d)
fork f g (Times x y) = Times (f x) (g y)

either : {a b c d : Set} -> (a -> c) -> (b -> d) -> (a + b) -> (c + d)
either f g (Inl x) = Inl (f x)
either f g (Inr x) = Inr (g x)

bushF : {X Y : Set -> Set} -> mon X (\ y -> y) Y -> mon (BushF X) (\ y -> y) (BushF Y)
bushF {X} {Y} s f = either (\ y -> y) (fork f (s (s f)))

mapBush : {X Y : Set} -> (X -> Y) -> (Bush' X -> Bush' Y)
mapBush = mfold bushF In         

