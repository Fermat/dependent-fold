{-#OPTIONS --rewriting  #-}
module Section-2 where
open import Equality


data Nat : Set where
  Z : Nat
  S : Nat -> Nat

add : Nat -> Nat -> Nat
add Z n = n
add (S m) n = S (add m n)

data Bush (a : Set) : Set where
  NilB : Bush a
  ConsB : a -> Bush (Bush a) -> Bush a

NTimes : (Set -> Set) -> Nat -> Set -> Set
NTimes p Z s = s
NTimes p (S n) s = p (NTimes p n s)

NBush : Nat -> Set -> Set
NBush = NTimes Bush 

foldB : {a : Set} -> {p : Nat -> Set} ->
             (a -> p Z) ->
             ((n : Nat) -> p (S n)) ->
             ((n : Nat) -> p n -> p (S (S n)) -> p (S n)) ->
             (n : Nat) ->
             NBush n a -> p n
foldB base nil cons Z x = base x
foldB base nil cons (S n) NilB = nil n
foldB base nil cons (S n) (ConsB x xs) = 
  cons n (foldB base nil cons n x) 
         (foldB base nil cons (S (S n)) xs)

-- mapB : {a b : Set} -> (n : Nat) -> (a -> b) -> NBush n a -> NBush n b
-- mapB Z f x = f x
-- mapB (S n) f NilB = NilB
-- mapB (S n) f (ConsB x xs) = ConsB (mapB n f x) (mapB (S (S n)) f xs)

mapB : {a b : Set} -> (n : Nat) -> (a -> b) -> NBush n a -> NBush n b
mapB {a} {b} n f = foldB {a} {\ n -> NBush n b} f (\ n -> NilB) (\ n -> ConsB) n

sumB : Bush Nat -> Nat
sumB = foldB {Nat} {\ n -> Nat} (\ x -> x) (\ n -> Z) (\ n -> add) (S Z) 

lengthB : {a : Set} -> Bush a -> Nat
lengthB {a} = foldB {a} {\ n -> Nat} (\ x -> Z) (\ n -> Z) (\ n r1 r2 -> S r2) (S Z)

bush2 : Bush Nat
bush2 = ConsB (S (S Z)) (ConsB (ConsB (S Z) (ConsB (ConsB (S Z) NilB) NilB)) NilB)


hfoldB : {a : Set} -> {p : Set -> Set} -> 
          ({b : Set} -> p b) -> ({b : Set} -> b -> p (p b) -> p b) -> Bush a -> p a
hfoldB {a} {p} base step =
  foldB {a} {\ n -> NTimes p n a} (\ x -> x) (\ n -> base) (\ n -> step) (S Z)


indB : {a : Set} -> {p : (n : Nat) -> NBush n a -> Set} -> 
             ((x : a) -> p Z x) -> 
             ((n : Nat) -> p (S n) NilB) ->
             ((n : Nat) -> {x : NBush n a} -> {xs : NBush (S (S n)) a} ->
              p n x -> p (S (S n)) xs -> p (S n) (ConsB x xs)) ->
             (n : Nat) ->
             (xs : NBush n a) -> p n xs
indB base nil cons Z xs = base xs
indB base nil cons (S n) NilB = nil n
indB base nil cons (S n) (ConsB x xs) =
  cons n (indB base nil cons n x)
      (indB base nil cons (S (S n)) xs)


identity : {a : Set} -> (n : Nat) -> (y : NBush n a) -> y == mapB n (\ x -> x) y
identity {a} n y =
  indB {a} {\ n v -> v == mapB n (\ x -> x) v} (\ x -> refl)
  (\ n -> refl) (\ n {x} {xs} ih1 ih2 -> cong2 ConsB ih1 ih2) n y

compose : {a b c : Set} -> (b -> c) -> (a -> b) -> (a -> c)
compose g f = \ x -> g (f x)

mapCompose : {a b c : Set} -> (n : Nat) -> (f : b -> c) -> (g : a -> b) ->
 (x : NBush n a) -> mapB n (compose f g) x == mapB n f (mapB n g x)
mapCompose {a} {b} {c} n f g x =
  indB {a} {\ n v -> mapB n (compose f g) v == mapB n f (mapB n g v)}
    (\ v -> refl) (\ n -> refl) (\ n {x1} {xs} ih1 ih2 -> cong2 ConsB ih1 ih2) n x

lemm3 : {a : Set} {p : Set -> Set}
         (n m : Nat) ->  NTimes p (add n m) a == NTimes p n (NTimes p m a) 
lemm3 {a} {p} Z m = refl'
lemm3 {a} {p} (S n) m = cong' p (lemm3 {a} {p} n m)
{-# REWRITE lemm3 #-}

mapNilB : forall {a b : Set} -> (f : a -> b) -> mapB (S Z) f NilB == NilB
mapNilB {a} {b} f = refl

addMap : {a b : Set} -> (n : Nat) -> (f : a -> b) -> (x : NBush (add n n) a) ->
          mapB (add n n) f x == mapB n (mapB n f) x
addMap {a} {b} n f x  = 
  indB {NBush n a} {\ m v -> mapB (add m n) f v == mapB m (mapB n f) v}
       (\ x -> refl) (\ n -> refl) 
       (\ n {x} {xs} ih1 ih2 -> cong2 ConsB ih1 ih2) n x

mapConsB : {a b : Set} -> (f : a -> b) -> (x : a) -> (xs : Bush (Bush a)) ->
           mapB (S Z) f (ConsB x xs) == ConsB (f x) (mapB (S Z) (mapB (S Z) f) xs)
mapConsB {a} {b} f x xs = cong (ConsB (f x)) (addMap {a} {b} (S Z) f xs)

foldBNilB : {a : Set} -> {p : Set -> Set} -> (base : {b : Set} -> p b) ->
            (step : {b : Set} -> b -> p (p b) -> p b) -> 
            hfoldB {a} {p} base step NilB == base
foldBNilB base step = refl

lemmConsB : {a : Set} -> {p : Set -> Set} -> (n : Nat) -> (base : {b : Set} -> p b) ->
        (step : {b : Set} -> b -> p (p b) -> p b) -> (xs : NBush n (NBush n a)) -> 
        foldB {a} {\ y -> NTimes p y a} (\ x -> x)
              (\ n -> base)
              (\ n -> step)
              (add n n) xs == 
        (foldB {NTimes p n a} {\ y -> NTimes p y (NTimes p n a)} (\ x -> x)
               (\ m -> base)
               (\ m -> step) n)
          (mapB n
           (foldB {a} {\ y -> NTimes p y a} (\ x -> x)
                  (\ n -> base)
                  (\ n -> step) n) xs)
lemmConsB {a} {p} n base step xs =
   indB {NBush n a}
    {\ m v ->
       foldB {a} {\ y -> NTimes p y a} (\ x -> x) (\ n -> base) (\ n -> step)
       (add m n) v
       == foldB {NTimes p n a} {\ y -> NTimes p y (NTimes p n a)}
           (\ x -> x) (\ m -> base) (\ m -> step) m
            (mapB m
             (foldB {a} {\ y -> NTimes p y a} (\ x -> x) (\ n -> base) (\ n -> step) n) v)}
    (\ x -> refl) (\ n -> refl) (\ n {x} {xs} ih1 ih2 -> cong2 step ih1 ih2) n xs


foldBConsB : {a : Set} {p : Set -> Set} -> (base : {b : Set} -> p b) ->
             (step : {b : Set} -> b -> p (p b) -> p b) ->
             (x : a) -> (xs : Bush (Bush a)) -> 
             hfoldB base step (ConsB x xs) ==
             step x (hfoldB base step (mapB (S Z) (hfoldB base step) xs))
foldBConsB {a} {p} base step x xs  = cong (step x) (lemmConsB {a} {p} (S Z) base step xs)

lift : {a : Set} {p : Set -> Set}
         (n : Nat) -> (g : {a : Set} -> Bush a -> p a) -> NBush n a -> NTimes p n a
lift {a} {p} Z g x = x
lift {a} {p} (S n) g x = g (mapB (S Z) (lift {a} {p} n g) x)

uniqueness :  (f : {a : Set} -> {p : Set -> Set} -> 
              ({b : Set} -> p b) -> ({b : Set} -> b -> p (p b) -> p b) -> Bush a -> p a) ->
        (hp1 : {a : Set} {p : Set -> Set} -> (base : {b : Set} -> p b) -> 
               (step : {b : Set} -> b -> p (p b) -> p b) ->
               f {a} {p} base step NilB == base) ->
        (hp2 : {a : Set} {p : Set -> Set} -> (base : {b : Set} -> p b) ->
               (step : {b : Set} -> b -> p (p b) -> p b) ->
               (x : a) (xs : Bush (Bush a)) ->
               f base step (ConsB x xs) ==
               step x (f base step (mapB (S Z) (f base step) xs))) ->
        {a : Set} -> {p : Set -> Set} ->        
        (base : {b : Set} -> p b) ->       
        (step : {b : Set} -> b -> p (p b) -> p b) -> (bush : Bush a) ->       
        f {a} {p} base step bush == hfoldB {a} {p} base step bush 
uniqueness f hp1 hp2 {a} {p} base step bush rewrite identity {a} (S Z) bush  =
  indB {a} {\ n v -> lift n (f base step) v == lift n (hfoldB base step) v}
   (\ x -> refl) (\ n -> (trans (hp1 base step) (sym (foldBNilB base step))))
   (\ n {x} {xs} ih1 ih2 ->
    equational (f base step (mapB (S Z) (lift n (f base step)) (ConsB x xs)))
         equals f base step (ConsB (lift n (f base step) x)
                                   (mapB (S (S Z)) (lift n (f base step)) xs))
           by refl
         equals f base step (ConsB (lift n (f base step) x)
                                   (mapB (S Z) (mapB (S Z) (lift n (f base step))) xs))
           by cong ((\ h -> f base step (ConsB (lift n (f base step) x) h)))
                (addMap (S Z) (lift n (f base step)) xs) 
         equals step (lift n (f base step) x)
                      (f base step (mapB (S Z) (f base step)
                                       (mapB (S Z) (mapB (S Z) (lift n (f base step))) xs)))
           by hp2 base step (lift n (f base step) x)
                (mapB (S Z) (mapB (S Z) (lift n (f base step))) xs)
         equals step (lift n (hfoldB base step) x)
                     (f base step (mapB (S Z)
                          (f base step) (mapB (S Z) (mapB (S Z) (lift n (f base step))) xs)))
           by cong
                   (\ h -> step h
                           (f base step (mapB (S Z)
                              (f base step)
                                 (mapB (S Z) (mapB (S Z) (lift n (f base step))) xs))))
                   ih1
         equals step (lift n (hfoldB base step) x)
                     (f base step (mapB (S Z)
                                     (\ x1 -> f base step
                                         (mapB (S Z) (lift n (f base step)) x1)) xs))
           by cong (\ h -> step (lift n (hfoldB base step) x) (f base step h))
               (sym (mapCompose (S Z) (f base step) (mapB (S Z) (lift n (f base step))) xs))
         equals step (lift n (hfoldB base step) x)
                     (hfoldB base step (mapB (S Z)
                                          (\ x1 -> hfoldB base step
                                                    (mapB (S Z)
                                                       (lift n (hfoldB base step)) x1)) xs))
           by cong (step (lift n (hfoldB base step) x)) ih2
         equals step (lift n (hfoldB base step) x)
                     (hfoldB base step
                         (mapB (S Z) (hfoldB base step)
                            (mapB (S Z) (mapB (S Z) (lift n (hfoldB base step))) xs)))
           by cong (\ h -> step (lift n (hfoldB base step) x) (hfoldB base step h))
                   (mapCompose (S Z) 
                     (hfoldB base step) (mapB (S Z) (lift n (hfoldB base step))) xs)
         equals hfoldB base step (ConsB (lift n (hfoldB base step) x)
                                   (mapB (S Z) (mapB (S Z) (lift n (hfoldB base step))) xs))
           by sym (foldBConsB base step
                         (lift n (hfoldB base step) x)
                         (mapB (S Z) (mapB (S Z) (lift n (hfoldB base step))) xs))
         equals hfoldB base step (ConsB (lift n (hfoldB base step) x)
                                    (mapB (S (S Z)) (lift n (hfoldB base step)) xs))
           by cong (\ h -> hfoldB base step (ConsB (lift n (hfoldB base step) x) h))
                    (sym (addMap (S Z) (lift n (hfoldB base step)) xs))
         equals hfoldB base step (mapB (S Z) (lift n (hfoldB base step)) (ConsB x xs))
           by refl)
    (S Z) bush
