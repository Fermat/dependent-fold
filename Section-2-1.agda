module Section-2-1 where
open import Equality
open import Section-2


data BushN : Nat -> Set -> Set where
  Base : {a : Set} -> a -> BushN Z a
  NilBN : {a : Set} -> {n : Nat} -> BushN (S n) a
  ConsBN : {a : Set} -> {n : Nat} -> 
            BushN n a -> BushN (S (S n)) a -> BushN (S n) a

foldBN : {a : Set} -> {p : Nat -> Set} ->
         (a -> p Z) ->
         ((n : Nat) -> p (S n)) ->
         ((n : Nat) -> p n -> p (S (S n)) -> p (S n)) ->
         (n : Nat) -> BushN n a -> p n
foldBN base nil cons Z (Base x) = base x
foldBN base nil cons (S n) NilBN = nil n
foldBN base nil cons (S n) (ConsBN x xs) = 
  cons n (foldBN base nil cons n x) (foldBN base nil cons (S (S n)) xs)
         

indBN : {a : Set} -> {p : (n : Nat) -> BushN n a -> Set} -> 
        ((x : a) -> p Z (Base x)) -> 
        ((n : Nat) -> p (S n) NilBN) ->
        ((n : Nat) -> {x : BushN n a} -> {xs : BushN (S (S n)) a} ->
              p n x -> p (S (S n)) xs -> p (S n) (ConsBN x xs)) ->
        (n : Nat) -> (xs : BushN n a) -> p n xs
indBN base nil cons Z (Base x) = base x
indBN base nil cons (S n) NilBN = nil n
indBN base nil cons (S n) (ConsBN x xs) =
  cons n (indBN base nil cons n x) (indBN base nil cons (S (S n)) xs)


to : {a : Set} -> (n : Nat) -> NBush n a -> BushN n a
to {a} n s = foldB {a} {\ n -> BushN n a} Base (\ n -> NilBN) (\ n -> ConsBN) n s

from : {a : Set} -> (n : Nat) -> BushN n a -> NBush n a
from {a} n s = foldBN {a} {\ n -> NBush n a} (\ x -> x) (\ n -> NilB) (\ n -> ConsB) n s 

mapBN : {a b : Set} -> (n : Nat) -> (a -> b) -> BushN n a -> BushN n b
mapBN {a} {b} n f = foldBN {a} {\ n -> BushN n b} (\ x -> Base (f x)) (\ n -> NilBN) (\ n -> ConsBN) n

toFrom : {a : Set} -> (n : Nat) -> (x : NBush n a) -> from n (to n x) == x
toFrom {a} n x =
  indB {a} {\ n v -> from n (to n v) == v} (\ x -> refl) (\ n -> refl)
  (\ n {x} {xs} ih1 ih2 -> cong2 ConsB ih1 ih2) n x 

fromTo : {a : Set} -> (n : Nat) -> (x : BushN n a) -> to n (from n x) == x
fromTo {a} n x =
  indBN {a} {\ n v -> to n (from n v) == v} (\ x -> refl) (\ n -> refl)
  (\ n {x} {xs} ih1 ih2 -> cong2 ConsBN ih1 ih2) n x 

-- The followings are a few theorems about BushN translated from NBush.
-- The translation involves defining conversion functions such as cvtAdd, cvtAdd'
-- For example, the theorem addMapBN is translated from addMap, with the conversion
-- functions applied. We do not translate all the theorems in Section 2 as it becomes
-- unnecessarily laborious.

cvtAdd : {a : Set} -> (n m : Nat) ->  BushN (add n m) a -> BushN n (BushN m a) 
cvtAdd {a} Z m l = Base l
cvtAdd {a} (S n) m NilBN = NilBN
cvtAdd {a} (S n) m (ConsBN l ls) = ConsBN (cvtAdd {a} n m l) (cvtAdd {a} (S (S n)) m ls)

cvtAdd' : {a : Set} -> (n m : Nat) -> BushN n (BushN m a) -> BushN (add n m) a 
cvtAdd' {a} Z m (Base x) = x
cvtAdd' {a} (S n) m NilBN = NilBN
cvtAdd' {a} (S n) m (ConsBN l ls) = ConsBN (cvtAdd' {a} n m l) (cvtAdd' {a} (S (S n)) m ls)

addMapBN : {a b : Set} -> (n : Nat) -> (f : a -> b) -> (x : BushN n (BushN n a)) ->
          (mapBN (add n n) f (cvtAdd' n n x)) == cvtAdd' n n (mapBN n (mapBN n f) x)
addMapBN {a} {b} n f x  = 
  indBN {BushN n a}
   {\ m v ->  (mapBN (add m n) f (cvtAdd' m n v)) == cvtAdd' m n (mapBN m (mapBN n f) v)}
       (\ x -> refl) (\ n -> refl) 
       (\ n {x} {xs} ih1 ih2 -> cong2 ConsBN ih1 ih2) n x

mapNilBN : forall {a b : Set} -> (f : a -> b) -> mapBN (S Z) f NilBN == NilBN
mapNilBN {a} {b} f = refl

mapConsBN : {a b : Set} -> (f : a -> b) -> (x : a) -> (xs : BushN (S Z) (BushN (S Z) a)) ->
           mapBN (S Z) f (ConsBN (Base x) (cvtAdd' (S Z) (S Z) xs)) ==
           ConsBN (Base (f x)) (cvtAdd' (S Z) (S Z) (mapBN (S Z) (mapBN (S Z) f) xs))
mapConsBN {a} {b} f x xs = cong (ConsBN (Base (f x))) (addMapBN {a} {b} (S Z) f xs)



