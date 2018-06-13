{-#OPTIONS --rewriting  #-}
module Section-3 where
open import Equality

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

data Bool : Set where
  True : Bool
  False : Bool

foldBool : {p : Set} -> p -> p -> Bool -> p 
foldBool x y True = x
foldBool x y False = y

indBool : {p : Bool -> Set} -> p True -> p False -> (v : Bool) -> p v
indBool x y True = x
indBool x y False = y



add : Nat -> Nat -> Nat
add Z n = n
add (S m) n = S (add m n)

data Char : Set where
  W : Char
  V : Char
  LP : Char
  RP : Char
  EMP : Char
  L : Char
  Ze : Char
  Su : Char

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

String : Set
String = List Char

infixr 5 _++_
_++_ : {a : Set} -> List a -> List a -> List a
Nil ++ xs = xs
(Cons a as) ++ xs = Cons a (as ++ xs)

`_` : Char -> String
` x ` = Cons x Nil
----------------------------


data Incr (a : Set) : Set where
  Zero : Incr a
  Succ : a -> Incr a

data Term (a : Set) : Set where
  Var : a -> Term a
  App : Term a -> Term a -> Term a
  Lam : Term (Incr a) -> Term a

term1 : Term Char
term1 = Lam (App (Var (Succ W))
                 (Lam (App (App (Var (Succ Zero))
                                (Var Zero))
                            (Lam (App (App (Var (Succ (Succ Zero)))
                                           (Var (Succ Zero)))
                                      (Var Zero))))))

term2 : Term Char
term2 = Lam (Lam (App (App (Var (Succ Zero)) (Var Zero))
                       (Var (Succ (Succ W)))))


NTimes : (Set -> Set) -> Nat -> Set -> Set
NTimes p Z s = s
NTimes p (S n) s = p (NTimes p n s)

NIncr : Nat -> Set -> Set
NIncr = NTimes Incr


foldI : {a : Set} -> {p : Nat -> Set} -> (n : Nat) ->
          (a -> p Z) ->
          ((m : Nat) -> p (S m)) ->
          ((m : Nat) -> p m -> p (S m)) -> NIncr n a -> p n
foldI Z base zero succ x = base x
foldI (S n) base zero succ Zero = zero n
foldI (S n) base zero succ (Succ x) = succ n (foldI n base zero succ x)


foldI' : {a : Set} -> {p : Set} -> 
          p ->
          (a -> p) -> Incr a -> p
foldI' {a} {p} zero succ = 
 foldI {a} {\ n -> p} (S Z) succ (\ m -> zero) (\ m x -> x)           

mapIncr : {a b : Set} -> (n : Nat) -> (a -> b) -> NIncr n a -> NIncr n b
mapIncr {a} {b} n f y = foldI {a} {\ n -> NIncr n b} n f (\ m -> Zero) (\ m -> Succ) y

num0 : NIncr (S (S (S (S (S Z))))) Char
num0 = Succ (Succ Zero)

num1 : NIncr (S (S (S (S (S (S Z)))))) Char
num1 = mapIncr {Incr (Incr Char)} {Incr (Incr (Incr Char))} (S (S (S Z))) Succ num0

num2 : NIncr (S (S (S (S (S (S Z)))))) Char
num2 = mapIncr {Incr (Incr (Incr Char))} {Incr (Incr (Incr (Incr Char)))} (S (S Z)) Succ num0


foldT : {a : Set} -> {p : Nat -> Set} -> (n : Nat) ->
         ((m : Nat) -> NIncr m a -> p m) ->
          ((m : Nat) -> p m -> p m -> p m) ->
          ((m : Nat) -> p (S m) -> p m) -> Term (NIncr n a) -> p n
foldT {a} {p} n var app lam (Var x) = var n x
foldT {a} {p} n var app lam (App x1 x2) =
   app n (foldT {a} {p} n var app lam x1) (foldT {a} {p} n var app lam x2) 
foldT {a} {p} n var app lam (Lam x) = 
   lam n (foldT {a} {p} (S n) var app lam x)

hfoldT : {a : Set} -> {p : Set -> Set} -> 
         ({a : Set} -> p a) ->
         ({a : Set} -> p a -> p a -> p a) ->
         ({a : Set} -> p (Incr a) -> p a) -> Term a -> p a
hfoldT {a} {p} var app lam =
  foldT {a} {\ n -> p (NTimes Incr n a)} Z (\ m a -> var) (\ m -> app) (\ m -> lam) 




mapT : {a b : Set} -> (n : Nat) -> (a -> b) -> Term (NIncr n a) -> Term (NIncr n b)
mapT {a} {b} n f =
  foldT {a} {\ n -> Term (NIncr n b)} n
    (\ m v -> Var (mapIncr m f v)) (\ m -> App) (\ m -> Lam)


showI : (m : Nat) -> NIncr m String -> String
showI m = foldI {String} {\ n -> String} m (\ x -> x) (\ m -> ` Ze `) (\ m x -> ` Su ` ++ x) 

showT : Term String -> String
showT = foldT {String} {\ n -> String} Z
  showI
  (\ m x y -> ` LP ` ++ x ++ ` EMP ` ++ y ++ ` RP `) 
  (\ m x -> ` L ` ++ x)

showTC : Term Char -> String
showTC x = showT (mapT Z (\ x -> Cons x Nil) x)

lemm4 : {a : Set} -> (n : Nat) -> NTimes Incr n (Incr a) == NTimes Incr (S n) a
lemm4 {a} Z = refl'
lemm4 {a} (S n) = cong' Incr (lemm4 {a} n)
{-# REWRITE lemm4 #-}

varcase : {a : Set} -> (m : Nat) -> Term a -> NIncr m (Incr a) -> Term (NIncr m a)
varcase {a} m s v =
  foldI {Incr a} {\ n -> Term (NIncr n a)} m
   (h s) (\ m -> Var Zero)
        (\ m r -> mapT Z Succ r ) v
  where h : {a : Set} -> Term a -> Incr a -> Term a
        h s Zero = s
        h s (Succ b) = Var b

subst : {a : Set} -> (n : Nat) -> Term a -> Term (NIncr n (Incr a)) -> Term (NIncr n a)
subst {a} n s t =
  foldT {Incr a} {\ n -> Term (NIncr n a)} n
       (\ m -> varcase m s) (\ m -> App) (\ m -> Lam) t

redex : {a : Set} -> Term a -> Term a
redex (App (Lam t) s) = subst Z s t
redex t = t

indT : {a : Set} -> {p : (n : Nat) -> Term (NIncr n a) -> Set} ->
         (n : Nat) ->
         ((m : Nat) -> (v : NIncr m a) -> p m (Var v)) ->
          ((m : Nat) -> {v1 v2 : Term (NIncr m a)} -> p m v1 -> p m v2 -> p m (App v1 v2)) ->
          ((m : Nat) -> {v : Term (NIncr (S m) a)} -> p (S m) v -> p m (Lam v)) ->
          (v : Term (NIncr n a)) -> p n v
indT {a} {p} n var app lam (Var x) = var n x
indT {a} {p} n var app lam (App x1 x2) =
   app n (indT {a} {p} n var app lam x1) (indT {a} {p} n var app lam x2) 
indT {a} {p} n var app lam (Lam x) = 
   lam n (indT {a} {p} (S n) var app lam x)


indI : {a : Set} -> {p : (n : Nat) -> NIncr n a -> Set} -> (n : Nat) ->
          ((x : a) -> p Z x) ->
          ((m : Nat) -> p (S m) Zero) ->
          ((m : Nat) -> {x : NIncr m a} -> p m x -> p (S m) (Succ x)) -> (v : NIncr n a) -> p n v
indI Z base zero succ x = base x
indI (S n) base zero succ Zero = zero n
indI (S n) base zero succ (Succ x) = succ n (indI n base zero succ x)


lemm3 : {a : Set} {p : Set -> Set}
         (n m : Nat) ->  NTimes p (add n m) a == NTimes p n (NTimes p m a) 
lemm3 {a} {p} Z m = refl'
lemm3 {a} {p} (S n) m = cong' p (lemm3 {a} {p} n m)
{-# REWRITE lemm3 #-}

mapTfuse : {a : Set} -> (m n : Nat) -> (s : Term (NIncr (add m n) a)) ->
            mapT {a} {(Incr a)} (S (add m n)) Succ
              (mapT {NIncr n a} {Incr (NIncr n a)} m Succ s) ==
            mapT {NIncr (S n) a} {Incr (NIncr (S n) a)} m Succ
              (mapT {a} {Incr a} (add m n) Succ s)
mapTfuse {a} m n =
  indT {NIncr n a} {\ m s -> mapT {a} {(Incr a)} (S (add m n)) Succ
              (mapT {NIncr (n) a} {Incr (NIncr (n) a)} m Succ s) ==
            mapT {NIncr ((S n)) a} {Incr (NIncr ((S n)) a)} m Succ
              (mapT {a} {Incr (a)} (add m n) Succ s)}
   m (\ m v -> 
       indI {NIncr n a}
            {\ m1 u -> mapT {a} {Incr a} (S (add m1 n)) Succ
                        (mapT {NIncr n a} {NIncr (S n) a} m1 Succ (Var u)) ==
                       mapT {NIncr (S n) a} {NIncr (S (S n)) a} m1 Succ
                        (mapT {a} {Incr a} (add m1 n) Succ (Var u))} m
       (\ x -> refl) (\ m -> refl) (\ m ih -> cong (mapT Z Succ) ih) v)
   (\ m ih1 ih2 -> cong2 App ih1 ih2)
   (\ m ih -> cong Lam ih)


mapTfuseZ : {a : Set} -> (n : Nat) -> (s : Term (NIncr n a)) ->
            mapT {a} {Incr a} (S n) Succ 
                 (mapT {NIncr n a} {Incr (NIncr n a)} Z Succ s) ==
            mapT {Incr (NIncr n a)} {Incr (Incr (NIncr n a))} Z Succ
                 (mapT {a} {Incr a} n Succ s)
mapTfuseZ {a} n s = mapTfuse {a} Z n s        


mapSubst' : {a : Set} -> (n m : Nat) -> (s : Term a) ->
            (t : Term (NIncr (S (add n m)) a)) ->
            mapT {NIncr m a} {NIncr (S m) a} n Succ (subst (add n m) s t)  ==
            subst (S (add n m)) s (mapT {NIncr (S m) a} {NIncr (S (S m)) a} n Succ t)
mapSubst' {a} n m s t =
  indT {NIncr (S m) a} {\ n t ->
        mapT {NIncr m a} {NIncr (S m) a} n Succ (subst (add n m) s t)  ==
        subst (S (add n m)) s (mapT {NIncr (S m) a} {NIncr (S (S m)) a} n Succ t)}
        n
        (\ n v ->
          indI {NIncr (S m) a} {\ n v ->  (mapT {NIncr m a} {NIncr (S m) a} n Succ
          (subst {a} (add n m) s (Var v))) == (subst {a} (S (add n m)) s
          (mapT {NIncr (S m) a} {NIncr (S (S m)) a} n Succ (Var v)))} n
          (\ x -> refl)
          (\ m -> refl)
          (\ n {x} ih ->
              equational mapT {NIncr (m) a} {NIncr ((S m)) a} (S n) Succ
                            (subst (S (add n m)) s (Var (Succ x)))
                 equals mapT {NIncr (m) a} {NIncr ((S m)) a} (S n) Succ
                        (mapT {NIncr (add n m) a} {NIncr (S (add n m)) a} Z Succ
                          (subst (add n m) s (Var x)))
                     by refl
                 equals mapT Z Succ (mapT {NIncr (m) a} {NIncr ((S m)) a} n Succ
                          (subst (add n m) s (Var x)))
                     by mapTfuseZ {NIncr m a} n (subst (add n m) s (Var x))
                 equals mapT Z Succ (subst (S (add n m)) s
                          (mapT {NIncr (S m) a} {NIncr (S (S m)) a} n Succ (Var x)))
                     by cong (mapT Z Succ ) ih
                  equals subst (S (S (add n m))) s
                          (mapT {NIncr (S m) a} {NIncr (S (S m)) a} (S n) Succ (Var (Succ x)))
                     by refl) v)
       (\ m1 ih1 ih2 -> cong2 App ih1 ih2)
       (\ m1 x -> cong Lam x) t

mapSubst : {a : Set} -> (m : Nat) -> (s : Term a) -> (t : Term (NIncr (S m) a)) ->
           mapT Z Succ (subst m s t) == subst (S m) s (mapT Z Succ t)
mapSubst {a} m s t = mapSubst' {a} Z m s t            


  module abstract-term where
  -- A local module that use postulation of cmp to prove
  -- a result about the interaction of abst and subst.
  postulate
    cmp : {a : Set} -> a -> a -> Bool
    axiom1 : {a : Set} -> (x x1 : a) -> cmp x x1 == True -> x == x1

  match : {a : Set} -> a -> a -> Incr a
  match {a} a1 a2 = foldBool {Incr a} Zero (Succ a2) (cmp a1 a2)

  abst : {a : Set} -> a -> Term a -> Term a
  abst x t = Lam (mapT Z (match x) t)

  lemm0 : {p : Set} -> (x : Bool) -> (x == True -> p) -> (x == False -> p) -> p
  lemm0 {p} =
    indBool {\ x -> (x == True -> p) -> (x == False -> p) -> p}
    (\ h1 h2 -> h1 refl) (\ h1 h2 -> h2 refl)

  lemm1 : {a : Set} -> (x x1 : a) -> 
          (cmp x x1 == True) ->
          subst Z (Var x) (mapT {a} {Incr a} Z (match {a} x) (Var x1)) == Var x1
  lemm1 {a} x x1 pf rewrite pf = cong Var (axiom1 {a} x x1 pf)

  lemm2 : {a : Set} -> (x x1 : a) -> 
        (cmp x x1 == False) ->
        subst Z (Var x) (mapT {a} {Incr a} Z (match {a} x) (Var x1)) == Var x1
  lemm2 {a} x x1 pf rewrite pf = refl

  thm0 : {a : Set} -> (x : a) -> (m : Nat) (v : NIncr m a) ->
         subst m (Var x) (mapT m (match x) (Var v)) == Var v
  thm0 {a} x m v =
    indI {a} {\ n u -> subst n (Var x) (mapT n (match x) (Var u)) == Var u} m
    (\ x1 -> lemm0 (cmp x x1) (lemm1 x x1) (lemm2 x x1))
    (\ m -> refl) (\ m {x1} ih -> cong (mapT Z Succ) ih)  v

  thm1 : {a : Set} -> (x : a) -> (t : Term a) ->
         redex (App (abst x t) (Var x)) == t
  thm1 {a} x t =
    indT {a} {\ n v -> subst n (Var x) (mapT n (match x) v) == v} Z
    (thm0 x) (\ m {v1} {v2} ih1 ih2 -> cong2 App ih1 ih2) (\ m {v} ih -> cong Lam ih) t
