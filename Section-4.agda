{-#OPTIONS --rewriting  #-}
module Section-4 where
open import Section-3
open import Equality



data TermE (a : Set) : Set where
  VarE : a -> TermE a
  AppE : TermE a -> TermE a -> TermE a
  LamE : TermE (Incr (TermE a)) -> TermE a

term1' : TermE Char
term1' = LamE (AppE (VarE Zero) (VarE (Succ (VarE W))))

term2' : TermE Char
term2' = AppE term1'
             (LamE (AppE (AppE (VarE (Succ term1'))
                               (VarE Zero))
                         (LamE (AppE (AppE (VarE (Succ (VarE (Succ term1'))))
                                           (VarE (Succ (VarE Zero))))
                                     (VarE Zero)))))


IncrTermE : Nat -> Set -> Set
IncrTermE = NTimes (\ x -> Incr (TermE x))

foldE : {a : Set} -> {p : Nat -> Set} -> (n : Nat) ->
          (a -> p Z) ->
          ((m : Nat) -> p (S m)) ->
          ((m : Nat) -> p m -> p (S m)) -> 
          ((m : Nat) -> p m -> p m -> p m) ->
          ((m : Nat) -> p (S m) -> p m) -> TermE (IncrTermE n a) -> p n
foldE {a} {p} n varBase varZero varSucc app lam (LamE x) =
  lam n (foldE {a} {p} (S n) varBase varZero varSucc app lam x)
foldE {a} {p} n varBase varZero varSucc app abs (AppE x x') =
  app n (foldE {a} {p} n varBase varZero varSucc app abs x)
        (foldE {a} {p} n varBase varZero varSucc app abs x')
foldE {a} {p} Z varBase varZero varSucc app abs (VarE x) = varBase x
foldE {a} {p} (S n) varBase varZero varSucc app abs (VarE Zero) = varZero n
foldE {a} {p} (S n) varBase varZero varSucc app abs (VarE (Succ x)) =
  varSucc n (foldE {a} {p} n varBase varZero varSucc app abs x)


indE : {a : Set} -> {p : (n : Nat) -> TermE (IncrTermE n a) -> Set} ->
          (n : Nat) ->
          ((x : a) -> p Z (VarE x)) ->
          ((m : Nat) -> p (S m) (VarE Zero)) ->
          ((m : Nat) -> {r : TermE (IncrTermE m a)} -> p m r -> p (S m) (VarE (Succ r))) -> 
          ((m : Nat) -> {x1 : TermE (IncrTermE m a)} -> {x2 : TermE (IncrTermE m a)}
             -> p m x1 -> p m x2 -> p m (AppE x1 x2)) ->
          ((m : Nat) -> {x : TermE (IncrTermE (S m) a)} ->
             p (S m) x -> p m (LamE x)) -> (v : TermE (IncrTermE n a)) -> p n v
indE {a} {p} n varBase varZero varSucc app lam (LamE x) =
  lam n (indE {a} {p} (S n) varBase varZero varSucc app lam x)
indE {a} {p} n varBase varZero varSucc app abs (AppE x x') =
  app n (indE {a} {p} n varBase varZero varSucc app abs x)
        (indE {a} {p} n varBase varZero varSucc app abs x')
indE {a} {p} Z varBase varZero varSucc app abs (VarE x) = varBase x
indE {a} {p} (S n) varBase varZero varSucc app abs (VarE Zero) = varZero n
indE {a} {p} (S n) varBase varZero varSucc app abs (VarE (Succ x)) =
  varSucc n (indE {a} {p} n varBase varZero varSucc app abs x)


mapE : {a b : Set} -> (n : Nat) -> (a -> b) -> TermE (IncrTermE n a) -> TermE (IncrTermE n b)
mapE {a} {b} n f x =
  foldE {a} {\ n -> TermE (IncrTermE n b)} n
  (\ x -> VarE (f x))
  (\ m -> VarE Zero)
  (\ m r -> VarE (Succ r))
  (\ m -> AppE)
  (\ m -> LamE) x


hfoldE : {a : Set} -> {p : Set -> Set} ->
          ({a : Set} -> a -> p a) ->
          ({a : Set} -> p a -> p a -> p a) ->
          ({a : Set} -> p (Incr (p a)) -> p a) -> TermE a -> p a
hfoldE {a} {p} var app lam =
  foldE {a} {\ n -> p (NTimes (\ y -> Incr (p y)) n a)}
    Z var (\ m -> var Zero) (\ m r -> var (Succ r))
    (\ m -> app) (\ m -> lam)
    

substE : {a : Set} -> (n : Nat) -> TermE a -> TermE (IncrTermE n (Incr (TermE a))) ->
         TermE (IncrTermE n a)
substE {a} n s t = 
  foldE {Incr (TermE a)} {\ n -> TermE (IncrTermE n a)} n
  (base s) (\ m -> VarE Zero)  (\ m r -> VarE (Succ r)) (\ m -> AppE) (\ m -> LamE) t
  where base : TermE a -> Incr (TermE a) -> TermE a
        base s Zero = s
        base s (Succ x) = x


redexE : {a : Set} -> TermE a -> TermE a
redexE (AppE (LamE t) s) = substE Z s t
redexE t = t


lemm5 : {a : Set} -> (n : Nat) ->
        NTimes (\ x -> Incr (TermE x)) n (Incr (TermE a)) ==
        NTimes (\ x -> Incr (TermE x)) (S n) a 
lemm5 {a} Z = refl'
lemm5 {a} (S n) = cong' (\ x -> Incr (TermE x)) (lemm5 {a} n)
{-# REWRITE lemm5 #-}

cvtE : {a : Set} -> (n : Nat) -> TermE (IncrTermE n a) -> Term (NIncr n a)   
cvtE {a} n t = foldE {a} {\ n -> Term (NIncr n a)} n
                (\ a -> Var a)
                (\ m -> Var Zero)
                (\ m t' -> mapT Z Succ t')
                (\ m -> App)
                (\ m -> Lam) t

lemmM : {a : Set} (m : Nat) (s : Term a) (t : Term (NIncr m a)) ->
                t == subst m s (mapT {a} {Incr a} m Succ t)
lemmM {a} m s x =
  indT {a} {\ n v -> v == subst n s (mapT {a} {Incr a} n Succ v)} m
  (\ m v -> indI {a} {\ n t -> Var t == subst n s (mapT {a} {Incr a} n Succ (Var t))} m
            (\ x -> refl) (\ m -> refl) (\ x ih -> cong (mapT Z Succ) ih) v)
  (\ m ih1 ih2 -> cong2 App ih1 ih2) (\ m {v} ih -> cong Lam ih) x                

lemmVar : {a : Set} (x : Incr (TermE a)) -> (s : TermE a) ->
           cvtE Z (substE Z s (VarE x)) ==
           subst Z (cvtE Z s) (cvtE (S Z) (VarE x))
lemmVar {a} Zero s = refl
lemmVar {a} (Succ x) s = lemmM {a} Z (cvtE Z s) (cvtE Z x)


           
cvtThm : {a : Set} -> (n : Nat) -> (s : TermE a) ->
         (t : TermE (IncrTermE (S n) a)) ->
           cvtE {a} n (substE n s t) == subst n (cvtE {a} Z s) (cvtE {a} (S n) t)
cvtThm {a} n s t =
     indE {Incr (TermE a)}
      {\ n v -> cvtE {a} n (substE n s v) == subst n (cvtE {a} Z s) (cvtE {a} (S n) v)} n
      (\ x -> lemmVar x s)
      (\ m -> refl)
      (\ m {r} ih ->
       equational cvtE {a} (S m) (substE (S m) s (VarE (Succ r)))
        equals cvtE {a} (S m) (VarE (Succ (substE m s r))) by refl
        equals mapT {NIncr m a} {Incr (NIncr m a)} Z Succ (cvtE {a} m (substE m s r)) by refl
        equals mapT {NIncr m a} {Incr (NIncr m a)} Z Succ
                  (subst m (cvtE {a} Z s) (cvtE {a} (S m) r))
         by cong (mapT {NIncr m a} {Incr (NIncr m a)} Z Succ) ih
        equals subst (S m) (cvtE {a} Z s)
                  (mapT {NIncr (S m) a} {Incr (Incr (NIncr m a))} Z Succ
                    (cvtE {a} (S m) r))
           by mapSubst {a} m (cvtE {a} Z s) (cvtE {a} (S m) r)
        equals subst (S m) (cvtE {a} Z s) (cvtE {a} (S (S m)) (VarE (Succ r))) by refl)
      (\ m {x1} {x2} ih1 ih2 -> cong2 App ih1 ih2) (\ m {x} ih -> cong Lam ih) t


  module abstract-termE where
  -- A local module that use postulation of cmp to prove
  -- a result about the interaction of abstE and substE.
  postulate
    cmp : {a : Set} -> a -> a -> Bool
    axiom1 : {a : Set} -> (x x1 : a) -> cmp x x1 == True -> x == x1

  matchE : {a : Set} -> a -> a -> Incr (TermE a)
  matchE {a} a1 a2 = foldBool {Incr (TermE a)} Zero (Succ (VarE a2)) (cmp a1 a2)

  abstE : {a : Set} -> a -> TermE a -> TermE a
  abstE x t = LamE (mapE Z (matchE x) t)

  lemm0 : {p : Set} -> (x : Bool) -> (x == True -> p) -> (x == False -> p) -> p
  lemm0 {p} =
    indBool {\ x -> (x == True -> p) -> (x == False -> p) -> p}
    (\ h1 h2 -> h1 refl) (\ h1 h2 -> h2 refl)

  lem1 : {a : Set} -> (x y : a) -> (cmp x y == True) ->
     substE Z (VarE x) (mapE Z (matchE x) (VarE y)) == VarE y
  lem1 {a} x y hy rewrite hy = cong VarE (axiom1 {a} x y hy)

  lem2 : {a : Set} -> (x y : a) -> (cmp x y == False) ->
     substE Z (VarE x) (mapE Z (matchE x) (VarE y)) == VarE y
  lem2 {a} x y hy rewrite hy = refl

  lem3 : {a : Set} -> (x y : a) -> 
         substE Z (VarE x) (mapE Z (matchE x) (VarE y)) == VarE y
  lem3 {a} x y = lemm0 (cmp x y) (lem1 x y) (lem2 x y)
  
  thm1 : {a : Set} -> (x : a) -> (t : TermE a) ->
         redexE (AppE (abstE x t) (VarE x)) == t
  thm1 {a} x t =
     indE {a} {\ n v -> substE n (VarE x) (mapE n (matchE x) v) == v} Z
      (lem3 x) (\ m -> refl) (\ m {r} ih -> cong (\ y -> VarE (Succ y)) ih)
      (\ m ih1 ih2 -> cong2 AppE ih1 ih2) (\ m ih -> cong LamE ih) t
