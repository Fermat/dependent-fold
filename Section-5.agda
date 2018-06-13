module Section-5 where

data I (a : Set) : Set where
  Zero : I a
  Succ : a -> I (I a) -> I a

data D (a b : Set) : Set where
  DNil : D a b
  DCons : a -> b -> D (I a) b -> D (D (I b) (I b)) (I a) -> D a b
  ACons : I b -> D (I (I (D b a))) (D (D b a) (D a b)) -> D a b


data IndexD : Set where
  VarA : IndexD
  VarB : IndexD
  IsD : IndexD -> IndexD -> IndexD
  IsI : IndexD -> IndexD

H : IndexD -> Set -> Set -> Set
H VarA a b = a
H VarB a b = b
H (IsD x y) a b = D (H x a b) (H y a b)
H (IsI x) a b = I (H x a b)

foldD : {a b : Set} {p : IndexD -> Set} ->
       (i : IndexD) ->
       (varA : a -> p VarA) ->
       (varB : b -> p VarB) ->
       (bnil : {i j : IndexD} -> p (IsD i j)) ->
       (bcons : {i j : IndexD} -> p i -> p j -> p (IsD (IsI i) j) ->
                p (IsD (IsD (IsI j) (IsI j)) (IsI i)) -> p (IsD i j)) ->
       (acons : {i j : IndexD} -> p (IsI j) ->
                            p (IsD (IsI (IsI (IsD j i))) (IsD (IsD j i) (IsD i j))) ->
                            p (IsD i j)) ->          
       (zero : {i : IndexD} -> p (IsI i)) ->
       (succ : {i : IndexD} -> p i -> p (IsI (IsI i)) -> p (IsI i)) ->
       H i a b -> p i
foldD {a} {b} {p} VarA varA varB bnil bcons acons zero succ l = varA l
foldD {a} {b} {p} VarB varA varB bnil bcons acons zero succ l = varB l
foldD {a} {b} {p} (IsD i j) varA varB bnil bcons acons zero succ DNil = bnil
foldD {a} {b} {p} (IsD i j) varA varB bnil bcons acons zero succ (DCons x y l v) =
  bcons (foldD {a} {b} {p} i varA varB bnil bcons acons zero succ x)
        (foldD {a} {b} {p} j varA varB bnil bcons acons zero succ y)
        (foldD {a} {b} {p} (IsD (IsI i) j) varA varB bnil bcons acons zero succ l)
        (foldD {a} {b} {p} (IsD (IsD (IsI j) (IsI j)) (IsI i)) varA varB bnil bcons acons zero succ v)
foldD {a} {b} {p} (IsD i j) varA varB bnil bcons acons zero succ (ACons x l) =
  acons (foldD {a} {b} {p} (IsI j) varA varB bnil bcons acons zero succ x)
        (foldD {a} {b} {p} (IsD (IsI (IsI (IsD j i))) (IsD (IsD j i) (IsD i j)))
            varA varB bnil bcons acons zero succ l)
foldD {a} {b} {p} (IsI i) varA varB bnil bcons acons zero succ Zero = zero
foldD {a} {b} {p} (IsI i) varA varB bnil bcons acons zero succ (Succ x y) =
   succ (foldD {a} {b} {p} i varA varB bnil bcons acons zero succ x)
        (foldD {a} {b} {p} (IsI (IsI i)) varA varB bnil bcons acons zero succ y)


mapD : {a b c d : Set} -> (i : IndexD) -> (a -> c) -> (b -> d) -> H i a b -> H i c d
mapD {a} {b} {c} {d} i f g l = foldD {a} {b} {\ i -> H i c d} i f g DNil DCons ACons Zero Succ l 

mapD' : {a b c d : Set} -> (a -> c) -> (b -> d) -> D a b -> D c d
mapD' = mapD (IsD VarA VarB)

mapI : {a c : Set} -> (a -> c) -> I a -> I c
mapI {a} {c} f = mapD {a} {a} {c} {c} (IsI VarA) f f

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

add : Nat -> Nat -> Nat
add Z n = n
add (S m) n = S (add m n)

sumD : D Nat Nat -> Nat
sumD x =  foldD {Nat} {Nat} {\ i -> Nat} (IsD VarA VarB) (\ y -> y) (\ y -> y)
  Z (\ x1 x2 x3 x4 -> add x1 (add x2 (add x3 x4))) add Z add x

sumI : I Nat -> Nat
sumI l = foldD {Nat} {Nat} {\ y -> Nat} (IsI VarA) (\ y -> y) (\ y -> y)
          Z (\ x x1 x2 x3 -> Z) (\ x x1 -> Z) Z add l

iterm : I Nat
iterm = Succ (S (S Z)) (Succ (Succ (S Z) (Succ (Succ (S Z) Zero) Zero)) Zero)

Hp : IndexD -> (Set -> Set -> Set) -> Set -> Set -> Set
Hp VarA p a b = a
Hp VarB p a b = b
Hp (IsD i j) p a b = p (Hp i p a b) (Hp j p a b)
Hp (IsI i) p a b = I (Hp i p a b)

hfoldD : {a b : Set} {p : Set -> Set -> Set} ->
         (dnil : {a b : Set} -> p a b) ->
         (dcons : {a b : Set} -> a -> b -> p (I a) b ->
                     p (p (I b) (I b)) (I a) -> p a b) ->
         (acons : {a b : Set} -> I b ->
                   p (I (I (p b a))) (p (p b a) (p a b)) -> p a b) ->
         D a b -> p a b
hfoldD {a} {b} {p} dnil dcons acons x =
  foldD {a} {b} {\ i -> Hp i p a b} (IsD VarA VarB)
   (\ y -> y) (\ y -> y) dnil dcons acons Zero Succ x

-- An induction principle for D.

indD : {a b : Set} {p : (i : IndexD) -> H i a b -> Set} ->
       (i : IndexD) ->
       (varA : (x : a) -> p VarA x) ->
       (varB : (x : b) -> p VarB x) ->
       (bnil : {i j : IndexD} -> p (IsD i j) DNil) ->
       (bcons : {i j : IndexD} {x : H i a b} {y : H j a b} {l : D (I (H i a b)) (H j a b)} {v : D (D (I (H j a b)) (I (H j a b))) (I (H i a b))} -> p i x -> p j y -> p (IsD (IsI i) j) l ->
                p (IsD (IsD (IsI j) (IsI j)) (IsI i)) v -> p (IsD i j) (DCons x y l v)) ->
       (acons : {i j : IndexD} {x : I (H j a b)} {l : D (I (I (D (H j a b) (H i a b))))
        (D (D (H j a b) (H i a b)) (D (H i a b) (H j a b)))} -> p (IsI j) x ->
                            p (IsD (IsI (IsI (IsD j i))) (IsD (IsD j i) (IsD i j))) l ->
                            p (IsD i j) (ACons x l)) ->          
       (zero : {i : IndexD} -> p (IsI i) Zero) ->
       (succ : {i : IndexD} {x : H i a b} {y : I (I (H i a b))} -> p i x -> p (IsI (IsI i)) y ->    p (IsI i) (Succ x y)) ->
       (l : H i a b) -> p i l
indD {a} {b} {p} VarA varA varB bnil bcons acons zero succ l = varA l
indD {a} {b} {p} VarB varA varB bnil bcons acons zero succ l = varB l
indD {a} {b} {p} (IsD i j) varA varB bnil bcons acons zero succ DNil = bnil
indD {a} {b} {p} (IsD i j) varA varB bnil bcons acons zero succ (DCons x y l v) =
  bcons (indD {a} {b} {p} i varA varB bnil bcons acons zero succ x)
        (indD {a} {b} {p} j varA varB bnil bcons acons zero succ y)
        (indD {a} {b} {p} (IsD (IsI i) j) varA varB bnil bcons acons zero succ l)
        (indD {a} {b} {p} (IsD (IsD (IsI j) (IsI j)) (IsI i)) varA varB bnil bcons acons zero succ v)
indD {a} {b} {p} (IsD i j) varA varB bnil bcons acons zero succ (ACons x l) =
  acons (indD {a} {b} {p} (IsI j) varA varB bnil bcons acons zero succ x)
        (indD {a} {b} {p} (IsD (IsI (IsI (IsD j i))) (IsD (IsD j i) (IsD i j)))
            varA varB bnil bcons acons zero succ l)
indD {a} {b} {p} (IsI i) varA varB bnil bcons acons zero succ Zero = zero
indD {a} {b} {p} (IsI i) varA varB bnil bcons acons zero succ (Succ x y) =
   succ (indD {a} {b} {p} i varA varB bnil bcons acons zero succ x)
        (indD {a} {b} {p} (IsI (IsI i)) varA varB bnil bcons acons zero succ y)


-- The indexed representation of H
data DH : IndexD -> Set -> Set -> Set where
  VarA : {a b : Set} -> a -> DH VarA a b
  VarB : {a b : Set} -> b -> DH VarB a b
  DNil : {a b : Set} {i j : IndexD} -> DH (IsD i j) a b
  DCons : {a b : Set} {i j : IndexD} -> DH i a b -> DH j a b -> DH (IsD (IsI i) j) a b ->
          H (IsD (IsD (IsI j) (IsI j)) (IsI i)) a b -> DH (IsD i j) a b
  ACons : {a b : Set} {i j : IndexD} -> DH (IsI j) a b ->
                            DH (IsD (IsI (IsI (IsD j i))) (IsD (IsD j i) (IsD i j))) a b ->
                            DH (IsD i j) a b 
  Zero : {a b : Set} {i : IndexD} -> DH (IsI i) a b
  Succ : {a b : Set} {i : IndexD} -> DH i a b -> DH (IsI (IsI i)) a b -> DH (IsI i) a b


