{-#OPTIONS --rewriting  #-}
module Equality where

infix 4 _==_

-- equality is defined for object at any level, including types.
-- for convenience we defined equality as a data type.

data _==_ {a} {A : Set a} (x : A) : A -> Set a where
    Refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REWRITE _==_ #-}

-- term level refl
refl : {a : Set} -> {x : a} -> x == x
refl = Refl

-- any level refl
refl' : forall {l} {a : Set l} -> {x : a} -> x == x
refl' = Refl

-- any level cong
cong' : forall {l} {a b : Set l} -> {m n : a} -> (f : a -> b) -> m == n -> f m == f n
cong' f Refl = Refl

-- term level cong
cong : {a b : Set} -> {m n : a} -> (f : a -> b) -> m == n -> f m == f n
cong f Refl = Refl

-- term level cong2
cong2 : {a b c : Set} -> {m1 n1 : a} -> {m2 n2 : b} -> (f : a -> b -> c) ->
        m1 == n1 -> m2 == n2  -> f m1 m2 == f n1 n2
cong2 f Refl Refl = Refl

-- term level trans
trans : {a : Set} {m n v : a} -> m == n -> n == v -> m == v
trans Refl Refl = Refl

-- term level sym
sym : {a : Set} {m n : a} -> m == n -> n == m
sym Refl = Refl

-- term level equational reasoning
equational_ : {a : Set} -> (x : a) -> x == x
equational_ x = refl
infix 2 equational_
  
_equals_by_ : {a : Set} -> {x y : a} -> x == y -> (z : a) -> y == z -> x == z
_equals_by_ eq c reason = trans eq reason
infixl 1 _equals_by_
