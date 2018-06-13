-- {-#OPTIONS --type-in-type #-}
module Section-2-2 where

  data Nat : Set where
    Z : Nat
    S : Nat -> Nat

  CNBush : Nat -> Set -> Set
  CNBush n a = {p : Nat -> Set} ->
               (a -> p Z) ->
               ((n : Nat) -> p (S n)) ->
               ((n : Nat) -> p n -> p (S (S n)) -> p (S n)) ->
               p n

  cbase : {a : Set} -> a -> CNBush Z a
  cbase x = \ base nil cons -> base x
  
  cnil : {a : Set} -> (n : Nat) -> CNBush (S n) a
  cnil n = \ base nil cons -> nil n

  ccons : {a : Set} -> (n : Nat) -> CNBush n a -> CNBush (S (S n)) a -> CNBush (S n) a
  ccons {a} n x xs = \ base nil cons -> cons n (x base nil cons) (xs base nil cons)

  cfoldB : {a : Set} -> {p : Nat -> Set} ->
             (a -> p Z) ->
             ((n : Nat) -> p (S n)) ->
             ((n : Nat) -> p n -> p (S (S n)) -> p (S n)) ->
             (n : Nat) ->
             CNBush n a -> p n
  cfoldB base nil cons n b = b base nil cons             

  cmapB : {a b : Set} -> (n : Nat) -> (a -> b) -> CNBush n a -> CNBush n b
  cmapB {a} {b} n f = 
    cfoldB {a} {\ n -> CNBush n b} (\ x -> cbase (f x)) cnil ccons n  

