
data Pair (a : Set) : Set where
  Times : a -> a -> Pair a
  
data BushedTree (a : Set) : Set where
   Leaf : a -> BushedTree a
   Cons : BushedTree (BushedTree a) -> BushedTree a
   Node : BushedTree (Pair a) -> BushedTree a


data Index : Set where
  VarA : Index
  IsBT : Index -> Index
  IsP : Index -> Index

BT : Index -> Set -> Set
BT VarA a = a
BT (IsBT x) a = BushedTree (BT x a)
BT (IsP x) a = Pair (BT x a)

foldBT : {a : Set} {p : Index -> Set} ->
   (i : Index) -> (a -> p VarA) ->
   ({i : Index} -> p i -> p (IsBT i)) ->
   ({i : Index} -> p (IsBT (IsBT i)) -> p (IsBT i)) ->
   ({i : Index} -> p (IsBT (IsP i)) -> p (IsBT i)) ->
   ({i : Index} -> p i -> p i -> p (IsP i)) 
   -> BT i a -> p i
foldBT {a} {p} VarA base leaf cons node times x = base x
foldBT {a} {p} (IsBT i) base leaf cons node times (Leaf x) =
  leaf (foldBT {a} {p} i base leaf cons node times x)
foldBT {a} {p} (IsBT i) base leaf cons node times (Cons x) =
  cons (foldBT {a} {p} (IsBT (IsBT i)) base leaf cons node times x)
foldBT {a} {p} (IsBT i) base leaf cons node times (Node x) =
  node (foldBT {a} {p} (IsBT (IsP i)) base leaf cons node times x)
foldBT {a} {p} (IsP i) base leaf cons node times (Times x y) =
  times (foldBT {a} {p} i base leaf cons node times x)
        (foldBT {a} {p} i base leaf cons node times y)


