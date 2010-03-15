Module Type Order.

  Parameter (A:Type).

  Parameter (LEQ:A -> A -> bool).

  Parameter (leqRefl: forall x, true = LEQ x x).

  Parameter 
    (leqTransTrue : forall x y z,
      true = LEQ x y ->
      true = LEQ y z ->
      true = LEQ x z).
  Parameter 
    (leqTransFalse : forall x y z,
      false = LEQ x y ->
      false = LEQ y z ->
      false = LEQ x z).

  Parameter
    (leqSymm : forall x y,
      false = LEQ x y ->
      true = LEQ y x).

End Order.

Module Type PQSig.

  Declare Module O:Order.

  Parameter PQ:Type.

  Parameter empty:PQ.

  Parameter insert: O.A -> PQ -> PQ.
  Parameter findMin : PQ -> option O.A.
  Parameter deleteMin : PQ -> PQ.
  Parameter meld : PQ -> PQ -> PQ.

  Parameter In : O.A -> PQ -> Prop.
  Parameter Size : PQ -> nat -> Prop.

  Parameter inTotal :
    forall x p,
      In x p \/ ~ In x p.

  Parameter sizeTotal :
    forall x,
      exists n,
        Size x n.

  Parameter sizeFunction :
    forall x n m,
      Size x n ->
      Size x m ->
      n = m.

  Parameter emptyIn : forall x, ~ In x empty.
  Parameter emptySize : Size empty 0.

  Parameter insertIn : 
    forall y x p, 
      In y (insert x p)
      <->
      (In y p \/ y = x).
  Parameter insertSize : 
    forall p n, Size p n <-> 
      forall x, Size (insert x p) (S n).

  Parameter findMinIn : 
    forall x p, 
      findMin p = Some x <-> 
      (In x p /\ forall y, In y p -> O.LEQ x y = true).
  Parameter findMinSize : forall p, findMin p = None <-> Size p 0.

  Parameter deleteMinIn :
    forall p x,
      findMin p = Some x <->
      (forall y, In y p <->
        In y (insert x (deleteMin p))).
  Parameter deleteMinSizeS : 
    forall p n, 
      Size p (S n) -> Size (deleteMin p) n.
  Parameter deleteMinSizeZ :
    forall p,
      Size p 0 ->
      Size (deleteMin p) 0.

  Parameter meldIn :
    forall p q x,
      In x (meld p q) <->
      (In x p \/ In x q).
  Parameter meldSize :
    forall p q n m,
      Size p n ->
      Size q m ->
      Size (meld p q) (n+m).


  Parameter fmEmpty: 
    forall p,
      findMin p = None
      <->
      p = empty.

  Parameter fmInsert:
    forall y p,
      exists x, 
        findMin (insert y p) = Some x 
        /\ O.LEQ x y = true.

  Parameter fmInsertEmpty:
    forall y, findMin (insert y empty) = Some y.

  Parameter newMin:
    forall x y p,
      findMin p = Some x ->
      O.LEQ x y = false ->
      findMin (insert y p) = Some y.

  Parameter oldMin:
    forall x y p,
      findMin p = Some x ->
      O.LEQ y x = false ->
      findMin (insert y p) = Some x.

  Parameter anyMin:
    forall x y p,
      findMin p = Some x ->
      O.LEQ x y = true ->
      O.LEQ y x = true ->
      (findMin (insert y p) = Some x
       \/ 
       findMin (insert y p) = Some y).

  Parameter dmEmpty : 
    deleteMin empty = empty.

  Parameter dmInsertEmpty :
    forall y,
      deleteMin (insert y empty) = empty.

  Parameter dmMin : 
    forall x y p,
      findMin p = Some x ->
      findMin (deleteMin p) = Some y ->
      O.LEQ y x = true.





  ssd

End PQSig.