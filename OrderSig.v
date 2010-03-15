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