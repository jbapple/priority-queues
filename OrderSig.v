Set Implicit Arguments.

Class ORDER A := Order {

  LEQ : A -> A -> bool; 

  leqRefl: forall x, true = LEQ x x;

  leqTransTrue : forall x y z,
      true = LEQ x y ->
      true = LEQ y z ->
      true = LEQ x z;

  leqTransFalse : forall x y z,
      false = LEQ x y ->
      false = LEQ y z ->
      false = LEQ x z;

  leqSymm : forall x y,
      false = LEQ x y ->
      true = LEQ y x
}.

(*Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].*)
