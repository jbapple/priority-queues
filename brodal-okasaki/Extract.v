Require Import Bootstrap.

Extraction Language Haskell.

Extract Inductive option => 
  "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive bool => 
  "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive prod => "(,)" ["(,)"].

Extraction Inline and_rect sig_rect proj1_sig LEQ.
Extraction Inline pLEQ aLEQ meldUniq_terminate.
Extraction Inline 
  preInsert preFindMin preMeld 
  preExtractMin preEmpty preToList.

Extraction "BootExtract.hs" 
  bootPQ empty insert 
  findMin extractMin toList meld.


Require Import List Lt.

Set Implicit Arguments.

Inductive ith_ind (A: Set) : nat -> list A -> A -> Prop:=
| ith_base : forall a l, ith_ind O (a :: l) a
| ith_step : forall n a l b, ith_ind n l b -> ith_ind  (S n) (a :: l) b.

Definition ith_def (A: Set) (l: list A) (n: nat) (H: n < length l) : { a : A | ith_ind n l a }.
  induction l; intros.
    contradict H.
    apply lt_n_O.
    destruct n.
      exists a; apply ith_base.
    simpl in H; apply lt_S_n in H.
    apply IHl in H.
    elim H; intros.
    exists x; apply ith_step; assumption.
Defined.

Fixpoint ith (A: Set) (l: list A) (n: nat) (H: n < length l) : A :=
match ith_def l H with
  exist l' _ => l'
end.

Set Printing Implicit.


Lemma t : forall A l n H x, @ith A l n H = x -> @ith_ind A n l x.
induction l; intros.
unfold length in *. inversion H.
destruct n. simpl in H0. subst. 
constructor.
constructor.
eapply IHl.
rewrite <- H0.
unfold ith_def.
simpl.
rewrite <- H0. simpl in *.
intros.