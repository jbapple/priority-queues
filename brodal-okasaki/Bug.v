Set Implicit Arguments.

Require Export List.
Require Export Arith.

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

Section Carrier.

Variable A:Type.
Variable N:Type.
Variable zero : N.
Variable succ : N -> N.
Variable comp : N -> N -> comparison.
Variable toNat : N -> nat.
Variable isoZero : toNat zero = 0.
Variable isoSucc : forall n, toNat (succ n) = S (toNat n).
Variable isoComp : forall n m, comp n m = nat_compare (toNat n) (toNat m).

Fixpoint fromNat (x:nat) : N :=
  match x with
    | 0 => zero
    | S y => succ (fromNat y)
  end.

Inductive Tree :=
  Node : Root -> N -> Many -> Tree
with Root :=
  Top : A -> Many -> Root
with Many :=
  Cil : Many
| Nons : Tree -> Many -> Many.

Notation "[[ x | .. | y ]]" := (Nons x .. (Nons y Cil) ..).
Notation "a ::: b" := (Nons a b) (at level 60, right associativity).
Notation "$" := Cil (at level 60).

Definition rank (x:Tree) :=
  match x with
    | Node _ r _ => r
  end.

Section Order.

Variable (O:ORDER A).

Definition aLEQ := @LEQ _ O.

Definition pLEQ x y :=
  match x,y with
    Top p _, Top q _ => aLEQ p q
  end.
Hint Unfold pLEQ.

Require Export Arith.
Require Export List.
Require Export Program.
Require Export Omega.
Require Export Recdef.
Require Export Coq.Program.Wf.
Require Export caseTactic.


Definition link (x y:Tree) :=
  match x, y with
    | Node v n p, Node w m q =>
      if pLEQ v w 
        then Node v (succ n) (y ::: p)
        else Node w (succ m) (x ::: q)
  end.

Fixpoint ins t xs :=
  match xs with
    | ($) => [[t]]
    | y:::ys =>
      match comp  (rank t) (rank y) with
        | Lt => t:::xs
        | _ => ins (link t y) ys
      end
  end.


Ltac pisp t := 
  unfold aLEQ in *; unfold pLEQ in *; 
  simpl in *;
  match goal with 
    | [ H : _ /\ _ |- _ ] => destruct H; pisp t
    | [ |- _ /\ _ ] => split; pisp t
    | [ _ : false = LEQ ?a ?b |- true = LEQ ?b ?a] 
      => eapply leqSymm; eauto; pisp t
    |  [_ : true = LEQ ?a ?b , 
        _ : true = LEQ ?b ?c 
        |- true = LEQ ?a ?c] 
      => eapply leqTransTrue; eauto; pisp t
    |  [_ : true = LEQ ?a ?b , 
        _ : false = LEQ  ?a ?c 
        |- true = LEQ  ?c ?b] => 
      assert (true = LEQ c a); pisp t
    |  [_ : true = LEQ  ?a ?b , 
        _ : false = LEQ  ?c ?b 
        |- true = LEQ  ?a ?c] => 
    assert (true = LEQ b c); pisp t
    |  [_ : false = LEQ  ?a ?b , 
        _ : false = LEQ  ?b ?c 
        |- true = LEQ  ?c ?a] => 
    assert (false = LEQ a c); pisp t
    |  [_ : false = LEQ  ?a ?b , 
        _ : false = LEQ  ?b ?c 
        |- false = LEQ  ?a ?c] => 
    eapply leqTransFalse; eauto; pisp t
    | [ |- true = LEQ  ?a ?a] => eapply leqRefl; eauto; pisp t
    | [ |- match ?a with | Top _ _ => _ end] => destruct a; auto; pisp t
    | [ _ : match ?a with | Top _ _ => _ end |- _] 
        => destruct a; auto; pisp t
    | _ => auto
  end.

Ltac lisp := pisp auto.

Set Maximal Implicit Insertion.
Implicit Arguments None [A].
Unset Maximal Implicit Insertion.


Ltac hisp := lisp.

Ltac cutLEQ :=
  match goal with
    | [ _ : context[if @LEQ ?x ?y ?a ?b then _ else _] |- _]
      => let ab := fresh a b 
        in remember (@LEQ x y a b) as ab; destruct ab
    | [ |- context[if @LEQ ?x ?y ?a ?b then _ else _] ]
      => let ab := fresh a b 
        in remember (@LEQ x y a b) as ab; destruct ab
  end.

Ltac cutIf :=
  match goal with
    | [ _ : context[if ?x then _ else _] |- _]
      => let xx := fresh x 
        in remember x as xx; destruct xx 
    | [ |- context[if ?x then _ else _] ]
      => let H := fresh x 
        in remember x as H; destruct H
  end.

Ltac cutThis x :=
  let xx := fresh 
    in remember x as xx; destruct xx.

Inductive TreeN :=
  NodeN : RootN -> nat -> ManyN -> TreeN
with RootN :=
  TopN : A -> ManyN -> RootN
with ManyN :=
  CilN : ManyN
| NonsN : TreeN -> ManyN -> ManyN.

Fixpoint toNatT x :=
  match x with
    | Node a b c => NodeN (toNatR a) (toNat b) (toNatM c)
  end
with toNatR x :=
  match x with
    | Top a b => TopN a (toNatM b)
  end
with toNatM x :=
  match x with
    | Cil => CilN
    | Nons a b => NonsN (toNatT a) (toNatM b)
  end.

Fixpoint fromNatT x :=
  match x with
    | NodeN a b c => Node (fromNatR a) (fromNat b) (fromNatM c)
  end
with fromNatR x :=
  match x with
    | TopN a b => Top a (fromNatM b)
  end
with fromNatM x :=
  match x with
    | CilN => Cil
    | NonsN a b => Nons (fromNatT a) (fromNatM b)
  end.

Scheme treen_w := Induction for TreeN Sort Prop
with rootn_w := Induction for RootN Sort Prop
with mln_w := Induction for ManyN Sort Prop.

Combined Scheme alln_ind from treen_w, rootn_w, mln_w.

Notation "[[[ x | .. | y ]]]" := (NonsN x .. (NonsN y CilN) ..).
Notation "a :::: b" := (NonsN a b) (at level 60, right associativity).
Notation "$$" := CilN (at level 60).

Definition rankn (x:TreeN) :=
  match x with
    | NodeN _ r _ => r
  end.


Inductive rankNN : TreeN -> nat -> Prop :=
  singleton : forall x, rankNN (NodeN x 0 ($$)) 0
| simple : forall n v p y,
             rankNN (NodeN v n p) n ->
             rankNN y n ->
             rankNN (NodeN v (S n) (y::::p)) (S n)
| skewA : forall n x y z,
          rankNN x n ->
          rankNN z n ->
          rankNN (NodeN y (S n) [[[x|z]]]) (S n)
| skewB : forall n x v p y,
          rankNN (NodeN v n p) n ->
          rankNN y n ->
          rankNN (NodeN v (S n) ((NodeN x 0 ($$))::::y::::p)) (S n).
Hint Constructors rankNN.

Definition rankN x n := rankNN (toNatT x) n.
Hint Unfold rankN.

Definition rankPN x := rankNN x (rankn x).

Definition rankP x := rankPN (toNatT x).
Hint Unfold rankP.

Inductive posBinaryRankN : ManyN -> nat -> Prop :=
  last : forall x n,
         rankNN x n ->
         posBinaryRankN [[[x]]] n
| next : forall x n m xs,
         rankNN x n ->
         n < m ->
         posBinaryRankN xs m ->
         posBinaryRankN (x::::xs) n.
Hint Constructors posBinaryRankN.

Definition posBinaryRank x n := posBinaryRankN (toNatM x) n.
Hint Unfold posBinaryRank.


Lemma rankDestruct :
  forall v n c m,
    rankN (Node v n c) m ->
    toNat n = m.
Proof.
  intros v n c m r.
  inversion r; subst; auto.
Qed.
Hint Resolve rankDestruct.


Lemma rankDestruct2 :
  forall v n c m,
    rankNN (NodeN v n c) m ->
    n = m.
Proof.
  intros v n c m r.
  inversion r; subst; auto.
Qed.
Hint Resolve rankDestruct2.


Ltac tra0 :=
  match goal with 
    | [H : context[toNat (succ ?x)] |- _]
      => rewrite isoSucc in H; tra0
    | [|- context [toNat (succ ?x)] ]
      => rewrite isoSucc; tra0        
    | [H : context[rankN (Node _ _ _) _] |- _]
      => unfold rankN in H; simpl in H; tra0
    | [|- context[rankN (Node _ _ _) _] ]
      => unfold rankN; simpl; tra0
    | [H : context[posBinaryRank (Node _ _ _) _] |- _]
      => unfold posBinaryRank in H; simpl in H; tra0
    | [|- context[posBinaryRank (Node _ _ _) _] ]
      => unfold posBinaryRank; simpl; tra0
    | _ => auto
  end.


Lemma eq_nat_compare :
  forall x, nat_compare x x = Eq.
Proof.
  induction x; simpl; auto.
Qed.

Lemma insNoDupeHelp : 
  forall n m x xs, 
    rankN x n ->
    posBinaryRank xs m ->
    n <= m ->
    exists k, k >= n /\ posBinaryRank (ins x xs) k.
Proof.
  intros n m x xs xn xsm nm.
  generalize dependent x;
    generalize dependent n. 
  unfold posBinaryRank in xsm.
  generalize dependent isoZero. clear isoZero.
  generalize dependent isoSucc. clear isoSucc.
  generalize dependent isoComp. clear isoComp.
  generalize dependent zero. clear zero.
  dependent induction xsm.
  Case "last".
    clear toNat0 comp0 succ0.
    intros zero isoComp isoSucc isoZero.
    destruct xs; simpl in *. inversion x.
    inversion x; subst. assert (xs = ($)).
    induction xs; auto.
    inversion x; subst. subst. clear x. clear H2.
    intros j jn y yj.
    destruct t as [v xx p]. tra0. hisp.

    assert (toNat xx = n). 
    eapply rankDestruct; eauto.
(* Or: 

   apply rankDestruct2 with (v := toNatR v) (c := toNatM p).
    exact H.*)
    destruct y as [w yy q]. 
    assert (toNat yy = j). eapply rankDestruct; eauto. subst.
    simpl.
    cutThis (comp yy xx).
    SCase "yy = xx".
      rewrite isoComp in HeqH0. symmetry in HeqH0.
      apply nat_compare_eq in HeqH0. clear jn.
      exists (S (toNat yy)); hisp.
      destruct w; destruct v.
      cutLEQ.
      SSCase "a <= a0".
        tra0. unfold posBinaryRank. simpl.
        constructor. tra0.
        apply simple; auto.
        rewrite HeqH0; auto.
      SSCase "a0 < a".
        tra0. unfold posBinaryRank. simpl.
        constructor. tra0. rewrite HeqH0.
        apply simple; auto.
        rewrite <- HeqH0; auto.
    SCase "yy < xx".
      rewrite isoComp in HeqH0. symmetry in HeqH0.
      apply nat_compare_lt in HeqH0. clear jn.
      exists (toNat yy); hisp.
      unfold posBinaryRank. simpl.
      eapply next. tra0. Focus 2.
      apply last. eauto. auto.
    SCase "yy > xx".
      rewrite isoComp in HeqH0. symmetry in HeqH0.
      apply nat_compare_gt in HeqH0. 
      assert False as f. omega. inversion f.

  Case "next".
    clear succ0 comp0 toNat0 O0.
    intros zero isoComp isoSucc isoZero.

    destruct xs; simpl in *. inversion x.
    inversion x; subst. 
    assert (forall n : nat,
      n <= m ->
      forall x : Tree,
        rankN x n -> exists k : nat, k >= n /\ posBinaryRank (ins x xs) k) 
    as IH.
    exact (IHxsm xs O toNat comp succ eq_refl zero isoComp isoSucc isoZero).
    clear IHxsm.
    clear x.
    intros; hisp; tra0.
    destruct x; destruct t; hisp.
    assert (toNat n1 = n0). eapply rankDestruct; eauto.
    tra0. rewrite H1 in xn.
    assert (toNat n2 = n). eapply rankDestruct; eauto.
    tra0. rewrite H2 in H.
    destruct r; destruct r0; hisp.
    cutThis (comp n1 n2).
    SCase "n1 = n2".
      rewrite isoComp in HeqH3. symmetry in HeqH3.
      apply nat_compare_eq in HeqH3. hisp.
      cutLEQ.
      SSCase "a <= a0".

        unfold posBinaryRank; simpl.
        edestruct IH with 
        (x := Node (Top a m2) (succ n1) (Node (Top a0 m3) n2 m1 ::: m0))
        (n := S (toNat n1)).
        omega. tra0.
        apply simple; auto.
        rewrite H1; auto.
        rewrite HeqH3.
        rewrite H2; auto.
        hisp.
        unfold posBinaryRank in H4.
        exists x; hisp. omega.
      SSCase "a > a0".
        unfold posBinaryRank; simpl.
        edestruct IH with 
        (x := Node (Top a0 m3) (succ n2) (Node (Top a m2) n1 m0 ::: m1))
        (n := S (toNat n2)).
        omega. tra0.
        apply simple; auto.
        rewrite H2; auto.
        rewrite <- HeqH3.
        rewrite H1; auto.
        hisp.
        unfold posBinaryRank in H4.
        exists x; hisp. omega.
    SCase "n1 < n2".
      rewrite isoComp in HeqH3. symmetry in HeqH3.
      apply nat_compare_lt in HeqH3.
      exists (toNat n1); hisp.
      omega.
      unfold posBinaryRank. simpl.
      eapply next.
      rewrite H1; auto. Focus 2.
      rewrite H2. eauto.
      rewrite <- H2. auto.
    SCase "n2 < n1".
      rewrite isoComp in HeqH3. symmetry in HeqH3.
      apply nat_compare_gt in HeqH3.
      assert False as f. omega. inversion f.
Qed.

End Order.
End Carrier.