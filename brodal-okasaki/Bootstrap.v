Set Implicit Arguments.

Require Export PQSig.
Require Export List.
Require Export Arith.

Section Carrier.

Variable N:Type.
Variable A:Type.
Variable zero : N.
Variable succ : N -> N.
Variable comp : N -> N -> comparison.

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

(*
Set Maximal Implicit Insertion.
Implicit Arguments Cil [A].
Unset Maximal Implicit Insertion.
*)

Scheme tree_w := Induction for Tree Sort Prop
with root_w := Induction for Root Sort Prop
with ml_w := Induction for Many Sort Prop.

Combined Scheme all_ind from tree_w, root_w, ml_w.

Notation "[[ x | .. | y ]]" := (Nons x .. (Nons y Cil) ..).
Notation "a ::: b" := (Nons a b) (at level 60, right associativity).
Notation "$" := Cil (at level 60).

Definition rank (x:Tree) :=
  match x with
    | Node _ r _ => r
  end.

Definition zoot (x:Root) :=
  match x with
    | Top v _ => v
  end.

Definition toot (x:Tree) :=
  match x with
    | Node v _ _ => zoot v
  end.

Definition root (x:Tree) :=
  match x with
    | Node v _ _ => v
  end.

Fixpoint toListT (x:Tree) (r:list A) {struct x} : list A :=
  match x with
    | Node h _ t => toListR h (toListM t r)
  end
with toListR (x:Root) r :=
  match x with
    | Top v t => toListM t (v::r)
  end
with toListM (x:Many) r : list A :=
  match x with
    | Cil => r
    | Nons h t => toListT h (toListM t r)
  end.

Section Order.

Variable (O:ORDER A).

Definition aLEQ := @LEQ _ O.
Definition aLeqRefl := @leqRefl _ O.
Definition aLeqSymm := @leqSymm _ O.
Definition aLeqTransTrue := @leqTransTrue _ O.
Definition aLeqTransFalse := @leqTransFalse _ O.

Fixpoint feapT v (x:Tree) {struct x} : Prop :=
  match x with
    | Node wc n d =>
      feapR v wc
      /\ match wc with
           | Top w c => feapM w d
         end
  end
with feapR v (x:Root) {struct x} : Prop :=
  match x with
    | Top w c => true = aLEQ v w /\ feapM w c
  end
with feapM v (x:Many) {struct x} : Prop :=
  match x with
    | ($) => True
    | x:::xs => feapT v x /\ feapM v xs
  end.

(*
Definition RA := {x:Root | feapR (zoot x) x}.

Definition rLEQ (x y:RA) :=
  match x,y with
    exist (Top p _) _, exist (Top q _) _ => aLEQ p q
  end.
Hint Unfold LEQ.
 
Lemma rLeqRefl: forall x, true = rLEQ x x.
Proof.
  unfold rLEQ.
  destruct x. destruct x.
  auto using aLeqRefl.
Qed.

Lemma rLeqTransTrue : 
  forall x y z,
    true = rLEQ x y ->
    true = rLEQ y z ->
    true = rLEQ x z.
Proof.
  intros. 
  destruct x as [x xf]; destruct x;
    destruct y as [y yf]; destruct y;
      destruct z as [z zf]; destruct z;
        simpl in *.
  eauto using aLeqTransTrue.
Qed.

Lemma rLeqTransFalse :
  forall x y z,
    false = rLEQ x y ->
    false = rLEQ y z ->
    false = rLEQ x z.
Proof.
  intros.
  destruct x as [x xf]; destruct x;
    destruct y as [y yf]; destruct y;
      destruct z as [z zf]; destruct z;
        simpl in *.
  eauto using aLeqTransFalse.
Qed.

Lemma rLeqSymm : 
  forall x y,
    false = rLEQ x y ->
    true = rLEQ y x.
Proof.
  intros.
  destruct x as [x xf]; destruct x;
    destruct y as [y yf]; destruct y;
      simpl in *.
  eauto using aLeqSymm.
Qed.
*)

Definition pLEQ x y :=
  match x,y with
    Top p _, Top q _ => aLEQ p q
  end.
Hint Unfold pLEQ.

Lemma pLeqRefl: forall x, true = pLEQ x x.
Proof.
  unfold pLEQ.
  destruct x. 
  auto using aLeqRefl.
Qed.

Lemma pLeqTransTrue : 
  forall x y z,
    true = pLEQ x y ->
    true = pLEQ y z ->
    true = pLEQ x z.
Proof.
  intros. 
  destruct x;
    destruct y;
      destruct z;
        simpl in *.
  eauto using aLeqTransTrue.
Qed.

Lemma pLeqTransFalse :
  forall x y z,
    false = pLEQ x y ->
    false = pLEQ y z ->
    false = pLEQ x z.
Proof.
  intros.
  destruct x;
    destruct y;
      destruct z;
        simpl in *.
  eauto using aLeqTransFalse.
Qed.

Lemma pLeqSymm : 
  forall x y,
    false = pLEQ x y ->
    true = pLEQ y x.
Proof.
  intros.
  destruct x;
    destruct y;
      simpl in *.
  eauto using aLeqSymm.
Qed.

Instance pOrder : ORDER Root := {
  LEQ := pLEQ;
  leqRefl := pLeqRefl;
  leqSymm := pLeqSymm;
  leqTransTrue := pLeqTransTrue;
  leqTransFalse := pLeqTransFalse
}.

Require Export Arith.
Require Export List.
Require Export Program.
Require Export Omega.
Require Export Recdef.
Require Export Coq.Program.Wf.
Require Export caseTactic.

(* TODO: stability *)

Definition link (x y:Tree) :=
  match x, y with
    | Node v n p, Node w m q =>
      if pLEQ v w 
        then Node v (succ n) (y ::: p)
        else Node w (succ m) (x ::: q)
  end.

Definition skewLink (x y z:Tree) :=
  match x, y, z with
    | Node a i p, 
      Node b j q,
      Node c k r =>
      if pLEQ a b
        then if pLEQ a c
          then Node a (succ  j) [[y | z]]
          else Node c (succ  k) (x:::y:::r)
        else if pLEQ b c
          then Node b (succ  j) (x:::z:::q)
          else Node c (succ  k) (x:::y:::r)
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

Definition uniqify xs :=
  match xs with
    | ($) => ($)
    | y:::ys => ins y ys
  end.

Fixpoint length (x:Many) :=
  match x with
    | ($) => 0
    | _:::xs => S (length xs)
  end.

Definition combLen (xy:Many * Many) := 
  let (x,y) := xy in
    length x + length y.

Function meldUniq (xy:Many * Many) {measure combLen xy} : Many :=
  match xy with
    | (($),y) => y
    | (x,($)) => x
    | (p:::ps,q:::qs) => 
      match comp  (rank p) (rank q) with
        | Lt => p ::: meldUniq (ps, q:::qs)
        | Gt => q ::: meldUniq (p:::ps, qs)
        | Eq => ins (link p q) (meldUniq (ps,qs))
      end
  end.
Proof.
  intros; subst.
  unfold combLen.
  simpl; omega.

  intros; subst.
  unfold combLen.
  simpl; omega.

  intros; subst.
  unfold combLen.
  simpl; omega.
Qed.

Definition skewEmpty : Many := ($).

Definition skewInsert x ys :=
  match ys with
    | z1:::z2:::zr =>
      match comp  (rank z1) (rank z2) with
        | Eq => skewLink (Node x zero  ($)) z1 z2 ::: zr
        | _ => Node x zero ($) ::: ys
      end
    | _ => Node x zero ($) ::: ys
  end.

Definition skewMeld x y :=
  meldUniq (uniqify x, uniqify y).

Fixpoint preFindMinHelp x xs :=
  match xs with 
    | ($) => root x
    | y:::ys => 
      let z := preFindMinHelp y ys in
        let w := root x in
          if pLEQ w z
            then w
            else z
  end.

Definition skewFindMin x :=
  match x with
    | ($) => None
    | y:::ys => Some (preFindMinHelp y ys)
  end.

Fixpoint getMin x xs :=
  match xs with
    | ($) => (x,($))
    | y:::ys =>
      let (t,ts) := getMin y ys in
        if pLEQ (root x) (root t)
          then (x,xs)
          else (t,x:::ts)
  end.

Definition children (x:Tree) :=
  match x with 
    | Node _ _ c => c
  end.

Fixpoint split t x c :=
  match c with
    | ($) => (t,x)
    | d:::ds => 
      match children d with
        | ($) => split t ((root d)::x) ds
        | _ => split (d:::t) x ds
      end
  end.

(*
Definition skewDeleteMin x :=
  match x with
    | ($) => ($)
    | y:::ys =>
      match getMin y ys with
        | (Node _ _ c,t) =>
          let (p,q) := split ($) [] c in
            fold_right preInsert (preMeld t p) q
      end
  end.
*)

Definition skewExtractMin x :=
  match x with
    | ($) => None
    | y:::ys => Some
      match getMin y ys with
        | (Node v _ c,t) => (v,
          let (p,q) := split ($) [] c in
            fold_right skewInsert (skewMeld t p) q)
      end
  end.

Definition skewDeleteMin x :=
  match skewExtractMin x with
    | None => x
    | Some (_,y) => y
  end.

(*
Fixpoint skewToListT (x:Tree) (r:list Root) {struct x} : list Root :=
  match x with
    | Node h _ t => h :: (skewToListM t r)
  end
with skewToListM (x:Many) r : list Root :=
  match x with
    | Cil => r
    | Nons h t => skewToListT h (skewToListM t r)
  end.

Definition skewToList x := skewToListM x nil.

Instance skewBin : @MINQ _ Many _ := {
  empty := skewEmpty;
  insert := skewInsert;
  findMin := skewFindMin;
  extractMin := skewExtractMin;
  toList := skewToList;
  meld := skewMeld
}.

End Order.
End Carrier.

Print skewBin.

Extraction Language Haskell.
Recursive Extraction skewBin.
*)

Lemma Nil : forall x, feapM x ($).
Proof.
  unfold feapM. simpl. auto.
Qed.
Hint Resolve Nil.

Definition oomin {t} `{ORDER t} (x y:t) :=
  if LEQ x y
    then x
    else y.

Definition amin x y := @oomin A O x y.

Lemma minLess :
  forall {t} `{ORDER t} (x y:t),
    true = LEQ (oomin x y) x
    /\ true = LEQ (oomin x y) y.
Proof.
  intros; unfold oomin.
  remember (LEQ x y) as xy; destruct xy;
    split; auto.
  apply leqRefl.
  apply leqSymm; auto.
  apply leqRefl.
Qed.

Lemma minLeft :
  forall {t} `{ORDER t} (x y:t),
    true = LEQ (oomin x y) x.
Proof.
  intros; unfold oomin.
  remember (LEQ x y) as xy; destruct xy;
     auto.
  apply leqRefl.
  apply leqSymm; auto.
Qed.

Check minLeft. Print minLeft.

Lemma dblMin : forall {t} `{ORDER t} (x:t), oomin x x = x.
Proof.
  unfold oomin.
  intros. rewrite <- leqRefl; auto.
Qed.

Ltac pisp t := 
  unfold aLEQ in *; unfold pLEQ in *; unfold amin in *;
  simpl in *;
  match goal with
    | [ |- true = LEQ (oomin ?a ?b) ?a] 
        => apply minLess; pisp t
    | [ |- true = LEQ (oomin ?a ?b) ?b] 
        => apply minLess; pisp t
    | [ H : _ /\ _ |- _ ] => destruct H; pisp t
    | [ |- _ /\ _ ] => split; pisp t
(*    | [ H : feapT _ |- _ ] => destruct H; lisp
    | [ H : feapR _ |- _ ] => destruct H; lisp
    | [ H : feapM _ |- _ ] => destruct H; lisp *)
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

Lemma heapLess :
  (forall x a b, 
    true = aLEQ a b -> 
    feapT b x -> 
    feapT a x)
  /\ (forall x a b, 
    true = aLEQ a b -> 
    feapR b x -> 
    feapR a x)
  /\ (forall x a b, 
    true = aLEQ a b -> 
    feapM b x -> 
    feapM a x).
Proof.
  apply all_ind; intros; lisp. 
  eapply H; eauto. 
  eapply H0; eauto.
Qed.
Hint Resolve heapLess.

Ltac lessHeapTac :=
  match goal with
    | [ _ : true = LEQ ?a ?b,
        _ : feapT ?b ?x
       |- feapT ?a ?x] 
      => eapply heapLess with b; lisp
    | [ _ : true = LEQ ?a ?b,
        _ : feapR ?b ?x
       |- feapR ?a ?x] 
      => eapply heapLess with b; lisp
    | [ _ : true = LEQ ?a ?b,
        _ : feapM ?b ?x
       |- feapM ?a ?x] 

      => eapply heapLess with b; lisp
    | [ _ : feapM ?b ?x
       |- feapM (oomin ?a ?b) ?x] 
      => eapply heapLess with b; lisp
    | [ _ : feapM ?a ?x
       |- feapM (oomin ?a ?b) ?x] 
      => eapply heapLess with a; lisp

    | [ _ : feapR ?b ?x
       |- feapR (oomin ?a ?b) ?x] 
      => eapply heapLess with b; lisp
    | [ _ : feapR ?a ?x
       |- feapR (oomin ?a ?b) ?x] 
      => eapply heapLess with a; lisp

    | [ _ : feapT ?b ?x
       |- feapT (oomin ?a ?b) ?x] 
      => eapply heapLess with b; lisp
    | [ _ : feapT ?a ?x
       |- feapT (oomin ?a ?b) ?x] 
      => eapply heapLess with a; lisp
    | _ => lisp
  end.

Ltac hisp := repeat lessHeapTac.

Lemma Cons : 
  forall xs a x b, 
    feapT a x ->
    feapM b xs ->
    feapM (amin a b) (x:::xs).
Proof.
  simpl.
  induction xs as [|y ys I]; simpl; intros a x b X XS; 
    hisp.
Qed.
Hint Resolve Cons.

Lemma lone : 
  forall a v n, 
    feapR a v ->
    exists b, feapT b (Node v n ($)).
Proof.
  unfold feapR; unfold feapT; intros.
  destruct v as [x c].
  exists x.
  lisp.
Qed.
Hint Resolve lone.

Ltac cutMin x := 
  eapply aLeqTransTrue with x; hisp.

(*
Ltac cutMin  :=
  match goal with
    | [ |- ?v
  assert (true = aLEQ (amin a b) c); hisp.
*)

Lemma top : forall a b v n n' w m m' p ys,
  feapT a (Node v n ys) ->
  true = pLEQ v w ->
  feapT b (Node w m' p) ->
  feapT (amin a b) (Node v n' ((Node w m p) ::: ys)).
Proof.
  intros; hisp.
  cutMin a.
Qed.
Hint Resolve top.

Ltac cutLEQ :=
  match goal with
    | [ _ : context[if @LEQ ?x ?y ?a ?b then _ else _] |- _]
      => let ab := fresh a b 
        in remember (@LEQ x y a b) as ab; destruct ab
    | [ |- context[if @LEQ ?x ?y ?a ?b then _ else _] ]
      => let ab := fresh a b 
        in remember (@LEQ x y a b) as ab; destruct ab
  end.

Lemma linkHeap :
  forall v x w y, 
    feapT v x -> 
    feapT w y -> 
    feapT (amin v w) (link x y).
Proof.
  intros v x w y X Y.
  unfold link.
  destruct x; destruct y; hisp.
  cutLEQ; hisp.
  cutMin v.
  cutMin w.
Qed.
Hint Resolve linkHeap.

Lemma skewLinkHeap :
  forall R x U y T z, 
    feapR R x -> 
    feapT T y -> 
    feapT U z -> 
    feapT (amin R (amin U T)) (skewLink (Node x zero ($)) y z).
Proof.
  unfold skewLink.
  intros; hisp.
  destruct y; destruct z; destruct x; hisp.
  cutLEQ; hisp.
  cutLEQ; hisp.
  cutMin R.
  cutMin U.
  cutMin (amin U T).
  cutLEQ; hisp.
  cutMin T. cutMin (amin U T).
  cutMin U. cutMin (amin U T).
Qed.
Hint Resolve skewLinkHeap.

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


Lemma preInsertHeapLess :
  forall a x,
    feapR  a x ->
    forall b ys,
      feapM  b ys ->
      feapM  (amin a b) (skewInsert x ys).
Proof.
  intros; destruct ys; hisp.
  destruct ys; hisp.
  cutThis (comp (rank t) (rank t0)).
  destruct t; destruct t0; destruct x; hisp.
  cutLEQ; hisp. cutLEQ; hisp.
  cutMin a. cutMin b.
  cutLEQ; hisp. cutMin b.
  cutMin b.

  hisp. hisp.
Qed.
Hint Resolve preInsertHeapLess.

Ltac heapCut x := eapply heapLess with x; hisp.

Lemma insHeapSome : 
  forall xs a x b,
    feapT a x ->
    feapM b xs ->
    feapM (amin a b) (ins x xs).
Proof.
  induction xs; hisp; intros; hisp.
  cutThis (comp (rank x) (rank t)); hisp.
  heapCut (amin (amin a b) b).
  unfold oomin. repeat (cutLEQ; hisp).
  inversion Heqab.
  heapCut (amin (amin a b) b).
  unfold oomin. repeat (cutLEQ; hisp).
  inversion Heqab.
Qed.
Hint Resolve insHeapSome.
 
Lemma meldUniqHeapSome :
  forall a x b y,
    feapM a x ->
    feapM b y ->
    feapM (amin a b) (meldUniq (x,y)).
Proof.
  assert 
    (let P := 
      fun (xy:(Many*Many)) r =>
        let (x,y) := xy in
          forall a b,
          feapM a x ->
          feapM b y ->
          feapM (amin a b) r
            in forall xy, P xy (meldUniq xy)).
  eapply meldUniq_ind; intros; hisp.
  heapCut (amin (amin a b) (amin a b)); hisp.
  unfold oomin; repeat (cutLEQ; hisp).
  
  intros. simpl in H.
  pose (H (x,y)) as Hxy.
  simpl in Hxy.
  eapply Hxy. auto. eauto. 
Qed.
Hint Resolve meldUniqHeapSome.

Lemma uniqifyHeap :
  forall a x, 
    feapM a x ->
    feapM a (uniqify x).
Proof.
  unfold uniqify; hisp.
  intros; destruct x; hisp.
  erewrite <- (dblMin a).
  apply insHeapSome; auto.
Qed.

Lemma preMeldHeapSome : 
  forall a x b y,
    feapM a x ->
    feapM b y ->
    feapM (amin a b) (skewMeld x y).
Proof.
  intros; hisp.
  unfold skewMeld; hisp.
  apply meldUniqHeapSome;
    apply uniqifyHeap;
      hisp.
Qed.
Hint Resolve preMeldHeapSome.

Lemma getMinTHeap :
  forall xs a x b,
    feapT a x ->
    feapM b xs ->
    forall y z, (y,z) = getMin x xs ->
      feapT (amin a b) y.
Proof.
  induction xs; intros; hisp.
  inversion_clear H1; subst; hisp.
  cutThis (getMin t xs).
  destruct x; destruct t0; hisp.
  destruct r0; hisp.
  cutLEQ; hisp.
  inversion_clear H1; subst; hisp.
  cutMin a.
  eapply IHxs in HeqH3; eauto.
  rewrite dblMin in HeqH3.
  inversion_clear H1; subst; hisp.
Qed.
Hint Resolve getMinTHeap.

Lemma getMinQHeap :
  forall xs a x b,
    feapT a x ->
    feapM b xs ->
    forall y z, (y,z) = getMin x xs ->
(*
      true = OO.LEQ (toot y) (toot x) /\
      feapM (toot y) xs /\
*)
      feapM (toot y) z
      /\ feapM (toot y) xs
      /\ feapT (toot y) x.
Proof.
  induction xs; intros; hisp.
  inversion_clear H1; subst; hisp.
  inversion_clear H1; subst; hisp.
  destruct x; hisp.
  cutThis (getMin t xs). 
  destruct x; destruct t0; hisp.
  destruct r0; hisp.
  cutLEQ; hisp.
  inversion_clear H1; subst; hisp.
  eapply IHxs in HeqH3; eauto; hisp.
  eapply IHxs in HeqH3; eauto; hisp.
  inversion_clear H1; subst; hisp.
  eapply IHxs in HeqH3; eauto; hisp.

  cutThis (getMin t xs). 
  destruct x; destruct t0; hisp.
  destruct r0; hisp.
  cutLEQ; hisp.
  inversion_clear H1; subst; hisp.
  eapply IHxs in HeqH3; eauto; hisp.
  inversion_clear H1; subst; hisp.
  eapply IHxs in HeqH3; eauto; hisp.

  cutThis (getMin t xs). 
  destruct x; destruct t0; hisp.
  destruct r0; hisp.
  cutLEQ; hisp.
  inversion_clear H1; subst; hisp.
  eapply IHxs in HeqH3; eauto; hisp.
  inversion_clear H1; subst; hisp.
  eapply IHxs in HeqH3; eauto; hisp.

  cutThis (getMin t xs). 
  destruct x; destruct t0; hisp.
  destruct r0; hisp.
  cutLEQ; hisp.
  inversion_clear H1; subst; hisp.
  inversion_clear H1; subst; hisp.
Qed.
Hint Resolve getMinQHeap.

Lemma getMinQHelp :
  forall a x b xs,
    feapT a x ->
    feapM b xs ->
    forall y z, (y,z) = getMin x xs ->
      feapM (amin a b) z.
Proof.
  intros.
  assert (feapM (toot y) z).
  eapply getMinQHeap with (x := x) (xs := xs); eauto.
  eapply heapLess with (toot y).
  eapply getMinTHeap in H1. Focus 2. eauto.
  Focus 2. eauto.
  destruct y; unfold feapT in *; lisp. auto.
Qed.

Lemma splitHeap :
  forall y a x, feapM a x ->
    forall b, feapM b y ->
      forall p q r, (p,q) = split x r y ->
        feapM (amin a b) p.
Proof.
  induction y; intros; hisp.
  inversion_clear H1; subst; hisp.
  destruct t; hisp.
  destruct m; hisp.
  eapply IHy in H1; eauto.
  cutThis (aLEQ a b).
  eapply IHy in H1; eauto; hisp.
  eapply IHy with (a:=b) in H1; eauto; hisp.
  rewrite dblMin in H1; hisp.
  heapCut a.
Qed.
Hint Resolve splitHeap.

Fixpoint Each {t} (P:t -> Prop) l :=
  match l with
    | nil => True
    | x::xs => P x /\ Each P xs
  end.
Hint Unfold Each.

Lemma weakenEach :
  forall t (P Q:t->Prop),
    (forall x, P x -> Q x) ->
    forall xs, Each P xs ->
      Each Q xs.
Proof.
  intros t P Q PQ xs.
  generalize dependent P;
    generalize dependent Q.
  induction xs; intros.
  constructor.
  lisp.
  eapply IHxs. eauto. eauto.
Qed.

Lemma splitEach :
  forall z a x, feapM a x ->
    forall b y, Each (feapR b) y -> 
      forall c, feapM c z ->
        forall p q, (p,q) = split x y z ->
          Each (feapR (amin b c)) q.
Proof.
  induction z; intros; hisp.
  inversion_clear H2; subst; hisp.
  eapply weakenEach with (feapR b); auto; intros; hisp.

  destruct t; hisp. destruct m; hisp.
  eapply weakenEach with (feapR (amin (amin b c) c)); 
    auto; intros; hisp.
  heapCut (amin (amin b c) c); hisp.
  unfold oomin; repeat (cutLEQ; hisp). inversion Heqbc.
  eapply IHz with (y := Top a0 m0 :: y). Focus 4. eauto.
  eauto.
  hisp.
  cutMin c; hisp.
  eapply weakenEach with (feapR b); auto; intros; hisp. auto.
  
  eapply IHz in H2. Focus 4. eauto.
  eauto. hisp.
  assert (true = aLEQ (amin c a) a0) as ans.
  cutMin c; hisp. eapply ans.
  heapCut a; hisp.
  auto.
Qed.

(*
Lemma preDeleteMinHeap :
  forall x v,
    feapM v x ->
    feapM v (skewDeleteMin x).
Proof.
  intros x.
  induction x; simpl; intros.
  eauto. lisp.
  rename p into a.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  remember (split ($) [] c) as pq; destruct pq as [p q].

  unfold feapM in H.
  lisp.
  assert (oomin v v = v) as vvv.
  unfold oomin; rewrite <- OO.leqRefl; lisp.
  assert (feapM v t) as vt.
  rewrite <- vvv. 
  eapply getMinQHelp. Focus 3. eauto.
  auto. auto.
  assert (feapM v c) as vc.
  eapply getMinTHeap in Heqpt.
  Focus 2. eauto. Focus 2. eauto.
  rewrite vvv in Heqpt. unfold feapT in Heqpt.
  lisp.
  destruct zz; lisp.
  apply heapLess with a0; lisp.
  assert (feapM v p) as vp.
  eapply splitHeap with (a:=v) (b:=v) in Heqpq. rewrite vvv in Heqpq. auto.
  lisp. lisp.
  assert (Each (feapR v) q) as vq.
  eapply splitEach with (a:=v) (b:=v) (c:= v) in Heqpq. 
  rewrite vvv in Heqpq. auto. lisp. lisp. lisp.
  clear Heqpq Heqpt.
  generalize dependent t.
  generalize dependent c.
  generalize dependent p.
  induction q; intros.
  lisp. unfold preMeld.
  unfold uniqify.
  destruct t; destruct p; lisp;
    rewrite meldUniq_equation; lisp.
  rewrite <- vvv.
  unfold feapM in vp; lisp.
  eapply insHeapSome; lisp.
  remember (ins p0 t) as p0t; destruct p0t; lisp.
  rewrite Heqp0t.
  rewrite <- vvv.
  unfold feapM in vt; lisp.
  eapply insHeapSome; lisp.

(* *)

  remember (ins p0 t) as p0t; destruct p0t; lisp.
  unfold feapM in vp; lisp.
  rewrite <- vvv.
  eapply insHeapSome; lisp.
  remember (ins p p1) as pp1; destruct pp1; lisp.
  rewrite Heqp0t.

  unfold feapM in vt; lisp.
  rewrite <- vvv.
  eapply insHeapSome; lisp.


(* *)


  unfold feapM in vt; lisp.
  assert (feapM (oomin v v) (ins p0 t)).
  apply insHeapSome; auto.
  rewrite <- Heqp0t in H3.
  rewrite vvv in H3.
  unfold feapM in H3; lisp.


  unfold feapM in vp; lisp.
  assert (feapM (oomin v v) (ins p p1)).
  apply insHeapSome; auto.
  rewrite <- Heqpp1 in H7.
  rewrite vvv in H7.
  unfold feapM in H7; lisp.


  destruct p2; destruct p3; lisp.
  remember (nat_compare n n0) as nn0; destruct nn0; lisp.
  rewrite <- vvv.
  apply insHeapSome.
  destruct r; destruct r0; lisp.
  remember (OO.LEQ a0 a1) as a01; destruct a01; lisp.
  unfold feapT; lisp.
  unfold feapT; lisp.
  rewrite <- vvv.
  apply meldUniqHeapSome; lisp.
  unfold feapM; lisp.
  rewrite <- vvv.
  apply meldUniqHeapSome; lisp.
  unfold feapM; lisp.
  unfold feapM; lisp.
  rewrite <- vvv.
  apply meldUniqHeapSome; lisp.
  unfold feapM; lisp.
  simpl.
  rewrite <- vvv.
  apply preInsertHeapLess.
  lisp.
  eapply IHq; lisp.
Qed.
*)


Lemma preExtractMinHeap :
  forall v x,
    feapM v x ->
    forall y z,
      Some (y,z) = skewExtractMin x ->
      feapM (zoot y) x /\ feapM (zoot y) z.
Proof.
  intros.
  unfold skewExtractMin in *.
  destruct x; hisp.
  inversion H0.
  cutThis (getMin t x); hisp.
  destruct t0; hisp.
  cutThis (split ($) [] m0); hisp.
  inversion_clear H0; subst.
  eapply getMinQHeap in HeqH2; eauto; hisp.

  cutThis (getMin t x); hisp.
  destruct t0; hisp.
  cutThis (split ($) [] m0); hisp.
  inversion_clear H0; subst.
  eapply getMinQHeap in HeqH2; eauto; hisp.

  cutThis (getMin t x); hisp.
  destruct t0; hisp.
  cutThis (split ($) [] m0); hisp.
  inversion_clear H0; subst.

  assert (forall xs x a,
    feapM a x ->
    Each (feapR a) xs ->
    feapM a (fold_right skewInsert x xs)) as ans.
  clear.
  induction xs; intros; hisp.
  erewrite <- (dblMin a0).
  apply preInsertHeapLess; hisp.

  eapply ans; hisp. clear ans.
  erewrite <- (dblMin (zoot _)).
  apply preMeldHeapSome.
  eapply getMinQHeap in HeqH2; hisp; eauto.
  eapply getMinTHeap in HeqH2; hisp; eauto.
  erewrite <- (dblMin a).
  eapply splitHeap. Focus 3. eauto. hisp. hisp.

  erewrite <- (dblMin (zoot _)).
  eapply splitEach with (a := (zoot r)). Focus 4. eauto. hisp. hisp.
  eapply getMinTHeap in HeqH2; hisp; eauto.
Qed.

Lemma preExtractMinRootHeap :
  forall x v,
    feapM v x ->
    forall y z,
      Some (y,z) = skewExtractMin x ->
      feapR v y.
Proof.
  intros x.
  destruct x; simpl; intros.
  inversion H0.
  rename t into a.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  inversion_clear H0; subst.
  unfold feapM in H; lisp.
  assert (feapT v (Node zz zzz c)).
  erewrite <- (dblMin v).
  eapply getMinTHeap. Focus 3. eauto. lisp. lisp.
  unfold feapT in *. lisp.
Qed.

Lemma preExtractMinHelp :
  forall v x,
    feapM v x ->
    forall y z,
      Some (y,z) = skewExtractMin x ->
      feapM v z.
Proof.
  intros.
  eapply heapLess with (zoot y).
  assert (feapR v y). eapply preExtractMinRootHeap; eauto.
  destruct y; unfold feapR in *; lisp.
  eapply preExtractMinHeap; eauto.
Qed.

Definition findMinHelpHeap :
  forall xs v, feapM v xs ->
    forall x w, feapT w x ->
      feapR (amin v w) (preFindMinHelp x xs).
Proof.
  induction xs; simpl; intros; lisp.
  destruct x; lisp. cutMin w; hisp. 
  destruct x; cutThis (preFindMinHelp t xs); hisp.
  assert (feapR (amin v v) (preFindMinHelp t xs)) as ans.
  apply IHxs; hisp. hisp.
  erewrite dblMin in ans. rewrite <- HeqH2 in ans.
  hisp.
  cutLEQ; hisp.
  cutMin w.
  cutMin v.
Qed.

Definition findMinHeap :
  forall x v,
    feapM v x ->
    forall y, Some y = skewFindMin x ->
      feapR v y.
Proof.
  induction x; simpl; intros.
  inversion H0.
  inversion_clear H0; subst.
  unfold feapM in H; lisp.
  erewrite <- (dblMin v).
  apply findMinHelpHeap; lisp; eauto.
Qed.

(*
Definition PQP x := skewBinaryRank x /\ (x = ($) \/ exists v, feapM v x).

Definition PQ := { x:Many | PQP x}.

Program Definition empty : PQ := ($).
Next Obligation.
  lisp. split. eauto. eauto.
Qed.

Program Definition insert : A -> PQ -> PQ := preInsert.
Next Obligation.
  destruct x0. destruct x.
  destruct p. 
  split; simpl.
  apply preInsertRank. assumption. destruct o.
  subst. right. destruct x. exists a; lisp.
  unfold feapM; lisp. right.
  simpl. 
  destruct x; lisp. destruct H.
  exists (amin a x).
  apply preInsertHeapLess; lisp.
Qed.

Definition findMin (x:PQ) : option A.
refine (fun x =>
  match x with
    | exist x' xp =>
      match preFindMin x' as j return ((j=preFindMin x') -> option A) with
        | None => fun _ => None
        | Some y => fun s => Some (@exist _ _ y _)
      end eq_refl
  end).
  destruct xp.
  Check findMinHeap.
  destruct H0; subst; lisp. inversion s.
  destruct H0.
  eapply findMinHeap in s.
  destruct y.
  unfold feapR in s; lisp. eauto.
Defined.

Lemma findMin_equality :
  forall x px y py,
    Some (exist _ y py) = findMin (exist _ x px) ->
    Some y = preFindMin x.
Proof.
  intros.
  generalize dependent H. 
  remember (preFindMin x) as pemx.
  unfold findMin.
  Check preFindMin.
(*  generalize dependent Heqpemx.*)
  Locate "_ \/ _". Print or.
  assert (forall (zz:option (Root OO.A)) (pp:zz= preFindMin x),
   Some (exist (fun x0 : Root OO.A => feapR OO.LEQ (zoot x0) x0) y py) =
   match zz as j return (j = preFindMin x -> option A) with
   | Some y0 =>
       fun s : Some y0 = preFindMin x =>
       Some
         (exist (fun x0 : Root OO.A => feapR OO.LEQ (zoot x0) x0) y0
            match px with
            | conj H (or_introl H1) =>
                eq_ind_r
                  (fun x' : Many =>
                   skewBinaryRank x' ->
                   Some y0 = preFindMin x' -> feapR OO.LEQ (zoot y0) y0)
                  (fun (_ : skewBinaryRank ($))
                     (s0 : Some y0 = preFindMin ($)) =>
                   match
                     s0 in (_ = y1)
                     return (y1 = None -> feapR OO.LEQ (zoot y0) y0)
                   with
                   | eq_refl =>
                       fun H3 : Some y0 = None =>
                       False_ind (feapR OO.LEQ (zoot y0) y0)
                         (eq_ind (Some y0)
                            (fun e : option (Root OO.A) =>
                             match e with
                             | Some _ => True
                             | None => False
                             end) I None H3)
                   end eq_refl) H1 H s
            | conj H (or_intror (ex_intro x0 H2)) =>
                match
                  y0 as r
                  return (feapR x0 r -> feapR OO.LEQ (zoot r) r)
                with
                | Top a m =>
                    fun s0 : feapR x0 (Top a m) =>
                    match s0 with
                    | conj _ H4 => conj (OO.leqRefl a) H4
                    end
                end (findMinHeap x x0 H2 s)
            end)
   | None => fun _ : None = preFindMin x => None
   end pp -> Some y = pemx).
  intros.
  destruct zz.
  inversion_clear H; subst. auto.
  inversion H.
  pose (H (preFindMin x) eq_refl) as Q.
  apply Q.
Qed.

Lemma findMin_none :
  forall x px,
    None = findMin (exist _ x px) ->
    None = preFindMin x.
Proof.
  intros.
  generalize dependent H. 
  remember (preFindMin x) as pemx.
  unfold findMin.  
  assert (forall (zz:option (Root OO.A)) (pp:zz= preFindMin x),
   None =
   match zz as j return (j = preFindMin x -> option A) with
   | Some y =>
       fun s : Some y = preFindMin x =>
       Some
         (exist (fun x0 : Root OO.A => feapR OO.LEQ (zoot x0) x0) y
            match px with
            | conj H (or_introl H1) =>
                eq_ind_r
                  (fun x' : Many =>
                   skewBinaryRank x' ->
                   Some y = preFindMin x' -> feapR OO.LEQ (zoot y) y)
                  (fun (_ : skewBinaryRank ($))
                     (s0 : Some y = preFindMin ($)) =>
                   match
                     s0 in (_ = y0)
                     return (y0 = None -> feapR OO.LEQ (zoot y) y)
                   with
                   | eq_refl =>
                       fun H3 : Some y = None =>
                       False_ind (feapR OO.LEQ (zoot y) y)
                         (eq_ind (Some y)
                            (fun e : option (Root OO.A) =>
                             match e with
                             | Some _ => True
                             | None => False
                             end) I None H3)
                   end eq_refl) H1 H s
            | conj H (or_intror (ex_intro x0 H2)) =>
                match
                  y as r
                  return (feapR x0 r -> feapR OO.LEQ (zoot r) r)
                with
                | Top a m =>
                    fun s0 : feapR x0 (Top a m) =>
                    match s0 with
                    | conj _ H4 => conj (OO.leqRefl a) H4
                    end
                end (findMinHeap x x0 H2 s)
            end)
   | None => fun _ : None = preFindMin x => None
   end pp -> None = pemx) as P.
   Focus 2.
  eapply P.
  intros.
  destruct zz.
  inversion_clear H; subst.
  rewrite Heqpemx. auto.
Qed.

Program Definition meld : PQ -> PQ -> PQ := preMeld.
Next Obligation.
  destruct x; destruct x0.
  destruct p; destruct p0; split; simpl.
  apply preMeldRank; auto.
  destruct o; destruct o0; subst.
  left; unfold preMeld. unfold uniqify.
  rewrite meldUniq_equation. auto.
  destruct H0; right. unfold preMeld.
  unfold uniqify at 1.
  rewrite meldUniq_equation. exists x.
  induction x0. lisp.
  simpl. unfold feapM in H. lisp.
  assert (forall v, amin v v = v) as vvv.
  unfold amin. intros.
  remember (OO.LEQ v v) as vv; destruct vv; auto.
  rewrite <- (vvv x).
  apply insHeapSome; lisp.
  right.
  unfold preMeld. unfold uniqify at 2; lisp.
  rewrite meldUniq_equation.
  remember (uniqify x) as ux; destruct ux; lisp.
  destruct H; lisp. exists x0; lisp.
  rewrite Hequx.
  destruct H. clear Hequx. unfold uniqify. destruct x.
  exists x0; lisp. unfold feapM in H; lisp.
  exists x0.
  assert (forall v, amin v v = v) as vvv.
  unfold amin. intros.
  remember (OO.LEQ v v) as vv; destruct vv; auto.
  rewrite <- (vvv x0).
  apply insHeapSome; lisp.
  destruct H; destruct H0. right.
  exists (amin x1 x2).
  apply preMeldHeapSome; lisp.
Qed.

Program Definition deleteMin : PQ -> PQ := preDeleteMin.
Next Obligation.
  destruct x. destruct p; split; simpl.
  apply deleteMinRank; auto.
  destruct o; subst. left; lisp. right.
  destruct H. exists x0.
  apply preDeleteMinHeap; auto.
Qed.

(*
Program Definition extractMin (x:PQ) : option (A*PQ) :=
  match preExtractMin x with
    | None => None
    | Some (y,z) => Some (y,z)
  end.
Next Obligation.
  destruct x. destruct p; split; simpl.
  eapply extractMinRank; eauto.
  eapply preExtractMinHeap; eauto.
Qed.
*)

(*
Print extractMin.

Locate "_ = _".
Print eq.
*)


Definition extractMin (x:PQ) : option (A*PQ).
refine (fun x =>
  match x with
    | exist x' xp =>
      match preExtractMin x' as j return ((j=preExtractMin x') -> option (A*PQ)) with
        | None => fun _ => None
        | Some (y,z) => fun s => Some ((@exist _ _ y _),(@exist _ _ z _))
      end eq_refl
  end).
  Check preExtractMinRootHeap.
  destruct xp. destruct H0; subst. unfold preExtractMin in s. inversion s.
  destruct H0.
  assert (feapR x0 y) as ANS.
  eapply preExtractMinRootHeap. Focus 2. eauto. auto.
  unfold feapR in *; destruct y; lisp.
  unfold PQP. lisp.
  destruct xp.
  eapply extractMinRank; eauto.
  destruct xp. destruct H0; subst; lisp. inversion s.
  destruct H0. right.
  exists x0. eapply preExtractMinHelp. Focus 2. eauto. auto.
Defined. 

(*
Definition extractMin (x:PQ) : option (A*PQ).
refine (fun x =>
  match x with
    | exist x' xp =>
      match preExtractMin x' as j return ((j=preExtractMin x') -> option (A*PQ)) with
        | None => fun _ => None
        | Some (y,z) => fun s => Some ((@exist _ _ y _),(@exist _ _ z _))
      end eq_refl
  end).


  edestruct preExtractMinRootHeap.
  Focus 2. eauto.
  destruct xp as [R M]. auto.
  destruct y; lisp; eauto.
  destruct xp as [R M].
  split.
  eapply extractMinRank; eauto.
  eapply preExtractMinHeap; eauto.
Defined.
*)

Lemma extractMin_equality :
  forall x px y py z pz,
    Some (exist _ y py,exist _ z pz) = extractMin (exist _ x px) ->
    Some (y,z) = preExtractMin x.
Proof.
  intros.
  generalize dependent H. 
  remember (preExtractMin x) as pemx.
  unfold extractMin.  

(*  generalize dependent Heqpemx.*)
  assert (forall (zz:option((Root OO.A)*Many)) (pp:zz= preExtractMin x),
   Some
     (exist (fun x0 : Root OO.A => feapR OO.LEQ (zoot x0) x0) y py,
     exist (fun x0 : Many => PQP x0) z pz) =
   match
     zz as j return (j = preExtractMin x -> option (A * PQ))
   with
   | Some p =>
       let (y0, z0) as p0
           return (Some p0 = preExtractMin x -> option (A * PQ)) := p in
       fun s : Some (y0, z0) = preExtractMin x =>
       Some
         (exist (fun x0 : Root OO.A => feapR OO.LEQ (zoot x0) x0) y0
            match px with
            | conj H (or_introl H1) =>
                eq_ind_r
                  (fun x' : Many =>
                   skewBinaryRank x' ->
                   Some (y0, z0) = preExtractMin x' ->
                   feapR OO.LEQ (zoot y0) y0)
                  (fun (_ : skewBinaryRank ($))
                     (s0 : Some (y0, z0) = preExtractMin ($)) =>
                   match
                     s0 in (_ = y1)
                     return (y1 = None -> feapR OO.LEQ (zoot y0) y0)
                   with
                   | eq_refl =>
                       fun H3 : Some (y0, z0) = None =>
                       False_ind (feapR OO.LEQ (zoot y0) y0)
                         (eq_ind (Some (y0, z0))
                            (fun e : option (Root OO.A * Many OO.A) =>
                             match e with
                             | Some _ => True
                             | None => False
                             end) I None H3)
                   end eq_refl) H1 H s
            | conj H (or_intror (ex_intro x0 H2)) =>
                match
                  y0 as r
                  return
                    (Some (r, z0) = preExtractMin x ->
                     feapR OO.LEQ x0 r -> feapR OO.LEQ (zoot r) r)
                with
                | Top a m =>
                    fun (_ : Some (Top a m, z0) = preExtractMin x)
                      (ANS : feapR OO.LEQ x0 (Top a m)) =>
                    match ANS with
                    | conj _ H4 => conj (OO.leqRefl a) H4
                    end
                end s (preExtractMinRootHeap x x0 H2 s)
            end,
         exist (fun x0 : Many => PQP x0) z0
           (conj match px with
                 | conj H _ => extractMinRank H s
                 end
              match px with
              | conj H (or_introl H1) =>
                  eq_ind_r
                    (fun x' : Many =>
                     skewBinaryRank x' ->
                     Some (y0, z0) = preExtractMin x' ->
                     z0 = $ \/ (exists v : OO.A, feapM v z0))
                    (fun (_ : skewBinaryRank ($))
                       (s0 : Some (y0, z0) = preExtractMin ($)) =>
                     match
                       s0 in (_ = y1)
                       return
                         (y1 = None ->
                          z0 = $ \/ (exists v : OO.A, feapM v z0))
                     with
                     | eq_refl =>
                         fun H3 : Some (y0, z0) = None =>
                         False_ind
                           (z0 = $ \/ (exists v : OO.A, feapM v z0))
                           (eq_ind (Some (y0, z0))
                              (fun e : option (Root OO.A * Many OO.A) =>
                               match e with
                               | Some _ => True
                               | None => False
                               end) I None H3)
                     end eq_refl) H1 H s
              | conj H (or_intror (ex_intro x0 H2)) =>
                  or_intror (z0 = $)
                    (ex_intro (fun v : OO.A => feapM v z0) x0
                       (preExtractMinHelp x0 x H2 s))
              end))
   | None => fun _ : None = preExtractMin x => None
   end pp -> Some (y, z) = pemx) as P.
  intros.
  destruct zz.
  destruct p.
  inversion_clear H; subst. auto.
  inversion H.
  pose (P (preExtractMin x) eq_refl) as Q.
  apply Q.
Qed.

Lemma extractMin_none :
  forall x px,
    None = extractMin (exist _ x px) ->
    None = preExtractMin x.
Proof.
  intros.
  generalize dependent H. 
  remember (preExtractMin x) as pemx.
  unfold extractMin.  

  assert (forall (zz:option((Root OO.A)*Many)) (pp:zz= preExtractMin x),
   None =
   match
     zz as j return (j = preExtractMin x -> option (A * PQ))
   with
   | Some p =>
       let (y, z) as p0
           return (Some p0 = preExtractMin x -> option (A * PQ)) := p in
       fun s : Some (y, z) = preExtractMin x =>
       Some
         (exist (fun x0 : Root OO.A => feapR OO.LEQ (zoot x0) x0) y
            match px with
            | conj H (or_introl H1) =>
                eq_ind_r
                  (fun x' : Many =>
                   skewBinaryRank x' ->
                   Some (y, z) = preExtractMin x' ->
                   feapR OO.LEQ (zoot y) y)
                  (fun (_ : skewBinaryRank ($))
                     (s0 : Some (y, z) = preExtractMin ($)) =>
                   match
                     s0 in (_ = y0)
                     return (y0 = None -> feapR OO.LEQ (zoot y) y)
                   with
                   | eq_refl =>
                       fun H3 : Some (y, z) = None =>
                       False_ind (feapR OO.LEQ (zoot y) y)
                         (eq_ind (Some (y, z))
                            (fun e : option (Root OO.A * Many OO.A) =>
                             match e with
                             | Some _ => True
                             | None => False
                             end) I None H3)
                   end eq_refl) H1 H s
            | conj H (or_intror (ex_intro x0 H2)) =>
                match
                  y as r
                  return
                    (Some (r, z) = preExtractMin x ->
                     feapR OO.LEQ x0 r -> feapR OO.LEQ (zoot r) r)
                with
                | Top a m =>
                    fun (_ : Some (Top a m, z) = preExtractMin x)
                      (ANS : feapR OO.LEQ x0 (Top a m)) =>
                    match ANS with
                    | conj _ H4 => conj (OO.leqRefl a) H4
                    end
                end s (preExtractMinRootHeap x x0 H2 s)
            end,
         exist (fun x0 : Many => PQP x0) z
           (conj match px with
                 | conj H _ => extractMinRank H s
                 end
              match px with
              | conj H (or_introl H1) =>
                  eq_ind_r
                    (fun x' : Many =>
                     skewBinaryRank x' ->
                     Some (y, z) = preExtractMin x' ->
                     z = $ \/ (exists v : OO.A, feapM v z))
                    (fun (_ : skewBinaryRank ($))
                       (s0 : Some (y, z) = preExtractMin ($)) =>
                     match
                       s0 in (_ = y0)
                       return
                         (y0 = None ->
                          z = $ \/ (exists v : OO.A, feapM v z))
                     with
                     | eq_refl =>
                         fun H3 : Some (y, z) = None =>
                         False_ind (z = $ \/ (exists v : OO.A, feapM v z))
                           (eq_ind (Some (y, z))
                              (fun e : option (Root OO.A * Many OO.A) =>
                               match e with
                               | Some _ => True
                               | None => False
                               end) I None H3)
                     end eq_refl) H1 H s
              | conj H (or_intror (ex_intro x0 H2)) =>
                  or_intror (z = $)
                    (ex_intro (fun v : OO.A => feapM v z) x0
                       (preExtractMinHelp x0 x H2 s))
              end))
   | None => fun _ : None = preExtractMin x => None
   end pp -> None = pemx) as P.

  Focus 2.
  eapply P.
  intros.
  destruct zz.
  destruct p.
  inversion_clear H; subst.
  rewrite Heqpemx. auto.
Qed.

End SkewBootHeap.
*)

(*
Module InlineBoot(OO:Order) <: PQSig.

Module O:=OO.
Export O.

Module SBH := SkewBootHeap(O).

Definition add a f (x:list a) := fold_right plus 0 (map f x).

Definition Tree := Tree A.
Definition Boot := Root A.

Fixpoint sizeT (x:Tree) :=
  match x with
    | Node r _ l => sizeR r + sizeM l
  end
with sizeR x := S
  match x with
    | Top _ l => sizeM l
  end
with sizeM x :=
  match x with
    | ($) => 0
    | y:::ys => sizeT y + sizeM ys
  end.
*)

Inductive bootWrap :=
  Empty : bootWrap
| Full : Root -> bootWrap.

Definition preMeld x y :=
  match x,y with
    | Empty,_ => y
    | _,Empty => x
    | Full (Top v c), Full (Top w d) =>
      if aLEQ v w
        then Full (Top v (skewInsert (Top w d) c))
        else Full (Top w (skewInsert (Top v c) d))
  end.
Hint Unfold preMeld.

Definition preInsert x xs :=
  preMeld (Full (Top x skewEmpty)) xs.
Hint Unfold preInsert.

Definition preFindMin x :=
  match x with
    | Empty => None
    | Full (Top v _) => Some v
  end.
Hint Unfold preFindMin.

Definition preExtractMin x :=
  match x with
    | Empty => None
    | Full (Top v c) => Some (v,
      match skewExtractMin c with
        | None => Empty
        | Some (Top w d,cs) =>
          Full (Top w (skewMeld d cs))
      end)
  end.
Hint Unfold preExtractMin.

(*
Definition preDeleteMin x :=
  match preExtractMin x with
    | None => x
    | Some (_,y) => y
  end.
Hint Unfold preDeleteMin.
*)

Definition treeHeap x := exists v, feapT  v x.
Definition rootHeap x := exists v, feapR  v x.
Definition listHeap x := exists v, feapM  v x.
Hint Unfold treeHeap.
Hint Unfold rootHeap.
Hint Unfold listHeap.

Definition wrapHeap x :=
  match x with
    | Empty => True
    | Full y => rootHeap y
  end.
Hint Unfold wrapHeap.

Definition PQ := {x:bootWrap | wrapHeap x}.

Program Definition bootInsert : A -> PQ -> PQ := preInsert.
Next Obligation.
  destruct x0; lisp.
  destruct x0; lisp.
  exists x; lisp.
  unfold preInsert; simpl.
  destruct r; lisp. unfold rootHeap in *; hisp.
  destruct w; hisp.
  cutLEQ; hisp; unfold rootHeap; hisp.
  exists x; hisp.
  hisp.
  exists a; hisp.
  erewrite <- (dblMin a).
  eapply preInsertHeapLess; hisp.
Qed.

Program Definition bootFindMin : PQ -> option A := preFindMin.

Program Definition bootMeld : PQ -> PQ -> PQ := preMeld.
Next Obligation.
  destruct x; destruct x0; unfold wrapHeap; simpl.
  destruct x; destruct x0; simpl; auto.
  destruct r. unfold wrapHeap in *. auto.
  destruct r; destruct r0; simpl.
  unfold wrapHeap in *. hisp.
  cutLEQ; unfold rootHeap in *; hisp;
      destruct w; destruct w0; hisp.
  exists a; hisp.
  erewrite <- (dblMin a).
  apply preInsertHeapLess; hisp.
  exists a0; hisp.
  erewrite <- (dblMin a0).
  apply preInsertHeapLess; hisp.
Qed.

Definition bootExtractMin (x:PQ) : option (A*PQ).
refine (fun x =>
  match x with
    | exist x _ => 
      match preExtractMin x as j return ((j=preExtractMin x) -> option (A*PQ)) with
        | None => fun _ => None
        | Some (a,b) => fun _ => Some (a,exist _ b _)
      end eq_refl
  end).
destruct x0. simpl in _H. inversion _H.
unfold wrapHeap.
unfold wrapHeap in w. unfold rootHeap in w.
destruct w.
unfold preExtractMin in _H.
destruct r; lisp.
inversion_clear _H; subst.
remember (skewExtractMin m) as mm; destruct mm; auto.
destruct p0; lisp.
destruct r; lisp.
unfold rootHeap; lisp.
assert (feapM a0 m0).
eapply preExtractMinHelp. Focus 2. eauto. auto.
assert (feapR a0 (Top a1 m1)).
eapply preExtractMinRootHeap. Focus 2. eauto. auto.
exists a1; lisp.
erewrite <- (dblMin a1).
eapply preMeldHeapSome.
unfold feapR in H2; lisp.
replace a1 with (zoot (Top a1 m1)).
eapply preExtractMinHeap. Focus 2. eauto.
eauto.
auto.
Defined.

Definition preEmpty := Empty.
Program Definition bootEmpty : PQ := preEmpty.

Definition preToList x :=
  match x with
    | Empty => nil
    | Full y => toListR y nil
  end.

Program Definition bootToList : PQ -> list A := preToList.

Instance bootPQ : @MINQ A PQ O := {
  empty := bootEmpty;
  insert := bootInsert;
  extractMin := bootExtractMin;
  findMin := bootFindMin;
  toList := bootToList;
  meld := bootMeld
}.

(*
End Order.
End Carrier.

Extraction Language Haskell.
Recursive Extraction bootPQ.
Extraction Inline and_rect sig_rect proj1_sig LEQ.
Recursive Extraction bootPQ.
Extraction Inline aLEQ meldUniq_terminate.
Extraction Inline 
  preInsert preFindMin preMeld 
  preExtractMin preEmpty preToList.
Recursive Extraction bootPQ empty insert findMin extractMin toList meld.
Recursive Extraction empty.

  insert: A -> PQ -> PQ;
  findMin : PQ -> option A;
  extractMin : PQ -> option (A*PQ);
  toList : PQ -> list A;
  meld : PQ -> PQ -> PQ
}.


Instance pOrder : ORDER Root := {
  LEQ := pLEQ;
  leqRefl := pLeqRefl;
  leqSymm := pLeqSymm;
  leqTransTrue := pLeqTransTrue;
  leqTransFalse := pLeqTransFalse
}.
*)

Fixpoint countR (f:A->A->bool) x r :=
  match r with
    | Top y l => 
      let ans := countM f x l in
        if f x y
          then S ans
          else ans
  end
with countT f x t :=
  match t with
    | Node r _ c =>
      countR f x r + countM f x c
  end
with countM f x l :=
  match l with
    | ($) => 0
    | y:::ys => countT f x y + countM f x ys
  end.


Definition preCount (same:@DER A O) x p :=
  match p with
    | Empty => 0
    | Full q =>
      match same with
        | exist f _ => countR f x q
      end
  end.
Hint Unfold preCount.

Program Definition count d x (v:PQ) := preCount d x v.
Hint Unfold count.

Check all_ind.

Lemma listAll :
  forall f q x,
(forall p l, countT f x p 
+ listCount (@exist _ _ f q) x l 
= listCount (@exist _ _ f q) x (toListT p l))
/\
(forall p l, countR f x p 
+ listCount (@exist _ _ f q) x l 
= listCount (@exist _ _ f q) x (toListR p l))
/\
(forall p l, countM f x p 
+ listCount (@exist _ _ f q) x l 
= listCount (@exist _ _ f q) x (toListM p l)).
Proof.
  intros. apply all_ind; intros; hisp.
  rewrite <- H. rewrite <- H0. omega.
  rewrite <- H. hisp. cutThis (f x a); hisp.
  rewrite <- H. rewrite <- H0. omega.  
Qed.

Lemma countList :
  forall (s : DER) (x : A) y, 
    count s x y = listCount s x (toList y).
Proof.
  intros; destruct y.
  unfold count; unfold toList; hisp.
  unfold preCount. destruct x0. hisp.
  destruct s. 
  hisp. unfold bootToList. hisp.
  pose (@listAll x0 d x) as ans.
  hisp.
  rewrite <- H0. hisp.
Qed.


Lemma countJoin :
  forall f,
    DERP f ->
    (forall p x y, true = f x y -> countT f x p = countT f y p)
    /\ (forall r x y, true = f x y -> countR f x r = countR f y r)
    /\ (forall m x y, true = f x y -> countM f x m = countM f y m).
Proof.
  intros.
  apply all_ind; simpl; intros.
  auto.
  remember (f x a) as xa; destruct xa;
    remember (f y a) as ya; destruct ya; auto.
  destruct H.
  assert (true = false) as F.
  rewrite Heqya.
  eapply derTrans; eauto. inversion F.
  destruct H.
  assert (true = false) as F.
  rewrite Heqxa.
  eapply derTrans; eauto. inversion F. auto.
  auto.
Qed.

Lemma countSAME :
  forall same x y,
    check same x y = true ->
    forall inp, count same x inp = count same y inp.
Proof.
  intros same x y xy p.
  destruct same as [f D]; unfold count.
  simpl in xy. destruct p; auto. simpl.
  unfold preCount. destruct x0; simpl; auto.
  apply countJoin; auto.
Qed.

Lemma emptyCount :
  forall same x, count same x empty = 0.
Proof.
  intros; auto.
Qed.

Check countM.
Check skewInsert.
Print countM.
Print skewInsert.

Lemma insertCountM : 
  forall f x,
  forall p q, 
    countM f x (skewInsert p q)
    = countR f x p
    + countM f x q.
Proof.
  intros f x p q.
  unfold skewInsert.
  destruct q; simpl; try omega.
  destruct q; simpl; try omega.
  destruct t; destruct t0; simpl.
  cutThis (comp n n0); hisp;
  destruct p; destruct r; hisp;
  cutLEQ; hisp; destruct r0; hisp; cutLEQ; hisp;
    try omega.
Qed.

Lemma insertCount :
  forall same x inp y,
    count same x (insert y inp) =
    let oldCount := count same x inp in
      if check same x y 
        then S oldCount
        else oldCount.
Proof.
  intros. unfold insert. hisp.
  unfold bootInsert.
  simpl. destruct same as [f D].
  destruct inp; simpl; auto.
  unfold count.
  simpl. destruct x0; simpl. auto.
  unfold preInsert. simpl.
  destruct r. hisp.
  cutLEQ; hisp.
  cutThis (f x a); cutThis (f x y); try omega.
  cutThis (f x a); cutThis (f x y); hisp; try omega.
  destruct D.
  assert (false = LEQ y y).
  erewrite <- derRight; eauto.
  rewrite <- aLeqRefl in H. inversion H.
  erewrite insertCountM. 
  simpl. rewrite <- HeqH0. omega.
  rewrite insertCountM.
  simpl. rewrite <- HeqH0. omega.
  rewrite insertCountM.
  simpl. rewrite <- HeqH0. omega.
Qed.


Lemma findMinAll :
  (forall x f (d:DERP  f) y a,
    feapT  a x ->
    (if f y a then S (countT f y x) else countT f y x) > 0 ->
    LEQ a y = true)
  /\ (forall x f (d:DERP  f) y a,
    feapR  a x ->
    (if f y a then S (countR f y x) else countR f y x) > 0 ->
    LEQ a y = true)
  /\ (forall x f (d:DERP  f) y a,
    feapM  a x ->
    (if f y a then S (countM f y x) else countM f y x) > 0 ->
    LEQ a y = true).
Proof.
  apply all_ind; simpl; intros.
  destruct H1; destruct r; simpl in *.
  destruct H1.
  remember (countM f y m) as fym; destruct fym.
  eapply H; eauto. 
  remember (f y a) as fya; destruct fya; try omega.
  eapply H0; eauto. eapply heapLess. eauto. auto.
  rewrite <- Heqfym.
  remember (f y a) as fya; destruct fya; try omega.
  destruct H0.
  remember (f y a) as fya; destruct fya. 
  destruct d.
  assert (forall z, LEQ z a = LEQ z y).
  apply derRight. rewrite derSymm. auto.
  erewrite <- H3. auto.
  remember (f y a0) as fya0; destruct fya0.
  eapply H; eauto. eapply heapLess. eauto. auto.
  rewrite <- Heqfya0. omega.
  eapply H; eauto. eapply heapLess. eauto. auto.
  rewrite <- Heqfya0. auto.
  remember (f y a) as fya; destruct fya.
  destruct d.
  eapply derRight in Heqfya. erewrite Heqfya. symmetry. hisp.
  inversion H0. hisp.
  remember (f y a) as fya; destruct fya.
  eapply H; eauto.
  rewrite <- Heqfya. omega.
  remember (countT f y t) as fyp; destruct fyp.
  eapply H0; eauto.
  rewrite <- Heqfya. omega.
  eapply H; eauto.
    rewrite <- Heqfya. omega.
Qed.

Lemma findMinCount :
  forall inp,
    match findMin inp with
      | None => forall same x, count same x inp = 0
      | Some x =>
        forall same y, 
          if check same y x
            then count same y inp > 0
            else count same y inp > 0 ->
              LEQ x y = true
    end.
Proof.
  intros; destruct inp; simpl; auto.
  unfold bootFindMin. simpl. lisp.
  destruct x; simpl.
  intros; unfold count; simpl; auto.
  destruct r.
  intros.
  simpl in w. destruct w.
  simpl in f. lisp.
  destruct same; simpl.
  unfold count; simpl.
  remember (x0 y a) as ya; destruct ya.
  omega.
  intros.
  eapply findMinAll. eauto. eauto. rewrite <- Heqya. auto.
Qed.

Lemma linkCount :
  forall q f x p,
    DERP f ->
    countT f x (link p q) 
    = countT f x p
    + countT f x q.
Proof.
  intros.
  unfold link.
  destruct p; destruct q; lisp. hisp.
  destruct r; destruct r0; hisp.
  cutLEQ; hisp. try omega. try omega.
Qed.

Lemma insCount :
  forall q f x p,
    DERP f ->
    countM f x (ins p q) 
    = countT f x p
    + countM f x q.
Proof.
  induction q; intros; lisp.
  remember (comp  (rank p) (rank t)) as pp; 
    destruct pp; lisp.
  rewrite IHq. rewrite linkCount. omega. auto. auto.
  rewrite IHq. rewrite linkCount. omega. auto. auto.
Qed.
  
Lemma insCons : 
  forall y x,
    ($) <> ins x y.
Proof.
  unfold not;
  induction y; intros; lisp;
    unfold not; intros; auto.
  unfold ins in H. inversion H.
  cutThis (comp  (rank x) (rank t)).
  eapply IHy; eauto.
  inversion H.
  eapply IHy; eauto.
Qed.

Lemma meldUniqCount :
  forall f inp inq x,
    DERP  f ->
    countM f x (meldUniq (inp,inq))
    = countM f x inp
    + countM f x inq.
Proof.
  Check meldUniq_ind.
  pose
    (fun (pq:Many * Many) r =>
      let (p,q) := pq in
        forall f,
          DERP f ->
          forall x,
            countM f x r = 
            countM f x p +
            countM f x q) as P.
  assert (forall tu, P tu (meldUniq tu)).
  apply meldUniq_ind; unfold P; clear P; lisp; intros.
  rewrite H; auto. omega.
  rewrite H; auto. omega.
  rewrite insCount; auto.
  rewrite H; auto. 
  rewrite linkCount; auto. omega.
  intros.
  unfold P in *. clear P.
  pose (H (inp,inq)) as hh.
  lisp.
Qed.

Lemma preMeldCount :
  forall f inp inq x,
    DERP  f ->
    countM f x (skewMeld inp inq) 
    = countM f x inp
    + countM f x inq.
Proof.
  intros; destruct inp; destruct inq; lisp;
    unfold skewMeld; unfold uniqify;
      rewrite meldUniq_equation; lisp.
  rewrite insCount; auto.
  remember (ins t inp) as pp; destruct pp; 
    rewrite Heqpp; rewrite insCount; lisp.
  remember (ins t inp) as pp; destruct pp.
  apply insCons in Heqpp. inversion Heqpp.
  remember (ins t0 inq) as qq; destruct qq.
  apply insCons in Heqqq. inversion Heqqq.
  cutThis (comp  (rank t1) (rank t2)).
  rewrite insCount; auto. rewrite linkCount; auto. 
  rewrite meldUniqCount; auto.
  rewrite <- insCount; auto. rewrite <- insCount; auto.
  rewrite <- Heqpp. rewrite <- Heqqq. lisp. omega.

  lisp. rewrite meldUniqCount; lisp.
  rewrite <- insCount with (p := t); auto. 
  rewrite <- insCount with (p := t0); auto.
  rewrite <- Heqpp. rewrite <- Heqqq. lisp. omega.

  lisp. rewrite meldUniqCount; lisp.
  rewrite <- insCount with (p := t); auto. 
  rewrite <- insCount with (p := t0); auto.
  rewrite <- Heqpp. rewrite <- Heqqq. lisp. omega.
Qed.

Lemma meldCount :
  forall same inp inq x,
    count same x (meld inp inq) 
    = count same x inp
    + count same x inq.
Proof.
  intros; destruct inp; destruct inq; destruct same; unfold count; lisp.
  unfold preCount; simpl.
  destruct x0; destruct x1; simpl; lisp.
  destruct r; lisp.
  destruct r as [v c]; destruct r0 as [w1 d0]; lisp.
  remember (LEQ v w1) as vw; destruct vw; simpl;
    rewrite insertCountM; simpl; 
      remember (x2 x v) as xv; destruct xv;
        remember (x2 x w1) as xw; destruct xw;
          try omega.
Qed.


Lemma getMinSplit :
  forall xs x,
    forall y z,
      (y,z) = getMin x xs ->
      forall f w, 
        DERP  f ->
        countT f w y
        + countM f w z
        = countT f w x 
        + countM f w xs.
Proof.
  induction xs; lisp; intros.
  inversion_clear H; lisp.
  remember (getMin t xs) as pxs; destruct pxs.
  eapply IHxs in Heqpxs; eauto. rewrite <- Heqpxs. Show Existentials.
  hisp. destruct x; destruct t0; hisp. destruct r; destruct r0; cutLEQ.
  inversion H; subst; hisp.
  inversion H; subst; hisp.
  omega.
Qed.

Lemma splitSplit :
  forall e a b c d,
    (a,b) = split c d e ->
      forall f w, 
        DERP  f ->
        countM f w a
        + fold_right plus 0 (map (countR f w) b)
        = countM f w c 
        + fold_right plus 0 (map (countR f w) d)
        + countM f w e.
Proof.
  induction e; intros; lisp.
  inversion_clear H; subst; try omega.
  destruct t; lisp.
  destruct m; lisp.
  eapply IHe in H. lisp. rewrite H. omega. auto.
  eapply IHe in H. lisp. rewrite H. omega. auto.
Qed.


Lemma countFold :
  forall l f w v,
    countM f w (fold_right skewInsert v l) 
    = countM f w v 
    + fold_right plus 0 (map (countR f w) l).
Proof.
  induction l; lisp; intros.
  rewrite insertCountM.
  rewrite IHl.  omega.
Qed.

Lemma preExtractMinSplit :
  forall x y z,
    Some (y,z) = skewExtractMin x ->
    forall f w, 
      DERP  f ->
      countM f w x
      = countR f w y 
      + countM f w z.
Proof.
  intros.
  destruct x; lisp.
  inversion H.
  remember (getMin t x) as px; destruct px; lisp.
  destruct t0; lisp.
  remember (split ($) nil m0) as mm; destruct mm; lisp.
  inversion_clear H; subst.
  erewrite <- getMinSplit; eauto. lisp.
  assert (countM f w m0 + countM f w m =
    countM f w (fold_right skewInsert (skewMeld m m1) l)).
  Focus 2. omega.

  eapply splitSplit in Heqmm; eauto. lisp.
(*1*)
  rewrite countFold. rewrite preMeldCount; auto.
  rewrite <- Heqmm. omega.
(*1*)
Qed.
  

Lemma extractMinCount :
  forall inp,
    match findMin inp with
      | None => None = extractMin inp
      | Some x => exists z,
        Some (x,z) = extractMin inp
        /\ forall same y,
          let newCount := count same y z in
            count same y inp =
            if check same y x
              then S newCount
              else newCount
    end.
Proof.
  intros.
  destruct inp.
  destruct x; lisp.
  destruct w; lisp.
  unfold findMin; lisp.
  destruct r; lisp.
  intros.
  unfold count; lisp.
  eauto.
  Print ex.
  eapply ex_intro. split. eauto.
(*
  exists (       exist (fun x0 : bootWrap => wrapHeap x0)
         match skewExtractMin m with
         | Some (pair (Top w d) cs) => Full (Top w (skewMeld d cs))
         | None => Empty
         end
         (match
            skewExtractMin m as o
            return
              (o = skewExtractMin m ->
               match
                 match o with
                 | Some (pair (Top w d) cs) => Full (Top w (skewMeld d cs))
                 | None => Empty
                 end
               with
               | Empty => True
               | Full y => rootHeap y
               end)
          with
          | Some p0 =>
              fun Heqmm : Some p0 = skewExtractMin m =>
              (let (r, m0) as p
                   return
                     (Some p = skewExtractMin m ->
                      match
                        (let (r, cs) := p in
                         match r with
                         | Top w d => Full (Top w (skewMeld d cs))
                         end)
                      with
                      | Empty => True
                      | Full y => rootHeap y
                      end) := p0 in
               fun Heqmm0 : Some (r, m0) = skewExtractMin m =>
               match
                 r as r0
                 return
                   (Some (r0, m0) = skewExtractMin m ->
                    match
                      match r0 with
                      | Top w d => Full (Top w (skewMeld d m0))
                      end
                    with
                    | Empty => True
                    | Full y => rootHeap y
                    end)
               with
               | Top a1 m1 =>
                   fun Heqmm1 : Some (Top a1 m1, m0) = skewExtractMin m =>
                   ex_intro
                     (fun v : A =>
                      true = LEQ v a1 /\ feapM a1 (skewMeld m1 m0)) a1
                     match preExtractMinRootHeap m a f Heqmm1 with
                     | conj _ H3 =>
                         conj (leqRefl a1)
                           (eq_ind (oomin a1 a1)
                              (fun a0 : A => feapM a0 (skewMeld m1 m0))
                              (preMeldHeapSome a1 m1 a1 m0 H3
                                 match preExtractMinHeap a m f Heqmm1 with
                                 | conj _ H0 => H0
                                 end) a1 (dblMin a1))
                     end
               end Heqmm0) Heqmm
          | None => fun _ : None = skewExtractMin m => I
          end eq_refl)).
*)

 
  destruct same; lisp. intros.
  remember (x0 y a) as xya; destruct xya; lisp.
  unfold preCount; lisp.
  unfold skewExtractMin; lisp.
  destruct m; lisp.
  f_equal. cutThis (getMin t m); hisp.
  destruct t0; hisp.
  destruct r; lisp.
  remember (x0 y a0) as xya0; destruct xya0; lisp.
  rewrite preMeldCount; auto.
  lisp. cutThis (split ($) [] m1); hisp.
  rewrite countFold. erewrite <- getMinSplit; auto.
  Focus 2. eauto. hisp. rewrite <- Heqxya0.
  eapply splitSplit in HeqH0; auto. hisp.
  rewrite <- HeqH0. 
  rewrite preMeldCount. omega. auto. auto.
  
  lisp. cutThis (split ($) [] m1); hisp.
  rewrite preMeldCount; auto.
  rewrite countFold. erewrite <- getMinSplit; auto.
  Focus 2. eauto. hisp. rewrite <- Heqxya0.
  eapply splitSplit in HeqH0; auto. hisp.
  rewrite <- HeqH0. 
  rewrite preMeldCount. omega. auto. auto.

  hisp.
  remember (skewExtractMin m) as mm; destruct mm; lisp.
  destruct p; lisp. destruct r; lisp.
  remember (x0 y a0) as xya0; destruct xya0; lisp.
  rewrite preMeldCount; auto.
  erewrite preExtractMinSplit; auto. Focus 2. eauto.
  lisp. rewrite <- Heqxya0. omega.
  rewrite preMeldCount; auto.
  erewrite preExtractMinSplit; auto. Focus 2. eauto.
  lisp. rewrite <- Heqxya0. omega.

  destruct m; lisp. inversion Heqmm.
Qed.
  
Instance bootV : MINQV bootPQ := {
  count := count;
  toListCount := countList;
  countSAME := countSAME;
  emptyCount := emptyCount;
  insertCount := insertCount;
  findMinCount := findMinCount;
  meldCount := meldCount;
  extractMinCount := extractMinCount
}.

(*
End Order.
End Carrier.
*)

(*
Extraction Language Haskell.
Recursive Extraction bootPQ.
Extraction Inline and_rect sig_rect proj1_sig LEQ.
Recursive Extraction bootPQ.
Extraction Inline aLEQ meldUniq_terminate.
Extraction Inline 
  preInsert preFindMin preMeld 
  preExtractMin preEmpty preToList.
Recursive Extraction bootPQ empty insert findMin extractMin toList meld.
*)
(*
Extraction "ExtractBoot.hs" 
  bootPQ empty insert findMin extractMin toList meld.
Recursive Extraction empty.
*)


Hint Unfold check.


Inductive TreeN :=
  NodeN : RootN -> nat -> ManyN -> TreeN
with RootN :=
  TopN : A -> ManyN -> RootN
with ManyN :=
  CilN : ManyN
| NonsN : TreeN -> ManyN -> ManyN.

Section ToNat.

Variable toNat : N -> nat.
Variable isoZero : toNat zero = 0.
Variable isoSucc : forall n, toNat (succ n) = S (toNat n).
Variable isoComp : forall n m, comp n m = nat_compare (toNat n) (toNat m).


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

(*
Scheme pbr_min := Minimality for posBinaryRankN Sort Prop.
Check pbr_min.
Check posBinaryRankN_ind.
*)

Definition posBinaryRank x n := posBinaryRankN (toNatM x) n.
Hint Unfold posBinaryRank.

Inductive binaryRankN : ManyN -> Prop :=
  zeroBin : binaryRankN ($$)
| posBin : forall n xs,
           posBinaryRankN xs n ->
           binaryRankN xs.
Hint Constructors binaryRankN.

Definition binaryRank x := binaryRankN (toNatM x).
Hint Unfold binaryRank.

Inductive posSkewBinaryRankN : ManyN -> nat -> Prop :=
  vanilla : forall xs n, 
            posBinaryRankN xs n ->
            posSkewBinaryRankN xs n
| skew : forall x n xs,
         rankNN x n ->
         posBinaryRankN xs n ->
         posSkewBinaryRankN (x::::xs) n.
Hint Constructors posSkewBinaryRankN.

Definition posSkewBinaryRank x n := posSkewBinaryRankN (toNatM x) n.
Hint Unfold posSkewBinaryRank.

Inductive skewBinaryRankN : ManyN -> Prop :=
  zeroSkew : skewBinaryRankN ($$)
| posSkew : forall n xs,
           posSkewBinaryRankN xs n ->
           skewBinaryRankN xs.
Hint Constructors skewBinaryRankN.

Definition skewBinaryRank x := skewBinaryRankN (toNatM x).
Hint Unfold skewBinaryRank.


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

Lemma rankRank :
  forall x n,
    rankN x n ->
    toNat (rank x) = n.
Proof.
  intros x n r. destruct x; simpl in *.
  inversion r; subst; auto.
Qed.
Hint Resolve rankRank.

Lemma rankFunction :
  forall x n m,
    rankN x n ->
    rankN x m -> 
    n = m.
Proof.
  intros x n m XN XM;
    destruct x as [v i p].
  assert (toNat i = n). eapply rankDestruct; eauto. subst.
  eapply rankDestruct; eauto.
Qed.

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

Lemma linkRank :
  forall n x y, 
    rankN x n -> 
    rankN y n -> 
    rankN (link x y) (S n).
Proof.
  intros n x y X Y.
  unfold link.
  destruct x as [v xn p]; destruct y as [w yn q].
  assert (toNat xn = n); try (eapply rankDestruct; eauto); subst.
  assert (toNat yn = toNat xn); try (eapply rankDestruct; eauto); subst.
  remember (pLEQ v w) as vw; destruct vw; simpl in *; tra0.
  rewrite H. apply simple; auto.
  rewrite H in Y. auto.
Qed.
Hint Resolve linkRank.

Lemma skewLinkRank :
  forall n x y z,
    rankN x 0 ->
    rankN y n ->
    rankN z n ->
    rankN (skewLink x y z) (S n).
Proof.
  intros n x y z X Y Z.
  unfold skewLink.
  destruct x as [a i p]; destruct y as [b j q]; destruct z as [c k r].
  tra0.
  assert (toNat i = 0); try (eapply rankDestruct; eauto); subst.
  assert (toNat j = n); try (eapply rankDestruct; eauto); subst.
  assert (toNat k = toNat j); try (eapply rankDestruct; eauto); subst.
  assert (p = ($)).  inversion X; subst.
  destruct p; simpl in *; auto. inversion H4. subst.
  unfold toNatM in X; simpl in X.
  hisp. destruct a; destruct b; destruct c.
  rewrite H0 in Z.
  cutLEQ; cutLEQ; tra0; rewrite H0; subst.
  apply skewA; auto.
  rewrite H. apply skewB; auto.
  rewrite H. apply skewB; auto.
  rewrite H. apply skewB; auto.
Qed.
Hint Resolve skewLinkRank.

Lemma eq_nat_compare :
  forall x, nat_compare x x = Eq.
Proof.
  induction x; simpl; auto.
Qed.

(*
Lemma insNoDupeHelp : 
  forall n m x xs, 
    rankN x n ->
    posBinaryRank xs m ->
    n <= m ->
    exists k, k >= n /\ posBinaryRank (ins x xs) k.
Proof.
  intros n m x xs.
  generalize dependent x;
    generalize dependent n;
      generalize dependent m.
  dependent induction xs; intros; hisp; tra0.
  Case "($)".
    unfold posBinaryRank in H0.
    unfold toNatM in H0. inversion H0.
  Case "t::xs".
    unfold posBinaryRank in H0.
    simpl in H0.
    inversion H0.
    SCase "last".
       subst.
       destruct xs. 
       SSCase "xs = ($)".
         simpl.
         destruct x; destruct t; hisp. tra0.
         assert (toNat n1 = m). eapply rankDestruct2; eauto.
         rewrite H2 in H5.
         assert (toNat n0 = n). eapply rankDestruct; eauto.
         rewrite H3 in H.
         destruct r; hisp. destruct r0; hisp.
         cutThis (comp n0 n1).
         SSSCase "n0 = n1".
           rewrite isoComp in HeqH6.
           symmetry in HeqH6.
           apply nat_compare_eq in HeqH6.
           cutLEQ.
           S4Case "a <= a0".
             exists (S (toNat n0)); hisp. omega.
             unfold posBinaryRank. simpl.
             apply last. tra0.
             apply simple.
             rewrite H3; auto.
             rewrite <- H2 in H5. 
             rewrite HeqH6. auto.
           S4Case "a < a0".
             exists (S (toNat n1)); hisp. omega.
             unfold posBinaryRank. simpl.
             apply last. tra0.
             apply simple.
             rewrite H2; auto.
             rewrite <- H3 in H.
             rewrite <- HeqH6. auto.
         SSSCase "n0 < n1".
           rewrite isoComp in HeqH6.
           symmetry in HeqH6.
           apply nat_compare_lt in HeqH6.
           exists n; hisp.
           unfold posBinaryRank; simpl.
           eapply next.
           rewrite H3; auto. Focus 2.
           rewrite H2. eauto. omega.
         SSSCase "n0 > n1".
           rewrite isoComp in HeqH6.
           symmetry in HeqH6.
           apply nat_compare_gt in HeqH6.
           assert False as f. omega. inversion f.
       SSCase "xs = t0 ::: xs".
         simpl in *. inversion H4.
     SCase "next".
       subst.
       destruct xs.
       SSCase "xs = ($)".
         simpl in *.
         inversion H7.
       SSCase "xs = t0 ::: xs".
         simpl in *.
         
           cutLEQ.
           S4Case "a <= a0".
             exists (S (toNat n0)); hisp. omega.
             unfold posBinaryRank. simpl.
             apply last. tra0.
             apply simple.
             rewrite H3; auto.
             rewrite <- H2 in H5. 
             rewrite HeqH6. auto.
           S4Case "a < a0".
             exists (S (toNat n1)); hisp. omega.
             unfold posBinaryRank. simpl.
             apply last. tra0.
             apply simple.
             rewrite H2; auto.
             rewrite <- H3 in H.
             rewrite <- HeqH6. auto.

           apply last; hisp.


             exists (S (toNat n1)); hisp. omega.
             unfold posBinaryRank. simpl.
             apply last. tra0.
             apply simple.
             assert (toNat n1 = m). eapply rankDestruct2; eauto.
             rewrite H3 in H5. rewrite H3; auto.
             rewrite HeqH3. auto.


             rewrite <- HeqH3. rewrite H2. auto.
             tra0.
             auto.
             apply 
    unfold toNatM in H0. simpl in H0.

    SCase "next".
    
  
  unfold posBinaryRank in xsm.
  dependent induction xsm.
  Case "last".
    intros j jn y yj.
    destruct x0 as [v xx p]. tra0.  
    assert (xx = n). eapply rankDestruct2; eauto. subst.
    destruct y as [w yy q]. 
    assert (toNat yy = j). eapply rankDestruct; eauto. subst.
    unfold ins.
    unfold rank. remember (toNat yy) as j.
    remember (nat_compare j n) as ncjn; destruct ncjn.
    SCase "j = n".
      assert (j = n). apply nat_compare_eq; auto. subst.
      exists (S n). split.
      auto.
      induction xs; simpl in *. inversion x.
      destruct t; simpl.
      simpl in x.
      inversion x; subst.
      rewrite isoComp.
      rewrite H3.
      rewrite eq_nat_compare.
      hisp. destruct w; destruct r; hisp.
      cutLEQ. simpl.
      Check nat_compare_eq.
      rewrite <- nat_compare_eq.
simpl.

simpl. fold (ins (Node w yy q) xs).

  tra0. 

constructor. apply linkRank; auto.
    SCase "j < n".
      assert (j < n) as jn2. apply nat_compare_lt; auto.
      exists j. 
      split. auto.
      eapply next; eauto.
    SCase "j > n".
      assert (j > n) as jn2. apply nat_compare_gt; auto.
      assert False as f. omega. inversion f.
  Case "next".
    intros j jn y yj.
    destruct x as [v xx p]. 
    assert (xx = n). eapply rankDestruct; eauto. subst.
    destruct y as [w yy q]. 
    assert (yy = j). eapply rankDestruct; eauto. subst.
    unfold ins.
    unfold rank at 1. unfold rank at 1.
    remember (nat_compare j n) as ncjn; destruct ncjn.
    SCase "j = n".
      assert (j = n). apply nat_compare_eq; auto. subst.
      fold ins.
      assert (exists k, k >= S n 
        /\ posBinaryRank (ins (link (Node w n q) (Node v n p)) xs) k).
      eapply IHxsm.
      auto. auto.
      destruct H1.
      destruct H1.
      exists x.
      split. auto with arith.
      auto.
    SCase "j < n".
      assert (j < n) as jn2. apply nat_compare_lt; auto.
      exists j. 
      split; auto.
      eapply next; eauto.
    SCase "j > n".
      assert (j > n) as jn2. apply nat_compare_gt; auto.
      assert False as f. omega. inversion f.
Qed.
*)

(*
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
      apply nat_compare_eq in HeqH3.
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
*)

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
  unfold posBinaryRank in xsm. (*
  generalize dependent isoZero. clear isoZero.
  generalize dependent isoSucc. clear isoSucc.
  generalize dependent isoComp. clear isoComp.
  generalize dependent zero. clear zero.*)
  dependent induction xsm generalizing xs.
  Case "last".
(*    clear toNat0 comp0 succ0.
    intros zero isoComp isoSucc isoZero.*)
    destruct xs; simpl in *. inversion x.
    inversion x; subst. assert (xs = ($)).
    induction xs; auto.
    inversion x; subst. subst. clear x. clear H2.
    intros j jn y yj.
    destruct t as [v xx p]. tra0. hisp.

    assert (toNat xx = n). eapply rankDestruct; eauto.
(*    apply rankDestruct2 with (v := toNatR v) (c := toNatM p).
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

  Case "next". (*
    clear succ0 comp0 toNat0 O0.
    intros zero isoComp isoSucc isoZero.
*)
    destruct xs; simpl in *. inversion x.
    inversion x; subst. 
    assert (forall n : nat,
      n <= m ->
      forall x : Tree,
        rankN x n -> exists k : nat, k >= n /\ posBinaryRank (ins x xs) k) 
    as IH.
    exact (IHxsm xs eq_refl).
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
      apply nat_compare_eq in HeqH3.
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

Lemma insNoDupe : 
  forall n x xs, 
    posSkewBinaryRank (x:::xs) n ->
    exists k, k >= n /\ posBinaryRank (ins x xs) k.
Proof.
  intros n x xs xxsn.
  inversion xxsn; subst.
  Case "vanilla".
    destruct xs.
    SCase "xs = nil".
      eauto.
    SCase "xs = p ::: _".
      simpl. rename t into p.
      assert (comp (rank x) (rank p) = Lt).
      destruct x; destruct p; simpl.
      inversion H; subst.
      inversion H5; subst.
      assert (toNat n0 = n). eapply rankDestruct; eauto.
      subst.
      assert (toNat n1 = m1). eapply rankDestruct; eauto.
      subst.
      rewrite isoComp.
      apply nat_compare_lt; auto.
      assert (toNat n0 = n). eapply rankDestruct; eauto.
      subst.
      assert (toNat n1 = m1). eapply rankDestruct; eauto.
      subst. rewrite isoComp.
      apply nat_compare_lt; auto.
      rewrite H0.
      eauto.
  Case "skew".
    rename H1 into xn.
    rename H3 into xsn.
    eapply insNoDupeHelp; eauto.
Qed.

Lemma preInsertRank :
  forall x ys,
    skewBinaryRank ys ->
    skewBinaryRank (skewInsert x ys).
Proof with auto.
  intros x ys P.
  destruct ys.
  Case "ys = ($)".
    simpl.
    SCase "skewBinaryRank [Node x 0 ($)]".
      eapply posSkew.
      eapply vanilla.
      eapply last. rewrite isoZero.
      apply singleton.
  Case "ys = p ::: _".
    unfold skewInsert.
    destruct ys.
    SCase "ys = nil".
      rename P into R.
      SSCase "skewBinaryRank [Node x 0 ($); p]".
        eapply posSkew.
        inversion R as [|n xs P]; subst.
        inversion P; subst.
        SSSCase "".
          destruct n.
          eapply skew; eauto. rewrite isoZero. constructor.
          constructor.
          eapply next. rewrite isoZero. constructor.
          Focus 2. eauto.
          auto with arith.
        SSSCase "impossible".
          inversion H3.
    SCase "ys = p0 ::: _".
      rename t0 into q.
      rename P into R. rename t into p.
      remember (comp (rank p) (rank q)) as pq; destruct pq.
      SSCase "rank p = rank q".
        assert (toNat (rank p) = toNat (rank q)) as pq. 
        rewrite isoComp in Heqpq.
        apply nat_compare_eq; auto.
        SSSCase "skewBinaryRank (skewLink (Node x 0 ($)) p q ::: ys".
          eapply posSkew.
          inversion R; subst.
          inversion H; subst.
          assert (toNat (rank p) = n).
          inversion H0; auto; eapply rankRank; auto.
          subst.
          assert (toNat (rank p) < toNat (rank q)).
          inversion H0; subst.
          assert (toNat (rank q) = m).
          inversion H6; auto; eapply rankRank; auto.
          subst. auto.
          assert False as f. omega. inversion f.

          instantiate (1 := S (toNat (rank p))).
          assert (toNat (rank p) = n).
          eapply rankRank; auto.
          subst.
          inversion H4; subst.
          eapply vanilla; auto.
          destruct ys; subst; auto.
          apply last. apply skewLinkRank; auto.
          tra0. rewrite isoZero. auto.
          simpl in H3. inversion H3.

          inversion H5; subst.
          eapply skew; auto.
          apply skewLinkRank; auto.
          tra0. rewrite isoZero. auto.
          
          eapply vanilla; auto.
          apply next with (m := S m0).
          apply skewLinkRank; auto.
          tra0. rewrite isoZero. auto.
          omega. auto.
      SSCase "rank p <> rank q".
        assert (toNat (rank p) <> toNat (rank q)) as pq. 
        rewrite isoComp in Heqpq.
        symmetry in Heqpq.
        apply nat_compare_lt in Heqpq. omega.
        apply posSkew with (n := 0).
        inversion R; subst.
        destruct n.
        SSSCase "skew".
          simpl.
          apply skew.
          rewrite isoZero. constructor.
          simpl in H.
          inversion H; subst.
          auto.
          assert (toNat (rank p) = 0). apply rankRank; auto.
          assert (toNat (rank q) = 0).
          inversion H4; subst; apply rankRank; auto.
          assert False as f. omega. inversion f.

       SSSCase "vanilla".
         simpl.
         apply vanilla.
         apply next with (m := S n). rewrite isoZero.
         constructor. omega.
         simpl in H.
         inversion H; subst.
         auto.
         assert (toNat (rank p) = S n). apply rankRank; auto.
         assert (toNat (rank q) = S n).
         inversion H4; subst;
         apply rankRank; auto.
         assert False as f. omega. inversion f.
      SSCase "rank p <> rank q".
        assert (toNat (rank p) <> toNat (rank q)) as pq. 
        rewrite isoComp in Heqpq.
        symmetry in Heqpq.
        apply nat_compare_gt in Heqpq. omega.
        apply posSkew with (n := 0).
        inversion R; subst.
        destruct n.
        SSSCase "skew".
          simpl.
          apply skew.
          rewrite isoZero. constructor.
          simpl in H.
          inversion H; subst.
          auto.
          assert (toNat (rank p) = 0). apply rankRank; auto.
          assert (toNat (rank q) = 0).
          inversion H4; subst; apply rankRank; auto.
          assert False as f. omega. inversion f.

       SSSCase "vanilla".
         simpl.
         apply vanilla.
         apply next with (m := S n). rewrite isoZero.
         constructor. omega.
         simpl in H.
         inversion H; subst.
         auto.
         assert (toNat (rank p) = S n). apply rankRank; auto.
         assert (toNat (rank q) = S n).
         inversion H4; subst;
         apply rankRank; auto.
         assert False as f. omega. inversion f.
Qed. 

Definition min x y :=
  match nat_compare x y with
    | Lt => x
    | _ => y
  end.

Lemma meldUniqRank :
  forall x n y m,
    posBinaryRank x n ->
    posBinaryRank y m ->
    exists k, k >= min n m
      /\ posBinaryRank (meldUniq (x,y)) k.
Proof with auto.
  assert 
    (let P := 
      fun (xy:(Many*Many)) r =>
        let (x,y) := xy in
          forall n m,
            posBinaryRank x n ->
            posBinaryRank y m ->
            exists k, k >= min n m
              /\ posBinaryRank r k
            in forall xy, P xy (meldUniq xy)).
  eapply meldUniq_ind; intros; auto.

  inversion H.
  inversion H0.
  assert (toNat (rank p) = n). inversion H0; apply rankRank; auto.
  assert (toNat (rank q) = m). inversion H1; apply rankRank; auto.
  subst.
  rewrite isoComp in e0.
  assert (toNat (rank p) < toNat (rank q)). apply nat_compare_lt; auto.
  inversion H0; subst. destruct ps.
  unfold min. rewrite e0.
  exists (toNat (rank p)); split; auto.
  simpl. unfold posBinaryRank. simpl.
  rewrite meldUniq_equation; fold toNatM.
  Check meldUniq_equation.
  eapply next.
  Focus 2. 
  eauto. auto. auto. simpl in H5. inversion H5.
  unfold min. rewrite e0. 
  exists (toNat (rank p)); split; auto.
  assert (exists k, k >= min m (toNat (rank q))
    /\ posBinaryRank (meldUniq (ps, q:::qs)) k).
  apply H; auto.
  destruct H3.
  destruct H3. unfold posBinaryRank. simpl.
  eapply next.
  Focus 3.
  eauto. eauto.
  unfold min in H3.
  remember (nat_compare m (toNat (rank q))) as mq; destruct mq; omega.
  
  assert (toNat (rank p) = n). inversion H0; apply rankRank; auto.
  assert (toNat (rank q) = m). inversion H1; apply rankRank; auto.
  subst.
  assert (toNat (rank q) < toNat (rank p)).
  rewrite isoComp in e0.
  apply nat_compare_gt; auto.
  inversion H1; subst.
  destruct qs.
  unfold min. rewrite <- isoComp.
  rewrite e0.
  exists (toNat (rank q)); split; auto.
  rewrite meldUniq_equation.  unfold posBinaryRank. simpl.
  eapply next.
  Focus 3.
  eauto. auto. auto. simpl in H5. inversion H5.
  unfold min. rewrite <- isoComp.
  rewrite e0. 
  exists (toNat (rank q)); split; auto.
  assert (exists k, k >= min (toNat (rank p)) m
    /\ posBinaryRank (meldUniq (p:::ps, qs)) k).
  apply H; auto.
  destruct H3.
  destruct H3. unfold posBinaryRank. simpl.
  eapply next.
  Focus 3.
  eauto. eauto.
  unfold min in H3.
  remember (nat_compare (toNat (rank p)) m) as mq; destruct mq; omega.

  assert (toNat (rank p) = toNat (rank q)). apply nat_compare_eq; auto.
  rewrite <- isoComp; auto.
  assert (exists k : nat,
    k >= S (min n m)
    /\ posBinaryRank (ins (link p q) (meldUniq (ps, qs))) k).
  apply insNoDupe.
  unfold posSkewBinaryRank. simpl.
  inversion H0; inversion H1; subst.
  destruct ps; destruct qs.
  rewrite meldUniq_equation.
  eapply vanilla. eapply last. eapply linkRank.
  assert (toNat (rank p) = n). apply rankRank; auto; subst.
  assert (toNat (rank q) = m). apply rankRank; auto; subst.
  unfold rankN. 
  rewrite H3 in *. rewrite H4 in *. subst.
  unfold min.
  remember (nat_compare (toNat (rank p)) (toNat (rank p))) as pp.
  destruct pp; auto.
  assert (toNat (rank p) = n). apply rankRank; auto; subst.
  assert (toNat (rank q) = m). apply rankRank; auto; subst.
  rewrite H3 in *. rewrite H4 in *. subst.
  unfold min.
  remember (nat_compare (toNat (rank p)) (toNat (rank p))) as pp.
  destruct pp; auto.
  simpl in H9. inversion H9.
  simpl in H5. inversion H5. simpl in H5. inversion H5.
  destruct ps.
  
  rewrite meldUniq_equation.
  assert (toNat (rank p) = n). apply rankRank; auto; subst.
  assert (toNat (rank q) = m). apply rankRank; auto; subst.
  rewrite H3 in *; rewrite H4 in *; subst.
  assert (min (toNat (rank p)) (toNat (rank p)) = toNat (rank p)) as rp.
  unfold min.
  remember (nat_compare (toNat (rank p)) (toNat (rank p))) as pp.
  destruct pp; auto.
  rewrite rp in *.
  inversion H10. subst.
  eapply skew; auto. 
  eapply linkRank; auto.
  subst.
  eapply vanilla; auto.
  eapply next. Focus 3. eauto. eapply linkRank; auto.
  auto. omega.
  simpl in H5. inversion H5.
  destruct qs.
  
  rewrite meldUniq_equation.
  assert (toNat (rank p) = n). apply rankRank; auto; subst.
  assert (toNat (rank q) = m). apply rankRank; auto; subst.
  rewrite H3 in *; rewrite H4 in *; subst.
  assert (min (toNat (rank p)) (toNat (rank p)) = toNat (rank p)) as rp.
  unfold min.
  remember (nat_compare (toNat (rank p)) (toNat (rank p))) as pp.
  destruct pp; auto.
  rewrite rp in *.
  inversion H6. subst.
  eapply skew; destruct ps; auto.
  apply linkRank; auto. apply linkRank; auto.
  subst.
  eapply vanilla; destruct ps; auto.
  eapply next. Focus 3. eauto. apply linkRank; auto.
  auto. omega. simpl in *.
  eapply next. Focus 3. eauto.
  apply linkRank; auto. auto. omega.
  simpl in H11. inversion H11.

  assert (toNat (rank p) = n). apply rankRank; auto; subst.
  assert (toNat (rank q) = m). apply rankRank; auto; subst.
  rewrite H3 in *; rewrite H4 in *; subst.
  assert (min (toNat (rank p)) (toNat (rank p)) = toNat (rank p)) as rp.
  unfold min.
  remember (nat_compare (toNat (rank p)) (toNat (rank p))) as pp.
  destruct pp; auto.
  rewrite rp in *.
  
  assert (exists k, k >= min m0 m1
    /\ posBinaryRank (meldUniq (ps,qs)) k).
  apply H; auto.
  destruct H2.
  destruct H2.
  remember (nat_compare (S (toNat (rank p))) x) as spx.
  destruct spx.
  assert (S (toNat (rank p)) = x). 
  apply nat_compare_eq. auto.
  subst.
  apply skew; auto. apply linkRank; auto.
  assert (S (toNat (rank p)) < x). apply nat_compare_lt. auto.
  apply vanilla.
  eapply next. apply linkRank; auto.
  Focus 2.
  eauto.
  auto.
  assert (S (toNat (rank p)) > x). apply nat_compare_gt. auto.
  assert (S (toNat (rank p)) < x).
  assert (S (toNat (rank p)) <= min m0 m1).
  assert (S (toNat (rank p)) <= m0); auto with arith.
  assert (S (toNat (rank p)) <= m1); auto with arith.
  unfold min.
  remember (nat_compare m0 m1) as mm; destruct mm; auto.
  omega. assert False as f. omega. inversion f.

  destruct H3.
  destruct H3.
  exists x. split.
  auto with arith.
  auto.

  simpl in H.
  intros.
  pose (H (x,y)) as I.
  simpl in I.
  pose (I n m H0 H1) as J.
  destruct J.
  exists x0.
  split.
  destruct H2.
  auto.
  destruct H2. auto.
Qed.
  
  
Lemma preMeldRank :
  forall x y,
    skewBinaryRank x ->
    skewBinaryRank y ->
    skewBinaryRank (skewMeld x y).
Proof with auto.
  intros x y xR yR.
  unfold skewMeld.
  destruct x; destruct y.
  simpl. rewrite meldUniq_equation. auto.
  simpl. rewrite meldUniq_equation.
  inversion yR; subst. rename t into p.
  edestruct insNoDupe with (n := n) (x := p); eauto.
  eapply posSkew. eapply vanilla.
  destruct H0. eapply H1.
  simpl. rewrite meldUniq_equation.
  inversion xR; subst. rename t into p.
  edestruct insNoDupe with (n := n) (x := p); eauto.
  eapply posSkew. eapply vanilla.
  destruct H0.
  destruct (ins p x); eauto.

  rename t0 into q.
  inversion xR; inversion yR; subst.
  rename n0 into m.
  inversion H; inversion H1;
    inversion H0; inversion H4; subst;
  simpl; edestruct insNoDupe as [R S]; 
    edestruct insNoDupe as [T U];
      edestruct meldUniqRank as [P Q];
        try (eapply posSkew; 
          apply vanilla; 
            destruct Q; eauto; eauto; eauto);
        try (destruct U; eauto);
          try (destruct S; eauto); eauto.
Qed.


Lemma toFromNat : forall n, toNat (fromNat n) = n.
Proof.
  induction n.
  simpl. rewrite isoZero. auto.
  simpl. rewrite isoSucc. auto.
Qed.

Lemma splitPosRank :
  forall v n c,
    rankP (Node v n c) ->
    forall r m, posBinaryRank r m ->
      toNat n <= m ->
      forall h t z, (h,t) = split r z c ->
        exists k, posSkewBinaryRank h k.
Proof.
  intros v n c H.
  unfold rankP in H.
  simpl in H.
  dependent induction H generalizing n c; intros. subst.
  destruct c.
  simpl in H1. inversion H1. subst.
  eauto. simpl in x1. inversion x1.
  destruct c. simpl in x0. inversion x0. simpl in x0.
  simpl in H3. inversion x0; subst. clear x0.
  destruct t0 as [w j q].
  simpl in *. assert (toNat j = n0). eauto. subst.
  destruct q.
  eapply IHrankNN1. Focus 4.
  eauto. auto. eauto. auto with arith. omega.
  eapply IHrankNN1. Focus 4.
  eauto. auto.
  unfold posBinaryRank. simpl.
  eapply next. eauto.
  Focus 2. eauto.
  auto with arith. omega. auto.
  destruct c. simpl in x1. inversion x1.
  destruct c. simpl in x1. inversion x1.
  simpl in x1. inversion x1. subst. clear x1.
  destruct c. 
  destruct t0 as [a b c]; destruct t1 as [d e f].
  assert (toNat b = n0). eauto; subst.
  assert (toNat e = n0). eauto; subst.
  subst.
  simpl in H3. destruct c; simpl in *.
(**)
  inversion H. subst. destruct f; simpl in *.
  inversion H3. subst. clear H3.
  exists m. eauto.
  inversion H3. subst. clear H3.
  rewrite H5 in H0. rewrite<- H8 in H0.
  inversion H0. subst.
  destruct f. inversion H3; subst. clear H3.
  exists (toNat b).
  apply vanilla.
  simpl.
  eapply next. auto. Focus 2. eauto. omega.
  inversion_clear H3; subst.
  exists (toNat e); eauto. subst.
  unfold posSkewBinaryRank. simpl.
  apply skew. auto. rewrite H5. auto.
  simpl in H0.
  subst. rewrite H5 in H0. auto.
  eapply next. rewrite H5. auto. Focus 2.
  eauto. omega.
  simpl in H7. inversion H7.
  destruct c. inversion x1. destruct c.
  inversion x1. simpl in x1.
  inversion x1; subst.
  destruct t0. clear x1. simpl in H5.
  inversion H5. subst. clear H5.
  simpl in H3.
  destruct t1; simpl in *.
  destruct m0.
  destruct m1. simpl in *. clear H8.
  eapply IHrankNN1. Focus 4. eauto.
  Focus 2. eauto.
  instantiate (1 := fromNat n0).
  rewrite toFromNat. auto. 
  rewrite toFromNat. omega.
  clear H8.
  eapply IHrankNN1. Focus 4. eauto.
  Focus 2. 
  assert (toNat n3 = n0). eauto.
  unfold posBinaryRank. simpl.
  eapply next. eauto. Focus 2. eauto.
  instantiate (1 := fromNat n0).
  rewrite toFromNat. auto. omega. rewrite toFromNat. auto.
  inversion H8.
Qed.

Lemma splitRank :
  forall v n c,
    rankP (Node v n c) ->
    forall h t z, (h,t) = split ($) z c ->
      skewBinaryRank h.
Proof.
  intros v n c H.
  unfold rankP in H.
  simpl in H. unfold rankPN in *.
  simpl in *.
  dependent induction H generalizing v n c; intros.
  Case "singleton".
  destruct c.
  simpl in H. inversion H; subst. eauto.
  inversion x1.
  Case "simple".

  destruct c. inversion x0. inversion x0. subst. clear x0.  

  rename t0 into y.
  destruct y as [a b d].
  assert (toNat b = n0); eauto; subst.
  simpl in H1.
    destruct d.
    SCase "d = ($)".
      inversion H0. subst.
      eapply IHrankNN1. auto. auto. eauto.
    SCase "d = t0 :: d".
      assert (exists k, posSkewBinaryRank h k).
      eapply splitPosRank.
      Focus 4. eauto. unfold rankP.
      simpl. unfold rankPN. simpl.
      simpl in *. eapply H.
      unfold posBinaryRank. simpl. eapply last. eauto.
      auto.
      destruct H2. eauto.
  Case "skewA".
    subst.
    destruct c. inversion x1.
    destruct c. inversion x1.
    destruct c. Focus 2. inversion x1.
    simpl in x1.
    inversion x1; subst.  clear x1.

    destruct t0. simpl in H1.
    destruct m; simpl in *.
    destruct t1; simpl in *.
    destruct m; simpl in *.
    inversion_clear H1; subst; auto.
    inversion_clear H1; subst; auto.
    unfold skewBinaryRank. simpl.
    eapply posSkew. eapply vanilla. eapply last. eauto.
    destruct t1; simpl in *.
    destruct m0; simpl in *.
    inversion_clear H1; subst; auto.
    eapply posSkew. eapply vanilla. eapply last. eauto.
    inversion_clear H1; subst; auto.
    unfold skewBinaryRank. simpl.
    eapply posSkew. eapply skew. eauto.
    eapply last. eauto.

Case "skewB".
    subst.
    destruct c. inversion x1.
    destruct c. inversion x1.
    simpl in x1. inversion x1. subst. clear x1.

    destruct t0. simpl in H1.
    destruct m; simpl in *.
    destruct t1; simpl in *.
    destruct m; simpl in *.

    eapply IHrankNN1 with (n := fromNat n0) in H1; auto.
    rewrite toFromNat; eauto. rewrite toFromNat. auto.

    eapply splitPosRank with (n := fromNat n0) in H1.
    destruct H1. eauto.
    unfold rankP. simpl. unfold rankPN. simpl. 
    rewrite toFromNat. eauto.
    unfold posBinaryRank. simpl.
    apply last. eauto.
    rewrite toFromNat. auto.

    inversion H3.
Qed.

Lemma getMinBinRank:
  forall x n,
    rankN x n ->
    forall xs m, posBinaryRank xs m ->
      n < m ->
      forall y z,
        (y,z) = getMin x xs ->
        (exists k, k >= n /\
          posBinaryRank z k)
        /\ (exists j, j >= n /\
          rankN y j).
Proof.
  intros x n xn xs. 
  generalize dependent x;
    generalize dependent n.
  induction xs; intros.
  inversion H. rename t into a.
  simpl in H1.
  remember (getMin a xs) as axs.
  destruct axs as [t ts].
  remember (pLEQ (root x) (root t)) as rxt.
  destruct rxt.
  inversion_clear H1; subst.
  split. exists m; eauto 10 with arith.
  eauto.
  inversion_clear H1; subst.
  inversion H; subst.
  destruct xs. Focus 2. inversion H3. clear H3.
  simpl in Heqaxs; eauto.
  inversion_clear Heqaxs; subst; eauto.
  split. eauto 10. exists n. split; auto.
  unfold posBinaryRank. simpl.
  apply last. auto.
  exists m. split. omega. auto.
  assert ((exists k, k >= m /\ posBinaryRank ts k) /\
    (exists j, j >= m /\ rankN t j)).
  eapply IHxs.
  Focus 2. eauto. Focus 3. eauto.
  eauto. eauto.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct H2.
  split.
  exists n. split; auto. eapply next. auto. Focus 2. eauto.
  omega.
  exists x1. split. omega. auto.
Qed.

Lemma getMinQRank:
  forall x xs,
    skewBinaryRank (x:::xs) ->
    forall y z,
      (y,z) = getMin x xs ->
      skewBinaryRank z.
Proof.
  intros x xs xxs.
  inversion xxs; subst.
  inversion H; subst.
  inversion H0; subst.
  destruct xs. Focus 2. inversion H3. clear H3.
  simpl; intros. inversion H1; subst; eauto.
  intros.
  assert ((exists k, k >= n /\
    posBinaryRank z k)
  /\ (exists j, j >= n /\
    rankN y j)). eapply getMinBinRank.
  Focus 4. eauto. auto. eauto. auto.
  destruct H2. destruct H5. destruct H5. destruct H2. destruct H2.
  eapply posSkew. eapply vanilla. eauto.
  inversion H4; subst.
  destruct xs. inversion H0. simpl in *. inversion H0. 
  destruct xs. Focus 2. inversion H6.
  clear H6; simpl in *. subst. clear H0.
  rename t into x0.
  remember (pLEQ (root x) (root x0)) as xx0; destruct xx0; intros.
  inversion_clear H0; subst; eauto.
  inversion_clear H0; subst; eauto.
  unfold skewBinaryRank. simpl.
  eauto.
  destruct xs. inversion H0.
  simpl in *. inversion H0. subst. clear H0.
  simpl.
  intros.
  remember (getMin t xs) as x00; destruct x00.
  rename t0 into p.
  remember (pLEQ (root x) (root p)) as xp; destruct xp.
  inversion_clear H0; subst. eauto.
  rename m0 into l.
  assert ((exists k, k >= n /\
    posBinaryRank l k)
  /\ (exists j, j >= n /\
    rankN p j)). eapply getMinBinRank.
  Focus 4. eauto.
  auto. eauto. auto.
  destruct H6.
  destruct H6. destruct H6. destruct H7. destruct H7.
  inversion_clear H0. subst.
  apply posSkew with (n := n).
  destruct H6. eapply skew. eauto. eauto.
  eapply vanilla.
  eapply next. eauto. Focus 2. eauto. omega.
Qed.

Lemma getMinTRank:
  forall x xs,
    skewBinaryRank (x:::xs) ->
    forall y z,
      (y,z) = getMin x xs ->
      rankP y.
Proof.
  intros x xs; generalize dependent x; induction xs; 
    intros x; destruct x; unfold rankP; intros.
  inversion_clear H0; simpl.
  inversion H; subst.
  inversion H0; subst.
  inversion H1; subst.
  pose H3 as NN.
  apply rankDestruct in NN; subst. auto.
  inversion H7.
  inversion H5.

  simpl in H0.
  rename t into a.
  remember (getMin a xs) as axs; destruct axs.
  remember (pLEQ r (root t)) as ap; destruct ap;
    inversion_clear H0; subst.
  inversion H; subst.
  inversion H0; subst.
  inversion H1; subst.
  pose H4 as NN.
  apply rankDestruct in NN; subst; auto.
  pose H3 as NN.
  apply rankDestruct in NN; subst; auto.
  eapply IHxs.
  Focus 2. eauto.
  inversion H; subst.
  inversion H0; subst.
  inversion H1; subst.
  eauto.
  eauto.
Qed.

Lemma extractMinRank :
  forall x,
    skewBinaryRank x ->
    forall t u,
      Some (t,u) = skewExtractMin x ->
      skewBinaryRank u.
Proof.
  intros x S t u T.
  unfold skewExtractMin in *.
  destruct x; eauto. inversion T.
  rename t0 into p.
  remember (getMin p x) as yz. destruct yz as [y z].
  destruct y as [a b c].
  remember (split ($) [] c) as rs.
  destruct rs as [r s].
  assert (skewBinaryRank r) as ss.
  eapply splitRank. Focus 2. eauto.
  eapply getMinTRank. Focus 2. eauto. auto.
  assert (skewBinaryRank z) as zz.
  eapply getMinQRank. Focus 2. eauto. auto.
  assert (skewBinaryRank (skewMeld z r)).
  eapply preMeldRank; auto.
  inversion_clear T; subst.
  clear Heqrs.
  induction s.
  simpl; auto.
  simpl.
  apply preInsertRank; auto.
Qed.
End ToNat.
End Order.
End Carrier.
