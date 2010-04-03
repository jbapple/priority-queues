Set Implicit Arguments.

Require Export PQSig.
Require Export List.

(*
Inductive preT' A :=
  Node : Root A -> nat -> list (preT' A) -> preT' A
with Root A :=
  Top : A -> list (preT' A) -> Root A.
Scheme pre_gen := Induction for preT' Sort Prop
with root_gen := Induction for Root Sort Prop.

Fixpoint preT'_size a (x:preT' a) :=
  match x with
    | Node y _ c =>
      Root_size y + fold_right plus 0 (map (@preT'_size _) c)
  end
with Root_size a (x:Root a) :=
  match x with
    | Top _ c => fold_right plus 0 (map (@preT'_size _) c)
  end.

Check pre_gen.
*)

(*Unset Elimination Schemes.*)

Inductive preT' A :=
  Node : Root A -> nat -> ml A -> preT' A
with Root A :=
  Top : A -> ml A -> Root A
with ml A :=
  cil : ml A
| nons : preT' A -> ml A -> ml A.

Set Maximal Implicit Insertion.
Implicit Arguments cil [A].
Unset Maximal Implicit Insertion.

Scheme preT'_w := Induction for preT' Sort Prop
with Root_w := Induction for Root Sort Prop
with ml_w := Induction for ml Sort Prop.

Set Elimination Schemes.

Notation "[[ x | .. | y ]]" := (nons x .. (nons y cil) ..).
Notation "a ::: b" := (nons a b) (at level 60, right associativity).
Notation "$" := cil (at level 60).

Definition root A (x:Root A) :=
  match x with
    | Top v _ => v
  end.

Definition toot A (x:preT' A) :=
  match x with
    | Node v _ _ => root v
  end.

Fixpoint toListT A (x:preT' A) (r:list A) {struct x} : list A :=
  match x with
    | Node h _ t => toListR h (toListM t r)
  end
with toListR (A:Type) (x:Root A) r :=
  match x with
    | Top v t => toListM t (v::r)
  end
with toListM (A:Type) (x:ml A) r : list A :=
  match x with
    | cil => r
    | nons h t => toListT h (toListM t r)
  end.


(*
Locate "$".
Locate "[]".
Locate "::".

Print cons.
Print cil.

Check (let x := Node (Top 1 cil) 0 cil in [[ x | x ]]).
*)

Combined Scheme all_ind from preT'_w, Root_w, ml_w.

(*
Inductive heapT A (leq:A->A->bool) v : preT' A -> Prop :=
  theap : forall w c d n,
          heapR leq v (Top w c) ->
          heapM leq w d ->
          heapT leq v (Node (Top w c) n d)
with heapR A (leq:A->A->bool) v : Root A -> Prop :=
  rheap : forall w c,
          true = leq v w ->
          heapM leq w c ->
          heapR leq v (Top w c)
with heapM A (leq:A->A->bool) v : ml A -> Prop :=
  hcil : heapM leq v cil
| hnons : forall x xs,
          heapT leq v x ->
          heapM leq v xs ->
          heapM leq v (x:::xs).
*)

Fixpoint feapT A (leq:A->A->bool) v (x:preT' A) {struct x} : Prop :=
  match x with
    | Node wc n d =>
      feapR leq v wc
      /\ match wc with
           | Top w c => feapM leq w d
         end
  end
with feapR A (leq:A->A->bool) v (x:Root A) {struct x} : Prop :=
  match x with
    | Top w c => true = leq v w /\ feapM leq w c
  end
with feapM A (leq:A->A->bool) v (x:ml A) {struct x} : Prop :=
  match x with
    | ($) => True
    | x:::xs => feapT leq v x /\ feapM leq v xs
  end.

(*
Fixpoint feapT A (leq:A->A->bool) v (x:preT' A) {struct x} : Prop :=
  match x with
    | Node wc n d =>
      feapR leq v wc
      /\ match wc with
           | Top w c => feapM leq (Some w) d
         end
  end
with feapR A (leq:A->A->bool) v (x:Root A) {struct x} : Prop :=
  match x with
    | Top w c => true = leq v w /\ feapM leq (Some w) c
  end
with feapM A (leq:A->A->bool) v (x:ml A) {struct x} : Prop :=
  match x with
    | ($) => True
    | x:::xs => 
      match v with
        | Some w => feapT leq w x /\ feapM leq (Some w) xs
        | None => False
      end
  end.

Check feapT. Check feapR. Check feapM.

Fixpoint feapT A (leq:A->A->bool) v (x:preT' A) {struct x} : Prop :=
  match x with
    | Node wc n d =>
      feapR leq v wc
      /\ match wc with
           | Top w c => feapM leq (Some w) d
         end
  end
with feapR A (leq:A->A->bool) v (x:Root A) {struct x} : Prop :=
  match x with
    | Top w c =>
      match v with
        | Some q => true = leq q w
        | None => True
      end
      /\ feapM leq (Some w) c
  end
with feapM A (leq:A->A->bool) v (x:ml A) {struct x} : Prop :=
  match x with
    | ($) => True
    | x:::xs => 
      feapT leq v x
      /\ feapM leq v xs
  end.
*)

(*
Functional Scheme feapT_ind := Induction for feapT Sort Prop
with feapR_ind := Induction for feapR Sort Prop
with feapM_ind := Induction for feapM Sort Prop.
*)

(*
Function weapT (A:Type) (leq:A->A->bool) (v:A) (x:preT' A) {struct x} : Prop :=
  match x with
    | Node wc n d =>
      weapR leq v wc
      /\ match wc with
           | Top w c => weapM leq w d
         end
  end
with weapR (A:Type) (leq:A->A->bool) (v:A) (x:Root A) {struct x} : Prop :=
  match x with
    | Top w c =>
      true = leq v w
      /\ weapM leq w c
  end
with weapM (A:Type) (leq:A->A->bool) (v:A) (x:ml A) {struct x} : Prop :=
  match x with
    | ($) => True
    | x:::xs => 
      weapT leq v x
      /\ weapM leq v xs
  end.

Check weapT_equation.
*)

(*
Functional Scheme weapT_ind := Induction for weapT Sort Prop.
*)

(*
Hint Constructors heapT.
Hint Constructors heapR.
Hint Constructors heapM.

Set Maximal Implicit Insertion.
Implicit Arguments hcil [A leq v].
Unset Maximal Implicit Insertion.

Scheme heapT_w := Induction for heapT Sort Prop
with heapR_w := Induction for heapR Sort Prop
with heapM_w := Induction for heapM Sort Prop.

Combined Scheme heap_ind from heapT_w, heapR_w, heapM_w.
*)

Module RootOrd (OO:Order) <: Order.

  Definition A := {x:Root OO.A | feapR OO.LEQ (root x) x}.

  Definition LEQ (x y:A) :=
    match x,y with
      exist (Top p _) _, exist (Top q _) _ => OO.LEQ p q
    end.
  Hint Unfold LEQ.
 
  Lemma leqRefl: forall x, true = LEQ x x.
  Proof.
    unfold LEQ.
    destruct x. destruct x.
    auto using OO.leqRefl.
  Qed.
  
  Lemma leqTransTrue : 
    forall x y z,
      true = LEQ x y ->
      true = LEQ y z ->
      true = LEQ x z.
  Proof.
    intros. 
    destruct x as [x xf]; destruct x;
      destruct y as [y yf]; destruct y;
        destruct z as [z zf]; destruct z;
          simpl in *.
    eauto using OO.leqTransTrue.
  Qed.
  
  Lemma leqTransFalse :
    forall x y z,
      false = LEQ x y ->
      false = LEQ y z ->
      false = LEQ x z.
  Proof.
    intros.
    destruct x as [x xf]; destruct x;
      destruct y as [y yf]; destruct y;
        destruct z as [z zf]; destruct z;
          simpl in *.
    eauto using OO.leqTransFalse.
  Qed.
  
  Lemma leqSymm : 
    forall x y,
      false = LEQ x y ->
      true = LEQ y x.
  Proof.
    intros.
    destruct x as [x xf]; destruct x;
      destruct y as [y yf]; destruct y;
        simpl in *.
    eauto using OO.leqSymm.
  Qed.

  Definition preLEQ x y :=
    match x,y with
      Top p _, Top q _ => OO.LEQ p q
    end.
  Hint Unfold preLEQ.
 
  Lemma preleqRefl: forall x, true = preLEQ x x.
  Proof.
    unfold preLEQ.
    destruct x. 
    auto using OO.leqRefl.
  Qed.
  
  Lemma preleqTransTrue : 
    forall x y z,
      true = preLEQ x y ->
      true = preLEQ y z ->
      true = preLEQ x z.
  Proof.
    intros. 
    destruct x;
      destruct y;
        destruct z;
          simpl in *.
    eauto using OO.leqTransTrue.
  Qed.
  
  Lemma preleqTransFalse :
    forall x y z,
      false = preLEQ x y ->
      false = preLEQ y z ->
      false = preLEQ x z.
  Proof.
    intros.
    destruct x;
      destruct y;
        destruct z;
          simpl in *.
    eauto using OO.leqTransFalse.
  Qed.
  
  Lemma preleqSymm : 
    forall x y,
      false = preLEQ x y ->
      true = preLEQ y x.
  Proof.
    intros.
    destruct x;
      destruct y;
        simpl in *.
    eauto using OO.leqSymm.
  Qed.

End RootOrd.

Definition preQ' := ml.

Module SkewBootHeap (OO:Order) <: PQSig.

Set Implicit Arguments.

Module O := RootOrd(OO).
Export O.
Require Export Arith.
Require Export List.
Require Export Program.
Require Export Omega.
Require Export Recdef.
Require Export Coq.Program.Wf.
Require Export caseTactic.

(* TODO: stability *)

Definition preT := preT' OO.A.
Definition preQ := ml OO.A.

Definition root (x:preT) :=
  match x with
    | Node v _ _ => v
  end.

Definition rank (x:preT) :=
  match x with
    | Node _ r _ => r
  end.

Print O.A.
Print O.LEQ.
Print A.

Inductive tree a :=
 branch : a -> list (tree a) -> tree a.

Fixpoint size a (x:tree a) :=
  match x with
    | branch _ c => fold_right plus 0 (map (@size _) c)
  end.

Print tree_ind.
Print tree_rect.

Check tree_ind.
Lemma size_ind :
  forall a (x:tree a), nat.
Proof.
  intros.
  induction x.
Abort.

Check tree_rect.

Definition link (x y:preT) :=
  match x, y with
    | Node v n p, Node w m q =>
      if preLEQ v w 
        then Node v (S n) (y ::: p)
        else Node w (S m) (x ::: q)
  end.

Locate "[ _ ; _ ]".
    Print Grammar constr.

Definition skewLink (x y z:preT) :=
  match x, y, z with
    | Node a i p, 
      Node b j q,
      Node c k r =>
      if preLEQ a b
        then if preLEQ a c
          then Node a (S j) [[y | z]]
          else Node c (S k) (x:::y:::r)
        else if preLEQ b c
          then Node b (S j) (x:::z:::q)
          else Node c (S k) (x:::y:::r)
  end.

Fixpoint ins t xs :=
  match xs with
    | ($) => [[t]]
    | y:::ys =>
      match nat_compare (rank t) (rank y) with
        | Lt => t:::xs
        | _ => ins (link t y) ys
      end
  end.

Definition uniqify xs :=
  match xs with
    | ($) => ($)
    | y:::ys => ins y ys
  end.

Fixpoint length (x:ml OO.A) :=
  match x with
    | ($) => 0
    | _:::xs => S (length xs)
  end.

Definition combLen (xy:preQ * preQ) := 
  let (x,y) := xy in
    length x + length y.

Function meldUniq (xy:preQ * preQ) {measure combLen xy} : preQ :=
  match xy with
    | (($),y) => y
    | (x,($)) => x
    | (p:::ps,q:::qs) => 
      match nat_compare (rank p) (rank q) with
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

Definition preEmpty : preQ := ($).

Definition preInsert x ys :=
  match ys with
    | z1:::z2:::zr =>
      if beq_nat (rank z1) (rank z2)
        then skewLink (Node x 0 ($)) z1 z2 ::: zr
        else Node x 0 ($) ::: ys
    | _ => Node x 0 ($) ::: ys
  end.

Definition preMeld x y :=
  meldUniq (uniqify x, uniqify y).

Fixpoint preFindMinHelp x xs :=
  match xs with 
    | ($) => root x
    | y:::ys => 
      let z := preFindMinHelp y ys in
        let w := root x in
          if preLEQ w z
            then w
            else z
  end.

Definition preFindMin x :=
  match x with
    | ($) => None
    | y:::ys => Some (preFindMinHelp y ys)
  end.

Fixpoint getMin x xs :=
  match xs with
    | ($) => (x,($))
    | y:::ys =>
      let (t,ts) := getMin y ys in
        if preLEQ (root x) (root t)
          then (x,xs)
          else (t,x:::ts)
  end.

Definition children (x:preT) :=
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
Fixpoint split t x c :=
  match c with
    | ($) => (t,x)
    | d:::ds => 
      match rank d with
        | 0 => split t ((root d)::x) ds
        | _ => split (d:::t) x ds
      end
  end.
*)

Definition preDeleteMin x :=
  match x with
    | ($) => ($)
    | y:::ys =>
      match getMin y ys with
        | (Node _ _ c,t) =>
          let (p,q) := split ($) [] c in
            fold_right preInsert (preMeld t p) q
      end
  end.

Definition preExtractMin x :=
  match x with
    | ($) => None
    | y:::ys => Some
      match getMin y ys with
        | (Node v _ c,t) => (v,
          let (p,q) := split ($) [] c in
            fold_right preInsert (preMeld t p) q)
      end
  end.


(*
Extraction preDeleteMin.
Extraction Language Haskell.
Extraction Inline and_rect sig_rect meldUniq_terminate.
Extract Inductive list => "($)" ["($)" "(:)"].
Extract Inductive bool => "Bool" ["True" "False"].
Recursive Extraction preDeleteMin.
Extraction "ExtractedSkew.hs" preDeleteMin preFindMin preInsert preMeld.
*)

Inductive rankN : preT -> nat -> Prop :=
  singleton : forall x, rankN (Node x 0 ($)) 0
| simple : forall n v p y,
             rankN (Node v n p) n ->
             rankN y n ->
             rankN (Node v (S n) (y:::p)) (S n)
| skewA : forall n x y z,
          rankN x n ->
          rankN z n ->
          rankN (Node y (S n) [[x|z]]) (S n)
| skewB : forall n x v p y,
          rankN (Node v n p) n ->
          rankN y n ->
          rankN (Node v (S n) ((Node x 0 ($)):::y:::p)) (S n).
Hint Constructors rankN.

Definition rankP x := rankN x (rank x).

Inductive posBinaryRank : preQ -> nat -> Prop :=
  last : forall x n,
         rankN x n ->
         posBinaryRank [[x]] n
| next : forall x n m xs,
         rankN x n ->
         n < m ->
         posBinaryRank xs m ->
         posBinaryRank (x:::xs) n.
Hint Constructors posBinaryRank.

Inductive binaryRank : preQ -> Prop :=
  zeroBin : binaryRank ($)
| posBin : forall n xs,
           posBinaryRank xs n ->
           binaryRank xs.
Hint Constructors binaryRank.

Inductive posSkewBinaryRank : preQ -> nat -> Prop :=
  vanilla : forall xs n, 
            posBinaryRank xs n ->
            posSkewBinaryRank xs n
| skew : forall x n xs,
         rankN x n ->
         posBinaryRank xs n ->
         posSkewBinaryRank (x:::xs) n.
Hint Constructors posSkewBinaryRank.

Inductive skewBinaryRank : preQ -> Prop :=
  zeroSkew : skewBinaryRank ($)
| posSkew : forall n xs,
           posSkewBinaryRank xs n ->
           skewBinaryRank xs.
Hint Constructors skewBinaryRank.

Lemma rankDestruct :
  forall v n c m,
    rankN (Node v n c) m ->
    n = m.
Proof.
  intros v n c m r.
  inversion r; subst; auto.
Qed.
Hint Resolve rankDestruct.

Lemma rankRank :
  forall x n,
    rankN x n ->
    rank x = n.
Proof.
  intros x n r.
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
  assert (i = n). eapply rankDestruct; eauto. subst.
  eapply rankDestruct; eauto.
Qed.

Lemma linkRank :
  forall n x y, 
    rankN x n -> 
    rankN y n -> 
    rankN (link x y) (S n).
Proof.
  intros n x y X Y.
  unfold link.
  destruct x as [v xn p]; destruct y as [w yn q].
  assert (xn = n); try (eapply rankDestruct; eauto); subst.
  assert (yn = n); try (eapply rankDestruct; eauto); subst.
  remember (preLEQ v w) as vw; destruct vw; apply simple; auto.
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
  assert (i = 0); try (eapply rankDestruct; eauto); subst.
  assert (j = n); try (eapply rankDestruct; eauto); subst.
  assert (k = n); try (eapply rankDestruct; eauto); subst.
  assert (p = ($)); try (inversion X; auto); subst.
  remember (preLEQ a b) as ab; remember (preLEQ a c) as ac;
    remember (preLEQ b c) as bc;
      destruct ab; destruct ac; 
        destruct bc;  simpl; 
          try (apply skewB; assumption);
            try (apply skewA; assumption).
Qed.
Hint Resolve skewLinkRank.

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
  induction xsm.
  Case "last".
    intros j jn y yj.
    destruct x as [v xx p]. 
    assert (xx = n). eapply rankDestruct; eauto. subst.
    destruct y as [w yy q]. 
    assert (yy = j). eapply rankDestruct; eauto. subst.
    unfold ins.
    unfold rank.
    remember (nat_compare j n) as ncjn; destruct ncjn.
    SCase "j = n".
      assert (j = n). apply nat_compare_eq; auto. subst.
      exists (S n). split.
      auto.  constructor. apply linkRank; auto.
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
      simpl.
      assert (nat_compare (rank x) (rank p) = Lt).
      destruct x; destruct p; simpl.
      inversion H; subst.
      inversion H5; subst.
      assert (n0 = n). eapply rankDestruct; eauto.
      subst.
      assert (n1 = m1). eapply rankDestruct; eauto.
      subst.
      apply nat_compare_lt; auto.
      assert (n0 = n). eapply rankDestruct; eauto.
      subst.
      assert (n1 = m1). eapply rankDestruct; eauto.
      subst.
      apply nat_compare_lt; auto.
      rewrite H0.
      eauto.
  rename H1 into xn.
  rename H3 into xsn.
  eapply insNoDupeHelp; eauto.
Qed.

Lemma preInsertRank :
  forall x ys,
    skewBinaryRank ys ->
    skewBinaryRank (preInsert x ys).
Proof with auto.
  intros x ys P.
  destruct ys.
  Case "ys = ($)".
    simpl.
    SCase "skewBinaryRank [Node x 0 ($)]".
      eapply posSkew.
      eapply vanilla.
      eapply last.
      apply singleton.
  Case "ys = p ::: _".
    unfold preInsert.
    destruct ys.
    SCase "ys = nil".
      rename P into R.
      SSCase "skewBinaryRank [Node x 0 ($); p]".
        eapply posSkew.
        inversion R as [|n xs P]; subst.
        inversion P; subst.
        SSSCase "".
          destruct n.
          eapply skew; eauto. constructor.
          eapply next. constructor.
          Focus 2. eauto.
          auto with arith.
        SSSCase "impossible".
          inversion H3.
    SCase "ys = p0 ::: _".
      rename p0 into q.
      rename P into R.
      remember (beq_nat (rank p) (rank q)) as pq; destruct pq.
      SSCase "rank p = rank q".
        assert (rank p = rank q) as pq. apply beq_nat_true; auto.
        SSSCase "skewBinaryRank (skewLink (Node x 0 ($)) p q ::: ys".
          eapply posSkew.
          inversion R; subst.
          inversion H; subst.
          assert (rank p = n).
          inversion H0; auto; eapply rankRank; auto.
          subst.
          assert (rank p < rank q).
          inversion H0; subst.
          assert (rank q = m).
          inversion H6; auto; eapply rankRank; auto.
          subst. auto.
          assert False as f. omega. inversion f.

          instantiate (1 := S (rank p)).
          assert (rank p = n).
          eapply rankRank; auto.
          subst.
          inversion H4; subst.
          eapply vanilla; auto.

          inversion H5.
          eapply skew; auto. 
          subst; auto.
          
          eapply vanilla; auto.
          apply next with (m := m).
          eapply skewLinkRank; auto.
          omega. auto.
      SSCase "rank p <> rank q".
        assert (rank p <> rank q) as pq. apply beq_nat_false; auto.
        
        apply posSkew with (n := 0).
        inversion R; subst.
        destruct n.
        SSSCase "skew".
          apply skew.
          constructor.
          inversion H; subst.
          auto.
          assert (rank p = 0). apply rankRank; auto.
          assert (rank q = 0).
          inversion H4; subst; apply rankRank; auto.
          assert False as f. omega. inversion f.

       SSSCase "vanilla".
         apply vanilla.
         apply next with (m := S n).
         constructor. omega.
         inversion H; subst.
         auto.
         assert (rank p = S n). apply rankRank; auto.
         assert (rank q = S n).
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
      fun (xy:(preQ*preQ)) r =>
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
  assert (rank p = n). inversion H0; apply rankRank; auto.
  assert (rank q = m). inversion H1; apply rankRank; auto.
  subst.
  assert (rank p < rank q). apply nat_compare_lt; auto.
  inversion H0; subst.
  unfold min. rewrite e0.
  exists (rank p); split; auto.
  rewrite meldUniq_equation. 
  eapply next.
  Focus 3.
  eauto. auto. auto.
  unfold min. rewrite e0. 
  exists (rank p); split; auto.
  assert (exists k, k >= min m (rank q)
    /\ posBinaryRank (meldUniq (ps, q:::qs)) k).
  apply H; auto.
  destruct H3.
  destruct H3.
  eapply next.
  Focus 3.
  eauto. eauto.
  unfold min in H3.
  remember (nat_compare m (rank q)) as mq; destruct mq; omega.
  
  assert (rank p = n). inversion H0; apply rankRank; auto.
  assert (rank q = m). inversion H1; apply rankRank; auto.
  subst.
  assert (rank q < rank p). apply nat_compare_gt; auto.
  inversion H1; subst.
  unfold min. rewrite e0.
  exists (rank q); split; auto.
  rewrite meldUniq_equation. 
  eapply next.
  Focus 3.
  eauto. auto. auto.
  unfold min. rewrite e0. 
  exists (rank q); split; auto.
  assert (exists k, k >= min (rank p) m
    /\ posBinaryRank (meldUniq (p:::ps, qs)) k).
  apply H; auto.
  destruct H3.
  destruct H3.
  eapply next.
  Focus 3.
  eauto. eauto.
  unfold min in H3.
  remember (nat_compare (rank p) m) as mq; destruct mq; omega.

  assert (rank p = rank q). apply nat_compare_eq; auto.
  assert (exists k : nat,
    k >= S (min n m)
    /\ posBinaryRank (ins (link p q) (meldUniq (ps, qs))) k).
  apply insNoDupe.
    inversion H0; inversion H1; subst.
  rewrite meldUniq_equation.
  eapply vanilla. eapply last. eapply linkRank.
  assert (rank p = n). apply rankRank; auto; subst.
  assert (rank q = m). apply rankRank; auto; subst.
  rewrite H3 in *. rewrite H4 in *. subst.
  unfold min.
  remember (nat_compare (rank p) (rank p)) as pp.
  destruct pp; auto.
  assert (rank p = n). apply rankRank; auto; subst.
  assert (rank q = m). apply rankRank; auto; subst.
  rewrite H3 in *. rewrite H4 in *. subst.
  unfold min.
  remember (nat_compare (rank p) (rank p)) as pp.
  destruct pp; auto.
  
  rewrite meldUniq_equation.
  assert (rank p = n). apply rankRank; auto; subst.
  assert (rank q = m). apply rankRank; auto; subst.
  rewrite H3 in *; rewrite H4 in *; subst.
  assert (min (rank p) (rank p) = rank p) as rp.
  unfold min.
  remember (nat_compare (rank p) (rank p)) as pp.
  destruct pp; auto.
  rewrite rp in *.
  inversion H10. subst.
  eapply skew; auto. 
  subst.
  eapply vanilla; auto.
  eapply next. Focus 3. eauto.
  auto. omega.
  
  rewrite meldUniq_equation.
  assert (rank p = n). apply rankRank; auto; subst.
  assert (rank q = m). apply rankRank; auto; subst.
  rewrite H3 in *; rewrite H4 in *; subst.
  assert (min (rank p) (rank p) = rank p) as rp.
  unfold min.
  remember (nat_compare (rank p) (rank p)) as pp.
  destruct pp; auto.
  rewrite rp in *.
  inversion H6. subst.
  eapply skew; destruct ps; auto.
  subst.
  eapply vanilla; destruct ps; auto.
  eapply next. Focus 3. eauto.
  auto. omega.

  assert (rank p = n). apply rankRank; auto; subst.
  assert (rank q = m). apply rankRank; auto; subst.
  rewrite H3 in *; rewrite H4 in *; subst.
  assert (min (rank p) (rank p) = rank p) as rp.
  unfold min.
  remember (nat_compare (rank p) (rank p)) as pp.
  destruct pp; auto.
  rewrite rp in *.
  
  assert (exists k, k >= min m0 m1
    /\ posBinaryRank (meldUniq (ps,qs)) k).
  apply H; auto.
  destruct H2.
  destruct H2.
  remember (nat_compare (S (rank p)) x) as spx.
  destruct spx.
  assert (S (rank p) = x). apply nat_compare_eq. auto.
  subst.
  apply skew; auto.
  assert (S (rank p) < x). apply nat_compare_lt. auto.
  apply vanilla.
  eapply next.
  Focus 3.
  eauto.
  auto.
  auto.
  assert (S (rank p) > x). apply nat_compare_gt. auto.
  assert (S (rank p) < x).
  assert (S (rank p) <= min m0 m1).
  assert (S (rank p) <= m0); auto with arith.
  assert (S (rank p) <= m1); auto with arith.
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
    skewBinaryRank (preMeld x y).
Proof with auto.
  intros x y xR yR.
  unfold preMeld.
  destruct x; destruct y.
  simpl. rewrite meldUniq_equation. auto.
  simpl. rewrite meldUniq_equation.
  inversion yR; subst.
  edestruct insNoDupe with (n := n) (x := p); eauto.
  eapply posSkew. eapply vanilla.
  destruct H0. eapply H1.
  simpl. rewrite meldUniq_equation.
  inversion xR; subst.
  edestruct insNoDupe with (n := n) (x := p); eauto.
  eapply posSkew. eapply vanilla.
  destruct H0.
  destruct (ins p x); eauto.

  rename p0 into q.
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


Lemma splitPosRank :
  forall v n c,
    rankP (Node v n c) ->
    forall r m, posBinaryRank r m ->
      n <= m ->
      forall h t z, (h,t) = split r z c ->
        exists k, posSkewBinaryRank h k.
Proof.
  intros v n c H.
  unfold rankP in H.
  simpl in H.
  dependent induction H; intros.
  simpl in H1. inversion H1. subst.
  eauto.
  simpl in H3.
  destruct y as [w j q].
  simpl in *. assert (j = n). eauto. subst.
  destruct q.
  eapply IHrankN1. Focus 3.
  eauto. eauto. auto with arith.
  eapply IHrankN1. Focus 3.
  eauto. eapply next. eauto.
  Focus 2. eauto.
  auto with arith. auto.
  destruct x as [a b c]; destruct z as [d e f].
  assert (b = n). eauto; subst.
  assert (e = n). eauto; subst.
  subst.
  simpl in H3. destruct c; simpl in *.
  inversion H. subst. destruct f; simpl in *.
  inversion H3. subst. clear H3.
  exists m. eauto.
  inversion H3. subst. clear H3.
  inversion H0.
  inversion H. subst.
  destruct f. inversion H3; subst. clear H3.
  exists (S n0). eauto.
  inversion_clear H3; subst.
  exists (S n0); eauto.
  subst.
  destruct f; simpl in *. inversion_clear H3; subst; eauto.
inversion_clear H3; subst; eauto.
subst. destruct f.
inversion_clear H3; subst. eauto.
inversion_clear H3; subst. eauto.
Show Existentials.

  destruct y as [a b c].
  assert (b = n). eauto.
  subst.
  simpl in H3.
  destruct c. assert (n=0). inversion H0. auto.
  subst.
  eapply IHrankN1. Focus 3. eauto.
  eauto. auto with arith.

  destruct n. inversion H0.
  
  eapply IHrankN1.
  Focus 3.
  eapply H3.
  eapply next. eauto.
  Focus 2. eauto.
  auto. auto.
Qed.

(*
Lemma splitPosRank :
  forall v n c,
    rankP (Node v n c) ->
    forall r m, posBinaryRank r m ->
      n <= m ->
      forall h t z, (h,t) = split r z c ->
        exists k, posSkewBinaryRank h k.
Proof.
  intros v n c H.
  unfold rankP in H.
  simpl in H.
  dependent induction H; intros.
  simpl in H1. inversion H1. subst.
  eauto.
  simpl in H3.
  destruct y as [w j q].
  simpl in *. assert (j = n). eauto. subst.
  destruct n.
  eapply IHrankN1. Focus 3.
  eauto. eauto. auto with arith.
  eapply IHrankN1. Focus 3.
  eauto. eapply next. eauto.
  Focus 2. eauto.
  auto with arith. auto.
  destruct x as [a b c]; destruct z as [d e f].
  assert (b = n). eauto; subst.
  assert (e = n). eauto; subst.
  subst.
  simpl in H3.
  destruct n.
  inversion H3; subst. eauto.
  inversion H3; subst.
  exists (S n).
  eapply skew; eauto.

  destruct y as [a b c].
  assert (b = n). eauto.
  subst.
  simpl in H3.
  destruct n.
  eapply IHrankN1. Focus 3. eauto.
  eauto. auto with arith.
  
  eapply IHrankN1.
  Focus 3.
  eapply H3.
  eapply next. eauto.
  Focus 2. eauto.
  auto. auto.
Qed.
*)

Lemma splitRank :
  forall v n c,
    rankP (Node v n c) ->
    forall h t z, (h,t) = split ($) z c ->
      skewBinaryRank h.
Proof.
  intros v n c H.
  unfold rankP in H.
  simpl in H.
  dependent induction H; intros.
  simpl in H. inversion H; subst. eauto.
  
  destruct y as [a b c].
  assert (b = n); eauto; subst.
  simpl in H1.
  destruct c. inversion H0. subst.
  eapply IHrankN1. eauto.
  destruct n. inversion H0.
  assert (exists k, posSkewBinaryRank h k).
  eapply splitPosRank.
  Focus 4. eauto.
  Focus 2. eapply last. eauto.
  eauto. auto.
  destruct H2. eauto.
  
  destruct x as [a b c]; destruct z as [d e f].
  assert (b = n); eauto; subst.
  assert (e = n); eauto; subst.
  simpl in H1. destruct c.
  inversion H. subst. destruct f.
  inversion H1; eauto.
  inversion H1; eauto.
  destruct n. inversion H. destruct f.
  inversion H1; subst; eauto.
  inversion H1; subst; eauto.
  
  simpl in H1.
  destruct y as [a b c].
  assert (b = n); eauto; subst. simpl in *.
  destruct c. inversion H0. subst.
  eapply IHrankN1; eauto.
  destruct n. inversion H0.
  assert (exists k, posSkewBinaryRank h k).
  eapply splitPosRank.
  Focus 4. eauto.
  Focus 2. eapply last. eauto.
  eauto. auto.
  destruct H2. eauto.
Qed.

(*
Lemma splitRank :
  forall v n c,
    rankP (Node v n c) ->
    forall h t z, (h,t) = split ($) z c ->
      skewBinaryRank h.
Proof.
  intros v n c H.
  unfold rankP in H.
  simpl in H.
  dependent induction H; intros.
  simpl in H. inversion H; subst. eauto.
  
  destruct y as [a b c].
  assert (b = n); eauto; subst.
  simpl in H1; destruct n.
  eapply IHrankN1. eauto.
  assert (exists k, posSkewBinaryRank h k).
  eapply splitPosRank.
  Focus 4. eauto.
  Focus 2. eapply last. eauto.
  eauto. auto.
  destruct H2. eauto.
  
  destruct x as [a b c]; destruct z as [d e f].
  assert (b = n); eauto; subst.
  assert (e = n); eauto; subst.
  simpl in H1; destruct n.
  inversion H1; eauto.
  inversion H1; subst; eauto.
  
  simpl in H1.
  destruct y as [a b c].
  assert (b = n); eauto; subst.
  destruct n; simpl in H1.
  eapply IHrankN1; eauto.
  assert (exists k, posSkewBinaryRank h k).
  eapply splitPosRank.
  Focus 4. eauto.
  Focus 2. eapply last. eauto.
  eauto. auto.
  destruct H2. eauto.
Qed.
*)

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
  inversion H. rename p into a.
  simpl in H1.
  remember (getMin a xs) as axs.
  destruct axs as [t ts].
  remember (preLEQ (root x) (root t)) as rxt.
  destruct rxt.
  inversion_clear H1; subst.
  split. exists m; eauto 10 with arith.
  eauto.
  inversion_clear H1; subst.
  inversion H; subst.
  simpl in Heqaxs; eauto.
  inversion_clear Heqaxs; subst; eauto.
  split. eauto 10.
  eauto 10 with arith.
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
  simpl; intros. inversion H1; subst; eauto.
  intros.
  assert ((exists k, k >= n /\
    posBinaryRank z k)
  /\ (exists j, j >= n /\
    rankN y j)). eapply getMinBinRank.
  Focus 4. eauto. auto. eauto. auto.
  inversion H2. destruct H5. destruct H5.
  eapply posSkew. eapply vanilla. eauto.
  inversion H4; subst.
  simpl. remember (preLEQ (root x) (root x0)) as xx0; destruct xx0; intros.
  inversion_clear H1; subst; eauto.
  inversion_clear H1; subst; eauto.
  simpl.
  intros.
  remember (getMin x0 xs0) as x00; destruct x00.
  remember (preLEQ (root x) (root p)) as xp; destruct xp;
    inversion_clear H5; subst.
  eauto.
  rename m0 into l.
  assert ((exists k, k >= n /\
    posBinaryRank l k)
  /\ (exists j, j >= n /\
    rankN p j)). eapply getMinBinRank.
  Focus 4. eauto.
  auto. eauto. auto.
  inversion H5.
  destruct H6.
  destruct H6.
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
  rename p into a.
  remember (getMin a xs) as axs; destruct axs.
  remember (preLEQ r (root p)) as ap; destruct ap;
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

Lemma deleteMinRank :
  forall x,
    skewBinaryRank x ->
    skewBinaryRank (preDeleteMin x).
Proof.
  intros x S.
  unfold preDeleteMin.
  destruct x; eauto.
  remember (getMin p x) as yz. destruct yz as [y z].
  destruct y as [a b c].
  remember (split ($) [] c) as rs.
  destruct rs as [r s].
  assert (skewBinaryRank r) as ss.
  eapply splitRank. Focus 2. eauto.
  eapply getMinTRank. Focus 2. eauto. auto.
  assert (skewBinaryRank z) as zz.
  eapply getMinQRank. Focus 2. eauto. auto.
  assert (skewBinaryRank (preMeld z r)).
  eapply preMeldRank; auto.
  clear Heqrs.
  induction s.
  simpl; auto.
  simpl.
  apply preInsertRank; auto.
Qed.


Lemma extractMinRank :
  forall x,
    skewBinaryRank x ->
    forall t u,
      Some (t,u) = preExtractMin x ->
      skewBinaryRank u.
Proof.
  intros x S t u T.
  unfold preExtractMin in *.
  destruct x; eauto. inversion T.
  remember (getMin p x) as yz. destruct yz as [y z].
  destruct y as [a b c].
  remember (split ($) [] c) as rs.
  destruct rs as [r s].
  assert (skewBinaryRank r) as ss.
  eapply splitRank. Focus 2. eauto.
  eapply getMinTRank. Focus 2. eauto. auto.
  assert (skewBinaryRank z) as zz.
  eapply getMinQRank. Focus 2. eauto. auto.
  assert (skewBinaryRank (preMeld z r)).
  eapply preMeldRank; auto.
  inversion_clear T; subst.
  clear Heqrs.
  induction s.
  simpl; auto.
  simpl.
  apply preInsertRank; auto.
Qed.

(*
Inductive minHeap : preT -> Prop :=
  lone : forall v n, minHeap (Node v n ($))
| top : forall v n n' w m m' p ys,
        minHeap (Node v n ys) ->
        true = LEQ v w ->
        minHeap (Node w m' p) ->
        minHeap (Node v n' ((Node w m p) ::: ys)).
Hint Constructors minHeap.

Inductive Aml (p:preT -> Prop) : ml OO.A -> Prop :=
  Nml : Aml p ($)
| Coms : forall x xs,
         p x ->
         Aml p xs ->
         Aml p (x:::xs).
Hint Constructors Aml.

Inductive All t (p:t -> Prop) : list t -> Prop :=
  Nil : All p []
| Cons : forall x xs,
         p x ->
         All p xs ->
         All p (x::xs).
Hint Constructors All.
*)

Definition minHeap := feapT OO.LEQ.
Definition rootHeap := feapR OO.LEQ.
Definition listHeap := feapM OO.LEQ.

Hint Unfold minHeap.
Hint Unfold rootHeap.
Hint Unfold listHeap.

(*
Lemma Nil : OO.A -> listHeap ($).
Proof.
  intros x; unfold listHeap.
  exists (Some x); auto.
  simpl. auto.
Qed.
Hint Resolve Nil.
*)

Lemma Nil : forall x, listHeap x ($).
Proof.
  unfold listHeap. simpl. auto.
Qed.
Hint Resolve Nil.

Ltac lisp := simpl in *;
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H; lisp
    | [ |- _ /\ _ ] => split; lisp
(*    | [ H : minHeap _ |- _ ] => destruct H; lisp
    | [ H : rootHeap _ |- _ ] => destruct H; lisp
    | [ H : listHeap _ |- _ ] => destruct H; lisp *)
    | [ _ : false = OO.LEQ ?a ?b |- true = OO.LEQ ?b ?a] 
      => apply OO.leqSymm; auto; lisp
    |  [_ : true = OO.LEQ ?a ?b , 
        _ : true = OO.LEQ ?b ?c 
        |- true = OO.LEQ ?a ?c] => eapply OO.leqTransTrue; eauto; lisp
    |  [_ : true = OO.LEQ ?a ?b , 
        _ : false = OO.LEQ ?a ?c 
        |- true = OO.LEQ ?c ?b] => 
    assert (true = OO.LEQ c a); lisp
    |  [_ : true = OO.LEQ ?a ?b , 
        _ : false = OO.LEQ ?c ?b 
        |- true = OO.LEQ ?a ?c] => 
    assert (true = OO.LEQ b c); lisp
    |  [_ : false = OO.LEQ ?a ?b , 
        _ : false = OO.LEQ ?b ?c 
        |- true = OO.LEQ ?c ?a] => 
    assert (false = OO.LEQ a c); lisp
    |  [_ : false = OO.LEQ ?a ?b , 
        _ : false = OO.LEQ ?b ?c 
        |- false = OO.LEQ ?a ?c] => 
    eapply OO.leqTransFalse; eauto; lisp
    | [ |- true = OO.LEQ ?a ?a] => apply OO.leqRefl; auto; lisp
    | [ |- match ?a with | Top _ _ => True end] => destruct a; auto; lisp
    | _ => auto
  end.

Set Maximal Implicit Insertion.
Implicit Arguments None [A].
Unset Maximal Implicit Insertion.


Definition oomin  x y :=
  if OO.LEQ x y
    then x
    else y.

Lemma minLess :
  forall x y,
    true = OO.LEQ (oomin x y) x
    /\ true = OO.LEQ (oomin x y) y.
Proof.
  intros; unfold oomin.
  remember (OO.LEQ x y) as xy; destruct xy;
    split; lisp.
Qed.

(*
Definition compt x y :=
  match x with
    | Some p => 
      match y with
        | Some q => 
          if OO.LEQ p q
            then Some p
            else Some q
        | None => Some p
      end
    | None => y
  end.
Hint Unfold compt.
*)

Lemma heapLess :
  (forall x a b, 
    true = OO.LEQ a b -> 
    minHeap b x -> 
    minHeap a x)
  /\ (forall x a b, 
    true = OO.LEQ a b -> 
    rootHeap b x -> 
    rootHeap a x)
  /\ (forall x a b, 
    true = OO.LEQ a b -> 
    listHeap b x -> 
    listHeap a x).
Proof.
  unfold minHeap; unfold rootHeap; unfold listHeap.
  apply all_ind; intros; lisp.
  eapply H; eauto.
  eapply H; eauto.
  eapply H0; eauto.
Qed.

Lemma Cons : 
  forall xs a x b, 
    minHeap a x ->
    listHeap b xs ->
    listHeap (oomin a b) (x:::xs).
Proof.
  simpl.
  unfold listHeap; unfold minHeap.
  induction xs as [|y ys I]; simpl; intros a x b X XS; lisp.

  eapply heapLess with a; lisp; apply minLess.
  eapply heapLess with a; lisp; apply minLess.
  eapply heapLess with b; lisp; apply minLess.
  eapply heapLess with b; lisp; apply minLess.
Qed.

(*
Lemma Cons : 
  forall xs x, 
    minHeap x ->
    listHeap xs ->
    listHeap (x:::xs).
Proof.
  unfold listHeap at 2. simpl.
  induction xs as [|y ys I]; simpl; intros x X XS.

  destruct x as [v i c]; destruct v as [r d]; simpl.
  exists (Some r); repeat (constructor; auto).
  apply OO.leqRefl.
  destruct X as [v X].
  simpl in X. destruct X. destruct H. auto.
  destruct X as [v X].
  simpl in X. lisp.

  destruct XS as [v XS]. lisp.
  rename x0 into w.
  
  destruct v as [v|]; destruct w as [w|].
  remember (OO.LEQ v w) as vw; destruct vw.

  exists (Some v); repeat (constructor; auto).
  destruct x. lisp.
  destruct r; lisp.

  exists (Some w); lisp.
  destruct y; lisp.
  destruct r; lisp.
  destruct ys; lisp.
  destruct p; lisp.
  destruct r; lisp.
  auto.
  clear H I H1 y x.
  generalize dependent w.
  generalize dependent v.
  induction ys; intros.
  eauto. lisp.
  Focus 2. eapply IHys; eauto.
  destruct p0; lisp.
  destruct r; lisp.
  auto.

  exists (None:option OO.A).
  lisp; lisp; lisp.
  destruct y; lisp.
  destruct r; lisp.
  generalize dependent H0.
  clear. generalize dependent v.
  induction ys; intros; lisp.
  destruct p; lisp. destruct r; lisp.
  eapply IHys. eauto.

  exists (None:option OO.A).
  lisp; lisp; lisp.
  destruct x; lisp.
  destruct r; eauto. lisp.

  exists (None:option OO.A).
  lisp; lisp; lisp.
Qed.
Hint Resolve Cons.  
*)

Lemma lone : 
  forall a v n, 
    rootHeap a v ->
    exists b, minHeap b (Node v n ($)).
Proof.
  unfold rootHeap; unfold minHeap; intros.
  destruct v as [x c].
  exists x.
  lisp.
Qed.
Hint Resolve lone.

Lemma top : forall a b v n n' w m m' p ys,
  minHeap a (Node v n ys) ->
  true = preLEQ v w ->
  minHeap b (Node w m' p) ->
  minHeap (oomin a b) (Node v n' ((Node w m p) ::: ys)).
Proof.
  intros. unfold minHeap in *. lisp.
  destruct v as [r i c]. lisp.
  apply OO.leqTransTrue with a; auto. apply minLess.
  destruct v; lisp.
  destruct w; lisp.
Qed.
Hint Resolve top.

Lemma linkHeap :
  forall v x w y, 
    minHeap v x -> 
    minHeap w y -> 
    minHeap (oomin v w) (link x y).
Proof.
  intros v x w y X Y.
  unfold link.
  destruct x as [vv n p]; destruct y as [ww m q].
  unfold minHeap in *; lisp.
  remember (preLEQ vv ww) as vw; destruct vw.
  unfold minHeap; lisp.
  lisp. apply heapLess with v. apply minLess. auto.
  destruct vv; lisp.
  destruct ww; lisp.
  lisp.
  apply heapLess with w; auto; apply minLess.
  destruct ww; lisp.
  destruct vv; lisp.
Qed.
Hint Resolve linkHeap.

(*
Lemma linkHeap :
  forall x y, minHeap x -> minHeap y -> minHeap (link x y).
Proof.
  intros x y X Y.
  unfold link.
  destruct x as [v n p]; destruct y as [w m q].
  remember (preLEQ v w) as vw; destruct vw; eapply top; eauto.
  apply preleqSymm; auto.
Qed.
Hint Resolve linkHeap.
*)

Lemma skewLinkHeap :
  forall R x U y T z, 
    rootHeap R x -> 
    minHeap T y -> 
    minHeap U z -> 
    minHeap (oomin R (oomin U T)) (skewLink (Node x 0 ($)) y z).
Proof.
  unfold rootHeap; unfold minHeap; unfold skewLink.
  intros R x T y U z X Y Z.
  rename x into a.
  destruct y as [b j q]; destruct z as [c k r].
  remember (preLEQ a b) as ab; destruct ab; simpl.
  Case "a <= b".
    remember (preLEQ a c) as ac; destruct ac; lisp.
    SCase "a <= c".
      apply heapLess with R; auto. apply minLess.
      destruct a; lisp. destruct b; destruct c; lisp.
      destruct b; destruct c; lisp.
      apply heapLess with T; auto.
      apply OO.leqTransTrue with (oomin T U); apply minLess.
    SCase "a > c".
      destruct c; lisp.
      destruct a. unfold preLEQ in *.
      destruct b. lisp. destruct b. lisp.
      unfold preLEQ in *. destruct a. lisp.
  Case "b > a".
    remember (preLEQ b c) as bc; destruct bc; lisp.
    SCase "b <= c".
      apply heapLess with U; auto.
      apply OO.leqTransTrue with (oomin T U); apply minLess.
    SCase "b > c".
      destruct b; lisp. destruct c; lisp.
      unfold preLEQ in *. destruct a; lisp.
      destruct c; lisp. destruct b; lisp. destruct c; lisp.
      unfold preLEQ in *; lisp. destruct a; lisp.
      apply OO.leqTransTrue with (oomin T U); try (apply minLess).
      apply OO.leqTransTrue with T; auto; try (apply minLess).
      destruct c; lisp.
      unfold preLEQ in *; destruct b; lisp.
      destruct a; lisp. destruct b; unfold preLEQ in *; lisp.
Qed.
Hint Resolve skewLinkHeap.

Lemma preInsertHeapLess :
  forall a x,
    feapR OO.LEQ a x ->
    forall b ys,
      feapM OO.LEQ b ys ->
      feapM OO.LEQ (oomin a b) (preInsert x ys).
Proof.
  intros a x X b ys P.
  destruct ys; lisp.
  apply heapLess with a; try apply minLess; auto.
  destruct ys; lisp.
  apply heapLess with a; try apply minLess; auto.
  apply heapLess with b; try apply minLess; auto.
  destruct p as [b0 j q]; lisp; destruct p0 as [c0 k r]; lisp.
  remember (beq_nat j k) as jk; destruct jk; destruct x; lisp.
  destruct b0; destruct c0; lisp.
  remember (OO.LEQ a0 a1) as a01; destruct a01; lisp.
  remember (OO.LEQ a0 a2) as a02; destruct a02; lisp.
  apply OO.leqTransTrue with a; lisp. apply minLess.
  apply OO.leqTransTrue with b; lisp. apply minLess.
  remember (OO.LEQ a1 a2) as a12; destruct a12; lisp.
  apply OO.leqTransTrue with b; lisp. apply minLess.
  apply OO.leqTransTrue with b; lisp. apply minLess.
  apply heapLess with b; try apply minLess; lisp.
  apply OO.leqTransTrue with a; try apply minLess; lisp.
  apply heapLess with b; try apply minLess; lisp.
  apply heapLess with b; try apply minLess; lisp.
  apply heapLess with b; try apply minLess; lisp.
Qed.

(*
Lemma preInsertHeapLess :
  forall a x,
    feapR OO.LEQ (Some a) x ->
    forall b ys,
      feapM OO.LEQ (Some b) ys ->
      forall c, c = (if OO.LEQ a b then a else b) ->
        feapM OO.LEQ (Some c) (preInsert x ys).
Proof.
  intros a x X b ys P c C.
  destruct ys; lisp.
  apply heapLess with (b := a); lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  destruct ys; lisp.
  apply heapLess with (b := a); lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  apply heapLess with (b := b); lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  destruct p as [b0 j q]; lisp; destruct p0 as [c0 k r]; lisp.
  remember (beq_nat j k) as jk; destruct jk; destruct x; lisp.
  destruct b0; destruct c0; lisp.
  remember (OO.LEQ a0 a1) as a01; destruct a01; lisp.
  remember (OO.LEQ a0 a2) as a02; destruct a02; lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  remember (OO.LEQ a1 a2) as a12; destruct a12; lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  apply heapLess with (b:= b); lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  apply heapLess with (b:= b); lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  apply heapLess with (b:= b); lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
  apply heapLess with (b:= b); lisp.
  remember (OO.LEQ a b) as ab; destruct ab; subst; lisp.
Qed.
*)

(*
Lemma preInsertHeap :
  forall a x b ys,
    rootHeap x ->
    listHeap ys ->
    listHeap (preInsert x ys).
Proof.
  unfold rootHeap; unfold listHeap; intros.
  destruct H; destruct H0.
  exists (@None OO.A).
  destruct ys; lisp.
  destruct x; lisp.
  destruct ys; lisp.
  destruct x; lisp.
  destruct p; lisp.
  destruct r; lisp.
  destruct p as[b j q]; destruct p0 as [c k r]; lisp.
  destruct b; destruct c; lisp.
  remember (beq_nat j k) as jk; destruct jk; lisp.
  destruct x; lisp.
  remember (OO.LEQ a1 a) as a1a; destruct a1a; lisp.
  remember (OO.LEQ a1 a0) as a10; destruct a10; lisp.
  remember (OO.LEQ a a0) as aa0; destruct aa0; lisp.
  induction ys; lisp.
  destruct x1; lisp.
  induction p; lisp.
  destruct r0; lisp.
  destruct x; lisp.
  destruct x1; lisp.
  induction ys; lisp.
  induction p; lisp.
  destruct r0; lisp.
Qed.

Print preT'.
*)

(*
Lemma noneHeap :
  (forall x, 
    feapT OO.LEQ None x ->
    exists y, feapT OO.LEQ (Some y) x)
  /\ (forall x, 
    feapR OO.LEQ None x ->
    exists y, feapR OO.LEQ (Some y) x)
  /\ (forall x, 
    forall z zs,
      z:::zs = x ->
      feapM OO.LEQ None x ->
      exists y, feapM OO.LEQ (Some y) x).
Proof.
  apply all_ind; lisp; intros; lisp.
  apply H in H1. destruct H1. exists x. lisp.
  exists a; lisp.
  inversion H.
  apply H in H2. destruct H2.
  destruct m.
  exists x; lisp.
  eapply H0 in H3. Focus 2. eauto.
  destruct H3.
  pose (if OO.LEQ x x0 then x else x0) as y.
  exists y. lisp.
  eapply heapLess; eauto.
  remember (OO.LEQ x x0) as xx0; destruct xx0; unfold y; lisp.
  eapply heapLess; eauto.
  remember (OO.LEQ x x0) as xx0; destruct xx0; unfold y; lisp.
  eapply heapLess; eauto.
  remember (OO.LEQ x x0) as xx0; destruct xx0; unfold y; lisp.
Qed.

Definition oomin  x y :=
  if OO.LEQ x y
    then x
    else y.

Lemma minLess :
  forall x y,
    true = OO.LEQ (oomin x y) x
    /\ true = OO.LEQ (oomin x y) y.
Proof.
  intros; unfold oomin.
  remember (OO.LEQ x y) as xy; destruct xy;
    split; lisp.
Qed.
*)

Lemma insHeapSome : 
  forall a x b xs,
    minHeap a x ->
    listHeap b xs ->
    listHeap (oomin a b) (ins x xs).
Proof.
  intros a x b xs.
  generalize dependent x;
    generalize dependent a; generalize dependent b.
  induction xs; intros; auto.
    unfold listHeap; lisp. apply heapLess with a; auto.
    apply minLess.
    
    unfold listHeap in *; lisp.
    destruct (nat_compare (rank x) (rank p)).
    
    apply heapLess with (oomin (oomin a b) b).
    unfold oomin. remember (OO.LEQ a b) as ab; destruct ab; lisp.
    rewrite <- Heqab; lisp.
    rewrite <- OO.leqRefl; lisp.
    apply IHxs; auto.
    
    lisp.
    apply heapLess with a; auto; try apply minLess.
    apply heapLess with b; auto; try apply minLess.
    apply heapLess with b; auto; try apply minLess.

    apply heapLess with (oomin (oomin a b) b).
    unfold oomin. remember (OO.LEQ a b) as ab; destruct ab; lisp.
    rewrite <- Heqab; lisp.
    rewrite <- OO.leqRefl; lisp.
    apply IHxs; auto.
Qed.

(*
Lemma insHeap : 
  forall x xs,
    minHeap x ->
    listHeap xs ->
    listHeap (ins x xs).
Proof.
  intros x xs.
  generalize dependent x.
  induction xs; intros; auto.
    simpl; auto. simpl; auto.
    inversion H0; subst. inversion H1; subst.
    simpl.
    rename p into a.
    remember (nat_compare (rank x) (rank a)) as xa; destruct xa; auto.
    apply IHxs; auto. eapply linkHeap; auto.
    exists x0. auto.
    exists x0; eauto.
    eapply IHxs. eapply linkHeap; auto.
    exists x0. auto.
    exists x0; eauto.
Qed.
*)

(*
Definition notBothNil (x y:ml OO.A) :=
  match x,y with
    | ($),($) => false
    | _,_ => true
  end.
Hint Unfold notBothNil.
*)

Lemma meldUniqHeapSome :
  forall a x b y,
    listHeap a x ->
    listHeap b y ->
    listHeap (oomin a b) (meldUniq (x,y)).
Proof.
  assert 
    (let P := 
      fun (xy:(preQ*preQ)) r =>
        let (x,y) := xy in
          forall a b,
          listHeap a x ->
          listHeap b y ->
          listHeap (oomin a b) r
            in forall xy, P xy (meldUniq xy)).
  eapply meldUniq_ind; intros; lisp.
  destruct y; lisp. 
  apply heapLess with b; auto; apply minLess.
  apply heapLess with a; auto; apply minLess.
  unfold listHeap in *; lisp.
  apply heapLess with a; auto; apply minLess.
  unfold listHeap in *; lisp.
  apply heapLess with b; auto; apply minLess.
  unfold listHeap in *; lisp.
  eapply heapLess. Focus 2.
  apply insHeapSome. apply linkHeap; eauto.
  apply H; eauto.
  unfold oomin. 
  remember (OO.LEQ a b) as ab; destruct ab; 
    try rewrite <- OO.leqRefl; lisp.

  intros. simpl in H.
  pose (H (x,y)) as Hxy.
  simpl in Hxy.
  eapply Hxy. auto. eauto. 
Qed.

(*
Lemma meldUniqHeapSome :
  forall a x b y,
    listHeap a x ->
    listHeap b y ->
    listHeap (oomin a b) (meldUniq (x,y)).
Proof.
  assert 
    (let P := 
      fun (xy:(preQ*preQ)) r =>
        let (x,y) := xy in
          true = notBothNil x y ->
          listHeap x ->
          listHeap y ->
          exists b, feapM OO.LEQ (Some b) r
            in forall xy, P xy (meldUniq xy)).
  eapply meldUniq_ind; intros; lisp.
  destruct y; lisp. 
  inversion H. clear xy e H H0.
  destruct x. exists a; lisp.
  apply noneHeap in H1.
  destruct H1.
  destruct y.
  exists x; lisp.
  eapply noneHeap in H2. destruct H2.
  exists (oomin x x1); lisp.
  apply heapLess with x; lisp; try apply minLess.
  apply heapLess with x1; lisp; try apply minLess.
  apply heapLess with x1; lisp; try apply minLess.
  eauto. destruct x; lisp. inversion H.
  clear e xy H y H1.
  destruct x1.
  exists a; lisp.
  apply noneHeap in H0. destruct H0.
  destruct x.
  exists x1; lisp.
  eapply noneHeap in H2. destruct H2.
  exists (oomin x1 x2); lisp.
  apply heapLess with x1; lisp; try apply minLess.
  apply heapLess with x2; lisp; try apply minLess.
  apply heapLess with x2; lisp; try apply minLess.
  eauto.
  edestruct H. unfold notBothNil. destruct ps; auto.
  unfold listHeap; lisp.
  eauto. unfold listHeap. lisp. eauto.
  destruct x0.
  exists (oomin a x1); lisp.
  apply heapLess with a; lisp; try apply minLess.
  apply heapLess with x1; lisp; try apply minLess.
  apply noneHeap in H1. destruct H1.
  exists (oomin x0 x1); lisp.
  apply heapLess with x0; lisp; apply minLess.
  apply heapLess with x1; lisp; apply minLess.

  edestruct H; lisp.
  unfold listHeap. lisp. eauto.
  unfold listHeap. eauto.
  destruct x.
  exists (oomin a x1); lisp.
  apply heapLess with a; lisp; try apply minLess.
  apply heapLess with x1; lisp; try apply minLess.
  apply noneHeap in H2. destruct H2.
  exists (oomin x x1); lisp.
  apply heapLess with x; lisp; apply minLess.
  apply heapLess with x1; lisp; apply minLess.

  eapply insHeapSome. eapply linkHeap; eauto.
  destruct ps; destruct qs; lisp. rewrite meldUniq_equation. lisp.

  rewrite meldUniq_equation; unfold listHeap; lisp; eauto.
  rewrite meldUniq_equation; unfold listHeap; lisp; eauto.
 
  edestruct H; lisp.
  unfold listHeap. lisp; eauto.
  unfold listHeap. lisp; eauto.
  unfold listHeap. eauto.

  intros. simpl in H.
  pose (H (x,y)) as Hxy.
  simpl in Hxy.
  eapply Hxy. auto. eauto. auto.
Qed.
*)

(*
Lemma meldUniqHeap :
  forall x y,
    listHeap x ->
    listHeap y ->
    listHeap (meldUniq (x,y)).
Proof.
  assert 
    (let P := 
      fun (xy:(preQ*preQ)) r =>
        let (x,y) := xy in
              listHeap x ->
              listHeap y ->
              listHeap r
              in forall xy, P xy (meldUniq xy)).
  eapply meldUniq_ind; intros; auto.
  inversion H0; subst.
  apply Cons; auto. inversion H2; subst; eauto.
  inversion H1; subst.
  apply H; auto.
  inversion H2; subst; auto.
  eauto.
  apply Cons.
  inversion_clear H1; subst; eauto.
  inversion_clear H2; subst; eauto.
  apply H; auto.
  inversion_clear H1; subst; eauto.
  inversion_clear H2; subst; eauto.
  apply insHeap; eauto.
  eapply linkHeap; eauto.
  inversion H0; eauto.
  inversion H2; subst; eauto.
  inversion H1; eauto.
  inversion H2; subst; eauto.
  eapply H.
  inversion H0; eauto.
  inversion H2; subst; eauto.
  inversion H1; eauto.
  inversion H2; subst; eauto.
  simpl in H.
  intros x y.
  pose (H (x, y)) as I.
  eapply I; auto.
Qed.
*)

Lemma preMeldHeapSome : 
  forall a x b y,
    listHeap a x ->
    listHeap b y ->
    listHeap (oomin a b) (preMeld x y).
Proof.
  intros a x b y xH yH.
  unfold preMeld.

  eapply meldUniqHeapSome.

  destruct x; lisp.
  apply heapLess with (oomin a a).
  unfold oomin. rewrite <- OO.leqRefl; lisp.
  unfold listHeap in xH. lisp.
  apply insHeapSome; auto.

  destruct y; lisp.
  apply heapLess with (oomin b b).
  unfold oomin. rewrite <- OO.leqRefl; lisp.
  unfold listHeap in yH. lisp.
  apply insHeapSome; auto.
Qed.

(*
Lemma preMeldHeapSome : 
  forall x y,
    true = notBothNil x y ->
    listHeap x ->
    listHeap y ->
    exists n, feapM OO.LEQ (Some n) (preMeld x y).
Proof.
  intros x y S xH yH.
  unfold preMeld.

  eapply meldUniqHeapSome.
  destruct x; simpl in *.
  clear xH yH; destruct y.
  inversion S. clear S; generalize dependent p.
  simpl. induction y; simpl; intros.
  auto.
  remember (nat_compare (rank p0) (rank p)) as pp0; destruct pp0.
  apply IHy. auto. apply IHy.

  clear xH yH S; generalize dependent p; generalize dependent y.
  induction x; simpl; intros. auto.
  remember (nat_compare (rank p0) (rank p)) as pp0; destruct pp0.
  apply IHx. unfold notBothNil. auto.
  apply IHx.
  destruct x. auto.
  simpl. apply insHeap; lisp. eauto. eauto.
  destruct y. auto.
  simpl. apply insHeap; lisp. eauto. eauto.
Qed.

Lemma preMeldHeap :
  forall x y,
    listHeap x ->
    listHeap y ->
    listHeap (preMeld x y).
Proof with auto.
  intros x y xH yH.

  apply meldUniqHeap.
  destruct x; inversion xH; subst; auto.
  apply insHeap; auto. inversion_clear H; subst; eauto.
  inversion_clear H; subst; eauto.
  destruct y; inversion yH; subst; auto.
  apply insHeap; auto.
 inversion_clear H; subst; eauto.
  inversion_clear H; subst; eauto.
Qed.
*)

Lemma getMinTHeap :
  forall a x b xs,
    minHeap a x ->
    listHeap b xs ->
    forall y z, (y,z) = getMin x xs ->
      minHeap (oomin a b) y.
Proof.
  intros a x b xs;
    generalize dependent x; generalize dependent a; generalize dependent b;
      induction xs;
        simpl; intros.
  inversion_clear H1; subst; auto.
  apply heapLess with a; auto; try apply minLess.
  remember (getMin p xs) as tts; destruct tts; subst.
  remember (preLEQ (root x) (root p0)) as xp; destruct xp.
  inversion_clear H1; subst.
  apply heapLess with a; auto; try apply minLess.
  inversion_clear H1; subst.
  unfold listHeap in H0; lisp.
  assert (minHeap (oomin b b) p0).
  eapply IHxs. Focus 3.
  eauto. auto. auto.
  unfold oomin in H2.
  rewrite <- OO.leqRefl in H2.
  apply heapLess with b; auto; try apply minLess.
Qed.

(*
Lemma getMinTHeap :
  forall a x b xs,
    minHeap x ->
    listHeap xs ->
    forall y z, (y,z) = getMin x xs ->
      minHeap y.
Proof.
  intros x xs;
    generalize dependent x;
      induction xs;
        simpl; intros.
  inversion_clear H1; subst; auto.
  rename p into a.
  remember (getMin a xs) as tts; destruct tts; subst.
  remember (preLEQ (root x) (root p)) as xp; destruct xp.
  inversion_clear H1; subst. auto.
  inversion_clear H1; subst.
  inversion_clear H0; subst.
  eapply IHxs. Focus 3.
  eauto.
  inversion_clear H1; subst; eauto.
  inversion_clear H1; subst; eauto.
Qed.
*)

(*
Definition oomax  x y :=
  if OO.LEQ x y
    then y
    else x.

Lemma maxMore :
  forall x y,
    true = OO.LEQ x (oomax x y)
    /\ true = OO.LEQ y (oomax x y).
Proof.
  intros; unfold oomax.
  remember (OO.LEQ x y) as xy; destruct xy;
    split; lisp.
Qed.
*)

Lemma dblMin : forall x, oomin x x = x.
Proof.
  unfold oomin.
  Check LEQ. Check leqRefl.
  intros. rewrite <- OO.leqRefl; auto.
Qed.


Lemma getMinQHeap :
  forall a x b xs,
    minHeap a x ->
    listHeap b xs ->
    forall y z, (y,z) = getMin x xs ->
(*
      true = OO.LEQ (toot y) (toot x) /\
      listHeap (toot y) xs /\
*)
      listHeap (toot y) z
      /\ listHeap (toot y) xs
      /\ minHeap (toot y) x.
Proof.
  intros a x b xs;
    generalize dependent x; generalize dependent a; generalize dependent b;
      induction xs; simpl; intros; lisp.
  inversion_clear H1; subst. lisp.
  inversion_clear H1; subst. 
  destruct x; lisp. unfold minHeap in *; lisp. destruct r; lisp.
  remember (getMin p xs) as tts; destruct tts.
  remember (preLEQ (root x) (root p0)) as xp; destruct xp;
    inversion_clear H1; subst.
  unfold listHeap in *; lisp.
  eapply heapLess with (toot p0); auto.
  destruct x; destruct p0; lisp.
  destruct r; destruct r0; lisp. eapply IHxs. Focus 3. eauto.
  eauto. eauto.
  eapply heapLess with (toot p0); auto.
  destruct x; destruct p0; lisp.
  destruct r; destruct r0; lisp. eapply IHxs. Focus 3. eauto.
  eauto. eauto.
  unfold listHeap in *; lisp.
  unfold minHeap in *; lisp.
  destruct x; destruct p0; lisp.
  destruct r; destruct r0; lisp.
  eapply IHxs. Focus 3. eauto.
  eauto. eauto.
  unfold listHeap in H0; lisp.
  remember (getMin p xs) as tts; destruct tts.
  remember (preLEQ (root x) (root p0)) as xp; destruct xp;
    inversion_clear H1; subst.
  unfold listHeap; lisp.
  eapply heapLess with (toot p0).
  destruct x; destruct p0; lisp.
  destruct r; destruct r0; lisp.
  eapply IHxs; eauto.
  eapply heapLess with (toot p0).
  destruct x; destruct p0; lisp.
  destruct r; destruct r0; lisp.
  eapply IHxs; eauto.
  assert (minHeap b p0).
  rewrite <- (dblMin b).
  eapply getMinTHeap; eauto.
  destruct p0; destruct x; lisp.
  unfold minHeap in H; unfold minHeap in H1; lisp.
  destruct r; destruct r0; lisp.
  pose Heqtts as hhh. eapply IHxs in hhh. lisp.
  unfold listHeap; lisp. eauto. eauto.
  
  remember (getMin p xs) as tts; destruct tts.
  remember (preLEQ (root x) (root p0)) as xp; destruct xp;
    inversion_clear H1; subst.
  unfold minHeap in *; destruct x; lisp. destruct r; lisp.
  destruct p0; destruct x; unfold minHeap in H; lisp.
  destruct r; unfold minHeap; lisp.
  destruct r0; lisp.
Qed.

Lemma getMinQHelp :
  forall a x b xs,
    minHeap a x ->
    listHeap b xs ->
    forall y z, (y,z) = getMin x xs ->
(*
      true = OO.LEQ (toot y) (toot x) /\
      listHeap (toot y) xs /\
*)
      listHeap (oomin a b) z.
Proof.
  intros.
  assert (listHeap (toot y) z).
  eapply getMinQHeap with (x := x) (xs := xs); eauto.
  eapply heapLess with (toot y).
  eapply getMinTHeap in H1. Focus 2. eauto.
  Focus 2. eauto.
  destruct y; unfold minHeap in *; lisp.
  destruct r; lisp.
  auto.
Qed.

(*
Lemma getMinQHeap :
  forall x xs,
    minHeap x ->
    listHeap xs ->
    forall y z, (y,z) = getMin x xs ->
      listHeap z.
Proof.
  intros x xs;
    generalize dependent x;
      induction xs; simpl; intros.
  inversion_clear H1; subst; eauto.
  rename p into a.
  remember (getMin a xs) as tts; destruct tts.
  remember (preLEQ (root x) (root p)) as xp; destruct xp;
    inversion_clear H1; subst; eauto.
  inversion_clear H0; subst.
  apply Cons; eauto. 
  eapply IHxs. Focus 3. eauto.
  inversion_clear H1; subst; eauto.
  inversion_clear H1; subst; eauto.
Qed.
*)

Check split.

Lemma splitHeap :
  forall a x, listHeap a x ->
    forall b y, listHeap b y ->
      forall p q r, (p,q) = split x r y ->
        listHeap (oomin a b) p.
Proof.
  intros a x XX b y.
  generalize dependent a;
    generalize dependent b; generalize dependent x.
  induction y; simpl; lisp; intros.
  inversion_clear H0; subst; auto.
  apply heapLess with a; auto; try apply minLess.
  destruct p as [i j k]; destruct k; simpl in *.
  eapply IHy. Focus 3. eauto.
  auto. unfold listHeap in H. lisp.
  unfold listHeap in H. lisp.
  destruct i; lisp.
  assert (listHeap (oomin (oomin a a0) b) p0).
  eapply IHy. Focus 2. auto.
  Focus 2. eauto.
  unfold listHeap; lisp.
  apply minLess; auto.
  apply heapLess with a; auto; apply minLess.
  apply heapLess with (oomin (oomin a a0) b).
  unfold oomin.
  remember (OO.LEQ a b) as ab; destruct ab; lisp;
    remember (OO.LEQ a a0) as aa0; destruct aa0; lisp.
  rewrite <- Heqab; lisp.
  remember (OO.LEQ a0 b) as a0b; destruct a0b; lisp.
  rewrite <- Heqab; lisp.
  remember (OO.LEQ a0 b) as a0b; destruct a0b; lisp.
  auto.
Qed.

(*

Lemma splitHeap :
  forall a x, listHeap a x ->
    forall b y, listHeap b y ->
      forall p q r, (p,q) = split x r y ->
        listHeap (oomin a b) p.
Proof.
  intros a x XX b y.
  generalize dependent a;
    generalize dependent b; generalize dependent x.
  induction y; simpl; lisp; intros.
  inversion_clear H0; subst; auto.
  apply heapLess with a; auto; try apply minLess.
  destruct p as [i j k]; destruct j; simpl in *.
  eapply IHy. Focus 3. eauto.
  auto. unfold listHeap in H. lisp.
  unfold listHeap in H. lisp.
  destruct i; lisp.
  assert (listHeap (oomin (oomin a a0) b) p0).
  eapply IHy. Focus 2. auto.
  Focus 2. eauto.
  unfold listHeap; lisp.
  apply minLess; auto.
  apply heapLess with a; auto; apply minLess.
  apply heapLess with (oomin (oomin a a0) b).
  unfold oomin.
  remember (OO.LEQ a b) as ab; destruct ab; lisp;
    remember (OO.LEQ a a0) as aa0; destruct aa0; lisp.
  rewrite <- Heqab; lisp.
  remember (OO.LEQ a0 b) as a0b; destruct a0b; lisp.
  rewrite <- Heqab; lisp.
  remember (OO.LEQ a0 b) as a0b; destruct a0b; lisp.
  auto.
Qed.
*)

(*
Lemma splitHeap :
  forall a, listHeap a ->
    forall b c, listHeap c ->
      forall y z, (y,z) = split a b c ->
        listHeap y.
Proof.
  intros a AA b c.
  generalize dependent a;
    generalize dependent b.
  induction c; simpl; intros.
  inversion_clear H0; subst; auto.
  rename a into aa.
  rename p into a.
  destruct a as [i j k]; destruct j; simpl in *.
  eapply IHc. Focus 3. eauto.
  auto. inversion_clear H; subst; eauto.
  inversion_clear H1; subst; eauto.
  inversion_clear H; subst.
  eapply IHc. Focus 3. eauto.
  apply Cons; eauto. inversion_clear H1; subst; eauto.
  inversion_clear H1; subst; eauto.
Qed.
*)

Fixpoint Each t (P:t -> Prop) l :=
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
  forall a x, listHeap a x ->
    forall b y, Each (rootHeap b) y -> 
      forall c z, listHeap c z ->
        forall p q, (p,q) = split x y z ->
          Each (rootHeap (oomin b c)) q.
Proof.
  intros a x XX b y YY c z.
  generalize dependent a;
    generalize dependent b;
      generalize dependent c;  
        generalize dependent x;
          generalize dependent y.
  induction z; simpl; intros; lisp.
  inversion_clear H0; subst; auto.
  eapply weakenEach with (rootHeap b); auto; intros.
  apply heapLess with b; auto; apply minLess.
  
  destruct p as [i j k]; destruct k; simpl in *.
  eapply IHz in H0.
  Focus 2.
  assert (Each (rootHeap (oomin b c)) (i::y)).
  lisp. unfold listHeap in H.
  lisp. 
  apply heapLess with c; auto; apply minLess.
  eapply weakenEach with (rootHeap b); auto; intros.
  apply heapLess with b; auto; apply minLess.
  eauto.
  
  Focus 3. unfold listHeap in H; lisp.
  eauto.
  eapply weakenEach with (rootHeap (oomin (oomin b c) c)); auto; intros.
  apply heapLess with (oomin (oomin b c) c); auto.
  unfold oomin.
  remember (OO.LEQ b c) as bc; destruct bc; lisp;
    try (rewrite <- Heqbc); lisp.
  rewrite <- OO.leqRefl; lisp.
  eauto.

  eapply IHz in H0.
  Focus 3.
  assert (listHeap (oomin a c) ((Node i (S j) k):::x)).
  lisp. unfold listHeap in H |- *.
  lisp; destruct i; lisp.
  apply OO.leqTransTrue with c; auto. apply minLess.
  apply heapLess with a; auto; apply minLess.
  unfold listHeap in *. lisp. destruct i. lisp.
  Focus 2. apply H2. eauto. auto. auto.
  unfold listHeap in *; lisp.
Qed.

(*
Lemma splitEach :
  forall a x, listHeap a x ->
    forall b y, Each (rootHeap b) y -> 
      forall c z, listHeap c z ->
        forall p q, (p,q) = split x y z ->
          Each (rootHeap (oomin b c)) q.
Proof.
  intros a x XX b y YY c z.
  generalize dependent a;
    generalize dependent b;
      generalize dependent c;  
        generalize dependent x;
          generalize dependent y.
  induction z; simpl; intros; lisp.
  inversion_clear H0; subst; auto.
  eapply weakenEach with (rootHeap b); auto; intros.
  apply heapLess with b; auto; apply minLess.
  
  destruct p as [i j k]; destruct j; simpl in *.
  eapply IHz in H0.
  Focus 2.
  assert (Each (rootHeap (oomin b c)) (i::y)).
  lisp. unfold listHeap in H.
  lisp. 
  apply heapLess with c; auto; apply minLess.
  eapply weakenEach with (rootHeap b); auto; intros.
  apply heapLess with b; auto; apply minLess.
  eauto.
  
  Focus 3. unfold listHeap in H; lisp.
  eauto.
  eapply weakenEach with (rootHeap (oomin (oomin b c) c)); auto; intros.
  apply heapLess with (oomin (oomin b c) c); auto.
  unfold oomin.
  remember (OO.LEQ b c) as bc; destruct bc; lisp;
    try (rewrite <- Heqbc); lisp.
  rewrite <- OO.leqRefl; lisp.
  eauto.

  eapply IHz in H0.
  Focus 3.
  assert (listHeap (oomin a c) ((Node i (S j) k):::x)).
  lisp. unfold listHeap in H |- *.
  lisp. 
  apply heapLess with c; auto; apply minLess.
  apply heapLess with a; auto; apply minLess.
  eauto.
  Focus 2. eauto.
  Focus 2. unfold listHeap in *; lisp. eauto.
  auto.
Qed.
*)

(*
Lemma splitEach :
  forall a, listHeap a ->
    forall b, Each rootHeap b -> 
      forall c, listHeap c ->
        forall y z, (y,z) = split a b c ->
          Each rootHeap z.
Proof.
  intros a AA b BB c.
  generalize dependent a;
    generalize dependent b.
  induction c; simpl; intros.
  inversion_clear H0; subst; auto.
  rename a into aa.
  rename p into a.
  destruct a as [i j k]; destruct j; simpl in *.
  eapply IHc. Focus 4. eauto. simpl. split.
  auto. inversion_clear H; subst; eauto.
  inversion_clear H1; subst; eauto.
  inversion_clear H; subst; eauto. eauto. eauto.
  auto. inversion_clear H; subst; eauto.
  inversion_clear H1; subst; eauto.
  eapply IHc. Focus 4. eauto. eauto.
  apply Cons; eauto. inversion_clear H; subst; eauto.
  inversion_clear H1; subst; eauto.
  inversion_clear H; subst; eauto.
  inversion_clear H1; subst; eauto.
Qed.
*)

(*
Lemma childrenHeap :
  forall v i c,
    minHeap (Node v i c) ->
    listHeap c.
Proof.
  intros v i c;
    generalize dependent v; 
      generalize dependent i; 
        induction c;
          simpl; intros.
  auto.
  inversion_clear H; subst. eauto.
  apply Cons.
  Show Existentials.
  inversion_clear H; subst; auto.
  inversion_clear H0; subst; auto.
  inversion_clear H1; subst; auto. eauto. Show Existentials.
  inversion_clear H; subst; auto.
  inversion_clear H0; subst; auto.
  inversion_clear H1; subst; auto.
  Show Existentials.
  exists w. auto.
Qed.
*)

Hint Resolve OO.leqRefl.

Lemma preDeleteMinHeap :
  forall x v,
    listHeap v x ->
    listHeap v (preDeleteMin x).
Proof.
  intros x.
  induction x; simpl; intros.
  eauto. lisp.
  rename p into a.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  remember (split ($) [] c) as pq; destruct pq as [p q].

  unfold listHeap in H.
  lisp.
  assert (oomin v v = v) as vvv.
  unfold oomin; rewrite <- OO.leqRefl; lisp.
  assert (listHeap v t) as vt.
  rewrite <- vvv. 
  eapply getMinQHelp. Focus 3. eauto.
  auto. auto.
  assert (listHeap v c) as vc.
  eapply getMinTHeap in Heqpt.
  Focus 2. eauto. Focus 2. eauto.
  rewrite vvv in Heqpt. unfold minHeap in Heqpt.
  lisp.
  destruct zz; lisp.
  apply heapLess with a0; lisp.
  assert (listHeap v p) as vp.
  eapply splitHeap with (a:=v) (b:=v) in Heqpq. rewrite vvv in Heqpq. auto.
  lisp. lisp.
  assert (Each (rootHeap v) q) as vq.
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
  unfold listHeap in vp; lisp.
  eapply insHeapSome; lisp.
  remember (ins p0 t) as p0t; destruct p0t; lisp.
  rewrite Heqp0t.
  rewrite <- vvv.
  unfold listHeap in vt; lisp.
  eapply insHeapSome; lisp.

(* *)

  remember (ins p0 t) as p0t; destruct p0t; lisp.
  unfold listHeap in vp; lisp.
  rewrite <- vvv.
  eapply insHeapSome; lisp.
  remember (ins p p1) as pp1; destruct pp1; lisp.
  rewrite Heqp0t.

  unfold listHeap in vt; lisp.
  rewrite <- vvv.
  eapply insHeapSome; lisp.


(* *)


  unfold listHeap in vt; lisp.
  assert (listHeap (oomin v v) (ins p0 t)).
  apply insHeapSome; auto.
  rewrite <- Heqp0t in H3.
  rewrite vvv in H3.
  unfold listHeap in H3; lisp.


  unfold listHeap in vp; lisp.
  assert (listHeap (oomin v v) (ins p p1)).
  apply insHeapSome; auto.
  rewrite <- Heqpp1 in H7.
  rewrite vvv in H7.
  unfold listHeap in H7; lisp.


  destruct p2; destruct p3; lisp.
  remember (nat_compare n n0) as nn0; destruct nn0; lisp.
  rewrite <- vvv.
  apply insHeapSome.
  destruct r; destruct r0; lisp.
  remember (OO.LEQ a0 a1) as a01; destruct a01; lisp.
  unfold minHeap; lisp.
  unfold minHeap; lisp.
  rewrite <- vvv.
  apply meldUniqHeapSome; lisp.
  unfold listHeap; lisp.
  rewrite <- vvv.
  apply meldUniqHeapSome; lisp.
  unfold listHeap; lisp.
  unfold listHeap; lisp.
  rewrite <- vvv.
  apply meldUniqHeapSome; lisp.
  unfold listHeap; lisp.
  simpl.
  rewrite <- vvv.
  apply preInsertHeapLess.
  lisp.
  eapply IHq; lisp.
Qed.

(*
Lemma preDeleteMinHeap :
  forall x v,
    listHeap v x ->
    listHeap v (preDeleteMin x).
Proof.
  intros x.
  induction x; simpl; intros.
  eauto. lisp.
  rename p into a.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  remember (split ($) [] c) as pq; destruct pq as [p q].
  assert (listHeap p). eapply splitHeap.
  Focus 3. eauto. auto.
  assert (minHeap (Node zz zzz c)). eapply getMinTHeap.
  Focus 3. eauto. eauto. eauto.
  destruct c; lisp.
  destruct p0; lisp. eauto.
  destruct r; lisp. eauto.
  destruct zz; lisp.
  exists (Some a1); lisp.
  assert (Each rootHeap q) as eq.
  eapply splitEach. Focus 4. eauto. eauto. simpl. auto.
  assert (minHeap (Node zz zzz c)). eapply getMinTHeap.
  Focus 3. eauto. eauto. eauto.
  destruct c; lisp.
  destruct p0; destruct zz; lisp.
  destruct r; lisp.
  exists (Some a0); lisp.
    
  clear Heqpq. generalize dependent eq.

  induction q; intros. simpl.
  apply preMeldHeap; auto.
  eapply getMinQHeap. Focus 3. eauto. eauto. eauto.
  apply preInsertHeap; auto.
  lisp. eauto.
  fold (fold_right preInsert (preMeld t p) q).
  apply IHq.
  lisp.
Qed.
*)

Check root.
Check preExtractMin.
Print Root.
Check root.
Check Top.root.

Lemma preExtractMinHeap :
  forall v x,
    listHeap v x ->
    forall y z,
      Some (y,z) = preExtractMin x ->
      listHeap (Top.root y) x /\ listHeap (Top.root y) z.
Proof.
  intros.
  unfold preExtractMin in *.
  destruct x.
  inversion H0.
  remember (getMin p x) as gt; destruct gt.
  destruct p0.
  inversion H0. subst. clear H0.
  Show Existentials.

  remember (split ($) [] m0) as dm; destruct dm.
  unfold listHeap in H; lisp.
  replace (Top.root r) with (toot (Node r n m0)).
  unfold listHeap; split.
  eapply getMinQHeap.  Focus 3. eauto. eauto. eauto.
  eapply getMinQHeap.  Focus 3. eauto. eauto. eauto.
  auto.
  assert (minHeap v (Node r n m0)).
  rewrite <- (dblMin v).
  Show Existentials.

  eapply getMinTHeap; eauto. Show Existentials.
  assert (Each (rootHeap (Top.root r)) l).
  rewrite <- (dblMin (Top.root r)).
  Check splitEach. destruct r.
  eapply splitEach with (a:=a). Focus 4. eauto.
  unfold listHeap. simpl. Show Existentials.
  lisp. Show Existentials.
  eauto. Show Existentials. eauto.
  unfold minHeap in H1; lisp.  lisp.
  assert (listHeap (toot (Node r n m0)) m).

  Show Existentials.
  Check getMinQHeap.
  eapply getMinQHeap with (xs:=x). Focus 3. eauto. eauto. eauto.
  assert (listHeap (toot (Node r n m0)) m0).
  lisp. unfold minHeap in *; lisp. destruct r; lisp.
  assert (listHeap (toot (Node r n m0)) m1).
  rewrite <- (dblMin (toot (Node r n m0))).
  eapply splitHeap. Focus 3. eauto.
  auto. auto.
  assert (listHeap (toot (Node r n m0)) (preMeld m m1)).
  rewrite <- (dblMin (toot (Node r n m0))).
  eapply preMeldHeapSome. auto. auto.
  clear Heqdm.
  induction l. auto. simpl.
  rewrite <- (dblMin (Top.root r)).
  apply preInsertHeapLess. lisp.
  apply IHl. lisp. Show Existentials.
Qed.


Lemma preExtractMinRootHeap :
  forall x v,
    listHeap v x ->
    forall y z,
      Some (y,z) = preExtractMin x ->
      rootHeap v y.
Proof.
  intros x.
  destruct x; simpl; intros.
  inversion H0.
  rename p into a.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  inversion_clear H0; subst.
  assert (oomin v v = v) as vvv.
  unfold oomin; rewrite <- OO.leqRefl; lisp.
  unfold listHeap in H; lisp.
  assert (minHeap v (Node zz zzz c)).
  rewrite <- vvv.
  eapply getMinTHeap. Focus 3. eauto. lisp. lisp.
  unfold minHeap in *. lisp.
Qed.


Lemma preExtractMinHelp :
  forall v x,
    listHeap v x ->
    forall y z,
      Some (y,z) = preExtractMin x ->
      listHeap v z.
Proof.
  intros.
  eapply heapLess with (Top.root y).
  assert (rootHeap v y). eapply preExtractMinRootHeap; eauto.
  destruct y; unfold rootHeap in *; lisp.
  eapply preExtractMinHeap; eauto.
Qed.

(*
  intros v x; generalize dependent v.
  induction x; simpl; intros.
  inversion H0.
  eauto. lisp.
  rename p into a.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  remember (split ($) [] c) as pq; destruct pq as [p q].

  unfold listHeap in H.
  lisp.
  assert (oomin v v = v) as vvv.
  unfold oomin; rewrite <- OO.leqRefl; lisp.
  assert (listHeap v t) as vt.
  rewrite <- vvv. 
  eapply getMinQHeap. Focus 3. eauto.
  auto. auto.
  assert (listHeap v c) as vc.
  eapply getMinTHeap in Heqpt.
  Focus 2. eauto. Focus 2. eauto.
  rewrite vvv in Heqpt. unfold minHeap in Heqpt.
  lisp.
  destruct zz; lisp.
  apply heapLess with a0; lisp.
  assert (listHeap v p) as vp.
  eapply splitHeap with (a:=v) (b:=v) in Heqpq. rewrite vvv in Heqpq. auto.
  lisp. lisp.
  assert (Each (rootHeap v) q) as vq.
  eapply splitEach with (a:=v) (b:=v) (c:= v) in Heqpq. 
  rewrite vvv in Heqpq. auto. lisp. lisp. lisp.
  clear Heqpq Heqpt.
  generalize dependent t.
  generalize dependent c.
  generalize dependent p.
  generalize dependent z.
  generalize dependent y.
  induction q; intros.
  lisp. inversion H0. unfold preMeld.
  unfold uniqify.
  destruct t; destruct p; lisp;
    rewrite meldUniq_equation; lisp.
  rewrite <- vvv.
  unfold listHeap in vp; lisp.
  eapply insHeapSome; lisp.
  remember (ins p0 t) as p0t; destruct p0t; lisp.
  rewrite Heqp0t.
  rewrite <- vvv.
  unfold listHeap in vt; lisp.
  eapply insHeapSome; lisp.

(* *)

  remember (ins p0 t) as p0t; destruct p0t; lisp.
  unfold listHeap in vp; lisp.
  rewrite <- vvv.
  eapply insHeapSome; lisp.
  remember (ins p p1) as pp1; destruct pp1; lisp.
  rewrite Heqp0t.

  unfold listHeap in vt; lisp.
  rewrite <- vvv.
  eapply insHeapSome; lisp.


(* *)


  unfold listHeap in vt; lisp.
  assert (listHeap (oomin v v) (ins p0 t)).
  apply insHeapSome; auto.
  rewrite <- Heqp0t in H6.
  rewrite vvv in H6.
  unfold listHeap in H6; lisp.


  unfold listHeap in vp; lisp.
  assert (listHeap (oomin v v) (ins p p1)).
  apply insHeapSome; auto.
  rewrite <- Heqpp1 in H10.
  rewrite vvv in H10.
  unfold listHeap in H10; lisp.


  destruct p2; destruct p3; lisp.
  remember (nat_compare n n0) as nn0; destruct nn0; lisp.
  rewrite <- vvv.
  apply insHeapSome.
  destruct r; destruct r0; lisp.
  remember (OO.LEQ a0 a1) as a01; destruct a01; lisp.
  unfold minHeap; lisp.
  unfold minHeap; lisp.
  rewrite <- vvv.
  apply meldUniqHeapSome; lisp.
  unfold listHeap; lisp.
  rewrite <- vvv.
  apply meldUniqHeapSome; lisp.
  unfold listHeap; lisp.
  unfold listHeap; lisp.
  rewrite <- vvv.
  apply meldUniqHeapSome; lisp.
  unfold listHeap; lisp.
  simpl in *.
  rewrite <- vvv.
  inversion H0.
  apply preInsertHeapLess.
  lisp.
  apply IHq with (y := zz) (t := t) (p := p) (c:= c); lisp.
Qed.
*)

(*
Lemma preExtractMinHeap :
  forall x,
    listHeap x ->
    forall y z,
      Some (y,z) = preExtractMin x ->
      listHeap z.
Proof.
  intros x.
  induction x; simpl; intros.
  inversion H0.
  rename p into a.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  remember (split ($) [] c) as pq; destruct pq as [p q].
  assert (listHeap p). eapply splitHeap.
  Focus 3. eauto. Show Existentials. auto.
  assert (minHeap (Node zz zzz c)). eapply getMinTHeap.
  Focus 3. eauto. lisp. eauto. eauto. lisp. eauto.
  lisp. destruct zz; eauto.
  eauto. lisp. eauto. 
  inversion_clear H0; subst.
  Show Existentials.

  assert (Each rootHeap q) as eq.
  eapply splitEach. Focus 4. eauto. auto. auto. 
  assert (minHeap (Node zz zzz c)). eapply getMinTHeap.
  Focus 3. eauto.  Show Existentials. eauto. eauto.
  lisp. destruct zz; eauto.
    
  clear Heqpq. generalize dependent eq.
  Show Existentials.
  induction q; intros; simpl.
  apply preMeldHeap; auto.
  eapply getMinQHeap. Focus 3. eauto. eauto. eauto. eauto.
  apply preInsertHeap; auto.  lisp; eauto. Show Existentials.
  lisp.
Qed.
*)

(*
Lemma preExtractMinRootHeap :
  forall x v,
    listHeap v x ->
    forall y z,
      Some (y,z) = preExtractMin x ->
      rootHeap v y.
Proof.
  intros x.
  destruct x; simpl; intros.
  inversion H0.
  rename p into a.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  inversion_clear H0; subst.
  assert (oomin v v = v) as vvv.
  unfold oomin; rewrite <- OO.leqRefl; lisp.
  unfold listHeap in H; lisp.
  assert (minHeap v (Node zz zzz c)).
  rewrite <- vvv.
  eapply getMinTHeap. Focus 3. eauto. lisp. lisp.
  unfold minHeap in *. lisp.
Qed.
*)

(*
Lemma preExtractMinRootHeap :
  forall x,
    listHeap x ->
    forall y z,
      Some (y,z) = preExtractMin x ->
      rootHeap y.
Proof.
  intros x.
  destruct x; simpl; intros.
  inversion H0.
  rename p into a.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  inversion_clear H0; subst.
  lisp.
  assert (minHeap (Node zz zzz c)).
  eapply getMinTHeap; auto. Focus 3. eauto.
  eauto. eauto.
  lisp; eauto.
Qed.
*)

Definition findMinHelpHeap :
  forall xs v, listHeap v xs ->
    forall x w, minHeap w x ->
      rootHeap (oomin v w) (preFindMinHelp x xs).
Proof.
  induction xs; simpl; intros; lisp.
  destruct x; lisp. 
  unfold minHeap in *; unfold rootHeap.
  lisp. apply heapLess with w; lisp. apply minLess.
  remember (preLEQ (root x) (preFindMinHelp p xs)) as xpxs;
    destruct xpxs; lisp.
  destruct x; lisp. 
  unfold minHeap in *; lisp.
  apply heapLess with w; lisp. apply minLess.
  unfold listHeap in H; lisp.
  assert (rootHeap (oomin v v) (preFindMinHelp p xs)) as ans.
  apply IHxs; lisp.
  assert (oomin v v = v) as vvv.
  unfold oomin; rewrite <- OO.leqRefl; lisp.
  rewrite vvv in ans.
  apply heapLess with v; lisp. apply minLess.
Qed.

Definition findMinHeap :
  forall x v,
    listHeap v x ->
    forall y, Some y = preFindMin x ->
      rootHeap v y.
Proof.
  induction x; simpl; intros.
  inversion H0.
  inversion_clear H0; subst.
  unfold listHeap in H; lisp.
  assert (oomin v v = v) as vvv.
  unfold oomin; rewrite <- OO.leqRefl; lisp.
  rewrite <- vvv.
  apply findMinHelpHeap; lisp; eauto.
Qed.

(*
Definition findMinHelpHeap :
  forall xs, listHeap xs ->
    forall x, minHeap x ->
      rootHeap (preFindMinHelp x xs).
Proof.
  induction xs; simpl; intros; lisp.
  destruct x; lisp. eauto.
  remember (preLEQ (root x) (preFindMinHelp p xs)) as xpxs;
    destruct xpxs; lisp.
  destruct x; lisp. eauto.
  apply IHxs; lisp. eauto. eauto.
Qed.
 
Definition findMinHeap :
  forall x,
    listHeap x ->
    forall y, Some y = preFindMin x ->
      rootHeap y.
Proof.
  induction x; simpl; intros.
  inversion H0.
  inversion_clear H0; subst.
  apply findMinHelpHeap; lisp; eauto.
Qed.
*)

Definition PQP x := skewBinaryRank x /\ (x = ($) \/ exists v, listHeap v x).

Definition PQ := { x:preQ | PQP x}.

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
  unfold listHeap; lisp. right.
  simpl. 
  destruct x; lisp. destruct H.
  exists (oomin a x).
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
  unfold rootHeap in s; lisp. eauto.
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
   Some (exist (fun x0 : Root OO.A => feapR OO.LEQ (Top.root x0) x0) y py) =
   match zz as j return (j = preFindMin x -> option A) with
   | Some y0 =>
       fun s : Some y0 = preFindMin x =>
       Some
         (exist (fun x0 : Root OO.A => feapR OO.LEQ (Top.root x0) x0) y0
            match px with
            | conj H (or_introl H1) =>
                eq_ind_r
                  (fun x' : preQ =>
                   skewBinaryRank x' ->
                   Some y0 = preFindMin x' -> feapR OO.LEQ (Top.root y0) y0)
                  (fun (_ : skewBinaryRank ($))
                     (s0 : Some y0 = preFindMin ($)) =>
                   match
                     s0 in (_ = y1)
                     return (y1 = None -> feapR OO.LEQ (Top.root y0) y0)
                   with
                   | eq_refl =>
                       fun H3 : Some y0 = None =>
                       False_ind (feapR OO.LEQ (Top.root y0) y0)
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
                  return (rootHeap x0 r -> feapR OO.LEQ (Top.root r) r)
                with
                | Top a m =>
                    fun s0 : rootHeap x0 (Top a m) =>
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
         (exist (fun x0 : Root OO.A => feapR OO.LEQ (Top.root x0) x0) y
            match px with
            | conj H (or_introl H1) =>
                eq_ind_r
                  (fun x' : preQ =>
                   skewBinaryRank x' ->
                   Some y = preFindMin x' -> feapR OO.LEQ (Top.root y) y)
                  (fun (_ : skewBinaryRank ($))
                     (s0 : Some y = preFindMin ($)) =>
                   match
                     s0 in (_ = y0)
                     return (y0 = None -> feapR OO.LEQ (Top.root y) y)
                   with
                   | eq_refl =>
                       fun H3 : Some y = None =>
                       False_ind (feapR OO.LEQ (Top.root y) y)
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
                  return (rootHeap x0 r -> feapR OO.LEQ (Top.root r) r)
                with
                | Top a m =>
                    fun s0 : rootHeap x0 (Top a m) =>
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
  simpl. unfold listHeap in H. lisp.
  assert (forall v, oomin v v = v) as vvv.
  unfold oomin. intros.
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
  exists x0; lisp. unfold listHeap in H; lisp.
  exists x0.
  assert (forall v, oomin v v = v) as vvv.
  unfold oomin. intros.
  remember (OO.LEQ v v) as vv; destruct vv; auto.
  rewrite <- (vvv x0).
  apply insHeapSome; lisp.
  destruct H; destruct H0. right.
  exists (oomin x1 x2).
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
  assert (rootHeap x0 y) as ANS.
  eapply preExtractMinRootHeap. Focus 2. eauto. auto.
  unfold rootHeap in *; destruct y; lisp.
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
  assert (forall (zz:option((Root OO.A)*preQ)) (pp:zz= preExtractMin x),
   Some
     (exist (fun x0 : Root OO.A => feapR OO.LEQ (Top.root x0) x0) y py,
     exist (fun x0 : preQ => PQP x0) z pz) =
   match
     zz as j return (j = preExtractMin x -> option (A * PQ))
   with
   | Some p =>
       let (y0, z0) as p0
           return (Some p0 = preExtractMin x -> option (A * PQ)) := p in
       fun s : Some (y0, z0) = preExtractMin x =>
       Some
         (exist (fun x0 : Root OO.A => feapR OO.LEQ (Top.root x0) x0) y0
            match px with
            | conj H (or_introl H1) =>
                eq_ind_r
                  (fun x' : preQ =>
                   skewBinaryRank x' ->
                   Some (y0, z0) = preExtractMin x' ->
                   feapR OO.LEQ (Top.root y0) y0)
                  (fun (_ : skewBinaryRank ($))
                     (s0 : Some (y0, z0) = preExtractMin ($)) =>
                   match
                     s0 in (_ = y1)
                     return (y1 = None -> feapR OO.LEQ (Top.root y0) y0)
                   with
                   | eq_refl =>
                       fun H3 : Some (y0, z0) = None =>
                       False_ind (feapR OO.LEQ (Top.root y0) y0)
                         (eq_ind (Some (y0, z0))
                            (fun e : option (Root OO.A * ml OO.A) =>
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
                     feapR OO.LEQ x0 r -> feapR OO.LEQ (Top.root r) r)
                with
                | Top a m =>
                    fun (_ : Some (Top a m, z0) = preExtractMin x)
                      (ANS : feapR OO.LEQ x0 (Top a m)) =>
                    match ANS with
                    | conj _ H4 => conj (OO.leqRefl a) H4
                    end
                end s (preExtractMinRootHeap x x0 H2 s)
            end,
         exist (fun x0 : preQ => PQP x0) z0
           (conj match px with
                 | conj H _ => extractMinRank H s
                 end
              match px with
              | conj H (or_introl H1) =>
                  eq_ind_r
                    (fun x' : preQ =>
                     skewBinaryRank x' ->
                     Some (y0, z0) = preExtractMin x' ->
                     z0 = $ \/ (exists v : OO.A, listHeap v z0))
                    (fun (_ : skewBinaryRank ($))
                       (s0 : Some (y0, z0) = preExtractMin ($)) =>
                     match
                       s0 in (_ = y1)
                       return
                         (y1 = None ->
                          z0 = $ \/ (exists v : OO.A, listHeap v z0))
                     with
                     | eq_refl =>
                         fun H3 : Some (y0, z0) = None =>
                         False_ind
                           (z0 = $ \/ (exists v : OO.A, listHeap v z0))
                           (eq_ind (Some (y0, z0))
                              (fun e : option (Root OO.A * ml OO.A) =>
                               match e with
                               | Some _ => True
                               | None => False
                               end) I None H3)
                     end eq_refl) H1 H s
              | conj H (or_intror (ex_intro x0 H2)) =>
                  or_intror (z0 = $)
                    (ex_intro (fun v : OO.A => listHeap v z0) x0
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

  assert (forall (zz:option((Root OO.A)*preQ)) (pp:zz= preExtractMin x),
   None =
   match
     zz as j return (j = preExtractMin x -> option (A * PQ))
   with
   | Some p =>
       let (y, z) as p0
           return (Some p0 = preExtractMin x -> option (A * PQ)) := p in
       fun s : Some (y, z) = preExtractMin x =>
       Some
         (exist (fun x0 : Root OO.A => feapR OO.LEQ (Top.root x0) x0) y
            match px with
            | conj H (or_introl H1) =>
                eq_ind_r
                  (fun x' : preQ =>
                   skewBinaryRank x' ->
                   Some (y, z) = preExtractMin x' ->
                   feapR OO.LEQ (Top.root y) y)
                  (fun (_ : skewBinaryRank ($))
                     (s0 : Some (y, z) = preExtractMin ($)) =>
                   match
                     s0 in (_ = y0)
                     return (y0 = None -> feapR OO.LEQ (Top.root y) y)
                   with
                   | eq_refl =>
                       fun H3 : Some (y, z) = None =>
                       False_ind (feapR OO.LEQ (Top.root y) y)
                         (eq_ind (Some (y, z))
                            (fun e : option (Root OO.A * ml OO.A) =>
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
                     feapR OO.LEQ x0 r -> feapR OO.LEQ (Top.root r) r)
                with
                | Top a m =>
                    fun (_ : Some (Top a m, z) = preExtractMin x)
                      (ANS : feapR OO.LEQ x0 (Top a m)) =>
                    match ANS with
                    | conj _ H4 => conj (OO.leqRefl a) H4
                    end
                end s (preExtractMinRootHeap x x0 H2 s)
            end,
         exist (fun x0 : preQ => PQP x0) z
           (conj match px with
                 | conj H _ => extractMinRank H s
                 end
              match px with
              | conj H (or_introl H1) =>
                  eq_ind_r
                    (fun x' : preQ =>
                     skewBinaryRank x' ->
                     Some (y, z) = preExtractMin x' ->
                     z = $ \/ (exists v : OO.A, listHeap v z))
                    (fun (_ : skewBinaryRank ($))
                       (s0 : Some (y, z) = preExtractMin ($)) =>
                     match
                       s0 in (_ = y0)
                       return
                         (y0 = None ->
                          z = $ \/ (exists v : OO.A, listHeap v z))
                     with
                     | eq_refl =>
                         fun H3 : Some (y, z) = None =>
                         False_ind (z = $ \/ (exists v : OO.A, listHeap v z))
                           (eq_ind (Some (y, z))
                              (fun e : option (Root OO.A * ml OO.A) =>
                               match e with
                               | Some _ => True
                               | None => False
                               end) I None H3)
                     end eq_refl) H1 H s
              | conj H (or_intror (ex_intro x0 H2)) =>
                  or_intror (z = $)
                    (ex_intro (fun v : OO.A => listHeap v z) x0
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

Module InlineBoot(OO:Order) <: PQSig.

Module O:=OO.
Export O.

Module SBH := SkewBootHeap(O).

Definition add a f (x:list a) := fold_right plus 0 (map f x).

Definition preT := preT' A.
Definition Boot := Root A.

Fixpoint sizeT (x:preT) :=
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

Inductive bootWrap :=
  Empty : bootWrap
| Full : Boot -> bootWrap.

Definition preMeld x y :=
  match x,y with
    | Empty,_ => y
    | _,Empty => x
    | Full (Top v c), Full (Top w d) =>
      if LEQ v w
        then Full (Top v (SBH.preInsert (Top w d) c))
        else Full (Top w (SBH.preInsert (Top v c) d))
  end.

Hint Unfold preMeld.

Definition preInsert x xs :=
  preMeld (Full (Top x SBH.preEmpty)) xs.

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
      match SBH.preExtractMin c with
        | None => Empty
        | Some (Top w d,cs) =>
          Full (Top w (SBH.preMeld d cs))
      end)
  end.

Hint Unfold preExtractMin.

Definition preDeleteMin x :=
  match preExtractMin x with
    | None => x
    | Some (_,y) => y
  end.

Hint Unfold preDeleteMin.

Definition minHeap x := exists v, feapT OO.LEQ v x.
Definition rootHeap x := exists v, feapR OO.LEQ v x.
Definition listHeap x := exists v, feapM OO.LEQ v x.

Hint Unfold minHeap.
Hint Unfold rootHeap.
Hint Unfold listHeap.

Definition wrapHeap x :=
  match x with
    | Empty => True
    | Full y => rootHeap y
  end.

Hint Unfold wrapHeap.

Definition PQ := {x:bootWrap | wrapHeap x}.

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

Definition preCount (same:DER LEQ) x p :=
  match p with
    | Empty => 0
    | Full q =>
      match same with
        | exist f _ => countR f x q
      end
  end.

Hint Unfold preCount.

Program Definition count : (DER LEQ) -> A -> PQ -> nat := preCount.

Hint Unfold count.

Definition check (same:DER LEQ) x y := 
  match same with
    | exist f _ => f x y
  end.

Hint Unfold check.

Check all_ind.

Lemma countJoin :
  forall f,
    DERP LEQ f ->
    (forall p x y, true = f x y -> countT f x p = countT f y p)
    /\ (forall r x y, true = f x y -> countR f x r = countR f y r)
    /\ (forall m x y, true = f x y -> countM f x m = countM f y m).
Proof.
  intros.
  apply all_ind; simpl; intros.
  auto.
  remember (f x a) as xa; destruct xa;
    remember (f y a) as ya; destruct ya; auto.
  destruct H as [H I]. destruct I as [I J].
  destruct J as [J K].
  assert (true = false) as F.
  rewrite Heqya.
  eapply K; eauto. inversion F.
  destruct H as [H I]. destruct I as [I J].
  destruct J as [J K].
  assert (true = false) as F.
  rewrite Heqxa.
  eapply K; eauto. inversion F. auto.
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

Definition preEmpty := Empty.
Program Definition empty : PQ := preEmpty.

Lemma emptyCount :
  forall same x, count same x empty = 0.
Proof.
  intros; auto.
Qed.


Ltac lisp := simpl in *;
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H; lisp
    | [ |- _ /\ _ ] => split; lisp
    | [ H : minHeap _ |- _ ] => unfold minHeap in H; lisp
    | [ H : rootHeap _ |- _ ] => unfold rootHeap in H; lisp
    | [ H : listHeap _ |- _ ] => unfold listHeap in H; lisp
    | [ _ : false = OO.LEQ ?a ?b |- true = OO.LEQ ?b ?a] 
      => apply OO.leqSymm; auto; lisp
    |  [_ : true = OO.LEQ ?a ?b , 
        _ : true = OO.LEQ ?b ?c 
        |- true = OO.LEQ ?a ?c] => eapply OO.leqTransTrue; eauto; lisp
    |  [_ : true = OO.LEQ ?a ?b , 
        _ : false = OO.LEQ ?a ?c 
        |- true = OO.LEQ ?c ?b] => 
    assert (true = OO.LEQ c a); lisp
    |  [_ : true = OO.LEQ ?a ?b , 
        _ : false = OO.LEQ ?c ?b 
        |- true = OO.LEQ ?a ?c] => 
    assert (true = OO.LEQ b c); lisp
    |  [_ : false = OO.LEQ ?a ?b , 
        _ : false = OO.LEQ ?b ?c 
        |- true = OO.LEQ ?c ?a] => 
    assert (false = OO.LEQ a c); lisp
    |  [_ : false = OO.LEQ ?a ?b , 
        _ : false = OO.LEQ ?b ?c 
        |- false = OO.LEQ ?a ?c] => 
    eapply OO.leqTransFalse; eauto; lisp
    | [ |- true = OO.LEQ ?a ?a] => apply OO.leqRefl; auto; lisp
    | [ |- match ?a with | Top _ _ => True end] => destruct a; auto; lisp
    | _ => auto
  end.

(*
Ltac lisp := simpl in *;
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H; lisp
    | [ |- _ /\ _ ] => split; lisp
    | [ H : minHeap _ |- _ ] => destruct H; lisp
    | [ H : rootHeap _ |- _ ] => destruct H; lisp
    | [ H : listHeap _ |- _ ] => destruct H; lisp
    | _ => auto
  end.
*)

Lemma dblMin : forall x, SBH.oomin x x = x.
Proof.
  unfold SBH.oomin.
  Check LEQ. Check leqRefl.
  intros. rewrite <- leqRefl; auto.
Qed.

Program Definition insert : A -> PQ -> PQ := preInsert.
Next Obligation.
  destruct x0; lisp.
  destruct x0; lisp.
  exists x; lisp.
  unfold preInsert; simpl.
  destruct b; lisp.
  destruct w. lisp. clear x0 H.
  remember (LEQ x a) as xa; destruct xa; lisp.
  exists x; lisp.
  exists (SBH.oomin a a); lisp.
  rewrite dblMin; lisp.
  rewrite <- (dblMin a).
  eapply SBH.preInsertHeapLess; lisp.
Qed.

Lemma insertCountM : 
  forall f x,
  forall p q, 
    countM f x (SBH.preInsert p q)
    = countR f x p
    + countM f x q.
Proof.
  intros f x p q.
  unfold SBH.preInsert.
  destruct q; simpl; try omega.
  destruct q; simpl; try omega.
  destruct p0; destruct p1; simpl.
  remember (EqNat.beq_nat n n0) as nn0; destruct nn0; simpl; auto;
  remember (SBH.O.preLEQ p r) as pr; destruct pr; simpl; auto;
  remember (SBH.O.preLEQ p r0) as pr0; destruct pr0; simpl; auto;
  remember (SBH.O.preLEQ r r0) as rr0; destruct rr0; simpl; auto;
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
  intros. unfold insert.
  unfold preInsert.
  simpl. destruct same as [f D].
  destruct inp; simpl; auto.
  unfold count.
  simpl. destruct x0; simpl. auto.
  destruct b.
  remember (LEQ y a) as ya; destruct ya; simpl.
  remember (f x y) as xy; destruct xy; simpl; auto;
    remember (f x a) as xa; destruct xa; simpl; auto;
      try omega.
  remember (f x y) as xy; destruct xy; simpl; auto;
    remember (f x a) as xa; destruct xa; simpl; auto;
      try omega.
  destruct D. 
  assert (false = LEQ y y).
  assert (forall z, LEQ z a = LEQ z y).
  apply H. destruct H0. destruct H1. eauto.
  rewrite <- H1. auto.
  rewrite <- leqRefl in H1. inversion H1.
  rewrite insertCountM.
  simpl. rewrite <- Heqxy. omega.
  rewrite insertCountM.
  simpl. rewrite <- Heqxy. omega.
  rewrite insertCountM.
  simpl. rewrite <- Heqxy. omega.
Qed.

Program Definition findMin : PQ -> option A := preFindMin.

Check all_ind.
Print all_ind.

Lemma findMinAll :
  (forall x f (d:DERP LEQ f) y a,
    feapT OO.LEQ a x ->
    (if f y a then S (countT f y x) else countT f y x) > 0 ->
    LEQ a y = true)
  /\ (forall x f (d:DERP LEQ f) y a,
    feapR OO.LEQ a x ->
    (if f y a then S (countR f y x) else countR f y x) > 0 ->
    LEQ a y = true)
  /\ (forall x f (d:DERP LEQ f) y a,
    feapM OO.LEQ a x ->
    (if f y a then S (countM f y x) else countM f y x) > 0 ->
    LEQ a y = true).
Proof.
  apply all_ind; simpl; intros.
  destruct H1; destruct r; simpl in *.
  destruct H1.
  remember (countM f y m) as fym; destruct fym.
  eapply H; eauto. 
  remember (f y a) as fya; destruct fya; try omega.
  eapply H0; eauto. eapply SBH.heapLess. eauto. auto.
  rewrite <- Heqfym.
  remember (f y a) as fya; destruct fya; try omega.
  destruct H0.
  remember (f y a) as fya; destruct fya. 
  destruct d.
  assert (forall z, LEQ z a = LEQ z y).
  apply H3. destruct H4. destruct H5. rewrite H5. auto.
  erewrite <- H5. auto.
  remember (f y a0) as fya0; destruct fya0.
  eapply H; eauto. eapply SBH.heapLess. eauto. auto.
  rewrite <- Heqfya0. omega.
  eapply H; eauto. eapply SBH.heapLess. eauto. auto.
  rewrite <- Heqfya0. auto.
  remember (f y a) as fya; destruct fya.
  destruct d.
  apply H1 in Heqfya. destruct Heqfya. erewrite H4. auto.
  inversion H0.
  destruct H1.
  remember (f y a) as fya; destruct fya.
  eapply H; eauto.
  rewrite <- Heqfya. omega.
  remember (countT f y p) as fyp; destruct fyp.
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
  unfold findMin. simpl. lisp.
  destruct x; simpl.
  intros; unfold count; simpl; auto.
  destruct b.
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

Program Definition meld : PQ -> PQ -> PQ := preMeld.
Next Obligation.
  destruct x; destruct x0; unfold wrapHeap; simpl.
  destruct x; destruct x0; simpl; auto.
  destruct b. unfold wrapHeap in *. auto.
  destruct b; destruct b0; simpl.
  unfold wrapHeap in *.
  destruct w; destruct w0.
  remember (LEQ a a0) as aa0; destruct aa0;
    unfold rootHeap; simpl.
  exists a; lisp.
  rewrite <- (dblMin a).
  apply SBH.preInsertHeapLess; lisp.
  exists a0; lisp.
  rewrite <- (dblMin a0).
  apply SBH.preInsertHeapLess; lisp.
Qed.

Lemma linkCount :
  forall q f x p,
    DERP LEQ f ->
    countT f x (SBH.link p q) 
    = countT f x p
    + countT f x q.
Proof.
  intros.
  unfold SBH.link.
  destruct p; destruct q; lisp.
  destruct (SBH.O.preLEQ r r0); lisp; try omega.
Qed.

Lemma insCount :
  forall q f x p,
    DERP LEQ f ->
    countM f x (SBH.ins p q) 
    = countT f x p
    + countM f x q.
Proof.
  induction q; intros; lisp.
  remember (Compare_dec.nat_compare (SBH.rank p0) (SBH.rank p)) as pp; 
    destruct pp; lisp.
  rewrite IHq. rewrite linkCount. omega. auto. auto.
  rewrite IHq. rewrite linkCount. omega. auto. auto.
Qed.
  

Lemma insCons : 
  forall y x,
    ($) <> SBH.ins x y.
Proof.
  unfold not;
  induction y; intros; lisp;
    unfold not; intros; auto.
  unfold SBH.ins in H. inversion H.
  destruct (Compare_dec.nat_compare (SBH.rank x) (SBH.rank p)).
  eapply IHy; eauto.
  inversion H.
  eapply IHy; eauto.
Qed.

Lemma meldUniqCount :
  forall f inp inq x,
    DERP LEQ f ->
    countM f x (SBH.meldUniq (inp,inq))
    = countM f x inp
    + countM f x inq.
Proof.
  Check SBH.meldUniq_ind.
  pose
    (fun (pq:SBH.preQ * SBH.preQ) r =>
      let (p,q) := pq in
        forall f,
          DERP LEQ f ->
          forall x,
            countM f x r = 
            countM f x p +
            countM f x q) as P.
  assert (forall tu, P tu (SBH.meldUniq tu)).
  apply SBH.meldUniq_ind; unfold P; clear P; lisp; intros.
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
    DERP LEQ f ->
    countM f x (SBH.preMeld inp inq) 
    = countM f x inp
    + countM f x inq.
Proof.
  intros; destruct inp; destruct inq; lisp;
    unfold SBH.preMeld; unfold SBH.uniqify;
      rewrite SBH.meldUniq_equation; lisp.
  rewrite insCount; auto.
  remember (SBH.ins p inp) as pp; destruct pp; 
    rewrite Heqpp; rewrite insCount; lisp.
  remember (SBH.ins p inp) as pp; destruct pp.
  apply insCons in Heqpp. inversion Heqpp.
  remember (SBH.ins p0 inq) as qq; destruct qq.
  apply insCons in Heqqq. inversion Heqqq.
  destruct (Compare_dec.nat_compare (SBH.rank p1) (SBH.rank p2)).
  rewrite insCount; auto. rewrite linkCount; auto. 
  rewrite meldUniqCount; auto.
  rewrite <- insCount; auto. rewrite <- insCount; auto.
  rewrite <- Heqpp. rewrite <- Heqqq. lisp. omega.

  lisp. rewrite meldUniqCount; lisp.
  rewrite <- insCount with (p := p); auto. 
  rewrite <- insCount with (p := p0); auto.
  rewrite <- Heqpp. rewrite <- Heqqq. lisp. omega.

  lisp. rewrite meldUniqCount; lisp.
  rewrite <- insCount with (p := p); auto. 
  rewrite <- insCount with (p := p0); auto.
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
  destruct b; lisp.
  destruct b as [v c]; destruct b0 as [w1 d0]; lisp.
  remember (LEQ v w1) as vw; destruct vw; simpl;
    rewrite insertCountM; simpl; 
      remember (x2 x v) as xv; destruct xv;
        remember (x2 x w1) as xw; destruct xw;
          try omega.
Qed.

Definition extractMin (x:PQ) : option (A*PQ).
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
destruct b0; lisp.
inversion_clear _H; subst.
remember (SBH.preExtractMin m) as mm; destruct mm; auto.
destruct p0; lisp.
destruct r; lisp.
unfold rootHeap; lisp.
Check SBH.preExtractMinHeap.
assert (SBH.listHeap a0 m0).
eapply SBH.preExtractMinHelp. Focus 2. eauto. auto.
assert (SBH.rootHeap a0 (Top a1 m1)).
eapply SBH.preExtractMinRootHeap. Focus 2. eauto. auto.
exists a1; lisp.
rewrite <- (dblMin a1).
eapply SBH.preMeldHeapSome.
unfold SBH.rootHeap in H2; lisp.
replace a1 with (root (Top a1 m1)).
eapply SBH.preExtractMinHeap. Focus 2. eauto.
eauto.
auto.
Defined.

Program Definition deleteMin : PQ -> PQ := preDeleteMin.
Next Obligation.
  destruct x; lisp.
  destruct x; destruct w; unfold wrapHeap; lisp.
  unfold preDeleteMin.
  unfold preExtractMin.
  destruct b.
  remember (SBH.preExtractMin m) as mm; destruct mm; lisp.
  destruct p; lisp.
  destruct r; lisp.
  unfold rootHeap; lisp.
  exists a0; lisp.
  rewrite <- (dblMin a0); apply SBH.preMeldHeapSome.
  eapply SBH.preExtractMinRootHeap in Heqmm; eauto. lisp.
  unfold SBH.rootHeap in *; lisp.
  eapply SBH.preExtractMinHeap in Heqmm; eauto.
  lisp.
Qed.

Lemma extractMinCount :
  forall inp,
    match findMin inp with
      | None => None = extractMin inp
      | Some x => exists z,
        Some (x,z) = extractMin inp
        /\ forall same y,
          count same y z = count same y (deleteMin inp)
    end.
Proof. 
  intros.
  destruct inp.
  destruct x. destruct w. lisp.
  destruct w. lisp.
  unfold findMin. 
  unfold preFindMin. lisp.
  destruct b; lisp.
  lisp.
  exists ( 
    exist (fun x0 : bootWrap => wrapHeap x0)
    match SBH.preExtractMin m with
      | Some (pair (Top w d) cs) => Full (Top w (SBH.preMeld d cs))
      | None => Empty
    end
    (match
       SBH.preExtractMin m as o
         return
         (o = SBH.preExtractMin m ->
           match
             match o with
               | Some (pair (Top w d) cs) =>
                 Full (Top w (SBH.preMeld d cs))
               | None => Empty
             end
             with
             | Empty => True
             | Full y => rootHeap y
           end)
       with
       | Some p0 =>
         fun Heqmm : Some p0 = SBH.preExtractMin m =>
           (let (r, m0) as p
             return
             (Some p = SBH.preExtractMin m ->
               match
                 (let (r, cs) := p in
                   match r with
                     | Top w d => Full (Top w (SBH.preMeld d cs))
                   end)
                 with
                 | Empty => True
                 | Full y => rootHeap y
               end) := p0 in
             fun Heqmm0 : Some (r, m0) = SBH.preExtractMin m =>
               match
                 r as r0
                   return
                   (Some (r0, m0) = SBH.preExtractMin m ->
                     match
                       match r0 with
                         | Top w d => Full (Top w (SBH.preMeld d m0))
                       end
                       with
                       | Empty => True
                       | Full y => rootHeap y
                     end)
                 with
                 | Top a1 m1 =>
                   fun Heqmm1 : Some (Top a1 m1, m0) = SBH.preExtractMin m =>
                     ex_intro
                     (fun v : OO.A =>
                       true = OO.LEQ v a1 /\
                       feapM OO.LEQ a1 (SBH.preMeld m1 m0)) a1
                     (conj (OO.leqRefl a1)
                       (eq_ind (SBH.oomin a1 a1)
                         (fun a0 : A => feapM OO.LEQ a0 (SBH.preMeld m1 m0))
                         (SBH.preMeldHeapSome a1 m1 a1 m0
                           match
                             SBH.preExtractMinRootHeap m a f Heqmm1
                             with
                             | conj _ H3 => H3
                           end
                           match SBH.preExtractMinHeap a m f Heqmm1 with
                             | conj _ H0 => H0
                           end) a1 (dblMin a1)))
               end Heqmm0) Heqmm
       | None => fun _ : None = SBH.preExtractMin m => I
     end eq_refl)).
lisp.
Qed.

(* TODO: extractList *)


Lemma getMinSplit :
  forall xs x,
    forall y z,
      (y,z) = SBH.getMin x xs ->
      forall f w, 
        DERP LEQ f ->
        countT f w y
        + countM f w z
        = countT f w x 
        + countM f w xs.
Proof.
  induction xs; lisp; intros.
  inversion_clear H; lisp.
  remember (SBH.getMin p xs) as pxs; destruct pxs.
  eapply IHxs in Heqpxs; eauto. rewrite <- Heqpxs. Show Existentials.
  remember (SBH.O.preLEQ (SBH.root x) (SBH.root p0)) as xp; destruct xp;
    inversion H; subst; lisp. 
  omega.
Qed.

Lemma splitSplit :
  forall e a b c d,
    (a,b) = SBH.split c d e ->
      forall f w, 
        DERP LEQ f ->
        countM f w a
        + fold_right plus 0 (map (countR f w) b)
        = countM f w c 
        + fold_right plus 0 (map (countR f w) d)
        + countM f w e.
Proof.
  induction e; intros; lisp.
  inversion_clear H; subst; try omega.
  destruct p; lisp.
  destruct m; lisp.
  eapply IHe in H. lisp. rewrite H. omega. auto.
  eapply IHe in H. lisp. rewrite H. omega. auto.
Qed.


Lemma countFold :
  forall l f w v,
    countM f w (fold_right SBH.preInsert v l) 
    = countM f w v 
    + fold_right plus 0 (map (countR f w) l).
Proof.
  induction l; lisp; intros.
  rewrite insertCountM.
  rewrite IHl.  omega.
Qed.

(*
Lemma countFold :
  forall l f w v,
    countM f w (fold_right SBH.preInsert v l) 
    = countM f w v 
    + countM f w (fold_right SBH.preInsert ($) l).
Proof.
  induction l; lisp; intros.
  repeat (rewrite insertCountM).
  rewrite IHl.  omega.
Qed.
*)

Lemma preExtractMinSplit :
  forall x y z,
    Some (y,z) = SBH.preExtractMin x ->
    forall f w, 
      DERP LEQ f ->
      countM f w x
      = countR f w y 
      + countM f w z.
Proof.
  intros.
  destruct x; lisp.
  inversion H.
  remember (SBH.getMin p x) as px; destruct px; lisp.
  destruct p0; lisp.
  remember (SBH.split ($) nil m0) as mm; destruct mm; lisp.
  inversion_clear H; subst.
  erewrite <- getMinSplit; eauto. lisp.
  assert (countM f w m0 + countM f w m =
    countM f w (fold_right SBH.preInsert (SBH.preMeld m m1) l)).
  Focus 2. omega.

  eapply splitSplit in Heqmm; eauto. lisp.
(*1*)
  rewrite countFold. rewrite preMeldCount; auto.
  rewrite <- Heqmm. omega.
(*1*)
Qed.
  
Lemma deleteMinCount :
  forall inp,
    match findMin inp with
      | None => forall same x, count same x (deleteMin inp) = 0
      | Some x =>
        forall same y, 
          let newCount := count same y (deleteMin inp) in
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
  destruct b; lisp.
  intros.
  unfold count; lisp.
  destruct same; lisp.
  remember (x0 y a) as xya; destruct xya; lisp.
  unfold preCount; lisp.
  unfold preDeleteMin; lisp.
  remember (SBH.preExtractMin m) as mm; destruct mm; lisp.
  destruct p; lisp. destruct r; lisp.
  remember (x0 y a0) as xya0; destruct xya0; lisp.
  erewrite preExtractMinSplit; auto. Focus 2. eauto.
  rewrite preMeldCount; auto.
  lisp. rewrite <- Heqxya0. omega.
  erewrite preExtractMinSplit; auto. Focus 2. eauto.
  rewrite preMeldCount; auto.
  lisp. rewrite <- Heqxya0. omega.
  destruct m; lisp. inversion Heqmm.
  
  unfold preCount; lisp.
  unfold preDeleteMin; lisp.
  remember (SBH.preExtractMin m) as mm; destruct mm; lisp.
  destruct p; lisp. destruct r; lisp.
  remember (x0 y a0) as xya0; destruct xya0; lisp.
  erewrite preExtractMinSplit; auto. Focus 2. eauto.
  rewrite preMeldCount; auto.
  lisp. rewrite <- Heqxya0. omega.
  erewrite preExtractMinSplit; auto. Focus 2. eauto.
  rewrite preMeldCount; auto.
  lisp. rewrite <- Heqxya0. omega.
  destruct m; lisp. inversion Heqmm.
Qed.

End InlineBoot.

Print PQVerify.

Module InlineV(OO:Order) <: PQVerify.

Module PQS := InlineBoot(OO).
Definition count := PQS.count.
Definition check := PQS.check.
Definition countSAME := PQS.countSAME.
Definition emptyCount := PQS.emptyCount.
Definition insertCount := PQS.insertCount.
Definition findMinCount := PQS.findMinCount.
Definition extractMinCount := PQS.extractMinCount.
Definition deleteMinCount := PQS.deleteMinCount.
Definition meldCount := PQS.meldCount.

End InlineV.