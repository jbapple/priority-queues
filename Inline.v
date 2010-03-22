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

(*
Locate "$".
Locate "[]".
Locate "::".

Print cons.
Print cil.

Check (let x := Node (Top 1 cil) 0 cil in [[ x | x ]]).
*)

Combined Scheme all_ind from preT'_w, Root_w, ml_w.

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

(*
Functional Scheme feapT_ind := Induction for feapT Sort Prop
with feapR_ind := Induction for feapR Sort Prop
with feapM_ind := Induction for feapM Sort Prop.
*)

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

(*
Functional Scheme weapT_ind := Induction for weapT Sort Prop.
*)

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

Module RootOrd (OO:Order) <: Order.

  Definition A := Root OO.A.

  Definition LEQ x y :=
    match x,y with
      Top p _, Top q _ => OO.LEQ p q
    end.
  Hint Unfold LEQ.
  
  Lemma leqRefl: forall x, true = LEQ x x.
  Proof.
    unfold LEQ.
    destruct x.
    auto using OO.leqRefl.
  Qed.
  
  Lemma leqTransTrue : 
    forall x y z,
      true = LEQ x y ->
      true = LEQ y z ->
      true = LEQ x z.
  Proof.
    intros. destruct x; destruct y; destruct z; simpl in *.
    eauto using OO.leqTransTrue.
  Qed.
  
  Lemma leqTransFalse :
    forall x y z,
      false = LEQ x y ->
      false = LEQ y z ->
      false = LEQ x z.
  Proof.
    intros. destruct x; destruct y; destruct z; simpl in *.
    eauto using OO.leqTransFalse.
  Qed.
  
  Lemma leqSymm : 
    forall x y,
      false = LEQ x y ->
      true = LEQ y x.
  Proof.
    intros. destruct x; destruct y; simpl in *.
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



Definition link (x y:preT) :=
  match x, y with
    | Node v n p, Node w m q =>
      if LEQ v w 
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
      if LEQ a b
        then if LEQ a c
          then Node a (S j) [[y | z]]
          else Node c (S k) (x:::y:::r)
        else if LEQ b c
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
          if LEQ w z
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
        if LEQ (root x) (root t)
          then (x,xs)
          else (t,x:::ts)
  end.

Fixpoint split t x c :=
  match c with
    | ($) => (t,x)
    | d:::ds => 
      match rank d with
        | 0 => split t ((root d)::x) ds
        | _ => split (d:::t) x ds
      end
  end.

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
  remember (LEQ v w) as vw; destruct vw; apply simple; auto.
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
  remember (LEQ a b) as ab; remember (LEQ a c) as ac;
    remember (LEQ b c) as bc;
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
  remember (LEQ (root x) (root t)) as rxt.
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
  simpl. remember (LEQ (root x) (root x0)) as xx0; destruct xx0; intros.
  inversion_clear H1; subst; eauto.
  inversion_clear H1; subst; eauto.
  simpl.
  intros.
  remember (getMin x0 xs0) as x00; destruct x00.
  remember (LEQ (root x) (root p)) as xp; destruct xp;
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
  remember (LEQ r (root p)) as ap; destruct ap;
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

Definition minHeap x := exists v, feapT OO.LEQ v x.
Definition rootHeap x := exists v, feapR OO.LEQ v x.
Definition listHeap x := exists v, feapM OO.LEQ v x.

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

Lemma Nil : listHeap ($).
Proof.
  exists (@None OO.A). simpl. auto.
Qed.
Hint Resolve Nil.

Ltac lisp := simpl in *;
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H; lisp
    | [ |- _ /\ _ ] => split; lisp
    | [ H : minHeap _ |- _ ] => destruct H; lisp
    | [ H : rootHeap _ |- _ ] => destruct H; lisp
    | [ H : listHeap _ |- _ ] => destruct H; lisp
    | _ => auto
  end.


Set Maximal Implicit Insertion.
Implicit Arguments None [A].
Unset Maximal Implicit Insertion.

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
  eapply OO.leqTransTrue; eauto.

  exists (Some w); lisp.
  destruct y; lisp.
  destruct r; lisp.
  eapply OO.leqTransTrue.
  eapply OO.leqSymm; eauto.
  auto.
  destruct ys; lisp.
  destruct p; lisp.
  destruct r; lisp.
  eapply OO.leqTransTrue.
  eapply OO.leqSymm; eauto.
  auto.
  clear H I H1 y x.
  generalize dependent w.
  generalize dependent v.
  induction ys; intros.
  eauto. lisp.
  Focus 2. eapply IHys; eauto.
  destruct p0; lisp.
  destruct r; lisp.
  eapply OO.leqTransTrue.
  eapply OO.leqSymm; eauto.
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

Lemma lone : 
  forall v n, 
    rootHeap v ->
    minHeap (Node v n ($)).
Proof.
  unfold rootHeap; unfold minHeap; intros.
  destruct H as [w R].
  destruct v as [x c].
  exists (Some x).
  lisp.
  apply OO.leqRefl.
Qed.
Hint Resolve lone.

Lemma top : forall v n n' w m m' p ys,
  minHeap (Node v n ys) ->
  true = LEQ v w ->
  minHeap (Node w m' p) ->
  minHeap (Node v n' ((Node w m p) ::: ys)).
Proof.
  intros.
  destruct v as [r i c].
  exists (Some r). lisp.
  apply OO.leqRefl.
  destruct i; lisp. 
  destruct w; lisp.
  destruct w; lisp.
Qed.
Hint Resolve top.

Lemma linkHeap :
  forall x y, minHeap x -> minHeap y -> minHeap (link x y).
Proof.
  intros x y X Y.
  unfold link.
  destruct x as [v n p]; destruct y as [w m q].
  remember (LEQ v w) as vw; destruct vw; eapply top; eauto.
  apply leqSymm; auto.
Qed.
Hint Resolve linkHeap.

Lemma skewLinkHeap :
  forall x y z, rootHeap x -> minHeap y -> minHeap z -> 
    minHeap (skewLink (Node x 0 ($)) y z).
Proof.
  intros x y z X Y Z.
  unfold skewLink.
  rename x into a.
  destruct y as [b j q]; destruct z as [c k r].
  unfold rank in *; subst.
  remember (LEQ a b) as ab; destruct ab; simpl.
  Case "a <= b".
    remember (LEQ a c) as ac; destruct ac; simpl.
    SCase "a <= c".
      lisp. destruct b; destruct c; lisp.
      destruct a; lisp.
      exists (Some a); lisp.
      apply OO.leqRefl.
    SCase "a > c".
      assert (true = LEQ c a). apply leqSymm; auto.
      destruct c. exists (Some a0).
      lisp. apply OO.leqRefl.
      destruct a; destruct b; lisp.
      destruct a; auto.
      destruct a; destruct b; lisp.
      eapply OO.leqTransTrue; eauto. 
  Case "b > a".
    assert (true = LEQ b a). apply leqSymm; auto.
    remember (LEQ b c) as bc; destruct bc; simpl.
    SCase "b <= c".
      destruct c; lisp.
      destruct b; lisp.
      exists (Some a1); lisp.
      apply OO.leqRefl.
      destruct a; lisp.
      destruct a; auto.
    SCase "b > c".
      assert (true = LEQ c b). apply leqSymm; auto.
      destruct c; lisp.
      destruct b; lisp.
      exists (Some a0); lisp.
      apply OO.leqRefl.
      destruct a; lisp.
      eapply OO.leqTransTrue; eauto.
      destruct a; auto.
Qed.
Hint Resolve skewLinkHeap.


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

Lemma preInsertHeap :
  forall x ys,
    rootHeap x ->
    listHeap ys ->
    listHeap (preInsert x ys).
Proof with auto.
  intros x ys P X.
  destruct ys.
  Case "ys = ($)".
    simpl. 
    SCase "Aml minHeap [Node x 0 ($)]".
      eauto.
  Case "ys = p ::: _".
    unfold preInsert.
    destruct ys.
    SCase "ys = nil".
      rename P into M.
      SSCase "Aml minHeap [Node x 0 ($); p]".
        inversion M; subst. auto.
    SCase "ys = p0 ::: _".
      rename p0 into q.
      rename P into M.
      remember (beq_nat (rank p) (rank q)) as pq; destruct pq.
      SSCase "Aml minHeap (skewLink (Node x 0 ($)) p q ::: ys)".
        apply Cons.
        apply skewLinkHeap; auto.
        inversion_clear X; auto.
        inversion_clear H. exists x0; auto.
        inversion_clear X; subst.
        inversion_clear H; subst.
        inversion_clear H1; subst.
        eauto. inversion_clear X; subst.
        inversion_clear H; subst.
        inversion_clear H1; subst.
        eauto.
      SSCase "Aml minHeap (Node x 0 ($) ::: p ::: q ::: ys".
         apply Cons; auto.
Qed.

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

Lemma getMinTHeap :
  forall x xs,
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
  remember (LEQ (root x) (root p)) as xp; destruct xp.
  inversion_clear H1; subst. auto.
  inversion_clear H1; subst.
  inversion_clear H0; subst.
  eapply IHxs. Focus 3.
  eauto.
  inversion_clear H1; subst; eauto.
  inversion_clear H1; subst; eauto.
Qed.

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
  remember (LEQ (root x) (root p)) as xp; destruct xp;
    inversion_clear H1; subst; eauto.
  inversion_clear H0; subst.
  apply Cons; eauto. 
  eapply IHxs. Focus 3. eauto.
  inversion_clear H1; subst; eauto.
  inversion_clear H1; subst; eauto.
Qed.

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

Fixpoint Each t (P:t -> Prop) l :=
  match l with
    | nil => True
    | x::xs => P x /\ Each P xs
  end.
Hint Unfold Each.

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
  forall x,
    listHeap x ->
    listHeap (preDeleteMin x).
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

Definition PQP x := skewBinaryRank x /\ listHeap x.

Definition PQ := { x:preQ | PQP x}.

Program Definition empty : PQ := ($).
Next Obligation.
  lisp. split. eauto. eauto.
Qed.

Program Definition insert : A -> PQ -> PQ := preInsert.
Next Obligation.
  destruct x0.
  destruct p.
  split.
  simpl.
  apply preInsertRank. assumption.
  simpl. apply preInsertHeap. auto.
Qed.

Program Definition findMin : PQ -> option A := preFindMin.

Program Definition meld : PQ -> PQ -> PQ := preMeld.
Next Obligation.
  destruct x; destruct x0.
  destruct p; destruct p0; split; simpl.
  apply preMeldRank; auto.
  apply preMeldHeap; auto.
Qed.

Program Definition deleteMin : PQ -> PQ := preDeleteMin.
Next Obligation.
  destruct x. destruct p; split; simpl.
  apply deleteMinRank; auto.
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
        | Some (y,z) => fun s => Some (y,(@exist _ _ z _))
      end eq_refl
  end).
  destruct xp as [R M].
  split.
  eapply extractMinRank; eauto.
  eapply preExtractMinHeap; eauto.
Defined.

Lemma extractMin_equality :
  forall x px y z pz,
    Some (y,exist _ z pz) = extractMin (exist _ x px) ->
    Some (y,z) = preExtractMin x.
Proof.
  intros.
  generalize dependent H. 
  remember (preExtractMin x) as pemx.
  unfold extractMin.  
(*  generalize dependent Heqpemx.*)
  assert (forall (zz:option(A*preQ)) (pp:zz= preExtractMin x),
    Some (y, exist (fun x0 : preQ => PQP x0) z pz) =
    match
      zz as j return (j = preExtractMin x -> option (A * PQ))
      with
      | Some p =>
        let (y0, z0) as p0
          return (Some p0 = preExtractMin x -> option (A * PQ)) := p in
          fun s : Some (y0, z0) = preExtractMin x =>
            Some
            (y0,
              exist (fun x0 : preQ => PQP x0) z0
              match px with
                | conj R M => conj (extractMinRank R s) (preExtractMinHeap M s)
              end)
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
(*  generalize dependent Heqpemx.*)
  assert (forall (zz:option(A*preQ)) (pp:zz= preExtractMin x),
    None =
    match
      zz as j return (j = preExtractMin x -> option (A * PQ))
      with
      | Some p =>
        let (y0, z0) as p0
          return (Some p0 = preExtractMin x -> option (A * PQ)) := p in
          fun s : Some (y0, z0) = preExtractMin x =>
            Some
            (y0,
              exist (fun x0 : preQ => PQP x0) z0
              match px with
                | conj R M => conj (extractMinRank R s) (preExtractMinHeap M s)
              end)
      | None => fun _ : None = preExtractMin x => None
   end pp -> None = pemx) as P. Focus 2.
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

Definition preInsert x xs :=
  preMeld (Full (Top x SBH.preEmpty)) xs.

Definition preFindMin x :=
  match x with
    | Empty => None
    | Full (Top v _) => Some v
  end.

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

Definition preDeleteMin x :=
  match preExtractMin x with
    | None => x
    | Some (_,y) => y
  end.

Definition PQ := Boot.

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

Definition count (same:DER LEQ) x p :=
  match p with
    | Empty => 0
    | Full q =>
      match same with
        | exist f _ => countR f x q
      end
  end.

Definition check (same:DER LEQ) x y := 
  match same with
    | exist f _ => f x y
  end.

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
  simpl in xy. destruct p; auto.
  apply countJoin; auto.
Qed.

Definition preEmpty := Empty.
Definition empty := preEmpty.

Lemma emptyCount :
  forall same x, count same x empty = 0.
Proof.
  intros; auto.
Qed.

Definition insert := preInsert.

Lemma insertCountM : 
  forall f x,
  forall p q, 
    countM f x ((SBH.preInsert p) q)
    = countR f x p
    + countM f x q.
Proof.
  intros f x p q.
  unfold SBH.preInsert.
  destruct q; simpl; try omega.
  destruct q; simpl; try omega.
  destruct p0; destruct p1; simpl.
  remember (EqNat.beq_nat n n0) as nn0; destruct nn0; simpl; auto;
  remember (SBH.O.LEQ p r) as pr; destruct pr; simpl; auto;
  remember (SBH.O.LEQ p r0) as pr0; destruct pr0; simpl; auto;
  remember (SBH.O.LEQ r r0) as rr0; destruct rr0; simpl; auto;
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
  simpl. destruct b.
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

Definition findMin := preFindMin.



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
  intros; destruct inp; simpl; intros; auto.
  destruct b; simpl; intros.
  destruct same as [f D]; simpl.
  remember (f y a) as ya; destruct ya. omega.
  intros.

  Parameter extractMinCount :
    forall inp,
      match findMin inp with
        | None => None = extractMin inp
        | Some x => exists z,
          Some (x,z) = extractMin inp
          /\ forall same y,
            count same y z = count same y (deleteMin inp)
      end.

(* TODO: extractList *)

  Parameter deleteMinCount :
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

  Parameter meldCount :
    forall same inp inq x,
      count same x (meld inp inq) = count same x inp
                                  + count same x inq.


Inductive rankT : preT -> Prop :=
  trank : forall r i c,
          SBH.rankP (Node r i c) ->
          rankR r ->
          rankT (Node r i c)
with rankR : Boot -> Prop :=
  rrank : forall h l,
          SBH.Aml rankT l ->
          SBH.skewBinaryRank l ->
          rankR (Top h l).
Hint Constructors rankT.
Hint Constructors rankR.

Definition rankB x :=
  match x with
    | Empty => True
    | Full y => rankR y
  end.
Hint Unfold rankB.

Lemma insertRankT :
  forall xs x,
  rankR x ->
  SBH.Aml rankT xs ->
  SBH.Aml rankT (SBH.preInsert x xs).
Proof.
  induction xs; simpl; intros.
  constructor; auto. constructor; auto. unfold SBH.rankP; auto.
  inversion_clear H0; subst.
  destruct xs.
  constructor; auto. constructor; auto. unfold SBH.rankP; auto.
  inversion_clear H2; subst.
  destruct a as [b j q]; destruct p as [c k r]; simpl.
  inversion H1; subst; inversion H0; subst; simpl; auto;
  remember (EqNat.beq_nat j k) as jk; destruct jk; simpl; auto;
  remember (SBH.O.LEQ x b) as xb; destruct xb; simpl; auto;
  remember (SBH.O.LEQ x c) as xc; destruct xc; simpl; auto;
  remember (SBH.O.LEQ b c) as bc; destruct bc; simpl; auto;
    constructor; auto; constructor; auto.
  remember (Eqneq_nat
  

Lemma meldRank :
  forall p q,
    rankB p -> rankB q -> rankB (preMeld p q).
Proof.
  intros p q P Q.
  unfold preMeld.
  destruct p as [|p]; destruct q as [|q]; auto.
  destruct p; auto.
  destruct p as [v c]; destruct q as [w d]; auto.
  remember (LEQ v w) as vw; destruct vw; simpl.
  constructor.
  simpl in *.
  inversion P; inversion Q; subst.
  induction H1.
  simpl. constructor; auto. constructor; auto. unfold SBH.rankP; auto.
  
  auto.
  Check rankT_ind.
  



    | Top _ l => SBH.Aml rankT l /\ SBH.skewBinaryRank l
  end.

Fixpoint rankT (x:preT) :=
  SBH.rankP x /\
  match x with 
    | Node r _ _ => rankR r
  end.
with rankR x :=
  match x with
    | Top _ l => SBH.Aml rankT l /\ SBH.skewBinaryRank l
  end.


Inductive Tree :=
  Node : A -> list Tree -> nat -> list Tree -> Tree.

Fixpoint size a := S
  match a with
    | Node b _ c =>
      let add x := fold_right plus 0 (map size x) in
        add b + add c
  end.

