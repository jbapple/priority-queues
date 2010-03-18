Require Export OrderSig.
Require Export PQSig.

Module SkewBinaryHeap (OO:Order) <: PQSig.

Set Implicit Arguments.

Module O := OO.
Export O.
Require Export Arith.
Require Export List.
Require Export Program.
Require Export Omega.
Require Export Recdef.
Require Export Coq.Program.Wf.
Require Export caseTactic.

Inductive preT  :=
  Node : A -> nat -> list preT -> preT.

Definition preQ := list preT.

Definition root x :=
  match x with
    | Node v _ _ => v
  end.

Definition rank x :=
  match x with
    | Node _ r _ => r
  end.

Definition link x y :=
  match x, y with
    | Node v n p, Node w m q =>
      if LEQ v w 
        then Node v (S n) (y::p)
        else Node w (S m) (x::q)
  end.

Definition skewLink x y z :=
  match x, y, z with
    | Node a i p, 
      Node b j q,
      Node c k r =>
      if LEQ a b
        then if LEQ a c
          then Node a (S j) [y;z]
          else Node c (S k) (x::y::r)
        else if LEQ b c
          then Node b (S j) (x::z::q)
          else Node c (S k) (x::y::r)
  end.

Fixpoint ins t xs :=
  match xs with
    | [] => [t]
    | y::ys =>
      match nat_compare (rank t) (rank y) with
        | Lt => t::xs
        | _ => ins (link t y) ys
      end
  end.

Definition uniqify xs :=
  match xs with
    | [] => []
    | y::ys => ins y ys
  end.

Definition combLen (xy:preQ * preQ) := 
  let (x,y) := xy in
    List.length x + List.length y.

Function meldUniq (xy:preQ * preQ) {measure combLen xy} : preQ :=
  match xy with
    | ([],y) => y
    | (x,[]) => x
    | (p::ps,q::qs) => 
      match nat_compare (rank p) (rank q) with
        | Lt => p :: meldUniq (ps, q::qs)
        | Gt => q :: meldUniq (p::ps, qs)
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

Definition preEmpty : preQ := [].

Definition preInsert x ys :=
  match ys with
    | z1::z2::zr =>
      if beq_nat (rank z1) (rank z2)
        then skewLink (Node x 0 []) z1 z2 :: zr
        else Node x 0 [] :: ys
    | _ => Node x 0 [] :: ys
  end.

Definition preMeld x y :=
  meldUniq (uniqify x, uniqify y).

Fixpoint preFindMinHelp x xs :=
  match xs with 
    | [] => root x
    | y::ys => 
      let z := preFindMinHelp y ys in
        let w := root x in
          if LEQ w z
            then w
            else z
  end.

Definition preFindMin x :=
  match x with
    | [] => None
    | y::ys => Some (preFindMinHelp y ys)
  end.

Fixpoint getMin x xs :=
  match xs with
    | [] => (x,[])
    | y::ys =>
      let (t,ts) := getMin y ys in
        if LEQ (root x) (root t)
          then (x,xs)
          else (t,x::ts)
  end.

Fixpoint split t x c :=
  match c with
    | [] => (t,x)
    | d::ds => 
      match rank d with
        | 0 => split t ((root d)::x) ds
        | _ => split (d::t) x ds
      end
  end.

Definition preDeleteMin x :=
  match x with
    | [] => []
    | y::ys =>
      match getMin y ys with
        | (Node _ _ c,t) =>
          let (p,q) := split [] [] c in
            fold_right preInsert (preMeld t p) q
      end
  end.

(*
Extraction preDeleteMin.
Extraction Language Haskell.
Extraction Inline and_rect sig_rect meldUniq_terminate.
Extract Inductive list => "[]" ["[]" "(:)"].
Extract Inductive bool => "Bool" ["True" "False"].
Recursive Extraction preDeleteMin.
Extraction "ExtractedSkew.hs" preDeleteMin preFindMin preInsert preMeld.
*)

Inductive rankN : preT -> nat -> Prop :=
  singleton : forall x, rankN (Node x 0 []) 0
| simple : forall n v p y,
             rankN (Node v n p) n ->
             rankN y n ->
             rankN (Node v (S n) (y::p)) (S n)
| skewA : forall n x y z,
          rankN x n ->
          rankN z n ->
          rankN (Node y (S n) [x;z]) (S n)
| skewB : forall n x v p y,
          rankN (Node v n p) n ->
          rankN y n ->
          rankN (Node v (S n) ((Node x 0 [])::y::p)) (S n).
Hint Constructors rankN.

Definition rankP x := rankN x (rank x).

Inductive posBinaryRank : preQ -> nat -> Prop :=
  last : forall x n,
         rankN x n ->
         posBinaryRank [x] n
| next : forall x n m xs,
         rankN x n ->
         n < m ->
         posBinaryRank xs m ->
         posBinaryRank (x::xs) n.
Hint Constructors posBinaryRank.

Inductive binaryRank : preQ -> Prop :=
  zeroBin : binaryRank []
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
         posSkewBinaryRank (x::xs) n.
Hint Constructors posSkewBinaryRank.

Inductive skewBinaryRank : preQ -> Prop :=
  zeroSkew : skewBinaryRank []
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
  assert (p = []); try (inversion X; auto); subst.
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
    posSkewBinaryRank (x::xs) n ->
    exists k, k >= n /\ posBinaryRank (ins x xs) k.
Proof.
  intros n x xs xxsn.
  inversion xxsn; subst.
  Case "vanilla".
    destruct xs.
    SCase "xs = nil".
      eauto.
    SCase "xs = p :: _".
      simpl.
      assert (nat_compare (rank x) (rank p) = Lt).
      destruct x; destruct p; simpl.
      inversion H; subst.
      inversion H5; subst.
      assert (n0 = n). eapply rankDestruct; eauto.
      subst.
      assert (n1 = m). eapply rankDestruct; eauto.
      subst.
      apply nat_compare_lt; auto.
      assert (n0 = n). eapply rankDestruct; eauto.
      subst.
      assert (n1 = m). eapply rankDestruct; eauto.
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
  Case "ys = []".
    simpl.
    SCase "skewBinaryRank [Node x 0 []]".
      eapply posSkew.
      eapply vanilla.
      eapply last.
      apply singleton.
  Case "ys = p :: _".
    unfold preInsert.
    destruct ys.
    SCase "ys = nil".
      rename P into R.
      SSCase "skewBinaryRank [Node x 0 []; p]".
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
    SCase "ys = p0 :: _".
      rename p0 into q.
      rename P into R.
      remember (beq_nat (rank p) (rank q)) as pq; destruct pq.
      SSCase "rank p = rank q".
        assert (rank p = rank q) as pq. apply beq_nat_true; auto.
        SSSCase "skewBinaryRank (skewLink (Node x 0 []) p q :: ys".
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
    /\ posBinaryRank (meldUniq (ps, q::qs)) k).
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
    /\ posBinaryRank (meldUniq (p::ps, qs)) k).
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
    forall h t z, (h,t) = split [] z c ->
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
  inversion H.
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
    skewBinaryRank (x::xs) ->
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
    skewBinaryRank (x::xs) ->
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
  remember (getMin a xs) as axs; destruct axs.
  remember (LEQ a0 (root p)) as ap; destruct ap;
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
  remember (split [] [] c) as rs.
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

Inductive minHeap : preT -> Prop :=
  lone : forall v n, minHeap (Node v n [])
| top : forall v n n' w m m' p ys,
        minHeap (Node v n ys) ->
        true = LEQ v w ->
        minHeap (Node w m' p) ->
        minHeap (Node v n' ((Node w m p) :: ys)).
Hint Constructors minHeap.

Inductive All t (p:t -> Prop) : list t -> Prop :=
  Nil : All p []
| Cons : forall x xs,
         p x ->
         All p xs ->
         All p (x::xs).
Hint Constructors All.

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
  forall x y z, minHeap y -> minHeap z -> 
    minHeap (skewLink (Node x 0 []) y z).
Proof.
  intros x y z Y Z.
  unfold skewLink.
  rename x into a.
  destruct y as [b j q]; destruct z as [c k r].
  unfold rank in *; subst.
  remember (LEQ a b) as ab; destruct ab; simpl.
  Case "a <= b".
    remember (LEQ a c) as ac; destruct ac; simpl.
    SCase "a <= c".
      eapply top with (n:=0); auto. eapply top.
      apply lone with (n := 0). auto.
      eauto. eauto.
    SCase "a > c".
      assert (true = LEQ c a). apply leqSymm; auto.
      eapply top with (n:=0).  Focus 3. apply lone with (n := 0).
      eapply top. eauto.
      eapply leqTransTrue; eauto. eauto. auto.
  Case "b > a".
    assert (true = LEQ b a). apply leqSymm; auto.
    remember (LEQ b c) as bc; destruct bc; simpl.
    SCase "b <= c".
      eapply top with (n:=0). Focus 3.
      eapply lone with (n:= 0). 
      eapply top; auto. eauto. eauto. auto.
    SCase "b > c".
      assert (true = LEQ c b). apply leqSymm; auto.
      eapply top with (n:=0). Focus 3. eapply lone with (n:=0).
      eapply top; auto. eauto. eauto.
      eapply leqTransTrue; eauto.
Qed.
Hint Resolve skewLinkHeap.

Lemma insHeap : 
  forall x xs,
    minHeap x ->
    All minHeap xs ->
    All minHeap (ins x xs).
Proof.
  intros x xs.
  generalize dependent x.
  induction xs; intros; auto.
    simpl; auto.
    inversion H0; subst.
    simpl.
    remember (nat_compare (rank x) (rank a)) as xa; destruct xa; auto.
Qed.

Lemma preInsertHeap :
  forall x ys,
    All minHeap ys ->
    All minHeap (preInsert x ys).
Proof with auto.
  intros x ys P.
  destruct ys.
  Case "ys = []".
    simpl. 
    SCase "All minHeap [Node x 0 []]".
      eapply Cons.
      SSCase "minHeap (Node x 0 [])".
        apply lone.
      SSCase "All minHeap []".
        apply Nil.
  Case "ys = p :: _".
    unfold preInsert.
    destruct ys.
    SCase "ys = nil".
      rename P into M.
      SSCase "All minHeap [Node x 0 []; p]".
        inversion M; subst.
        eapply Cons; eauto. 
    SCase "ys = p0 :: _".
      rename p0 into q.
      rename P into M.
      remember (beq_nat (rank p) (rank q)) as pq; destruct pq.
      SSCase "All minHeap (skewLink (Node x 0 []) p q :: ys)".
        apply Cons.
        apply skewLinkHeap; auto.
        inversion M; auto.
        inversion M. inversion H2; auto.
        inversion M. inversion H2; auto.
      SSCase "All minHeap (Node x 0 [] :: p :: q :: ys".
         apply Cons; auto.
Qed.

Lemma meldUniqHeap :
  forall x y,
    All minHeap x ->
    All minHeap y ->
    All minHeap (meldUniq (x,y)).
Proof.
  assert 
    (let P := 
      fun (xy:(preQ*preQ)) r =>
        let (x,y) := xy in
              All minHeap x ->
              All minHeap y ->
              All minHeap r
              in forall xy, P xy (meldUniq xy)).
  eapply meldUniq_ind; intros; auto.
  inversion H0; subst.
  apply Cons; auto.
  inversion H1; subst.
  apply Cons; auto.
  inversion H1; inversion H0; subst.
  apply insHeap; auto.
  intros.
  simpl in H.
  pose (H (x, y)) as I.
  eapply I; auto.
Qed.

Lemma preMeldHeap :
  forall x y,
    All minHeap x ->
    All minHeap y ->
    All minHeap (preMeld x y).
Proof with auto.
  intros x y xH yH.

  apply meldUniqHeap.
  destruct x; inversion xH; subst; auto.
  apply insHeap; auto. 
  destruct y; inversion yH; subst; auto.
  apply insHeap; auto.
Qed.

Lemma getMinTHeap :
  forall x xs,
    minHeap x ->
    All minHeap xs ->
    forall y z, (y,z) = getMin x xs ->
      minHeap y.
Proof.
  intros x xs;
    generalize dependent x;
      induction xs;
        simpl; intros.
  inversion_clear H1; subst; auto.
  remember (getMin a xs) as tts; destruct tts; subst.
  remember (LEQ (root x) (root p)) as xp; destruct xp.
  inversion_clear H1; subst. auto.
  inversion_clear H1; subst.
  inversion_clear H0; subst.
  eapply IHxs; eauto. 
Qed.

Lemma getMinQHeap :
  forall x xs,
    minHeap x ->
    All minHeap xs ->
    forall y z, (y,z) = getMin x xs ->
      All minHeap z.
Proof.
  intros x xs;
    generalize dependent x;
      induction xs; simpl; intros.
  inversion_clear H1; subst; eauto.
  remember (getMin a xs) as tts; destruct tts.
  remember (LEQ (root x) (root p)) as xp; destruct xp;
    inversion_clear H1; subst; eauto.
  inversion_clear H0; subst.
  apply Cons; eauto.
Qed.

Lemma splitHeap :
  forall a, All minHeap a ->
    forall b c, All minHeap c ->
      forall y z, (y,z) = split a b c ->
        All minHeap y.
Proof.
  intros a AA b c.
  generalize dependent a;
    generalize dependent b.
  induction c; simpl; intros.
  inversion_clear H0; subst; auto.
  destruct a as [i j k]; destruct j; simpl in *.
  eapply IHc. Focus 3. eauto.
  auto. inversion_clear H; subst; auto.
  inversion_clear H; subst.
  eapply IHc. Focus 3. eauto.
  auto. auto.
Qed.


Lemma childrenHeap :
  forall v i c,
    minHeap (Node v i c) ->
    All minHeap c.
Proof.
  intros v i c;
    generalize dependent v; 
      generalize dependent i; 
        induction c;
          simpl; intros.
  auto.
  inversion_clear H; subst.
  apply Cons.
  inversion_clear H2; subst; auto.
  eapply top. eauto. auto. eauto.
  eapply IHc. eauto.
Qed.

Lemma preDeleteMinHeap :
  forall x,
    All minHeap x ->
    All minHeap (preDeleteMin x).
Proof.
  intros x.
  induction x; simpl; intros.
  eauto.
  inversion_clear H; subst.
  remember (getMin a x) as pt; destruct pt as [p t].
  destruct p as [zz zzz c].
  remember (split [] [] c) as pq; destruct pq as [p q].
  assert (All minHeap p). eapply splitHeap.
  Focus 3. eauto. auto.
  assert (minHeap (Node zz zzz c)). eapply getMinTHeap.
  Focus 3. eauto. auto. auto.
  eapply childrenHeap. eauto.
  assert (All minHeap t). eapply getMinQHeap. Focus 3. eauto.
  auto. auto.

  clear Heqpq.
  
  induction q. simpl.
  apply preMeldHeap; auto.
  simpl.
  apply preInsertHeap; auto.
Qed.

Definition PQP x := skewBinaryRank x /\ All minHeap x.

Definition PQ := { x:preQ | PQP x}.

Program Definition empty : PQ := [].
Next Obligation.
  split; constructor.
Qed.

Program Definition insert : A -> PQ -> PQ := preInsert.
Next Obligation.
  destruct x0.
  destruct p.
  split.
  simpl.
  apply preInsertRank. assumption.
  simpl. apply preInsertHeap. assumption.
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

End SkewBinaryHeap.