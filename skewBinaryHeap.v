Require Export OrderSig.

Module SkewBinaryHeap (O:Order).

Set Implicit Arguments.

Import O.
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

Definition isEmpty (x : preQ) :=
  match x with
    | [] => true
    | _ => false
  end.

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

Fixpoint preFindMin x xs :=
  match xs with 
    | [] => root x
    | y::ys => 
      let z := preFindMin y ys in
        let w := root x in
          if LEQ w z
            then w
            else z
  end.

Fixpoint getMin x xs :=
  match xs with
    | [] => (x,[])
    | y::ys =>
      let (t,ts) := getMin y ys in
        if LEQ (root y) (root t)
          then (y,ys)
          else (t,y::ts)
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

Definition rankP x := rankN x (rank x).

Inductive minHeap : preT -> Prop :=
  lone : forall v n, minHeap (Node v n [])
| top : forall v n n' w m p ys,
        minHeap (Node v n ys) ->
        true = LEQ v w ->
        minHeap (Node v n' ((Node w m p) :: ys)).

Definition PTP x := rankP x /\ minHeap x.

Inductive posBinaryRank : preQ -> nat -> Prop :=
  last : forall x n,
         rankN x n ->
         posBinaryRank [x] n
| next : forall x n m xs,
         rankN x n ->
         n < m ->
         posBinaryRank xs m ->
         posBinaryRank (x::xs) n.

Inductive binaryRank : preQ -> Prop :=
  zeroBin : binaryRank []
| posBin : forall n xs,
           posBinaryRank xs n ->
           binaryRank xs.

Inductive posSkewBinaryRank : preQ -> nat -> Prop :=
  vanilla : forall xs n, 
            posBinaryRank xs n ->
            posSkewBinaryRank xs n
| skew : forall x n xs,
         rankN x n ->
         posBinaryRank xs n ->
         posSkewBinaryRank (x::xs) n.

Inductive skewBinaryRank : preQ -> Prop :=
  zeroSkew : skewBinaryRank []
| posSkew : forall n xs,
           posSkewBinaryRank xs n ->
           skewBinaryRank xs.

Inductive All t (p:t -> Prop) : list t -> Prop :=
  Nil : All p []
| Cons : forall x xs,
         p x ->
         All p xs ->
         All p (x::xs).

Definition PQP x := skewBinaryRank x /\ All minHeap x.

Definition PQ := { x:preQ | PQP x}.

Program Definition empty : PQ := [].
Next Obligation.
  split; constructor.
Qed.

Lemma rankDestruct :
  forall v n c m,
    rankN (Node v n c) m ->
    n = m.
Proof.
  intros v n c m r.
  inversion r; subst; auto.
Qed.

Lemma rankRank :
  forall x n,
    rankN x n ->
    rank x = n.
Proof.
  intros x n r.
  inversion r; subst; auto.
Qed.

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

Lemma linkHeap :
  forall x y, minHeap x -> minHeap y -> minHeap (link x y).
Proof.
  intros x y X Y.
  unfold link.
  destruct x as [v n p]; destruct y as [w m q].
  remember (LEQ v w) as vw; destruct vw; eapply top; eauto.
  apply leqSymm; auto.
Qed.

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

Lemma skewLinkHeap :
  forall x y z, 0 = rank x -> minHeap y -> minHeap z -> 
    minHeap (skewLink x y z).
Proof.
  intros x y z X Y Z.
  unfold skewLink.
  destruct x as [a i p]; destruct y as [b j q]; destruct z as [c k r].
  unfold rank in *; subst.
  remember (LEQ a b) as ab; destruct ab; simpl.
  Case "a <= b".
    remember (LEQ a c) as ac; destruct ac; simpl.
    SCase "a <= c".
      eapply top with (n:=0); auto. eapply top; auto. apply lone with (n := 0).
    SCase "a > c".
      assert (true = LEQ c a). apply leqSymm; auto.
      eapply top with (n:=0); auto. eapply top; auto. eauto.
      eapply leqTransTrue; eauto.
  Case "b > a".
    assert (true = LEQ b a). apply leqSymm; auto.
    remember (LEQ b c) as bc; destruct bc; simpl.
    SCase "b <= c".
      eapply top with (n:=0); auto. eapply top; auto. eauto.
    SCase "b > c".
      assert (true = LEQ c b). apply leqSymm; auto.
      eapply top with (n:=0); auto. eapply top; auto. eauto.
      eapply leqTransTrue; eauto.
Qed.

Lemma insNoDupeHelp : 
  forall n m x xs, 
    rankN x n ->
    posBinaryRank xs m ->
    n <= m ->
    exists k, posBinaryRank (ins x xs) k.
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
      exists (S n). constructor. apply linkRank; auto.
    SCase "j < n".
      assert (j < n) as jn2. apply nat_compare_lt; auto.
      exists j. eapply next; eauto.
      constructor; auto.
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
      eapply IHxsm; eauto. apply linkRank; auto.
    SCase "j < n".
      assert (j < n) as jn2. apply nat_compare_lt; auto.
      exists j. eapply next; eauto.
      eapply next; eauto.
    SCase "j > n".
      assert (j > n) as jn2. apply nat_compare_gt; auto.
      assert False as f. omega. inversion f.
Qed.

Lemma insNoDupe : 
  forall n x xs, 
    posSkewBinaryRank (x::xs) n ->
    exists k, posBinaryRank (ins x xs) k.
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

Lemma preInsertType :
  forall x ys,
    PQP ys ->
    PQP (preInsert x ys).
Proof.
  intros x ys P.
  destruct ys.
  Case "ys = []".
    simpl. split.
    SCase "skewBinaryRank [Node x 0 []]".
      eapply posSkew.
      eapply vanilla.
      eapply last.
      apply singleton.
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
      destruct P as [R M].
      split.
      SSCase "skewBinaryRank [Node x 0 []; p]".
        eapply posSkew.
        inversion R as [|n xs P]; subst.
        inversion P; subst.
        SSSCase "".
          destruct n.
          eapply skew; eauto. constructor.
          apply vanilla.
          eapply next. constructor.
          Focus 2. eauto.
          auto with arith.
        SSSCase "impossible".
          inversion H3.
      SSCase "All minHeap [Node x 0 []; p]".
        inversion M; subst.
        eapply Cons; eauto. constructor.
    SCase "ys = p0 :: _".
      rename p0 into q.
      destruct P as [R M].
      remember (beq_nat (rank p) (rank q)) as pq; destruct pq.
      SSCase "rank p = rank q".
        assert (rank p = rank q) as pq. apply beq_nat_true; auto.
        split.
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

          Show Existentials.

          instantiate (1 := S (rank p)).
          assert (rank p = n).
          eapply rankRank; auto.
          subst.
          inversion H4; subst.
          eapply vanilla; auto. eapply last; auto. 
          apply skewLinkRank; auto.
          constructor. 

          inversion H5.
          eapply skew; auto. eapply skewLinkRank; auto.
          constructor.
          subst; auto.
          
          eapply vanilla; auto.
          eapply next.
          eapply skewLinkRank; auto.
          constructor.
          Focus 2. 
          eauto. omega.
        
        SSSCase "All minHeap (skewLink (Node x 0 []) p q :: ys)".
          apply Cons.
          apply skewLinkHeap; auto.
          inversion M; auto.
          inversion M. inversion H2; auto.
          inversion M. inversion H2; auto.
      SSCase "rank p <> rank q".
        assert (rank p <> rank q) as pq. apply beq_nat_false; auto.
        split.
        
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

       SSSCase "heap".
         apply Cons; auto.
         constructor.
Qed.
    

Fixpoint skewSize x :=
  match x with
    | Node v _ r => S (fold_right plus 0 (map skewSize r))
  end.

Lemma skewSizePos :
  forall x, skewSize x > 0.
Proof.
  intros x; destruct x; simpl; omega.
Qed.

End SkewBinaryHeap.