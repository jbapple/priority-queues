Set Implicit Arguments.
Require Export PQSig.
Require Export skewBinaryHeap.

Module SBHeapVerify (OO:Order) <: PQVerify.

Module PQS := SkewBinaryHeap(OO).
Export PQS.

Definition check (same:DER LEQ) (x y:A) := 
  match same with
    | exist f _ => f x y
  end.

Fixpoint countTree (same:A -> A -> bool) x l :=
  match l with
    | Node v _ c => 
      let r := fold_right plus 0 (map (countTree same x) c)
        in if same x v
          then S r
          else r
  end.

Fixpoint size (l:preT) :=
  match l with
    | Node _ _ c =>
      S (fold_right plus 0 (map size c))
  end.

Lemma sizePos :
  forall x, size x > 0.
Proof.
  intros; destruct x; simpl; auto with arith.
Qed.
Hint Resolve sizePos.

Lemma preT_nest_ind :
  forall P : preT -> Prop,
    (forall a n, P (Node _ a n [])) ->
    (forall a n x l, P (Node _ a n l) -> P x -> P (Node _ a n (x::l))) ->
    forall v, P v.
Proof.
  intros P emp ful v.
  generalize dependent P.
  pose well_founded_ind as i.
  pose (i _ (ltof preT size)) as j.
  pose (j (well_founded_ltof _ _)) as k.
  intros; apply k.
  clear k j i. intros.
  unfold ltof in H.
  destruct x.
  destruct l.
  auto.
  apply ful.
  apply H.
  simpl. 
  assert (size p > 0); auto.
  omega.
  apply H.
  simpl. omega.
Qed.

Lemma countTreeSAME :
  forall same x y,
    DERP LEQ same ->
    same x y = true ->
    forall inp, countTree same x inp = countTree same y inp.
Proof.
  intros f x y d ST.
  destruct d as [leq [refl [symm trans]]].
  apply preT_nest_ind.
  simpl. intros a n.
  remember (f x a) as xa; remember (f y a) as ya;
    destruct xa; destruct ya; auto.
  assert False as fa.
  assert (true = f y a).
  eapply trans. symmetry. rewrite symm. eauto.
  auto.
  rewrite <- H in Heqya. inversion Heqya. inversion fa.
  assert False as fa.
  assert (true = f x a).
  eapply trans. symmetry. eauto.
  auto.
  rewrite <- H in Heqxa. inversion Heqxa. inversion fa.
  intros.
  simpl.
  simpl in H.
  remember (f x a) as xa; remember (f y a) as ya;
    destruct xa; destruct ya; auto.  
  rewrite H0. rewrite <- H.
  omega.
  rewrite H0.
  rewrite H.
  omega.
Qed.

Definition preCount f x l :=
  fold_right plus 0 (map (countTree f x) l).
Hint Unfold preCount.

Definition count (same:DER LEQ) x (l:PQ) :=
  match same, l with
    | exist f _, exist v _ => preCount f x v
  end.

Lemma countSAME :
  forall same x y,
    check same x y = true ->
    forall inp, count same x inp = count same y inp.
Proof.
  intros same x y xy inp.
  destruct same; simpl in *.
  destruct inp; simpl in *.
  clear p; induction x1.
  simpl. auto.
  unfold preCount in *. simpl.
  erewrite countTreeSAME. Focus 3. eauto.
  omega. auto.
Qed.

Lemma emptyCount :
  forall same x, count same x empty = 0.
Proof.
  simpl; intros.
  unfold empty. simpl.
  unfold count. simpl.
  destruct same; simpl; auto.
Qed.


Lemma preInsertCount :
  forall f x p y,
    preCount f x (preInsert y p) =
    (let old := preCount f x p in
      if f x y
        then S old 
        else old).
Proof.
  intros.
  destruct p.
  simpl.
  unfold preCount.
  remember (f x y) as fxy; destruct fxy; simpl.
  rewrite <- Heqfxy; auto.
  rewrite <- Heqfxy; auto.
  unfold preCount.
  unfold preInsert.
  destruct p0.
  simpl.
  remember (f x y) as fxy; destruct fxy; simpl; auto.
  simpl.
  destruct p; destruct p0; simpl.
  remember (beq_nat n n0) as nn0; destruct nn0; simpl; auto; try omega;
  remember (LEQ y a) as ya; destruct ya; simpl; auto; try omega;
  remember (LEQ y a0) as ya0; destruct ya0; simpl; auto; try omega;
  remember (LEQ a a0) as aa0; destruct aa0; simpl; auto; try omega;
  remember (f x y) as xy; destruct xy; simpl; auto; try omega;
  remember (f x a) as xa; destruct xa; simpl; auto; try omega;
  remember (f x a0) as xa0; destruct xa0; simpl; auto; try omega.
Qed.


Lemma insertCount :
  forall same x inp y,
    count same x (insert y inp) =
    let oldCount := count same x inp in
      if check same x y 
        then S oldCount
        else oldCount.
Proof.
  intros.
  destruct same; destruct inp.
  unfold count; simpl.
  apply preInsertCount.
Qed.

(*
Lemma insertCount :
  forall same x inp,
    let oldCount := count same x inp in
      forall y,
        count same x (insert y inp) =
        if check same x y 
          then S oldCount
          else oldCount.
Proof.
  intros.
  destruct inp.
  destruct same.
  simpl in *. unfold preCount in *; simpl in *.
  unfold preInsert. simpl.
  destruct x0; simpl in *.
  destruct (x1 x y); auto.
  destruct x0; simpl in *.
  destruct (x1 x y); auto.
  destruct p0; destruct p1; simpl in *.
  unfold oldCount;
  remember (beq_nat n n0) as nn0; destruct nn0; simpl; auto; try omega;
  remember (LEQ y a) as ya; destruct ya; simpl; auto; try omega;
  remember (LEQ y a0) as ya0; destruct ya0; simpl; auto; try omega;
  remember (LEQ a a0) as aa0; destruct aa0; simpl; auto; try omega;
  remember (x1 x y) as xy; destruct xy; simpl; auto; try omega;
  remember (x1 x a) as xa; destruct xa; simpl; auto; try omega;
  remember (x1 x a0) as xa0; destruct xa0; simpl; auto; try omega.
Qed.
*)

Lemma minHeapCount :
  forall x, 
    minHeap x ->
    forall same y,
      DERP LEQ same ->
      countTree same y x > 0 ->
      LEQ (root x) y = true.
Proof.

  pose preT_nest_ind as i.
  pose (fun z => minHeap z -> forall same y, DERP LEQ same -> countTree same y z > 0 -> LEQ (root z) y = true) as P.
  pose (i P) as j.
  unfold P in j.
  apply j; unfold P. intros; clear i P j.
  simpl in *.
  remember (same y a) as ya; destruct ya.
  destruct H0. symmetry. 
  replace true with (LEQ a a).
  apply H0; auto. destruct H2. destruct H3. rewrite H3. auto.
  symmetry.
  apply leqRefl.
  inversion H1.
  clear i P j.
  simpl. intros.
  remember (same y a) as ya; destruct ya.
  destruct H2.
  replace true with (LEQ a a).
  apply H2; auto.
  symmetry.
  apply leqRefl.
  remember (countTree same y x) as yx; destruct yx.
  eapply H.
  inversion_clear H1; subst; auto.
  inversion_clear H4; subst; eauto.
  eauto.
  rewrite <- Heqya. omega.
  inversion H1; subst.
  symmetry.
  eapply leqTransTrue with (y := w).
  auto.
  symmetry.
  eapply H0.
  inversion H10; subst; eauto. eauto.
  omega.
Qed.
  
Lemma preFindFirst :
  forall v i c a ps,
    true = LEQ v (preFindMinHelp a ps) ->
    v = preFindMinHelp (Node _ v i c) ps.
Proof.
  intros.
  induction ps.
  simpl. auto.
  simpl.
  rename a0 into z.
  simpl in H.
  remember (LEQ (root a) (preFindMinHelp z ps)) as azps; destruct azps;
  remember (LEQ v (preFindMinHelp z ps)) as vzps; destruct vzps.
  auto.
  Focus 2. auto.
  Focus 2. inversion H.
  assert (true = LEQ v (preFindMinHelp z ps)).
  eapply leqTransTrue; eauto.
  rewrite <-H0 in Heqvzps. inversion Heqvzps.
Qed.


Lemma findMinHelpCount :
  forall ps, All minHeap ps ->
    forall p, minHeap p ->
    let x := preFindMinHelp p ps in
      forall f (D:DERP LEQ f) y, 
        if check (exist _ f D) y x
          then fold_right plus 0 (map (countTree f y) (p::ps)) > 0
          else fold_right plus 0 (map (countTree f y) (p::ps)) > 0 ->
            LEQ x y = true.
Proof.
  induction ps; simpl; intros.
  destruct p; simpl.
  remember (f y a) as ya; destruct ya.
  auto with arith.
  intros.
  replace a with (root (Node _ a n l)) by auto.
  eapply minHeapCount. auto. eauto.
  simpl. rewrite <- Heqya. omega.
  destruct p as [v i c]; simpl.
  remember (countTree f y (Node _ v i c)) as yvic. destruct yvic.
  remember (LEQ v (preFindMinHelp a ps)) as vaps; destruct vaps.
  remember (f y v) as yv; destruct yv.
  auto with arith.
  intros.
  simpl in IHps.
  inversion H; subst.
  remember (f y (preFindMinHelp a ps)) as yaps; destruct yaps.
  symmetry.
  eapply leqTransTrue. eauto.
  destruct D as [E [F [G I]]]. 
  replace true with (LEQ y y).
  apply E. auto.
  symmetry.
  apply leqRefl.
  remember (f y (preFindMinHelp (Node _ v i c) ps)) as yvps; destruct yvps.
  pose (@IHps H5 _ H0 _ D y) as j.
  rewrite <- Heqyvps in j.
  assert (v = preFindMinHelp (Node _ v i c) ps) as T.
  eapply preFindFirst. eauto.
  rewrite <- T in Heqyvps.
  destruct D as [E [F [G I]]].
  symmetry.
  replace true with (LEQ y y).
  apply E. auto.
  symmetry. apply leqRefl.
  pose (@IHps H5 _ H4 _ D y) as j.
  rewrite <- Heqyaps in j.
  symmetry.
  eapply leqTransTrue.
  eauto.
  symmetry.
  apply j. simpl in Heqyvic. 
  rewrite <- Heqyv in Heqyvic. omega.
  remember (f y (preFindMinHelp a ps)) as yaps; destruct yaps;
    remember (f y v) as yv; destruct yv.
  auto with arith.
  inversion H; subst.
  pose (@IHps H4 _ H3 _ D y) as j.
  simpl in j.
  rewrite <- Heqyaps in j.
  omega.
  intros.
  symmetry.
  eapply leqSymm.
  
  Focus 2.

  simpl in Heqyvic.
  rewrite <- Heqyv in Heqyvic.
  rewrite <- Heqyvic. simpl.
  intros.
  inversion H; subst.
  pose (@IHps H5 _ H4 _ D y) as j.
  simpl in j.
  rewrite <- Heqyaps in j.
  apply j. auto.
  
  Focus 2.

  remember (LEQ v (preFindMinHelp a ps)) as vaps; destruct vaps.
  remember (f y v) as yv; destruct yv.
  auto with arith.
  intros.
  simpl in IHps.
  inversion H; subst.
  remember (f y (preFindMinHelp a ps)) as yaps; destruct yaps.
  symmetry.
  eapply leqTransTrue. eauto.
  destruct D as [E [F [G I]]]. 
  replace true with (LEQ y y).
  apply E. auto.
  symmetry. apply leqRefl.
  remember (f y (preFindMinHelp (Node _ v i c) ps)) as yvps; destruct yvps.
  pose (@IHps H5 _ H0 _ D y) as j.
  rewrite <- Heqyvps in j.
  assert (v = preFindMinHelp (Node _ v i c) ps) as T.
  eapply preFindFirst. eauto.
  rewrite <- T in Heqyvps.
  destruct D as [E [F [G I]]].
  symmetry.
  replace true with (LEQ y y).
  apply E. auto.
  symmetry. apply leqRefl.
  replace v with (root (Node _ v i c)) by auto.
  eapply minHeapCount. auto. eauto. omega.
  remember (f y (preFindMinHelp a ps)) as yaps; destruct yaps;
    remember (f y v) as yv; destruct yv.
  auto with arith.
  simpl in Heqyvic. rewrite <- Heqyv in Heqyvic.
  rewrite <- Heqyvic. auto with arith.
  intros.
  symmetry.
  eapply leqTransTrue.
  eapply leqSymm. eauto.
  replace v with (root (Node _ v i c)) by auto.
  symmetry.
  eapply minHeapCount. auto. eauto. omega.
  intros.
  symmetry.
  eapply leqTransTrue.
  eapply leqSymm. eauto.
  replace v with (root (Node _ v i c)) by auto.
  symmetry.
  eapply minHeapCount. auto. eauto. omega.
  
  destruct D as [E [F [G I]]].
  replace false with (LEQ v (preFindMinHelp a ps)).
  apply E.
  rewrite G. auto.
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
  intros p.
  destruct p.
  destruct p.
  destruct x.
  simpl.
  intros.
  destruct same.
  simpl. auto.
  simpl.
  intros.
  destruct same.
  eapply findMinHelpCount.
  inversion a; subst. auto.
  inversion a; subst. auto.
Qed.

Lemma linkCount :
  forall f x p q,
    countTree f x (link p q) 
    = countTree f x p
    + countTree f x q.
Proof.
  intros; unfold link.
  destruct p; destruct q.
  remember (LEQ a a0) as aa0; destruct aa0; simpl; auto.
  remember (f x a) as xa; destruct xa;
    remember (f x a0) as xa0; destruct xa0;
      simpl; auto; try omega.
  remember (f x a) as xa; destruct xa;
    remember (f x a0) as xa0; destruct xa0;
      simpl; auto; try omega.
Qed.

Lemma insCount :
  forall f x p ps,
    preCount f x (ins p ps) 
    = countTree f x p 
    + preCount f x ps.
Proof.
  intros f x p ps.
  generalize dependent p.
  induction ps; simpl; auto.
  intros.
  remember (nat_compare (rank p) (rank a)) as pa; destruct pa.
  rewrite IHps.
  rewrite linkCount. unfold preCount; simpl; omega.
  unfold preCount; simpl; omega.
  rewrite IHps.
  rewrite linkCount. unfold preCount; simpl; omega.
Qed.

Lemma meldUniqCount :
  forall p q x f,
    preCount f x (meldUniq (p,q)) 
    = preCount f x p 
    + preCount f x q.
Proof.
  pose (fun (xy:preQ*preQ) r =>
    let (x,y) := xy in
      forall z f,
        preCount f z r
        = preCount f z x 
        + preCount f z y) as P.
  assert (forall xy, P xy (meldUniq xy)) as ans.
  eapply meldUniq_ind; unfold P; clear P; simpl; intros; auto.
  unfold preCount in *; simpl in *.
  rewrite H.
  omega.
  unfold preCount in *; simpl in *.
  rewrite H.
  omega.
  rewrite insCount.
  rewrite H.
  rewrite linkCount.
  unfold preCount; simpl; omega.
  unfold P in ans; clear P; intros.
  eapply (ans (p,q)).
Qed.

Lemma insNotNil :
  forall x xs,
    ins x xs <> [].
Proof.
  unfold not; intros; generalize dependent x; induction xs; intros.
  simpl in H. inversion H.
  simpl in H.
  remember (nat_compare (rank x) (rank a)) as xa; destruct xa.
  eapply IHxs. eauto.
  inversion H.
  eapply IHxs. eauto.
Qed.
  
Lemma preMeldCount :
  forall f p q x,
    preCount f x (preMeld p q) 
    = preCount f x p
    + preCount f x q.
Proof.
  intros.
  unfold preMeld.
  unfold uniqify.
  destruct p; destruct q; simpl.
  rewrite meldUniq_equation; auto.
  rewrite meldUniq_equation. rewrite insCount; unfold preCount; simpl.
  auto.
  rewrite meldUniq_equation.
  remember (ins p p0) as px; destruct px.
  assert False as ff.
  eapply insNotNil. eauto.
  inversion ff.
  rewrite Heqpx.
  rewrite insCount.
  unfold preCount; simpl; auto.
  rewrite meldUniqCount.
  rewrite insCount.
  rewrite insCount.
  unfold preCount; simpl; omega.
Qed.

Lemma meldCount :
  forall same inp inq x,
    count same x (meld inp inq) = count same x inp
                                + count same x inq.
Proof.
  intros; destruct same; destruct inp; destruct inq;
    unfold count; unfold meld; simpl.
  apply preMeldCount.
Qed.

Lemma getFindMin :
  forall xs x y z, 
    (y,z) = getMin x xs ->
    root y = preFindMinHelp x xs.
Proof.
  induction xs; simpl; intros.
  inversion H; subst; auto.
  remember (getMin a xs) as gaxs; destruct gaxs.
  assert (root p = preFindMinHelp a xs). eapply IHxs. eauto.
  rewrite <- H0.
  remember (LEQ (root x) (root p)) as xp; destruct xp.
  inversion H; auto.
  inversion H; auto.
Qed.

Lemma getMinCount :
  forall xs x y z,
    (y,z) = getMin x xs ->
    forall f a,
      countTree f a x + preCount f a xs =
      countTree f a y + preCount f a z.
Proof.
  induction xs; simpl; intros.
  inversion_clear H; subst. auto.
  remember (getMin a xs) as tts; destruct tts.
  remember (LEQ (root x) (root p)) as xp; destruct xp;
    inversion_clear H; subst; unfold preCount; simpl.
  auto.
  pose (IHxs _ _ _ Heqtts) as I.
  unfold preCount in I.
  rewrite I. omega.
Qed.
  
Fixpoint countList (f:A -> A -> bool) x l :=
  match l with
    | [] => 0
    | y::ys =>
      if f x y
        then S (countList f x ys)
        else countList f x ys
  end.

Lemma splitCount :
  forall c, 
    All rankP c ->
    forall a b d e, 
      (d,e) = split a b c ->
        forall f x,
          preCount f x d +
          countList f x e =
          preCount f x a +
          countList f x b +
          preCount f x c.
Proof.
  induction c; simpl; intros.
  inversion_clear H0; subst.
  unfold preCount at 3.
  simpl. auto.
  destruct a; simpl in H0.
  destruct n.
  inversion_clear H; subst.
  pose (IHc H2 _ _ _ _ H0) as I.
  rewrite I.
  unfold rankP in H1.
  simpl in H1.
  inversion H1; subst.
  simpl in H1.
  unfold countList at 1.
  fold (countList f x b).
  unfold preCount at 4.
  simpl.
  remember (f x a) as xa; destruct xa; try omega.
  unfold preCount at 2. omega.
  unfold preCount at 2. omega.
  inversion_clear H; subst.
  pose (IHc H2 _ _ _ _ H0) as I.
  rewrite I.
  unfold preCount at 1.
  simpl.
  unfold preCount at 3.
  simpl.
  remember (f x a) as xa; destruct xa; try omega.
  unfold preCount; simpl; omega.
  unfold preCount; simpl; omega.
Qed.

Lemma foldInsertCount :
  forall l f x q,
    preCount f x (fold_right preInsert q l)
    = preCount f x q
    + countList f x l.
Proof.
  induction l; intros; simpl.
  auto.
  rewrite preInsertCount.
  simpl.
  rewrite IHl.
  remember (f x a) as fxa; destruct fxa; auto.
Qed.

Lemma rankChildren :
  forall n v c,
    rankP (Node _ v n c) ->
    All rankP c.
Proof.
  induction n; unfold rankP; simpl; intros.
  inversion_clear H; subst; simpl; auto.
  inversion H; subst.
  apply Cons. destruct y. simpl.
  inversion H; subst.
  assert (n0 = n). eapply rankDestruct. eauto.
  subst. auto.
  assert (n0 = n). eapply rankDestruct. eauto.
  subst. auto.
  auto.
  fold rankP.
  eapply IHn.
  eauto.
  fold rankP.
  destruct x; destruct z.
  assert (n0 = n). eapply rankDestruct. eauto.
  subst. 
  assert (n1 = n). eapply rankDestruct. eauto.
  subst. 
  repeat (apply Cons); unfold rankP; simpl; auto.
  inversion H; subst.
  apply Cons. auto.
  eapply IHn; auto. eauto.
  repeat (apply Cons).
  auto.
  destruct y.
  assert (n0 = n). eapply rankDestruct. eauto.
  subst. auto.
  auto.
  apply Cons. auto.
  apply Cons. destruct y.
  assert (n0 = n). eapply rankDestruct. eauto.
  subst. auto.
  eapply IHn. eauto.
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
  intros p.
  destruct p.
  unfold findMin; simpl.
  destruct x; unfold preFindMin.
  simpl; intros.
  unfold count. destruct same; simpl.
  unfold preCount; simpl. auto.
  remember (getMin p0 x) as pox; destruct pox.  
  destruct p1; simpl.
  remember (split [] [] l0) as sl; destruct sl.
  unfold deleteMin.
  unfold preDeleteMin. simpl.
  erewrite <- getFindMin. Focus 2. eauto.
  simpl. unfold count; simpl.
  intros.
  destruct same.
  unfold check; simpl.
  unfold preCount. simpl.
  rewrite <- Heqpox.
  rewrite <- Heqsl.
  
  simpl.
  pose foldInsertCount as fic.
  unfold preCount in fic.
  rewrite fic.
  pose preMeldCount as pmc.
  unfold preCount in pmc.
  rewrite pmc.
  remember (x0 y a) as ya; destruct ya.
  pose (getMinCount _ _ Heqpox) as gmc. 
  unfold preCount in gmc.
  rewrite gmc. 
  pose Heqpox as oth.
  apply getMinTRank in oth.
  assert (All rankP l0) as J.
  eapply rankChildren.
  eapply getMinTRank. Focus 2. eauto.
  destruct p; auto.
  pose (splitCount J _ _ Heqsl) as sc.
  simpl in sc.
  unfold countTree at 1.
  fold countTree. simpl.
  unfold preCount in sc.
  rewrite <- sc.
  rewrite <- Heqya. omega.
  destruct p; auto.
  pose (getMinCount _ _ Heqpox) as gmc. 
  unfold preCount in gmc.
  rewrite gmc. 
  pose Heqpox as oth.
  apply getMinTRank in oth.
  assert (All rankP l0) as J.
  eapply rankChildren.
  eapply getMinTRank. Focus 2. eauto.
  destruct p; auto.
  pose (splitCount J _ _ Heqsl) as sc.
  simpl in sc.
  unfold countTree at 1.
  fold countTree. simpl.
  unfold preCount in sc.
  rewrite <- sc.
  rewrite <- Heqya. omega.
  destruct p; auto.
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
  intros p.
  destruct p.
  unfold findMin.
  simpl. fold (extractMin (exist _ x p)).
  destruct x; unfold preFindMin.
  unfold extractMin. simpl. auto.
  remember (extractMin (exist PQP (p0::x) p)) as pppp.
  destruct pppp.
  destruct p1.
  exists p1.
  split.
  destruct p1.
  eapply extractMin_equality in Heqpppp.
  f_equal.
  unfold preExtractMin in Heqpppp.
  remember (getMin p0 x) as pox; destruct pox. 
  destruct p2.
  apply getFindMin in Heqpox.
  simpl in Heqpox.
  rewrite <- Heqpox. 
  inversion Heqpppp.
  auto.
  destruct p1.
  eapply extractMin_equality in Heqpppp.
  unfold count; simpl.
  intros.
  destruct same.
  unfold preExtractMin in Heqpppp.
  remember (getMin p0 x) as pox; destruct pox.
  destruct p2.
  inversion Heqpppp. 
  auto.
  apply extractMin_none in Heqpppp.
  unfold extractMin in Heqpppp.
  unfold preExtractMin in Heqpppp.
  simpl in Heqpppp.
  inversion Heqpppp.
Qed.

End SBHeapVerify.