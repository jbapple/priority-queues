Set Implicit Arguments.
Require Export PQSig.
Require Export skewBinaryHeap.

Module SkewBinHeapVerify (OO:Order) <: PQVerify.

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

Fixpoint size l :=
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
    (forall a n, P (Node a n [])) ->
    (forall a n x l, P (Node a n l) -> P x -> P (Node a n (x::l))) ->
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

Definition count (same:DER LEQ) x (l:PQ) :=
  match same, l with
    | exist f _, exist v _ => fold_right plus 0 (map (countTree f x) v)
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
  simpl.
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
  simpl in *.
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
    v = preFindMinHelp (Node v i c) ps.
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
  replace a with (root (Node a n l)) by auto.
  eapply minHeapCount. auto. eauto.
  simpl. rewrite <- Heqya. omega.
  destruct p as [v i c]; simpl.
  remember (countTree f y (Node v i c)) as yvic. destruct yvic.
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
  remember (f y (preFindMinHelp (Node v i c) ps)) as yvps; destruct yvps.
  pose (@IHps H5 _ H0 _ D y) as j.
  rewrite <- Heqyvps in j.
  assert (v = preFindMinHelp (Node v i c) ps) as T.
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
  remember (f y (preFindMinHelp (Node v i c) ps)) as yvps; destruct yvps.
  pose (@IHps H5 _ H0 _ D y) as j.
  rewrite <- Heqyvps in j.
  assert (v = preFindMinHelp (Node v i c) ps) as T.
  eapply preFindFirst. eauto.
  rewrite <- T in Heqyvps.
  destruct D as [E [F [G I]]].
  symmetry.
  replace true with (LEQ y y).
  apply E. auto.
  symmetry. apply leqRefl.
  replace v with (root (Node v i c)) by auto.
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
  replace v with (root (Node v i c)) by auto.
  symmetry.
  eapply minHeapCount. auto. eauto. omega.
  intros.
  symmetry.
  eapply leqTransTrue.
  eapply leqSymm. eauto.
  replace v with (root (Node v i c)) by auto.
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

End SkewBinHeapVerify.