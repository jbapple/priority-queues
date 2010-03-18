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

(*
Scheme preT_nest := Induction for preT Sort Prop.
Scheme preT_min := Minimality for preT Sort Prop.
Check preT_nest.
Check preT_min.
*)(*
Scheme preT_nest := Induction for preT Sort Prop
with list_nest := Induction for list Sort Prop.
*)

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



  Parameter findMinCount :
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