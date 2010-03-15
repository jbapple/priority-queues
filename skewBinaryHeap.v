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

Program Fixpoint meldUniqP (xy:preQ * preQ) {measure (combLen xy)} : preQ :=
  match xy with
    | ([],y) => y
    | (x,[]) => x
    | (p::ps,q::qs) => 
      match nat_compare (rank p) (rank q) with
        | Lt => p :: meldUniqP (ps, q::qs)
        | Gt => q :: meldUniqP (p::ps, qs)
        | Eq => ins (link p q) (meldUniqP (ps,qs))
      end
  end.
Next Obligation.
unfold combLen; simpl; omega.
Qed.
Next Obligation.
unfold combLen; simpl; omega.
Qed.

Check meldUniq_equation.
(*
Functional Scheme meldUniqP_ind := Induction for meldUniqP Sort Prop.
*)


Lemma meldUniqP_equation :
  forall xy : preQ * preQ,
       meldUniqP xy =
       (let (x, y) := xy in
        match x with
        | nil => y
        | p :: ps =>
            match y with
            | nil => x
            | q :: qs =>
                match nat_compare (rank p) (rank q) with
                | Eq => ins (link p q) (meldUniqP (ps, qs))
                | Lt => p :: meldUniqP (ps, q :: qs)
                | Gt => q :: meldUniqP (p :: ps, qs)
                end
            end
        end).
Proof.
  intros.
  destruct xy as [x y].
  unfold meldUniqP at 1.
Admitted.

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

Lemma rankDestruct :
  forall v n c m,
    rankN (Node v n c) m ->
    n = m.
Proof.
  intros v n c m r.
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

Fixpoint skewSize x :=
  match x with
    | Node v _ r => S (fold_right plus 0 (map skewSize r))
  end.

Lemma skewSizePos :
  forall x, skewSize x > 0.
Proof.
  intros x; destruct x; simpl; omega.
Qed.


(*
Inductive simpleLink : preT -> nat -> Prop :=
  | simple : forall v i ys y n,
             rankP (Node v i ys) n ->
             rankP y n ->
             simpleLink (Node v i (y::ys)) (S n)
with typeAlink : preT -> nat -> Prop
  | typeA : forall x y z n,
            rankP x n ->
            rankP z n ->
            


Definition simpleLink 
  (x:preT) 
  (fr:forall y, skewSize y < skewSize x -> option nat) 
  : option nat.
refine (
fun (x:preT) 
     =>
  match x return (forall y, skewSize y < skewSize x -> option nat) -> option nat with
    | Node v i c =>
      match c return (forall y, skewSize y < skewSize (Node v i c) -> option nat) -> option nat with
        | [] => fun _ => None
        | y::ys => fun fr =>
          match @fr y _, @fr (Node v i ys) _ with
            | Some j, Some k => 
              if beq_nat j k
                then Some (S j)
                else None
            | _,_ => None
          end
      end
  end).
Lemma simpleLink1 : forall v i y ys, 
  (skewSize y < skewSize (Node v i (y :: ys))).
Proof.
  intros; simpl; omega.
Qed.
apply simpleLink1.
Lemma simpleLink2 : forall v i y ys, 
  (skewSize (Node v i ys) < skewSize (Node v i (y :: ys))).
Proof.
  intros.
  simpl. 
  assert (skewSize y > 0) as ssy. apply skewSizePos.
  omega.
Qed.
apply simpleLink2.
Defined.

Print simpleLink.

(*
Program Definition simpleLink 
  (x:preT) 
  (fr:forall y, skewSize y < skewSize x -> option nat) 
  : option nat :=
  match x with
    | Node v i c =>
      match c with
        | [] => None
        | y::ys =>
          match @fr y _, @fr (Node v i ys) _ with
            | Some j, Some k => 
              if beq_nat j k
                then Some (S j)
                else None
            | _,_ => None
          end
      end
  end.
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl. 
  assert (skewSize y > 0) as ssy. apply skewSizePos.
  omega.
Qed.
*)
Program Definition skewAlink
  (x:preT) 
  (fr:forall y, skewSize y < skewSize x -> option nat) 
  : option nat :=
  match x with
    | Node v i c =>
      match c with
        | [y; z] =>
          match @fr y _, @fr z _ with
            | Some j, Some k =>
              if beq_nat j k
                then Some (S j)
                else None
            | _,_ => None
          end
        | _ => None
      end
  end.
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl. omega.
Qed.

Program Definition skewBlink
  (x:preT) 
  (fr:forall y, skewSize y < skewSize x -> option nat) 
  : option nat :=
  match x with
    | Node v i c =>
      match c with
        | y::ys =>
          match @fr y _ with
            | Some 0 => simpleLink (Node v i ys) (fun z p => @fr z _)
            | _ => None
          end
        | _ => None
      end
  end.
Next Obligation.
  simpl; omega.
Qed.
Next Obligation.
  simpl. omega.
Qed.

(*
Function findRank (x:preT) {measure skewSize x} : option nat :=
  match x with
    | Node v i c =>
      match c with
        | [] => Some 0
        | _ => let fr := (fun y _ => findRank y) in
          match simpleLink x fr, 
                skewAlink x fr, 
                skewBlink x fr with
            | Some k,_,_ => Some k
            | _,Some k,_ => Some k
            | _,_,Some k => Some k
            | None,None,None => None
          end
      end
  end.
*)

Program Fixpoint findRank (x:preT) {measure (skewSize x)} : option nat :=
  match x with
    | Node v i c =>
      match c with
        | [] => Some 0
        | _ => 
          match simpleLink x findRank, 
                skewAlink x findRank, 
                skewBlink x findRank with
            | Some k,_,_ => Some k
            | _,Some k,_ => Some k
            | _,_,Some k => Some k
            | None,None,None => None
          end
      end
  end.
Next Obligation.
  split; unfold not; intros d e f J.
  destruct J as [J [K L]].
  inversion J.
  destruct J as [J [K L]].
  inversion K.
Qed.

(*
Functional Scheme findRankEq := Induction for findRank Sort Prop.
*)

Lemma findRankEq : forall x,
  findRank x = 
  match x with
    | Node v i c =>
      match c with
        | [] => Some 0
        | _ => let fr := (fun y _ => findRank y) in
          match simpleLink x fr, 
                skewAlink x fr, 
                skewBlink x fr with
            | Some k,_,_ => Some k
            | _,Some k,_ => Some k
            | _,_,Some k => Some k
            | None,None,None => None
          end
      end
  end.
Proof.
  intros x.
  pose (skewSize x) as sx.
  fold sx.
  remember (skewSize x) as rsx in |- *.
  unfold sx. 
  clear sx.
  generalize dependent x.
  apply lt_wf_ind with (n := rsx).

  intros s IH.
  intros x sx.
  destruct x as [v i [|p l]].
  compute; auto.
  unfold findRank at 1.
  Print WfExtensionality.
  rewrite WfExtensionality.fix_sub_eq_ext.
  fold_sub (.
  simpl proj1_sig.
  simpl.
  rewrite <- sx in *.
  simpl.


  induction rsx.

  intros x sx.
  destruct x; simpl in sx. 
  assert False as f.
  
  unfold skewSize in sx.


  dependent rewrite Heqrsx.
  generalize dependent rsx.
  generalize dependent Heqrsx.
  rewrite Heqrsx.
  generalize x.
  


  dependent induction x.
  induction
  induction x.
  


  pose (skewSize x) as sx.
  fold sx.
  generalize dependent sx.
  remember (skewSize x) as rsx.  induction rsx.
  unfold sx.
  generalize dependent x.
  induction x.

    generalize dependent x.



  compute; auto.
  unfold findRank.
  WfExtensionality.unfold_sub findRank (Node v i (p :: l)).
  reflexivity.
  unfold 
  reflexivity.

  intros x; unfold findRank at 1.
  simpl; unfold Fix_sub.
  erewrite F_unfold.

  destruct c as [|p l].
  reflexivity.

*)  
  


Inductive prenomial a :=
  single : nat -> a -> prenomial a
| multiple : nat -> a -> list (prenomial a) -> prenomial a.

Fixpoint size a (x:prenomial a) :=
  match x with
    | single _ _ => 1
    | multiple _ _ xs => S (fold_right plus 0 (map (@size a) xs))
  end.

Lemma preSizePos : 
  forall a (x:prenomial a),
    size x > 0.
Proof.
  intros; destruct x; simpl; auto with arith.
Qed.

Program Fixpoint rank a (x:prenomial a) {measure (size x)} : option nat :=
  match x with
    | single _ _ => Some 0
    | multiple _ v xs => 
      match xs with
        | nil => None
        | y::nil => match rank y with
                      | Some 0 => Some 1
                      | _ => None
                    end
        | y::z::zs => 
          match rank y with
            | Some (S k) =>
              match rank (multiple 0 v (z::zs)) with
                | Some (S j) => 
                  if beq_nat k j 
                    then Some (S (S k))
                    else None
                | _ => None
              end
            | _ => None
          end
      end
  end.
Next Obligation.
  Print size.
  simpl. auto with arith.
Qed.
Next Obligation.
  simpl.
  auto with arith.
Qed.
Next Obligation.
  simpl.
  assert (size y > 0). apply preSizePos.
  omega.
Qed.

Fixpoint maxHeapOrderWithHelp 
  a (maxim:a) (ord:a -> a -> comparison) (x:prenomial a) : bool :=
  match x with
    | single _ y => match ord maxim y with
                    | Lt => false
                    | _ => true
                  end
    | multiple _ y ys =>
      (match ord maxim y with
        | Lt => false
        | _ => true
      end
      &&
      fold_right andb true (map (maxHeapOrderWithHelp y ord) ys))%bool
  end.

Definition maxHeapOrderWith 
  a (ord:a -> a -> comparison) (x:prenomial a) : bool :=
  match x with
    | single _ _ => true
    | multiple _ y ys =>
      fold_right andb true (map (maxHeapOrderWithHelp y ord) ys)
  end.

Definition nominalRank a (x:prenomial a) :=
  match x with
    | single k _ => k
    | multiple k _ _ => k
  end.

Definition binomTree a ord := 
  {x : prenomial a 
    | rank x = Some (nominalRank x) 
    /\ maxHeapOrderWith ord x = true}.

Definition preQ a := list (prenomial a).

Fixpoint isbinQWithHelp a m ord (xs:preQ a) :=
  match xs with
    | [] => true
    | y::ys =>
      (maxHeapOrderWith ord y &&
        match nominalRank y, rank y with
          | _,None => false
          | k,Some n => 
            beq_nat k n &&
            match nat_compare m n with
              | Lt => isbinQWithHelp n ord ys
              | _ => false
            end
        end)%bool
  end.

Definition isbinQWith a ord (xs:preQ a) :=
  match xs with
    | [] => true
    | y::ys =>
      (maxHeapOrderWith ord y &&
        match nominalRank y, rank y with
          | _,None => false
          | k,Some n => beq_nat k n && isbinQWithHelp n ord ys
        end)%bool
  end.

Definition findTMax a (xs:prenomial a) :=
  match xs with
    | single _ v => v
    | multiple _ v _ => v
  end.

Definition maxWith a ord (x:a) y :=
  match ord x y with
    | Lt => y
    | _ => x
  end.

Fixpoint findQMaxWith a ord (xs:preQ a) :=
  match xs with
    | [] => None
    | y::ys => Some
      (let p := findTMax y in
        match findQMaxWith ord ys with
          | None => p
          | Some q => maxWith ord p q
        end)
  end.

Fixpoint join a ord (x:prenomial a) (y:prenomial a) :=
  match ord (findTMax x) (findTMax y) with
    | Lt => match y with
              | single k y => multiple (S k) y [x]
              | multiple k y ys => multiple (S k) y (x::ys)
            end
    | _ => match x with
              | single k x => multiple (S k) x [y]
              | multiple k x xs => multiple (S k) x (y::xs)
            end
    end.

Fixpoint cascade a ord (x:prenomial a) (xs:preQ a) :=
  match xs with
    | [] => [x]
    | y::ys =>
      if beq_nat (nominalRank x) (nominalRank y)
        then cascade ord (join ord x y) ys
        else x::y::ys
  end.

Fixpoint insertWith a ord x (xs:preQ a) :=
  match xs with
    | [] => [single 0 x]
    | y::ys =>
      match nominalRank y with
        | 0 => cascade ord (join ord (single 0 x) y) ys
        | S _ => (single 0 x)::xs
      end
  end.

Lemma insertKeeps :
  forall a ord x (xs:preQ a),
    isbinQWith ord xs = true ->
    isbinQWith ord (insertWith ord x xs) = true.
Proof.
  intros a ord x xs;
    generalize dependent ord;
      generalize dependent x.
  induction xs; intros.

  simpl in *; reflexivity.

  rename a0 into b.
  unfold insertWith.
  destruct b.
  rename a0 into b.
  simpl.
  destruct n.
  remember (ord x b) as oxb.
  destruct oxb.
  
  rewrite <- IHxs with (ord := ord) (.
  

  simpl in *.
  

  sdfsdf
  