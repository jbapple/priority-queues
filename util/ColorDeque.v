Set Implicit Arguments.

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

Variable size : forall t, list t -> N.
Variable sizeNat : forall t (x:list t), fromNat (length x) = size x.


(*
Definition Buffer t := list t.

Definition bufferSize t (b:list t) := @length _ b < 6.
*)

Inductive Buffer t :=
  Zero 
| One : t -> Buffer t
| Two : t -> t -> Buffer t
| Three : t -> t -> t -> Buffer t
| Four : t -> t -> t -> t -> Buffer t
| Five : t -> t -> t -> t -> t -> Buffer t.

Set Maximal Implicit Insertion.
Implicit Arguments Zero [t].
Unset Maximal Implicit Insertion.

(*
Inductive SimpleDeque t :=
  Empty : SimpleDeque t
| Full : Buffer t ->
         SimpleDeque (prod t t) ->
         Buffer t ->
         SimpleDeque t.
*)

(*
Inductive LeafTree t :=
  One : t -> LeafTree t
| More : LeafTree (prod t t) -> LeafTree t.

Definition Elem := LeafTree A.
*)

Inductive SubStack s : Type -> Type :=
  Single : Buffer s -> Buffer s -> SubStack s s
| Multiple : forall t,
             Buffer s -> Buffer s -> 
             SubStack (prod s s) t -> 
             SubStack s t.

Inductive Deque s :=
  Empty : Deque s
| Full : forall t,
         SubStack s t ->
         Deque (prod t t) ->
         Deque s.

Set Maximal Implicit Insertion.
Implicit Arguments Empty [s].
Unset Maximal Implicit Insertion.

Definition toListBufferC t (x:Buffer t) r :=
  match x with
    | Zero => r
    | One a => a::r
    | Two a b => a::b::r
    | Three a b c => a::b::c::r
    | Four a b c d => a::b::c::d::r
    | Five a b c d e => a::b::c::d::e::r
  end.

(*
Definition toListPairBufferC t (x:Buffer (prod t t)) r :=
  match x with
    | Zero => r
    | One (a,b) => a::b::r
    | Two (a,b) (c,d) => a::b::c::d::r
    | Three (a,b) (c,d) (e,f) => a::b::c::d::e::f::r
    | Four (a,b) (c,d) (e,f) (g,h) => a::b::c::d::e::f::g::h::r
    | Five (a,b) (c,d) (e,f) (g,h) (i,j) => a::b::c::d::e::f::g::h::i::j::r
  end.
*)

Fixpoint unzipMix t (x:list (prod t t)) r :=
  match x with
    | nil => r
    | (a,b)::tyl => a::b::(unzipMix tyl r)
  end.

(*
Require Import Program.
Require Import Coq.Logic.JMeq.
*)
(* Error: Library Coq.Logic.JMeq has to be required first. *)
(*
Program Fixpoint toListSubStack t s (x:SubStack t s) (r:list s -> list s) : list t :=
  match x with
    | Single a b => toListBufferC a (r (toListBufferC b nil))
    | Multiple _ a b tyl =>
      toListBufferC a 
      (unzipMix (toListSubStack tyl r) 
        (toListBufferC b nil))
  end.
*)

Fixpoint toListSubStack t s (x:SubStack t s) : 
  (list s -> list s) -> list t :=
  match x with
    | Single a b => fun r => toListBufferC a (r (toListBufferC b nil))
    | Multiple _ a b tyl => fun r => 
      toListBufferC a 
      (unzipMix (toListSubStack tyl r) 
        (toListBufferC b nil))
  end.

Fixpoint toListDeque t (x:Deque t) : list t :=
  match x with
    | Empty => nil
    | Full u hed tyl =>
      toListSubStack hed (unzipMix (toListDeque tyl))
  end. 

Inductive Color :=
  Red
| Yellow
| Green.

Definition bufferColor t (b:Buffer t) :=
  match b with
    | Two _ _ => Green
    | Three _ _ _ => Green
    | One _ => Yellow
    | Four _ _ _ _ => Yellow
    | _ => Red
  end.
Hint Unfold bufferColor.
Hint Unfold length.

Definition minColor a b :=
  match a with
    | Red => Red
    | Yellow => 
      match b with
        | Red => Red
        | _ => Yellow
      end
    | _ => b
  end.

Definition bottomSubStackColor s t (x:SubStack s t) :=
  match x with
    | Single pre suf =>
      match pre with
        | Zero => bufferColor suf
        | _ => 
          match suf with
            | Zero => bufferColor pre
            | _ => minColor (bufferColor pre) (bufferColor suf)
          end
      end
    | Multiple _ pre suf _ => minColor (bufferColor pre) (bufferColor suf)
  end.

Definition topSubStackColor s t (x:SubStack s t) :=
  match x with
    | Single pre suf =>
        minColor (bufferColor pre) (bufferColor suf)
    | Multiple _ pre suf _ => 
        minColor (bufferColor pre) (bufferColor suf)
  end.

Definition dequeColor t (d:Deque t) :=
  match d with
    | Empty => None
    | Full _ hed tyl => Some (
      match tyl with
        | Empty => bottomSubStackColor hed
        | _ => topSubStackColor hed
      end)
  end.

Fixpoint allSubStackYellow (f:forall s t, SubStack s t -> Color) 
  s t (x:SubStack s t) :=
  f _ _ x = Yellow /\
  match x with
    | Single _ _ => True
    | Multiple _ _ _ r => allSubStackYellow f r
  end.

Definition tailStackColor (f: forall s t, SubStack s t -> Color)
  s t (x:SubStack s t) :=
  match x with
    | Single _ _ => None
    | Multiple _ _ _ r => Some (f _ _ r)
  end.

Definition yellowOrNothing x :=
  match x with
    | None => True
    | Some c =>
      match c with
        | Yellow => True
        | _ => False
      end
  end.

Definition tailStackProp (f: forall s t, SubStack s t -> Prop)
  s t (x:SubStack s t) :=
  match x with
    | Single _ _ => True
    | Multiple _ _ _ r => f _ _ r
  end.

Fixpoint restWellStacked s (x:Deque s) :=
  match x with
    | Empty => True
    | Full _ hed tyl =>
      match tyl with
        | Empty => 
          bottomSubStackColor hed <> Yellow
          /\
          tailStackProp (allSubStackYellow bottomSubStackColor) hed
        | _ =>
          topSubStackColor hed <> Yellow
          /\
          tailStackProp (allSubStackYellow topSubStackColor) hed
          /\
          restWellStacked tyl
      end
  end.

Definition wellStacked s (x:Deque s) :=
  match x with
    | Empty => True
    | Full _ hed tyl =>
      match tyl with
        | Empty => tailStackProp (allSubStackYellow bottomSubStackColor) hed
        | _ => 
          tailStackProp (allSubStackYellow topSubStackColor) hed
          /\
          restWellStacked tyl
      end
  end.

Fixpoint topDequeColors s (x:Deque s) :=
  match x with
    | Empty => nil
    | Full _ hed tyl =>
      match tyl with
        | Empty => (bottomSubStackColor hed) :: nil
        | _ => (topSubStackColor hed) :: (topDequeColors tyl)
      end
  end.

Fixpoint semiRegularColorListGreenBeforeRed x :=
  match x with
    | nil => True
    | y::ys =>
      match y with
        | Red => False
        | Green => semiRegularColorList ys
        | Yellow => semiRegularColorListGreenBeforeRed ys
      end
  end
with semiRegularColorList x :=
  match x with
    | nil => True
    | y::ys =>
      match y with
        | Red => semiRegularColorListGreenBeforeRed ys
        | _ => semiRegularColorList ys
      end
  end.

Fixpoint nonEmptySubStack t s (x:SubStack t s) :=
  match x with
    | Single pre suf => 
      match pre, suf with
        | Zero,Zero => False
        | _,_ => True
      end
    | Multiple _ pre suf tyl =>
        (match pre, suf with
           | Zero,Zero => False
           | _,_ => True
         end)
        /\
        nonEmptySubStack tyl
  end.

(* Full deques are not empty *)
Fixpoint fullDequeIs t (d:Deque t) :=
  match d with
    | Empty => True
    | Full _ hed tyl =>
      match tyl with
        | Empty => nonEmptySubStack hed
        | _ =>
          nonEmptySubStack hed 
          /\
          fullDequeIs tyl
      end
  end.

Fixpoint eachBufferSubStack (f: forall a, Buffer a -> Prop) 
  s t (x:SubStack s t) :=
  match x with
    | Single pre suf => f _ pre /\ f _ suf
    | Multiple _ pre suf tyl => f _ pre /\ f _ suf /\ eachBufferSubStack f tyl
  end.

Fixpoint eachSubStackDeque (f:forall s t, SubStack s t -> Prop)
  s (x:Deque s) :=
  match x with
    | Empty => True
    | Full _ hed tyl =>
      f _ _ hed /\ eachSubStackDeque f tyl
  end.

Definition semiRegular s (x:Deque s) :=
  wellStacked x
  /\
  fullDequeIs x
  /\
(*  eachSubStackDeque (eachBufferSubStack bufferSize) x
  /\*)
  semiRegularColorList (topDequeColors x).
Hint Unfold semiRegular.

Fixpoint topNonYellowIsGreen x :=
  match x with
    | nil => True
    | y::ys =>
      match y with
        | Red => False
        | Yellow => topNonYellowIsGreen ys
        | Green => True
      end
  end.

(*
Fixpoint regularColorList x :=
  topNonYellowIsGreen x
  /\
  semiRegularColorList x.
*)

Definition regular s (x:Deque s) :=
  semiRegular x
  /\
  topNonYellowIsGreen (topDequeColors x).
Hint Unfold regular.

Definition restoreBottom t (pre suf:Buffer t) : Deque t :=
  match pre,suf with
    | Zero,Five a b c d e => 
      Full (Single (Two a b) (Three c d e)) Empty
    | One a,Five b c d e f => 
      Full (Single (Three a b c) (Three d e f)) Empty
    | Two a b,Five c d e f g => 
      Full (Single (Three a b c) (Four d e f g)) Empty
    | Three a b c,Five d e f g h => 
      Full (Single (Four a b c d) (Four e f g h)) Empty
    | Four a b c d,Five e f g h i => 
      Full (Multiple (Four a b c d) (Three g h i) 
        (Single Zero (One (e,f)))) Empty
    | Five a b c d e,Five f g h i j => 
      Full (Multiple (Three a b c) (Three h i j) 
        (Single (One (d,e)) (One (f,g)))) Empty
      
    | Five a b c d e, Zero => 
      Full (Single (Two a b) (Three c d e)) Empty
    | Five a b c d e, One f => 
      Full (Single (Three a b c) (Three d e f)) Empty
    | Five a b c d e, Two f g => 
      Full (Single (Three a b c) (Four d e f g)) Empty
    | Five a b c d e, Three f g h => 
      Full (Single (Four a b c d) (Four e f g h)) Empty
    | Five a b c d e, Four f g h i => 
      Full (Multiple (Four a b c d) (Three g h i) 
        (Single Zero (One (e,f)))) Empty
      
    | _,_ => Full (Single pre suf) Empty
  end.

Ltac cutThis x :=
  let xx := fresh 
    in remember x as xx; destruct xx.

Ltac pisp t := try subst;
  unfold bufferColor in *; unfold not; intros; 
    simpl in *; auto; t;
  match goal with
    | [H:Red=Yellow |- _] => inversion H;  pisp t
    | [H:Red=Green |- _] => inversion H;  pisp t
    | [H:Yellow=Green |- _] => inversion H;  pisp t
    | [H:Yellow=Red |- _] => inversion H;  pisp t
    | [H:Green=Red |- _] => inversion H;  pisp t
    | [H:Green=Yellow |- _] => inversion H;  pisp t
    | [ H : true = false |- _] => inversion H;  pisp t
    | [ H : None = Some ?a |- _] => inversion H;  pisp t
    | [ H : Some ?a = None |- _] => inversion H;  pisp t
    | [ H : False |- _] => inversion H;  pisp t

    | [ H : True |- _] => clear H; pisp t
    | [ H : ?a = ?a |- _] => clear H;  pisp t

    | [ H : Some ?a = Some ?b |- _] => inversion_clear H; subst;  pisp t
    | [ |- regular (Full _ _) ] => unfold regular;  pisp t
    | [ H : semiRegular (Full _ _) |- _] => unfold semiRegular in H;  pisp t
    | [ |- semiRegular (Full _ _) ] => unfold semiRegular;  pisp t

    | [H : ?A \/ ?B |- _] => destruct H;  pisp t
    | [ H : _ /\ _ |- _ ] => destruct H;  pisp t
    | [ |- _ /\ _ ] => split;  pisp t

    | [ |- context[
      match ?x with
         | Single _ _ => _
         | Multiple _ _ _ _ => _ 
       end]] => destruct x; pisp t
    | [ |- context
      [match ?x with
         | Zero => _
         | One _ => _ 
         | Two _ _ => _
         | Three _ _ _ => _
         | Four _ _ _ _ => _
         | Five _ _ _ _ _ => _
       end]] => destruct x; pisp t
    | [ H : prod _ _ |- _] => cutThis H; pisp t
(*    | [ |- context
      [let (_,_) := ?x in _]] => destruct x; pisp t *)
    | _ => auto
  end.

Ltac asp := progress pisp auto.

Lemma restoreBottomDoes :
  forall t (pre suf:Buffer t), 
    semiRegular (Full (Single pre suf) Empty) ->
    regular (restoreBottom pre suf).
Proof.
  intros.
  destruct pre; asp.
Qed.
Hint Resolve restoreBottomDoes.

Lemma restoreBottomPreserves :
  forall t (pre suf:Buffer t), 
    let x := (Full (Single pre suf) Empty) in
      semiRegular x ->
      toListDeque (restoreBottom pre suf) = toListDeque x.
Proof.
  intros.
  destruct pre; asp.
Qed.
Hint Resolve restoreBottomPreserves.

Definition restoreOneYellowBottom
  T (p1 s1:Buffer T) (p2 s2:Buffer (prod T T)) : option (Deque T) :=
  match p1,p2,s2,s1 with
    | Zero,Zero,One (a,b),Five c d e f g => 
      Some (Full (Single (Three a b c) (Four d e f g)) Empty)
    | Zero,Zero,Four (a,b) cd ef gh,Five i j k l m => 
      Some (Full 
      (Single (Two a b) (Three k l m))
        (Full (Single (Two cd ef) (Two gh (i,j))) Empty))

    | Zero,One (a,b),Zero,Five c d e f g =>
      Some (Full (Single (Three a b c) (Four d e f g)) Empty)
    | Zero,One (a,b),One (c,d), Five e f g h i =>
      Some (
        Full (Multiple (Four a b c d) (Three g h i) 
          (Single Zero (One (e,f)))) Empty)
    | Zero,One (a,b),Two (c,d) (e,f), Five g h i j k =>
      Some (
        Full (Multiple (Four a b c d) (Three i j k) 
          (Single (One (e,f)) (One (g,h)))) Empty)
    | Zero,One (a,b),Three (c,d) (e,f) (g,h), Five i j k l m =>
      Some (
        Full (Multiple (Four a b c d) (Three k l m) 
          (Single (One (e,f)) (Two (g,h) (i,j)))) Empty)
    | Zero,One (a,b),Four (c,d) (e,f) (g,h) (i,j), Five k l m n o=>
      Some (
        Full (Multiple (Four a b c d) (Three m n o) 
          (Single (One (e,f)) (Three (g,h) (i,j) (k,l)))) Empty)

    | Zero,Two (a,b) (c,d), One (e,f), Five g h i j k =>
      Some (
        Full (Multiple (Four a b c d) (Three i j k) 
          (Single (One (e,f)) (One (g,h)))) Empty)
    | Zero,Two (a,b) (c,d),Four (e,f) (g,h) (i,j) (k,l), Five m n o p q=>
      Some (
        Full (Multiple (Four a b c d) (Three o p q) 
          (Single (One (e,f)) (Four (g,h) (i,j) (k,l) (m,n)))) Empty)

    | Zero,Three (a,b) (c,d) (e,f), One (g,h), Five i j k l m=>
      Some (
        Full (Multiple (Four a b c d) (Three k l m) 
          (Single (One (e,f)) (Two (g,h) (i,j)))) Empty)
    | Zero,Three (a,b) (c,d) (e,f), Four (g,h) (i,j) (k,l) (m,n), Five o p q r s =>
      Some (
        Full (Multiple (Four a b c d) (Three q r s) 
          (Single (Two (e,f) (g,h)) (Four (i,j) (k,l) (m,n) (o,p)))) Empty)

    |_,_,_,_ => None
  end.

Lemma restoreOneYellowBottomDoes :
  forall t (p1 s1:Buffer t) p2 s2,
    semiRegular (Full (Multiple p1 s1 (Single p2 s2)) Empty) ->
    match restoreOneYellowBottom p1 s1 p2 s2 with
      | None => True
      | Some v => regular v
    end.
Proof.
  intros.
  destruct p1; asp.
Qed.

Lemma restoreOneYellowBottomPreserves :
  forall t (p1 s1:Buffer t) p2 s2,
    let x := (Full (Multiple p1 s1 (Single p2 s2)) Empty) in
    semiRegular x ->
    match restoreOneYellowBottom p1 s1 p2 s2 with
      | None => True
      | Some v => toListDeque x = toListDeque v
    end.
Proof.
  intros.
  destruct p1; asp.
Qed.


Lemma restoreBottomPreserves :
  forall t (pre suf:Buffer t), 
    let x := (Full (Single pre suf) Empty) in
      semiRegular x ->
      toListDeque (restoreBottom pre suf) = toListDeque x.
Proof.
  intros.
  destruct pre; asp.
Qed.
Hint Resolve restoreBottomPreserves.


(Four a b c d) (Three g h i) 
        (Single Zero (One (e,f)))) Empty
    | Zero,One a,Zero,Five b c d e f =>
      Full (Single (Three a b c) (Three d e f)) Empty
    | Zero,One a,One b,Five c d e f g =>
      Full (Single (Three a b c) (Four d e f g)) Empty
    | Zero,One a,One b,Five c d e f g =>
      Full (Single (Three a b c) (Four d e f g)) Empty





    | One a,Five b c d e f => 
      Full (Single (Three a b c) (Three d e f)) Empty
    | Two a b,Five c d e f g => 
      Full (Single (Three a b c) (Four d e f g)) Empty
    | Three a b c,Five d e f g h => 
      Full (Single (Four a b c d) (Four e f g h)) Empty
    | Four a b c d,Five e f g h i => 
      Full (Multiple (Four a b c d) (Three g h i) 
        (Single Zero (One (e,f)))) Empty
    | Five a b c d e,Five f g h i j => 
      Full (Multiple (Three a b c) (Three h i j) 
        (Single (One (d,e)) (One (f,g)))) Empty
      
    | Five a b c d e, Zero => 
      Full (Single (Two a b) (Three c d e)) Empty
    | Five a b c d e, One f => 
      Full (Single (Three a b c) (Three d e f)) Empty
    | Five a b c d e, Two f g => 
      Full (Single (Three a b c) (Four d e f g)) Empty
    | Five a b c d e, Three f g h => 
      Full (Single (Four a b c d) (Four e f g h)) Empty
    | Five a b c d e, Four f g h i => 
      Full (Multiple (Four a b c d) (Three g h i) 
        (Single Zero (One (e,f)))) Empty
      
    | _,_ => Full (Single pre suf) Empty
end

Definition restore s (x:Deque s) : option (Deque s) :=
  match x with
    | Empty => Some Empty
    | Full _ y ys =>
      match ys with
        | Empty =>
          match y with
            | Single pre suf => 
              Some (restoreBottom pre suf)
            | Multiple _ pre suf tyl => 
              match tyl with
                | Single p2 s2 => None
                | Multiple _ p2 s2 _ => None
              end 
          end
        | _ => None
      end
  end.

Lemma regEmpty : forall s, regular (@Empty s).
Proof.
  intros.
  unfold regular.
  unfold semiRegular; unfold topNonYellowIsGreen; unfold topDequeColors;
    asp.
Qed.
Hint Resolve regEmpty.

Lemma restoreDoes :
  forall s (x:Deque s), semiRegular x ->
    match restore x with
      | None => True
      | Some v => regular v
    end.
Proof.
  intros.
  destruct x; simpl in *; auto.
  destruct x; simpl in *; auto.
  destruct s0; auto.
  destruct s0; auto.
Qed.
Lemma restorePreserves :
  forall s (x:Deque s), semiRegular x ->
    match restore x with
      | None => True
      | Some v => toListDeque v = toListDeque x
    end.
Proof.
  intros.
  destruct x; simpl in *; auto.
  destruct x; simpl in *; auto.
  destruct s0; auto.
  apply restoreBottomPreserves; auto.
  destruct s0; auto.
Qed.



Definition restore s (x:Deque s) : option (Deque s) :=
  match x with
    | Empty => Some Empty
    | Full _ y ys =>
      match ys with
        | Empty =>
          match bottomSubStackColor y with
            | Green => Some x
            | Yellow => Some x              
            | Red => 
              match y with
                | Single pre suf => 
                  match pre,suf with

                    | Zero,Five a b c d e => 
                      Some (Full (Single (Two a b) (Three c d e)) Empty)
                    | One a,Five b c d e f => 
                      Some (Full (Single (Three a b c) (Three d e f)) Empty)
                    | Two a b,Five c d e f g => 
                      Some (Full (Single (Three a b c) (Four d e f g)) Empty)
                    | Three a b c,Five d e f g h => 
                      Some (Full (Single (Four a b c d) (Four e f g h)) Empty)
                    | Four a b c d,Five e f g h i => 
                      Some (Full (Multiple (Four a b c d) (Three g h i) 
                        (Single Zero (One (e,f)))) Empty)
                    | Five a b c d e,Five f g h i j => 
                      Some (Full (Multiple (Three a b c) (Three h i j) 
                        (Single (One (d,e)) (One (f,g)))) Empty)

                    | Five a b c d e, Zero => 
                      Some (Full (Single (Two a b) (Three c d e)) Empty)
                    | Five a b c d e, One f => 
                      Some (Full (Single (Three a b c) (Three d e f)) Empty)
                    | Five a b c d e, Two f g => 
                      Some (Full (Single (Three a b c) (Four d e f g)) Empty)
                    | Five a b c d e, Three f g h => 
                      Some (Full (Single (Four a b c d) (Four e f g h)) Empty)
                    | Five a b c d e, Four f g h i => 
                      Some (Full (Multiple (Four a b c d) (Three g h i) 
                        (Single Zero (One (e,f)))) Empty)

                    | _,_ => Some x
                  end
                | Multiple _ pre suf tyl => 
                  match pre,suf with
                    | Zero,Five a b c d e => 
                      match tyl with
                        | Single p2 s2 =>
                          match s2 with
                            | Zero => 
                              Some (Full (Multiple Zero (Three c d e) (Single p2 (One (a,b)))) Empty)
                            | _ => None
                          end
                        | _ => None
                      end 
                    | _,_ => None
                  end
(*
                    | One a,Five b c d e f => 
                      Some (Full (Single (Three a b c) (Three d e f)) Empty)
                    | Two a b,Five c d e f g => 
                      Some (Full (Single (Three a b c) (Four d e f g)) Empty)
                    | Three a b c,Five d e f g h => 
                      Some (Full (Single (Four a b c d) (Four e f g h)) Empty)
                    | Four a b c d,Five e f g h i => 
                      Some (Full (Multiple (Four a b c d) (Three g h i) 
                        (Single Zero (One (e,f)))) Empty)
                    | Five a b c d e,Five f g h i j => 
                      Some (Full (Multiple (Three a b c) (Three h i j) 
                        (Single (One (d,e)) (One (f,g)))) Empty)

                    | Five a b c d e, Zero => 
                      Some (Full (Single (Two a b) (Three c d e)) Empty)
                    | Five a b c d e, One f => 
                      Some (Full (Single (Three a b c) (Three d e f)) Empty)
                    | Five a b c d e, Two f g => 
                      Some (Full (Single (Three a b c) (Four d e f g)) Empty)
                    | Five a b c d e, Three f g h => 
                      Some (Full (Single (Four a b c d) (Four e f g h)) Empty)
                    | Five a b c d e, Four f g h i => 
                      Some (Full (Multiple (Four a b c d) (Three g h i) 
                        (Single Zero (One (e,f)))) Empty)

                    | _,_ => Some x

                  match tyl with
                    | Single pre1 suf1 =>
                      match pre1 with
                        | Zero =>
                          match suf1 with
                            | Zero => Some x
                            | _ => None
                          end
                        | _ => None
                      end
                    | _ => None
                  end*)
              end
          end
        | _ => None
      end
  end.

(*
      match topSubStackColor y with
        | Green => x
        | Yellow => restoreRest ys
        | Red =>
*)

Ltac cutThis x :=
  let xx := fresh 
    in remember x as xx; destruct xx.

Ltac pisp t := try subst;
  unfold bufferColor in *; simpl in *; auto; t; 
  match goal with
    | [H:Red=Yellow |- _] => inversion H;  pisp t
    | [H:Red=Green |- _] => inversion H;  pisp t
    | [H:Yellow=Green |- _] => inversion H;  pisp t
    | [H:Yellow=Red |- _] => inversion H;  pisp t
    | [H:Green=Red |- _] => inversion H;  pisp t
    | [H:Green=Yellow |- _] => inversion H;  pisp t
    | [ H : true = false |- _] => inversion H;  pisp t
    | [ H : None = Some ?a |- _] => inversion H;  pisp t
    | [ H : Some ?a = None |- _] => inversion H;  pisp t
    | [ H : False |- _] => inversion H;  pisp t

    | [ H : True |- _] => clear H; pisp t
    | [ H : ?a = ?a |- _] => clear H;  pisp t


    | [ H : Some ?a = Some ?b |- _] => inversion_clear H; subst;  pisp t
    | [ |- regular (Full _ _) ] => unfold regular;  pisp t
    | [ H : semiRegular (Full _ _) |- _] => unfold semiRegular in H;  pisp t
    | [ |- semiRegular (Full _ _) ] => unfold semiRegular;  pisp t
(*
    | [ _ : context[length ?a] |- _] => destruct a; pisp t
*)
    | [H : ?A \/ ?B |- _] => destruct H;  pisp t
    | [ H : _ /\ _ |- _ ] => destruct H;  pisp t
    | [ |- _ /\ _ ] => split;  pisp t

(*
    | [ _ : _ = 
      match ?x with
         | Single _ _ => _
         | Multiple _ _ _ _ => _ 
       end |- _] => cutThis x; pisp t
*)
    | [ |- context[
      match ?x with
         | Single _ _ => _
         | Multiple _ _ _ _ => _ 
       end]] => destruct x; pisp t
    | [ |- context
      [match ?x with
         | Zero => _
         | One _ => _ 
         | Two _ _ => _
         | Three _ _ _ => _
         | Four _ _ _ _ => _
         | Five _ _ _ _ _ => _
       end]] => destruct x; pisp t

(*
    | [ _ : context[bufferColor (?a :: ?b :: ?c :: ?d :: ?e)] |- _]
      => destruct e; pisp t
    | [ _ : context[bufferColor (?a :: ?b :: ?c :: ?e)] |- _]
      => destruct e; pisp t
    | [ _ : context[bufferColor (?a :: ?b :: ?e)] |- _]
      => destruct e; pisp t
(*    | [ _ : context[bufferColor (?a :: ?e)] |- _]
      => destruct e; pisp t*)
*)
    | _ => auto
  end.

Ltac asp := progress pisp auto.

Lemma regEmpty : forall s, regular (@Empty s).
Proof.
  intros.
  unfold regular.
  unfold semiRegular; unfold topNonYellowIsGreen; unfold topDequeColors;
    asp.
Qed.
Hint Resolve regEmpty.


Lemma restoreDoes :
  forall s (x:Deque s), semiRegular x ->
    match restore x with
      | None => True
      | Some v => regular v
    end.
Proof.
  intros.
  destruct x.
  Focus 2.
  simpl.
  destruct x; simpl.
  destruct s0; simpl.
  Focus 2.
  destruct s0.
  destruct b2.
  destruct b0.
  Focus 6.
  destruct b.
  simpl in *.
  unfold regular in *.
  unfold semiRegular in *.
  destruct H. destruct H0.
  split. split.
  simpl in *. asp.
  asp.
  simpl.
  asp.
  split. 
  asp.
  destruct x; asp;
    destruct x; asp.
  Focus 2.
  destruct b1; asp.
Qed.

Lemma restorePreserves :
  forall s (x:Deque s), semiRegular x ->
    match restore x with
      | None => True
      | Some v => toListDeque v = toListDeque x
    end.
Proof.
  intros.
  destruct x; asp;
    destruct x; asp.
Qed.

End Carrier.

Extraction Language Haskell.
Recursive Extraction dequeColor.

Lemma help : 
  forall t (p q:t), proj1 (conj p q) = p.
Proof.
  Print proj1.
  unfold proj1.
  simpl.


         

