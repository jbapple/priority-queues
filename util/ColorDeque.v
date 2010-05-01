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
         Deque t ->
         Deque s.

Set Maximal Implicit Insertion.
Implicit Arguments Empty [s].
Unset Maximal Implicit Insertion.

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
        \/
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
          \/
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
                | Multiple _ pre suf tyl => None
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

Ltac pisp t := 
  unfold bufferColor in *; simpl in *; t;
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H; pisp t
    | [ |- _ /\ _ ] => split; pisp t
    | [ H : true = false |- _] => inversion H; pisp t
    | [ H : None = Some ?a |- _] => inversion H; pisp t
    | [ H : Some ?a = None |- _] => inversion H; pisp t
    | [ H : False |- _] => inversion H; pisp t
    | [ H : ?a = ?a |- _] => clear H; pisp t
    | [ H : Some ?a = Some ?b |- _] => inversion_clear H; subst; pisp t
    | [ |- regular (Full _ _) ] => unfold regular; pisp t
    | [ H : semiRegular (Full _ _) |- _] => unfold semiRegular in H; pisp t
    | [ |- semiRegular (Full _ _) ] => unfold semiRegular; pisp t
    | [ _ : context[length ?a] |- _] => destruct a; pisp t
    | [ _ : context
      [match ?x with
         | Zero => _
         | One _ => _ 
         | Two _ _ => _
         | Three _ _ _ => _
         | Four _ _ _ _ => _
         | Five _ _ _ _ _ => _
       end] |- _] => destruct x; pisp t

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

Ltac asp := pisp auto.

Lemma regEmpty : forall s, regular (@Empty s).
Proof.
  asp. intros.
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
  asp;  intros.
  cutThis (restore x); auto.
  destruct x; asp.
  destruct x; asp.
  destruct s0; asp.
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


         

