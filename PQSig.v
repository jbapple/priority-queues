Set Implicit Arguments.

Require Export OrderSig.

Module Type PQSig.

  Declare Module O:Order.
  
  Export O.

  Parameter PQ:Type.

  Parameter empty:PQ.

  Parameter insert: A -> PQ -> PQ.
  Parameter findMin : PQ -> option A.
  Parameter extractMin : PQ -> option (A*PQ).
  Parameter deleteMin : PQ -> PQ.
  Parameter meld : PQ -> PQ -> PQ.

End PQSig.

Definition DERP a (leq:a -> a -> bool) (der:a -> a -> bool) := 
  (forall x y, true = der x y -> 
    ((forall z, leq x z = leq y z)
      /\
      (forall z, leq z x = leq z y)))
  /\ (forall x, der x x = true)
  /\ (forall x y, der x y = der y x)
  /\ (forall x y z, 
    true = der x y ->
    true = der y z ->
    true = der x z).

Definition DER a leq := {der | @DERP a leq der}.

Module Type PQVerify.

  Declare Module PQS:PQSig.

  Export PQS.

  Parameter count : DER LEQ -> A -> PQ -> nat.

  Definition check (same:DER LEQ) x y := 
    match same with
      | exist f _ => f x y
    end.

  Parameter countSAME :
    forall same x y,
      check same x y = true ->
      forall inp, count same x inp = count same y inp.

  Parameter emptyCount :
    forall same x, count same x empty = 0.

  Parameter insertCount :
    forall same x inp y,
      count same x (insert y inp) =
      let oldCount := count same x inp in
        if check same x y 
          then S oldCount
          else oldCount.

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

End PQVerify.