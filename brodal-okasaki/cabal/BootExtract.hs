module BootExtract where

import qualified Prelude

data Nat = O
           | S Nat

data Comparison = Eq
                  | Lt
                  | Gt

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type ORDER a =
  a -> a -> Prelude.Bool
  -- singleton inductive, whose constructor was Order
  
nat_compare :: Nat -> Nat -> Comparison
nat_compare n m =
  case n of
    O -> (case m of
            O -> Eq
            S n0 -> Lt)
    S n' -> (case m of
               O -> Gt
               S m' -> nat_compare n' m')

beq_nat :: Nat -> Nat -> Prelude.Bool
beq_nat n m =
  case n of
    O -> (case m of
            O -> Prelude.True
            S n0 -> Prelude.False)
    S n1 -> (case m of
               O -> Prelude.False
               S m1 -> beq_nat n1 m1)

fold_right :: (a2 -> a1 -> a1) -> a1 -> ([] a2) -> a1
fold_right f a0 l =
  case l of
    [] -> a0
    (:) b t -> f b (fold_right f a0 t)

data MINQ a pQ = Minq pQ (a -> pQ -> pQ) (pQ -> Prelude.Maybe a) 
               (pQ -> Prelude.Maybe ((,) a pQ)) (pQ -> [] a) 
               (pQ -> pQ -> pQ)

empty :: (ORDER a1) -> (MINQ a1 a2) -> a2
empty h mINQ =
  case mINQ of
    Minq empty0 insert0 findMin0 extractMin0 toList0 meld0 -> empty0

insert :: (ORDER a1) -> (MINQ a1 a2) -> a1 -> a2 -> a2
insert h mINQ x x0 =
  case mINQ of
    Minq empty0 insert0 findMin0 extractMin0 toList0 meld0 -> insert0 x x0

findMin :: (ORDER a1) -> (MINQ a1 a2) -> a2 -> Prelude.Maybe a1
findMin h mINQ x =
  case mINQ of
    Minq empty0 insert0 findMin0 extractMin0 toList0 meld0 -> findMin0 x

extractMin :: (ORDER a1) -> (MINQ a1 a2) -> a2 -> Prelude.Maybe ((,) a1 a2)
extractMin h mINQ x =
  case mINQ of
    Minq empty0 insert0 findMin0 extractMin0 toList0 meld0 -> extractMin0 x

toList :: (ORDER a1) -> (MINQ a1 a2) -> a2 -> [] a1
toList h mINQ x =
  case mINQ of
    Minq empty0 insert0 findMin0 extractMin0 toList0 meld0 -> toList0 x

meld :: (ORDER a1) -> (MINQ a1 a2) -> a2 -> a2 -> a2
meld h mINQ x x0 =
  case mINQ of
    Minq empty0 insert0 findMin0 extractMin0 toList0 meld0 -> meld0 x x0

data Tree a = Node (Root a) Nat (Many a)
data Root a = Top a (Many a)
data Many a = Cil
              | Nons (Tree a) (Many a)

rank :: (Tree a1) -> Nat
rank x =
  case x of
    Node r0 r m -> r

root :: (Tree a1) -> Root a1
root x =
  case x of
    Node v n m -> v

toListR :: (Root a1) -> ([] a1) -> [] a1
toListR =
  let
    toListT x r =
      case x of
        Node h n t -> toListR0 h (toListM t r)
    toListR0 x r =
      case x of
        Top v t -> toListM t ((:) v r)
    toListM x r =
      case x of
        Cil -> r
        Nons h t -> toListT h (toListM t r)
  in toListR0

link :: (ORDER a1) -> (Tree a1) -> (Tree a1) -> Tree a1
link o x y =
  case x of
    Node v n p ->
      (case y of
         Node w m q ->
           (case case v of
                   Top p0 m0 -> (case w of
                                   Top q0 m1 -> o p0 q0) of
              Prelude.True -> Node v (S n) (Nons y p)
              Prelude.False -> Node w (S m) (Nons x q)))

skewLink :: (ORDER a1) -> (Tree a1) -> (Tree a1) -> (Tree a1) -> Tree a1
skewLink o x y z =
  case x of
    Node a i p ->
      (case y of
         Node b j q ->
           (case z of
              Node c k r ->
                (case case a of
                        Top p0 m -> (case b of
                                       Top q0 m0 -> o p0 q0) of
                   Prelude.True ->
                     (case case a of
                             Top p0 m -> (case c of
                                            Top q0 m0 -> o p0 q0) of
                        Prelude.True -> Node a (S j) (Nons y (Nons z Cil))
                        Prelude.False -> Node c (S k) (Nons x (Nons y r)))
                   Prelude.False ->
                     (case case b of
                             Top p0 m -> (case c of
                                            Top q0 m0 -> o p0 q0) of
                        Prelude.True -> Node b (S j) (Nons x (Nons z q))
                        Prelude.False -> Node c (S k) (Nons x (Nons y r))))))

ins :: (ORDER a1) -> (Tree a1) -> (Many a1) -> Many a1
ins o t xs =
  case xs of
    Cil -> Nons t Cil
    Nons y ys ->
      (case nat_compare (rank t) (rank y) of
         Lt -> Nons t xs
         _ -> ins o (link o t y) ys)

uniqify :: (ORDER a1) -> (Many a1) -> Many a1
uniqify o xs =
  case xs of
    Cil -> Cil
    Nons y ys -> ins o y ys

meldUniq :: (ORDER a1) -> ((,) (Many a1) (Many a1)) -> Many a1
meldUniq o x =
  case x of
    (,) x0 y ->
      (case x0 of
         Cil -> y
         Nons p ps ->
           (case y of
              Cil -> Nons p ps
              Nons q qs ->
                (case nat_compare (rank p) (rank q) of
                   Eq -> ins o (link o p q) (meldUniq o ((,) ps qs))
                   Lt -> Nons p (meldUniq o ((,) ps (Nons q qs)))
                   Gt -> Nons q (meldUniq o ((,) (Nons p ps) qs)))))

skewEmpty :: Many a1
skewEmpty =
  Cil

skewInsert :: (ORDER a1) -> (Root a1) -> (Many a1) -> Many a1
skewInsert o x ys =
  case ys of
    Cil -> Nons (Node x O Cil) ys
    Nons z1 m ->
      (case m of
         Cil -> Nons (Node x O Cil) ys
         Nons z2 zr ->
           (case beq_nat (rank z1) (rank z2) of
              Prelude.True -> Nons (skewLink o (Node x O Cil) z1 z2) zr
              Prelude.False -> Nons (Node x O Cil) ys))

skewMeld :: (ORDER a1) -> (Many a1) -> (Many a1) -> Many a1
skewMeld o x y =
  meldUniq o ((,) (uniqify o x) (uniqify o y))

getMin :: (ORDER a1) -> (Tree a1) -> (Many a1) -> (,) (Tree a1) (Many a1)
getMin o x xs =
  case xs of
    Cil -> (,) x Cil
    Nons y ys ->
      (case getMin o y ys of
         (,) t ts ->
           (case case root x of
                   Top p m -> (case root t of
                                 Top q m0 -> o p q) of
              Prelude.True -> (,) x xs
              Prelude.False -> (,) t (Nons x ts)))

children :: (Tree a1) -> Many a1
children x =
  case x of
    Node r n c -> c

split :: (Many a1) -> ([] (Root a1)) -> (Many a1) -> (,) 
         (Many a1) ([] (Root a1))
split t x c =
  case c of
    Cil -> (,) t x
    Nons d ds ->
      (case children d of
         Cil -> split t ((:) (root d) x) ds
         Nons t0 m -> split (Nons d t) x ds)

skewExtractMin :: (ORDER a1) -> (Many a1) -> Prelude.Maybe
                  ((,) (Root a1) (Many a1))
skewExtractMin o x =
  case x of
    Cil -> Prelude.Nothing
    Nons y ys -> Prelude.Just
      (case getMin o y ys of
         (,) t0 t ->
           (case t0 of
              Node v n c -> (,) v
                (case split Cil [] c of
                   (,) p q ->
                     fold_right (\x0 x1 -> skewInsert o x0 x1)
                       (skewMeld o t p) q)))

data BootWrap a = Empty
                  | Full (Root a)

type PQ a = (BootWrap a)

bootInsert :: (ORDER a1) -> a1 -> (PQ a1) -> PQ a1
bootInsert o x x0 =
  let x1 = Full (Top x skewEmpty) in
  (case x1 of
     Empty -> x0
     Full r ->
       (case r of
          Top v c ->
            (case x0 of
               Empty -> x1
               Full r0 ->
                 (case r0 of
                    Top w d ->
                      (case o v w of
                         Prelude.True -> Full (Top v
                           (skewInsert o (Top w d) c))
                         Prelude.False -> Full (Top w
                           (skewInsert o (Top v c) d)))))))

bootFindMin :: (ORDER a1) -> (PQ a1) -> Prelude.Maybe a1
bootFindMin o x =
  case x of
    Empty -> Prelude.Nothing
    Full r -> (case r of
                 Top v m -> Prelude.Just v)

bootMeld :: (ORDER a1) -> (PQ a1) -> (PQ a1) -> PQ a1
bootMeld o x x0 =
  case x of
    Empty -> x0
    Full r ->
      (case r of
         Top v c ->
           (case x0 of
              Empty -> x
              Full r0 ->
                (case r0 of
                   Top w d ->
                     (case o v w of
                        Prelude.True -> Full (Top v
                          (skewInsert o (Top w d) c))
                        Prelude.False -> Full (Top w
                          (skewInsert o (Top v c) d))))))

bootExtractMin :: (ORDER a1) -> (PQ a1) -> Prelude.Maybe ((,) a1 (PQ a1))
bootExtractMin o x =
  case x of
    Empty -> Prelude.Nothing
    Full r ->
      (case r of
         Top v c -> Prelude.Just ((,) v
           (case skewExtractMin o c of
              Prelude.Just p ->
                (case p of
                   (,) r0 cs ->
                     (case r0 of
                        Top w d -> Full (Top w (skewMeld o d cs))))
              Prelude.Nothing -> Empty)))

bootEmpty :: (ORDER a1) -> PQ a1
bootEmpty o =
  Empty

bootToList :: (ORDER a1) -> (PQ a1) -> [] a1
bootToList o x =
  case x of
    Empty -> []
    Full y -> toListR y []

bootPQ :: (ORDER a1) -> MINQ a1 (PQ a1)
bootPQ o =
  Minq (bootEmpty o) (\x x0 -> bootInsert o x x0) (\x -> 
    bootFindMin o x) (\x -> bootExtractMin o x) (\x -> 
    bootToList o x) (\x x0 -> bootMeld o x x0)

