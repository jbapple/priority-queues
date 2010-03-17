{-# LANGUAGE TypeSynonymInstances,TypeFamilies #-}

module ExtractedSkew where

import qualified Heap as H

instance H.Heap (PreQ a) where
    type H.Elem (PreQ a) = a
    empty = []
    insert = preInsert 
    extractMin [] = Nothing
    extractMin (x:xs) = Just (preFindMin x xs, preDeleteMin (x:xs))

--import qualified Prelude
coq_LEQ :: Ord a => a -> a -> Bool
coq_LEQ = (<=)

data Nat = O
           | S Nat

data Prod a b = Pair a b

data Comparison = Eq
                  | Lt
                  | Gt

nat_compare :: Nat -> Nat -> Comparison
nat_compare n m =
  case n of
    O -> (case m of
            O -> Eq
            S n0 -> Lt)
    S n' -> (case m of
               O -> Gt
               S m' -> nat_compare n' m')

beq_nat :: Nat -> Nat -> Bool
beq_nat n m =
  case n of
    O -> (case m of
            O -> True
            S n0 -> False)
    S n1 -> (case m of
               O -> False
               S m1 -> beq_nat n1 m1)

fold_right :: (a2 -> a1 -> a1) -> a1 -> ([] a2) -> a1
fold_right f a0 l =
  case l of
    [] -> a0
    (:) b t -> f b (fold_right f a0 t)

data PreT a = Node a Nat ([] (PreT a))

type PreQ a = [] (PreT a)

root :: (Ord a) => (PreT a) -> a
root x =
  case x of
    Node v n l -> v

rank :: (Ord a) => (PreT a) -> Nat
rank x =
  case x of
    Node a r l -> r

link :: (Ord a) => (PreT a) -> (PreT a) -> (PreT a)
link x y =
  case x of
    Node v n p ->
      (case y of
         Node w m q ->
           (case coq_LEQ v w of
              True -> Node v (S n) ((:) y p)
              False -> Node w (S m) ((:) x q)))

skewLink :: (Ord a) => (PreT a) -> (PreT a) -> (PreT a) -> (PreT a)
skewLink x y z =
  case x of
    Node a i p ->
      (case y of
         Node b j q ->
           (case z of
              Node c k r ->
                (case coq_LEQ a b of
                   True ->
                     (case coq_LEQ a c of
                        True -> Node a (S j) ((:) y ((:) z []))
                        False -> Node c (S k) ((:) x ((:) y r)))
                   False ->
                     (case coq_LEQ b c of
                        True -> Node b (S j) ((:) x ((:) z q))
                        False -> Node c (S k) ((:) x ((:) y r))))))

ins :: (Ord a) => (PreT a) -> ([] (PreT a)) -> [] (PreT a)
ins t xs =
  case xs of
    [] -> (:) t []
    (:) y ys ->
      (case nat_compare (rank t) (rank y) of
         Lt -> (:) t xs
         _ -> ins (link t y) ys)

uniqify :: (Ord a) => ([] (PreT a)) -> [] (PreT a)
uniqify xs =
  case xs of
    [] -> []
    (:) y ys -> ins y ys

meldUniq :: (Ord a) => (Prod (PreQ a) (PreQ a)) -> (PreQ a)
meldUniq xy =
  case xy of
    Pair x y ->
      (case x of
         [] -> y
         (:) p ps ->
           (case y of
              [] -> (:) p ps
              (:) q qs ->
                (case nat_compare (rank p) (rank q) of
                   Eq -> ins (link p q) (meldUniq (Pair ps qs))
                   Lt -> (:) p (meldUniq (Pair ps ((:) q qs)))
                   Gt -> (:) q (meldUniq (Pair ((:) p ps) qs)))))

preInsert :: (Ord a) => a -> ([] (PreT a)) -> [] (PreT a)
preInsert x ys =
  case ys of
    [] -> (:) (Node x O []) ys
    (:) z1 l ->
      (case l of
         [] -> (:) (Node x O []) ys
         (:) z2 zr ->
           (case beq_nat (rank z1) (rank z2) of
              True -> (:) (skewLink (Node x O []) z1 z2) zr
              False -> (:) (Node x O []) ys))

preMeld :: (Ord a) => ([] (PreT a)) -> ([] (PreT a)) -> (PreQ a)
preMeld x y =
  meldUniq (Pair (uniqify x) (uniqify y))

preFindMin :: (Ord a) => (PreT a) -> ([] (PreT a)) -> a
preFindMin x xs =
  case xs of
    [] -> root x
    (:) y ys ->
      let z = preFindMin y ys in
      let w = root x in (case coq_LEQ w z of
                           True -> w
                           False -> z)

getMin :: (Ord a) => (PreT a) -> ([] (PreT a)) -> Prod (PreT a) ([] (PreT a))
getMin x xs =
  case xs of
    [] -> Pair x []
    (:) y ys ->
      (case getMin y ys of
         Pair t ts ->
           (case coq_LEQ (root x) (root t) of
              True -> Pair x xs
              False -> Pair t ((:) x ts)))

split :: (Ord a) => ([] (PreT a)) -> ([] a) -> ([] (PreT a)) -> Prod ([] (PreT a)) ([] a)
split t x c =
  case c of
    [] -> Pair t x
    (:) d ds ->
      (case rank d of
         O -> split t ((:) (root d) x) ds
         S n -> split ((:) d t) x ds)

preDeleteMin :: (Ord a) => ([] (PreT a)) -> [] (PreT a)
preDeleteMin x =
  case x of
    [] -> []
    (:) y ys ->
      (case getMin y ys of
         Pair p t ->
           (case p of
              Node a n c ->
                (case split [] [] c of
                   Pair p0 q -> fold_right preInsert (preMeld t p0) q)))

