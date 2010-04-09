{-# LANGUAGE TypeSynonymInstances #-}

{-| 

A heap is a container supporting the insertion of elements and the extraction of the minimum element.
This library models the implementation of asymptotically optimal purely functional heaps given by Brodal and Okasaki in their paper \"Optimal Purely Functional Priority Queues\".
The Coq proof assistant has been used to prove this implementation correct.
The proofs are available in the Cabal package or at <http://code.google.com/p/priority-queues/>.
-}
module Data.MeldableHeap 
    (PQ()
    ,empty
    ,insert
    ,findMin
    ,extractMin
    ,meld
    ,toList
    )
    where

import qualified Data.MeldableHeap.BrodalOkasakiExtract as B

type PQ a = B.PQ a Integer

inst :: Ord a => B.MINQ a (B.PQ a Integer)
inst = B.bootPQ 0 (+1) compare (<=)

empty :: Ord a => PQ a
empty = B.empty (<=) inst
-- |'insert' (O(1)) adds an element to a heap.
insert :: Ord a => a -> PQ a -> PQ a
insert = B.insert (<=) inst
-- |'findMin' (O(1)) returns the minimum element of a nonempty heap.
findMin :: Ord a => PQ a -> Maybe a
findMin = B.findMin (<=) inst
-- |'extractMin' (O(lg n)) returns (if the heap is nonempty) a pair containing the minimum element and a heap that contains all of the other elements. It does not remove copies of the minimum element if some exist in the heap.
extractMin :: Ord a => PQ a -> Maybe (a,PQ a)
extractMin = B.extractMin (<=) inst
-- |'meld' (O(1)) joins two heaps P and Q into a heap containing exactly the elements in P and Q. It does not remove duplicates.
meld :: Ord a => PQ a -> PQ a -> PQ a
meld =  B.meld (<=) inst
-- |'toList' (O(n)) returns a list of the elements in the heap in some arbitrary order.
toList :: Ord a => PQ a -> [a]
toList = B.toList (<=) inst 