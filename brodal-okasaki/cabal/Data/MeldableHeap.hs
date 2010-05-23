{-# LANGUAGE TypeSynonymInstances #-}

{-| 

A heap is a container supporting the insertion of elements and the extraction of the minimum element.
This library models the implementation of asymptotically optimal purely functional heaps given by Brodal and Okasaki in their paper \"Optimal Purely Functional Priority Queues\".
The Coq proof assistant has been used to prove this implementation correct.
The proofs are available in the Cabal package or at <http://code.google.com/p/priority-queues/>.

The default implementation is lazy.
A strict implementation is available in this package as "Data.MeldableHeap.Strict". 
The lazy implementation is available in this module ("Data.MeldableHeap") or in "Data.MeldableHeap.Lazy".

-}
module Data.MeldableHeap 
    (PQ()
    ,empty
    ,toList
    ,insert
    ,findMin
    ,extractMin
    ,meld
    )
    where

import qualified Data.MeldableHeap.Lazy as L

type PQ = L.PQ

-- |'empty' is the heap with no elements
empty :: Ord a => PQ a
empty = L.empty

{- |

'toList' (O(n)) returns a list of the elements in the heap in some arbitrary order.

> [] == toList empty

-}
toList :: Ord a => PQ a -> [a]
toList = L.toList

{- |

'insert' (O(1)) adds an element to a heap.

> [1,2,1,0] == toList $ insert 1 $ insert 0 $ insert 2 $ insert 1 $ empty

-}
insert :: Ord a => a -> PQ a -> PQ a
insert = L.insert

{- |

'findMin' (O(1)) returns the minimum element of a nonempty heap.

> Just 0 == findMin $ insert 0 $ insert 2 $ insert 1 $ empty

-}
findMin :: Ord a => PQ a -> Maybe a
findMin = L.findMin

{- |

'extractMin' (O(lg n)) returns (if the heap is nonempty) a pair containing the minimum element and a heap that contains all of the other elements.
It does not remove copies of the minimum element if some exist in the heap.

> (0,[2,1]) == let x = insert 0 $ insert 2 $ insert 1 $ empty in let Just (p,q) = extractMin x in (p,toList q)

-}
extractMin :: Ord a => PQ a -> Maybe (a,PQ a)
extractMin = L.extractMin

{- |

'meld' (O(1)) joins two heaps P and Q into a heap containing exactly the elements in P and Q. It does not remove duplicates.

> [2,1,0,2,1,0] == let x = insert 0 $ insert 2 $ insert 1 $ empty in toList (meld x x)

-}
meld :: Ord a => PQ a -> PQ a -> PQ a
meld =  L.meld
