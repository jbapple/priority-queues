_Priority queues_ over some ordered type `T` are data structures supporting at least the following:

  * `empty` is a priority queue containing no elements
  * `insert(v,PQ)` inserts `v` (of type `T`) into the priority queue `PQ`
  * `findMin(PQ)` returns the minimum element from a non-empty priority queue `PQ`
  * `deleteMin(PQ)` deletes the minimum element from a non-empty priority queue `PQ`

Priority queues are sometimes called _heaps_. The goal of this project is to implement and verify priority queues.

There is a [Coq](http://coq.inria.fr/)-verified implementation of Brodal-Okasaki heaps [available in the source repository](http://code.google.com/p/priority-queues/source/browse/brodal-okasaki). It is based on the paper ["Optimal Purely Functional Priority Queues"](ftp://ftp.daimi.au.dk/pub/BRICS/Reports/RS/96/37/BRICS-RS-96-37.pdf). In addition to the operations above, this implementation also offers:

  * `toList(PQ)` returns a list of the elements in a priority queue `PQ` in no particular order
  * `meld(P,Q)` returns a priority queue containing the elements in the priority queues `P` and `Q`.

The operation `toList` takes O(n) time, `deleteMin` takes O(lg n) time, and the other operations take O(1) time.

A [haskell library based on code extracted by Coq is available in the downloads section](http://code.google.com/p/priority-queues/downloads/list) or [on Hackage](http://hackage.haskell.org/package/meldable-heap/). A description of the differences between versions of this package is available in the [CHANGELOG](http://priority-queues.googlecode.com/hg/brodal-okasaki/cabal/CHANGELOG).