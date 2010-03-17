{-# LANGUAGE CPP,DeriveDataTypeable,TypeFamilies #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.PQueue.Min
-- Copyright   :  (c) Louis Wasserman 2010
-- License     :  BSD-style
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  portable
--
-- General purpose priority queue, supporting extract-minimum operations.
--
-- An amortized running time is given for each operation, with /n/ referring
-- to the length of the sequence and /i/ being the integral index used by
-- some operations.  These bounds hold even in a persistent (shared) setting.
--
-- This implementation is based on a binomial heap augmented with a global root.
-- The spine of the heap is maintained strictly, ensuring that computations happen
-- as they are performed.
-- 
-- /WARNING:/ 'toList' and 'toAscList' are /not/ equivalent, unlike for example
-- "Data.Map".
-----------------------------------------------------------------------------
module Labor (
	MinQueue,
	-- * Utility types
	Prio(..),
	-- * Basic operations
	empty,
	null,
	size, 
	-- * Query operations
	top,
	delete,
	extract,
	-- * Construction operations
	singleton,
	insert,
	union,
	unions,
	-- * Subsets
	-- ** Extracting subsets
	(!!),
	take,
	drop,
	splitAt,
	-- ** Predicates
	takeWhile,
	dropWhile,
	span,
	break,
	filter,
	partition,
	-- * Fold\/Functor\/Traversable variations
	mapMonotonic,
	foldrAsc,
	foldlAsc,
	foldrDesc,
	foldlDesc,
	traverseMonotonic,
	-- * List operations
	toList,
	toAscList,
	toDescList,
	fromList,
	fromAscList,
	fromDescList) where

import Prelude hiding (null, foldr, foldl, take, drop, takeWhile, dropWhile, splitAt, span, break, (!!), filter)

import Control.Applicative (Applicative(..), (<$>))

import Data.Monoid
import Data.Foldable hiding (toList)
import Data.Traversable

import qualified Data.List as List

import qualified Heap as H

#ifdef __GLASGOW_HASKELL__
import GHC.Exts (build)
import Text.Read (Lexeme(Ident), lexP, parens, prec,
	readPrec, readListPrec, readListPrecDefault)
import Data.Data
#else
build :: ((a -> [a] -> [a]) -> [a] -> [a]) -> [a]
build f = f (:) []
#endif

instance H.Heap (MinQueue a) where
    type H.Elem (MinQueue a) = a
    empty = Empty
    insert = Labor.insert
    extractMin = Labor.extract
    findMin = error "MinQueue findMin"
    meld = error "MinQueue meld"

-- | Type which orders only based on its priority value.  Useful for putting in a priority queue
-- which is meant to account for both an ordering value and other information.
data Prio p a = Prio {priority :: p, prioValue :: a}
# if __GLASGOW_HASKELL__
	deriving (Read, Show, Data, Typeable)
# else
	deriving (Read, Show)
# endif

instance Eq p => Eq (Prio p a) where
	Prio p1 _ == Prio p2 _ = p1 == p2

instance Ord p => Ord (Prio p a) where
	Prio p1 _ `compare` Prio p2 _ = p1 `compare` p2
	Prio p1 _ <= Prio p2 _ = p1 <= p2

-- instance 

-- | A priority queue implementation.  Implemented as a find-min wrapper around a binomial heap.
-- /Warning/: the 'Functor', 'Foldable', and 'Traversable' instances of this type /ignore ordering/.
-- For 'Functor', it is guaranteed that if @f@ is a monotonic function, then @'fmap' f@ on a valid
-- 'MinQueue' will return a valid 'MinQueue'.  An analogous guarantee holds for 'traverse'.  (Note:
-- if passed constant-time operations, every function in 'Functor', 'Foldable', and 'Traversable'
-- will run in /O(n)/.)
-- 
-- If you wish to perform folds on a priority queue that respect order, use 'foldrAsc' or
-- 'foldlAsc'.
-- 
-- For any operation @op@ in 'Eq' or 'Ord', @queue1 `op` queue2@ is equivalent to
-- @toAscList queue1 `op` toAscList queue2@.
data MinQueue a = Empty | MinQueue {-# UNPACK #-} !Int a !(BinomHeap a)

#ifdef __GLASGOW_HASKELL__
instance (Ord a, Data a) => Data (MinQueue a) where
	gfoldl f z q	= case extract q of
		Nothing	-> z Empty
		Just (x, q')
			-> z insertMinQ `f` x `f` q'
	
	gunfold k z c = case constrIndex c of
		1	-> z Empty
		2	-> k (k (z insertMinQ))
		_	-> error "gunfold"
	
	toConstr q
		| null q	= emptyConstr
		| otherwise	= consConstr
	
	dataTypeOf _ = queueDataType

queueDataType :: DataType
queueDataType = mkDataType "Data.PQueue.Min.MinQueue" [emptyConstr, consConstr]

emptyConstr, consConstr :: Constr
emptyConstr = mkConstr queueDataType "empty" [] Prefix
consConstr  = mkConstr queueDataType "<|" [] Infix
#endif

#include "Typeable.h"
INSTANCE_TYPEABLE1(MinQueue,minQTC,"MinQueue")

type BinomHeap = BinomForest Zero

instance Ord a => Eq (MinQueue a) where
	Empty == Empty = True
	MinQueue n1 x1 q1 == MinQueue n2 x2 q2
		= n1 == n2 && x1 == x2 && foldr (&&) True 
			(zipWith (==) (heapToList q1) (heapToList q2))
	_ == _ = False

instance Ord a => Ord (MinQueue a) where
	Empty `compare` Empty = EQ
	Empty `compare` _ = LT
	_ `compare` Empty = GT
	MinQueue n1 x1 q1 `compare` MinQueue n2 x2 q2 = 
		compare x1 x2 `mappend` foldr mappend (compare n1 n2) (zipWith compare (heapToList q1) (heapToList q2))
		-- We compare their first elements, then their other elements up to the smaller queue's length,
		-- and then the longer queue wins.
		-- This is equivalent to @comparing toAscList@, except it fuses much more nicely.

heapToList :: Ord a => BinomHeap a -> [a]
heapToList q = build (\ c nil -> foldrUnfold c nil extractHeap q)

instance (Ord a, Show a) => Show (MinQueue a) where
	showsPrec p xs = showParen (p > 10) $
		showString "fromAscList " . shows (toAscList xs)

instance Read a => Read (MinQueue a) where
#ifdef __GLASGOW_HASKELL__
	readPrec = parens $ prec 10 $ do
		Ident "fromAscList" <- lexP
		xs <- readPrec
		return (fromAscList xs)

	readListPrec = readListPrecDefault
#else
	readsPrec p = readParen (p > 10) $ \ r -> do
		("fromAscList",s) <- lex r
		(xs,t) <- reads s
		return (fromAscList xs,t)
#endif

instance Ord a => Monoid (MinQueue a) where
	mempty = Empty
	mappend = union
	mconcat = unions

-- We implement tree ranks in the type system with a nicely elegant approach, as follows.
-- The goal is to have the type system automatically guarantee that our binomial forest
-- has the correct binomial structure.
-- 
-- In the traditional set-theoretic construction of the natural numbers, we define
-- each number to be the set of numbers less than it, and zero to be the empty set,
-- as follows:
-- 
-- 0 = {}	1 = {0}		2 = {0, 1}	3={0, 1, 2} ...
-- 
-- Binomial trees have a similar structure: a tree of rank @k@ has one child of each
-- rank less than @k@.  Let's define the type @rk@ corresponding to rank @k@ to refer
-- to a collection of binomial trees of ranks @0..k-1@.  Then we can say that
-- 
-- > data Succ rk a = Succ (BinomTree rk a) (rk a)
-- 
-- and this behaves exactly as the successor operator for ranks should behave.  Furthermore,
-- we immediately obtain that
-- 
-- > data BinomTree rk a = BinomTree a (rk a)
-- 
-- which is nice and compact.  With this construction, things work out extremely nicely:
-- 
-- > BinomTree (Succ (Succ (Succ Zero)))
-- 
-- is a type constructor that takes an element type and returns the type of binomial trees
-- of rank @3@.
data BinomForest rk a = Nil | Skip !(BinomForest (Succ rk) a) | 
	Cons {-# UNPACK #-} !(BinomTree rk a) !(BinomForest (Succ rk) a)

data BinomTree rk a = BinomTree a (rk a)

-- | If |rk| corresponds to rank @k@, then |'Succ' rk| corresponds to rank @k+1@.
data Succ rk a = Succ {-# UNPACK #-} !(BinomTree rk a) (rk a)

-- | Type corresponding to the zero rank.
data Zero a = Zero

-- | Type alias for a comparison function.
type LEq a = a -> a -> Bool

-- basics

-- | /O(1)/.  The empty priority queue.
empty :: MinQueue a
empty = Empty

-- | /O(1)/.  Is this the empty priority queue?
null :: MinQueue a -> Bool
null Empty = True
null _ = False

-- | /O(1)/.  The number of elements in the queue.
size :: MinQueue a -> Int
size Empty = 0
size (MinQueue n _ _) = n

-- queries
-- | /O(1)/.  View the top (minimum) element of the queue, if there is one.
top :: Ord a => MinQueue a -> Maybe a
top = fmap fst . extract

-- | /O(log n)/.  Delete the top element of the sequence, if there is one.
delete :: Ord a => MinQueue a -> Maybe (MinQueue a)
delete = fmap snd . extract

-- | /O(log n)/.  Extract the top (minimum) element of the sequence, if there is one.
extract :: Ord a => MinQueue a -> Maybe (a, MinQueue a)
extract Empty = Nothing
extract (MinQueue n x ts) = Just (x, maybe Empty (\ (x', ts') -> MinQueue (n-1) x' ts') (extractHeap ts))

-- | /O(1)/.  Construct a priority queue with a single element.
singleton :: a -> MinQueue a
singleton x = MinQueue 1 x Nil

-- | Amortized /O(1)/, worst-case /O(log n)/.  Insert an element into the priority queue.  
insert :: Ord a => a -> MinQueue a -> MinQueue a
insert x' (MinQueue n x f)
	| x' <= x	= MinQueue (n+1) x' (insertBin x f)
	| otherwise	= MinQueue (n+1) x (insertBin x' f)
	where	insertBin = incr (<=) . tip
insert x Empty = singleton x

-- | /O(log (min(n,m)))/.  Take the union of two priority queues.
union :: Ord a => MinQueue a -> MinQueue a -> MinQueue a
union = union' (<=)

-- | Takes the union of a list of priority queues.  Equivalent to @'foldl' 'union' 'empty'@.
unions :: Ord a => [MinQueue a] -> MinQueue a
unions = foldl union Empty

-- | Index (subscript) operator, starting from 0.  @queue !! k@ returns the @(k+1)@th smallest element in the queue.
(!!) :: Ord a => MinQueue a -> Int -> a
q !! n	| n >= size q
		= error "Data.PQueue.Min.!!: index too large"
q !! n = (List.!!) (toAscList q) n

{-# INLINE takeWhile #-}
-- | 'takeWhile', applied to a predicate @p@ and a queue @queue@, returns the
-- longest prefix (possibly empty) of @queue@ of elements that satisfy @p@.
takeWhile :: Ord a => (a -> Bool) -> MinQueue a -> [a]
takeWhile p = foldWhileFB p . toAscList

{-# INLINE foldWhileFB #-}
-- | Equivalent to Data.List.takeWhile, but is a better producer.
foldWhileFB :: (a -> Bool) -> [a] -> [a]
foldWhileFB p xs = build (\ c nil -> let 
	consWhile x xs
		| p x		= x `c` xs
		| otherwise	= nil
	in foldr consWhile nil xs)

-- | 'dropWhile' @p queue@ returns the queue remaining after 'takeWhile' @p queue@.
dropWhile :: Ord a => (a -> Bool) -> MinQueue a -> MinQueue a
dropWhile p = drop' where
	drop' q = case extract q of
	  Just (x, q')
		| p x	-> drop' q'
	  _		-> q

-- | 'span', applied to a predicate @p@ and a queue @queue@, returns a tuple where
-- first element is longest prefix (possibly empty) of @queue@ of elements that
-- satisfy @p@ and second element is the remainder of the queue.
span :: Ord a => (a -> Bool) -> MinQueue a -> ([a], MinQueue a)
span p queue = case extract queue of
	Just (x, q') 
		| p x	-> let (ys, q'') = span p q' in (x:ys, q'')
	_		-> ([], queue)

-- | 'break', applied to a predicate @p@ and a queue @queue@, returns a tuple where
-- first element is longest prefix (possibly empty) of @queue@ of elements that
-- /do not satisfy/ @p@ and second element is the remainder of the queue.
break :: Ord a => (a -> Bool) -> MinQueue a -> ([a], MinQueue a)
break p = span (not . p)

{-# INLINE take #-}
-- | /O(k log n)/. 'take' @k@, applied to a queue @queue@, returns a list of the smallest @k@ elements of @queue@,
-- or all elements of @queue@ itself if @k >= 'size' queue@.
take :: Ord a => Int -> MinQueue a -> [a]
take n = List.take n . toAscList

-- | /O(k log n)/.  'drop' @k@, applied to a queue @queue@, returns @queue@ with the smallest @k@ elements deleted,
-- or an empty queue if @k >= size 'queue'@.
drop :: Ord a => Int -> MinQueue a -> MinQueue a
drop n queue = n `seq` case delete queue of
	Just queue'
	  | n > 0	-> drop (n-1) queue'
	_		-> queue

-- | /O(k log n)/.  Equivalent to @('take' k queue, 'drop' k queue)@.
splitAt :: Ord a => Int -> MinQueue a -> ([a], MinQueue a)
splitAt n queue = n `seq` case extract queue of
	Just (x, queue')
	  | n > 0	-> let (xs, queue'') = splitAt (n-1) queue' in (x:xs, queue'')
	_		-> ([], queue)

-- | /O(n)/.  Returns the queue with all elements not satisfying @p@ removed.
filter :: Ord a => (a -> Bool) -> MinQueue a -> MinQueue a
filter _ Empty = Empty
filter p (MinQueue _ x ts) = if p x then insertMinQ x q' else q'
	where	q' = filterQueue p (<=) (const Empty) Empty ts

-- | /O(n)/.  Returns a pair where the first queue contains all elements satisfying @p@, and the second queue
-- contains all elements not satisfying @p@.
partition :: Ord a => (a -> Bool) -> MinQueue a -> (MinQueue a, MinQueue a)
partition _ Empty = (Empty, Empty)
partition p (MinQueue _ x ts) = case partitionQueue p (<=) (const (Empty, Empty)) (Empty, Empty) ts of
	(q0, q1)  | p x		-> (insertMinQ x q0, q1)
		  | otherwise	-> (q0, insertMinQ x q1)

-- | /O(n)/.  Assumes that the function it is given is monotonic, and applies this function to every element of the priority queue,
-- as in 'fmap'.  If it is not, the result is undefined.
mapMonotonic :: (a -> b) -> MinQueue a -> MinQueue b
mapMonotonic _ Empty = Empty
mapMonotonic f (MinQueue n x ts) = MinQueue n (f x) (fmap f ts)

-- | /O(n)/.  Assumes that the function it is given is monotonic, in some sense, and performs the 'traverse' operation.
-- If the function is not monotonic, the result is undefined.
traverseMonotonic :: Applicative f => (a -> f b) -> MinQueue a -> f (MinQueue b)
traverseMonotonic _ Empty = pure Empty
traverseMonotonic f (MinQueue n x ts) = MinQueue n <$> f x <*> traverse f ts

{-# INLINE toAscList #-}
-- | /O(n log n)/.  Extracts the elements of the priority queue in ascending order.
toAscList :: Ord a => MinQueue a -> [a]
toAscList queue = build (\ c nil -> foldrAsc c nil queue)

{-# INLINE toDescList #-}
-- | /O(n log n)/.  Extracts the elements of the priority queue in descending order.
toDescList :: Ord a => MinQueue a -> [a]
toDescList queue = build (\ c nil -> foldrDesc c nil queue)

{-# INLINE toList #-}
-- | /O(n)/.  Returns the elements of the priority queue in no particular order.
toList :: MinQueue a -> [a]
toList q = build (\ c nil -> foldr c nil q)

{-# INLINE foldrAsc #-}
-- | /O(n log n)/.  Performs a right-fold on the elements of a priority queue in ascending order.
foldrAsc :: Ord a => (a -> b -> b) -> b -> MinQueue a -> b
foldrAsc _ z Empty = z
foldrAsc f z (MinQueue _ x ts) = x `f` foldrUnfold f z extractHeap ts

{-# INLINE foldrUnfold #-}
-- | Equivalent to @foldr f z (unfoldr suc s0)@.
foldrUnfold :: (a -> c -> c) -> c -> (b -> Maybe (a, b)) -> b -> c
foldrUnfold f z suc s0 = unf s0 where
	unf s = case suc s of
		Nothing		-> z
		Just (x, s')	-> x `f` unf s'

-- | /O(n log n)/.  Performs a left-fold on the elements of a priority queue in ascending order.
foldlAsc :: Ord a => (b -> a -> b) -> b -> MinQueue a -> b
foldlAsc _ z Empty = z
foldlAsc f z (MinQueue _ x ts) = foldlUnfold f (z `f` x) extractHeap ts

-- | /O(n log n)/.  Performs a right-fold on the elements of a priority queue in descending order.
-- @foldrDesc f z q == foldlAsc (flip f) z q@.
foldrDesc :: Ord a => (a -> b -> b) -> b -> MinQueue a -> b
foldrDesc = foldlAsc . flip

-- | /O(n log n)/.  Performs a left-fold on the elements of a priority queue in descending order.
-- @foldlDesc f z q == foldrAsc (flip f) z q@.
foldlDesc :: Ord a => (b -> a -> b) -> b -> MinQueue a -> b
foldlDesc = foldrAsc . flip

{-# INLINE foldlUnfold #-}
-- | @foldlUnfold f z suc s0@ is equivalent to @foldl f z (unfoldr suc s0)@.
foldlUnfold :: (c -> a -> c) -> c -> (b -> Maybe (a, b)) -> b -> c
foldlUnfold f z suc s0 = unf z s0 where
	unf z s = case suc s of
		Nothing		-> z
		Just (x, s')	-> unf (z `f` x) s'

{-# INLINE fromList #-}
-- | /O(n)/.  Constructs a priority queue from an unordered list.
fromList :: Ord a => [a] -> MinQueue a
fromList = foldr insert Empty

{-# INLINE fromAscList #-}
-- | /O(n)/.  Constructs a priority queue from an ascending list.  /Warning/: Does not check the precondition.
fromAscList :: [a] -> MinQueue a
fromAscList = foldr insertMinQ Empty

-- | /O(n)/.  Constructs a priority queue from an descending list.  /Warning/: Does not check the precondition.
fromDescList :: [a] -> MinQueue a
fromDescList [] = Empty
fromDescList (x:xs) = descList 1 x Nil xs where
	descList n x ts xs = n `seq` case xs of
		[]	-> MinQueue n x ts
		x':xs'	-> descList (n+1) x' (tip x `insertMin` ts) xs'

{-# INLINE union' #-}
union' :: LEq a -> MinQueue a -> MinQueue a -> MinQueue a
union' _ Empty q = q
union' _ q Empty = q
union' (<=) (MinQueue n1 x1 f1) (MinQueue n2 x2 f2)
	| x1 <= x2	= MinQueue (n1 + n2) x1 (carry (<=) (tip x2) f1 f2)
	| otherwise	= MinQueue (n1 + n2) x2 (carry (<=) (tip x1) f1 f2)

-- | Takes a size and a binomial forest and produces a priority queue with a distinguished global root.
extractHeap :: Ord a => BinomHeap a -> Maybe (a, BinomHeap a)
extractHeap ts = case extractBin (<=) ts of
	Yes (Extract x _ ts')	-> Just (x, ts')
	_			-> Nothing

-- | A specialized type intended to organize the return of extract-min queries
-- from a binomial forest.  We walk all the way through the forest, and then
-- walk backwards.  @Extract rk a@ is the result type of an extract-min 
-- operation that has walked as far backwards of rank @rk@ -- that is, it
-- has visited every root of rank @>= rk@.
-- 
-- The interpretation of @Extract minKey children forest@ is
-- 
-- 	* @minKey@ is the key of the minimum root visited so far.  It may have
-- 		any rank @>= rk@.  We will denote the root corresponding to 
-- 		@minKey@ as @minRoot@.
-- 	
-- 	* @children@ is those children of @minRoot@ which have not yet been 
-- 		merged with the rest of the forest. Specifically, these are 
-- 		the children with rank @< rk@.
-- 	
-- 	* @forest@ is an accumulating parameter that maintains the partial 
-- 		reconstruction of the binomial forest without @minRoot@. It is 
-- 		the union of all old roots with rank @>= rk@ (except @minRoot@), 
-- 		with the set of all children of @minRoot@ with rank @>= rk@.  
-- 		Note that @forest@ is lazy, so if we discover a smaller key 
-- 		than @minKey@ later, we haven't wasted significant work.
data Extract rk a = Extract a (rk a) (BinomForest rk a)
data MExtract rk a = No | Yes {-# UNPACK #-} !(Extract rk a)

incrExtract :: Extract (Succ rk) a -> Extract rk a
incrExtract (Extract minKey (Succ kChild kChildren) ts)
	= Extract minKey kChildren (Cons kChild ts)

incrExtract' :: LEq a -> BinomTree rk a -> Extract (Succ rk) a -> Extract rk a
incrExtract' (<=) t (Extract minKey (Succ kChild kChildren) ts)
	= Extract minKey kChildren (Skip (incr (<=) (t `cat` kChild) ts))
	where	cat = joinBin (<=)

-- | Walks backward from the biggest key in the forest, as far as rank @rk@.
-- Returns its progress.  Each successive application of @extractBin@ takes
-- amortized /O(1)/ time, so applying it from the beginning takes /O(log n)/ time.
extractBin :: LEq a -> BinomForest rk a -> MExtract rk a
extractBin _ Nil = No
extractBin (<=) (Skip f) = case extractBin (<=) f of
	Yes ex	-> Yes (incrExtract ex)
	No	-> No
extractBin (<=) (Cons t@(BinomTree x ts) f) = Yes $ case extractBin (<=) f of
	Yes ex@(Extract minKey _ _)
		| minKey < x	-> incrExtract' (<=) t ex
	_			-> Extract x ts (Skip f)
	where	a < b = not (b <= a)

filterQueue :: (a -> Bool) -> LEq a -> (rk a -> MinQueue a) -> MinQueue a -> BinomForest rk a -> MinQueue a
filterQueue p (<=) fCh q0 forest = q0 `seq` case forest of
	Nil		-> q0
	Skip forest'	-> filterQueue p (<=) fCh' q0 forest'
	Cons t forest'	-> filterQueue p (<=) fCh' (union' (<=) (filterT t) q0) forest'
	where	fCh' (Succ t tss) = union' (<=) (filterT t) (fCh tss)
		filterT (BinomTree x ts)
			| p x		= insertMinQ x (fCh ts)
			| otherwise	= fCh ts

type Partition a = (MinQueue a, MinQueue a)

partitionQueue :: (a -> Bool) -> LEq a -> (rk a -> Partition a) -> Partition a ->
	BinomForest rk a -> Partition a
partitionQueue p (<=) fCh (q0, q1) ts = q0 `seq` q1 `seq` case ts of
	Nil		-> (q0, q1)
	Skip ts'	-> partitionQueue p (<=) fCh' (q0, q1) ts'
	Cons t ts'	-> partitionQueue p (<=) fCh' (both (union' (<=)) (partitionT t) (q0, q1)) ts'
	where	both f (x1, x2) (y1, y2) = (f x1 y1, f x2 y2)
		fCh' (Succ t tss) = both (union' (<=)) (partitionT t) (fCh tss)
		partitionT (BinomTree x ts) = case fCh ts of
			(q0, q1)
	  			| p x		-> (insertMinQ x q0, q1)
	  			| otherwise	-> (q0, insertMinQ x q1)

{-# INLINE tip #-}
-- | Constructs a binomial tree of rank 0.
tip :: a -> BinomTree Zero a
tip x = BinomTree x Zero

insertMinQ :: a -> MinQueue a -> MinQueue a
insertMinQ x Empty = singleton x
insertMinQ x (MinQueue n x' f) = MinQueue (n+1) x (insertMin (tip x') f)

-- | @insertMin t f@ assumes that the root of @t@ compares as less than
-- every other root in @f@, and merges accordingly.
insertMin :: BinomTree rk a -> BinomForest rk a -> BinomForest rk a
insertMin t Nil = Cons t Nil
insertMin t (Skip f) = Cons t f
insertMin (BinomTree x ts) (Cons t' f) = Skip (insertMin (BinomTree x (Succ t' ts)) f)

-- | Given two binomial forests starting at rank @rk@, takes their union.
-- Each successive application of this function costs /O(1)/, so applying it
-- from the beginning costs /O(log n)/.
merge :: LEq a -> BinomForest rk a -> BinomForest rk a -> BinomForest rk a
merge (<=) f1 f2 = case (f1, f2) of
	(Skip f1', Skip f2')
			-> Skip (merge (<=) f1' f2')
	(Skip f1', Cons t2 f2')
			-> Cons t2 (merge (<=) f1' f2')
	(Cons t1 f1', Skip f2')
			-> Cons t1 (merge (<=) f1' f2')
	(Cons t1 f1', Cons t2 f2')
			-> Skip (carry (<=) (t1 `cat` t2) f1' f2')
	(Nil, _)	-> f2
	(_, Nil)	-> f1
	where	cat = joinBin (<=)

-- | Merges two binomial forests with another tree. If we are thinking of the trees 
-- in the binomial forest as binary digits, this corresponds to a carry operation.
-- Each call to this function takes /O(1)/ time, so in total, it costs /O(log n)/.
carry :: LEq a -> BinomTree rk a -> BinomForest rk a -> BinomForest rk a -> BinomForest rk a
carry (<=) t0 f1 f2 = t0 `seq` case (f1, f2) of
	(Skip f1', Skip f2')	-> Cons t0 (merge (<=) f1' f2')
	(Skip f1', Cons t2 f2')	-> Skip (mergeCarry t0 t2 f1' f2')
	(Cons t1 f1', Skip f2')	-> Skip (mergeCarry t0 t1 f1' f2')
	(Cons t1 f1', Cons t2 f2')
				-> Cons t0 (mergeCarry t1 t2 f1' f2')
	(Nil, _f2)		-> incr (<=) t0 f2
	(_f1, Nil)		-> incr (<=) t0 f1
	where	cat = joinBin (<=)
		mergeCarry tA tB = carry (<=) (tA `cat` tB)

-- | Merges a binomial tree into a binomial forest.  If we are thinking
-- of the trees in the binomial forest as binary digits, this corresponds
-- to adding a power of 2.  This costs amortized /O(1)/ time.
incr :: LEq a -> BinomTree rk a -> BinomForest rk a -> BinomForest rk a
incr (<=) t f = t `seq` case f of
	Nil	-> Cons t Nil
	Skip f	-> Cons t f
	Cons t' f' -> Skip (incr (<=) (t `cat` t') f')
	where	cat = joinBin (<=)

-- | The carrying operation: takes two binomial heaps of the same rank @k@
-- and returns one of rank @k+1@.  Takes /O(1)/ time.
joinBin :: LEq a -> BinomTree rk a -> BinomTree rk a -> BinomTree (Succ rk) a
joinBin (<=) t1@(BinomTree x1 ts1) t2@(BinomTree x2 ts2)
	| x1 <= x2	= BinomTree x1 (Succ t2 ts1)
	| otherwise	= BinomTree x2 (Succ t1 ts2)

instance Functor Zero where
	fmap _ _ = Zero

instance Functor rk => Functor (Succ rk) where
	fmap f (Succ t ts) = Succ (fmap f t) (fmap f ts)

instance Functor rk => Functor (BinomTree rk) where
	fmap f (BinomTree x ts) = BinomTree (f x) (fmap f ts)

instance Functor rk => Functor (BinomForest rk) where
	fmap _ Nil = Nil
	fmap f (Skip ts) = Skip (fmap f ts)
	fmap f (Cons t ts) = Cons (fmap f t) (fmap f ts)

instance Foldable Zero where
	foldr _ z _ = z
	foldl _ z _ = z

instance Foldable rk => Foldable (Succ rk) where
	foldr f z (Succ t ts) = foldr f (foldr f z ts) t
	foldl f z (Succ t ts) = foldl f (foldl f z t) ts

instance Foldable rk => Foldable (BinomTree rk) where
	foldr f z (BinomTree x ts) = x `f` foldr f z ts
	foldl f z (BinomTree x ts) = foldl f (z `f` x) ts

instance Foldable rk => Foldable (BinomForest rk) where
	foldr _ z Nil = z
	foldr f z (Skip ts) = foldr f z ts
	foldr f z (Cons t ts) = foldr f (foldr f z ts) t
	foldl _ z Nil = z
	foldl f z (Skip ts) = foldl f z ts
	foldl f z (Cons t ts) = foldl f (foldl f z t) ts

instance Foldable MinQueue where
	foldr _ z Empty = z
	foldr f z (MinQueue _ x ts) = x `f` foldr f z ts
	foldl _ z Empty = z
	foldl f z (MinQueue _ x ts) = foldl f (z `f` x) ts
	foldl1 _ Empty = error "Error: foldl1 called on empty queue"
	foldl1 f (MinQueue _ x ts) = foldl f x ts

instance Traversable Zero where
	traverse _ _ = pure Zero

instance Traversable rk => Traversable (Succ rk) where
	traverse f (Succ t ts) = Succ <$> traverse f t <*> traverse f ts

instance Traversable rk => Traversable (BinomTree rk) where
	traverse f (BinomTree x ts) = BinomTree <$> f x <*> traverse f ts

instance Traversable rk => Traversable (BinomForest rk) where
	traverse _ Nil = pure Nil
	traverse f (Skip ts) = Skip <$> traverse f ts
	traverse f (Cons t ts) = Cons <$> traverse f t <*> traverse f ts
