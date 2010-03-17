{-# LANGUAGE CPP,TypeFamilies #-}

module QuickBinom (insert, extract, fromList, toAscList, PQueue)  where


#ifdef __GLASGOW_HASKELL__
import GHC.Exts (build)
#endif
import qualified Heap as H

instance H.Heap (PQueue a) where
    type H.Elem (PQueue a) = a
    empty = Empty
    insert = QuickBinom.insert
    findMin = error "PQueue findMin"
    meld = error "PQueue meld"
    extractMin = QuickBinom.extractMin

data PQueue a = Empty | PQueue {-# UNPACK #-} !Int (BinomQueue a)
-- type PQueue = BinomQueue
data BinomQueue a = Nil | Cons {-# UNPACK #-} !Int {-# UNPACK #-} !(BinHeap a) (BinomQueue a)
data BinomQueue' a = Nil' | Cons' {-# UNPACK #-} !(BinHeap a) (BinomQueue' a)
data BinHeap a = Bin a (BinomQueue' a)

getMin i t Nil = (i,t,Nil)
getMin i t@(Bin r _) rs@(Cons k y ys) =
    let (j,z@(Bin s _),zs) = getMin k y ys
    in if r <= s
       then (i,t,rs)
       else (j,z,Cons i t zs)

extractMin Empty = Nothing
extractMin (PQueue n y) = 
    case deleteMinHelp y of
      Nothing -> Nothing
      Just (x,xs) -> Just (x,PQueue (n-1) xs)


deleteMinHelp Nil = Nothing
deleteMinHelp (Cons k x xs) = Just $
    let (i,Bin v c,ys) = getMin k x xs
    in (v,merge (<=) (revQueue i c) ys)


data Extract a = NoExtract | YesExtract a {-# UNPACK #-} !Int (BinomQueue' a) (BinomQueue a)

revQueue :: Int -> BinomQueue' a -> BinomQueue a
revQueue k = revQueue' (k-1) Nil where
	revQueue' :: Int -> BinomQueue a -> BinomQueue' a -> BinomQueue a
	revQueue' k rev ts = k `seq` case ts of
		Cons' t ts	-> revQueue' (k-1) (Cons k t rev) ts
		Nil'		-> rev

tip :: a -> BinHeap a
tip x = Bin x Nil'


extract :: Ord a => PQueue a -> Maybe (a, PQueue a)
extract Empty = Nothing
extract (PQueue n h) = case extractQueue (<=) h of
	NoExtract	-> Nothing
	YesExtract x' rk ts tss
		-> Just (x', PQueue (n-1) (merge (<=) (revQueue rk ts) tss))

insert :: Ord a => a -> PQueue a -> PQueue a
insert x Empty = PQueue 1 (Cons 0 (tip x) Nil)
insert x (PQueue n h) = PQueue (n+1) (ins x h)
	where ins = carry1 (<=) 0 . tip

fromList :: Ord a => [a] -> PQueue a
fromList = foldr insert Empty

{-# INLINE toAscList #-}
-- | /O(n log n)/.  Extracts the elements of the priority queue in ascending order.
toAscList :: Ord a => PQueue a -> [a]
#ifdef __GLASGOW_HASKELL__
toAscList q = build (\ c nil -> foldrAsc c nil q)
#else
toAscList = foldrAsc (:) []
#endif

foldrAsc :: Ord a => (a -> b -> b) -> b -> PQueue a -> b
foldrAsc f z (PQueue _ h) = foldrHeap (<=) f z h
foldrAsc _ z _ = z

foldrHeap :: (a -> a -> Bool) -> (a -> b -> b) -> b -> BinomQueue a -> b
foldrHeap (<=) f z = foldrH' where
	foldrH' h = case extractQueue (<=) h of
		NoExtract	-> z
		YesExtract x rk ts tss
			-> x `f` foldrH' (merge (<=) (revQueue rk ts) tss)

{-# NOINLINE extractQueue #-}
extractQueue :: (a -> a -> Bool) -> BinomQueue a -> Extract a
extractQueue _ Nil = NoExtract
extractQueue (<=) (Cons k t@(Bin x ts) tss) = case extractQueue (<=) tss of
	NoExtract	-> YesExtract x k ts tss
	YesExtract minK rk minKids rest
		| x <= minK	-> YesExtract x k ts tss
		| otherwise	-> YesExtract minK rk minKids (Cons k t rest)

meldH :: (a -> a -> Bool) -> Int -> BinHeap a -> BinHeap a -> BinHeap a
meldH (<=) k t1@(Bin x1 ts1) t2@(Bin x2 ts2)
	| k `seq` x1 <= x2	= Bin x1 (Cons' t2 ts1)
	| otherwise		= Bin x2 (Cons' t1 ts2)

merge :: (a -> a -> Bool) -> BinomQueue a -> BinomQueue a -> BinomQueue a
merge (<=) ts1 ts2 = case (ts1, ts2) of
	(Nil, _)	-> ts2
	(_, Nil)	-> ts1
	(Cons k1 t1 ts1', Cons k2 t2 ts2') -> case compare k1 k2 of
		LT	-> Cons k1 t1 (merge (<=) ts1' ts2)
		EQ	-> carry (<=) (k1 + 1) (meld k1 t1 t2) ts1' ts2'
		GT	-> Cons k2 t2 (merge (<=) ts1 ts2')
	where	meld = meldH (<=)

-- Invariant: k0 <= rank of first trees in ts1, ts2
carry :: (a -> a -> Bool) -> Int -> BinHeap a -> BinomQueue a -> BinomQueue a -> BinomQueue a
carry (<=) k0 t0 ts1 ts2 = k0 `seq` t0 `seq` case (ts1, ts2) of
	(Nil, _)	-> carry1 (<=) k0 t0 ts2
	(_, Nil)	-> carry1 (<=) k0 t0 ts1
	(Cons k1 t1 ts1', Cons k2 t2 ts2') -> case (k0 == k1, k0 == k2) of
		(True, True)	-> Cons k0 t0 (carry (<=) (k0+1) (meld k0 t1 t2) ts1' ts2')
		(True, False)	-> carry (<=) (k0+1) (meld k0 t0 t1) ts1' ts2
		(False, True)	-> carry (<=) (k0+1) (meld k0 t0 t2) ts1 ts2'
		(False, False)	-> Cons k0 t0 $ case compare k1 k2 of
			LT	-> Cons k1 t1 (merge (<=) ts1' ts2)
			EQ	-> carry (<=) (k1 + 1) (meld k1 t1 t2) ts1' ts2'
			GT	-> Cons k2 t2 (merge (<=) ts1 ts2')
	where	meld = meldH (<=)

carry1 :: (a -> a -> Bool) -> Int -> BinHeap a -> BinomQueue a -> BinomQueue a
carry1 (<=) k0 t0 ts = k0 `seq` t0 `seq` case ts of
	Cons k t ts'
		| k0 == k	-> carry1 (<=) (k0 + 1) (meld k0 t0 t) ts'
	_			-> Cons k0 t0 ts
	where	meld = meldH (<=)
