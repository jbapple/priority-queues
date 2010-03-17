{-# OPTIONS -fglasgow-exts #-}

module NestedBinom where

import Heap

instance Heap MinQueue where
    empty = Vacant
    insert = tinsert
    findMin = tfindMin
    extractMin = textractMin
--    meld = tmeld

data MinQueue a = Vacant | MinQueue {-# UNPACK #-} !Int a !(BinomHeap a)

type BinomHeap = BinomForest Zero

data BinomForest rk a = Nil 
                      | Skip !(BinomForest (Succ rk) a) 
                      | Cons {-# UNPACK #-} !(BinomTree rk a) !(BinomForest (Succ rk) a)

data BinomTree rk a = BinomTree a (rk a)

data Succ rk a = Succ {-# UNPACK #-} !(BinomTree rk a) (rk a)
    
data Zero a = Zero

empty = Vacant

tfindMin Vacant = Nothing
tfindMin (MinQueue _ x _) = Just x

textractMin Vacant = Nothing
textractMin (MinQueue n x xs) = Just (x,
    case extractHeap xs of
      Nothing -> Vacant
      Just (y,ys) -> MinQueue (n-1) y ys)

extractHeap :: Ord a => BinomHeap a -> Maybe (a, BinomHeap a)
extractHeap ts = case extractBin ts of
                   Yes (Extract x _ ts')   -> Just (x, ts')
                   _                       -> Nothing

data Extract rk a = Extract a (rk a) (BinomForest rk a)
data MExtract rk a = No | Yes {-# UNPACK #-} !(Extract rk a)

incrExtract :: Extract (Succ rk) a -> Extract rk a
incrExtract (Extract minKey (Succ kChild kChildren) ts)
    = Extract minKey kChildren (Cons kChild ts)
      
incrExtract' :: Ord a => BinomTree rk a -> Extract (Succ rk) a -> Extract rk a
incrExtract' t (Extract minKey (Succ kChild kChildren) ts)
    = Extract minKey kChildren (Skip (insertHelp (t `link` kChild) ts))

                    
extractBin :: Ord a => BinomForest rk a -> MExtract rk a
extractBin Nil = No
extractBin (Skip f) = case extractBin f of
                             Yes ex  -> Yes (incrExtract ex)
                             No      -> No
extractBin (Cons t@(BinomTree x ts) f) = Yes $ case extractBin f of
                                                 Yes ex@(Extract minKey _ _)
                                                     | minKey < x    -> incrExtract' t ex
                                                 _                       -> Extract x ts (Skip f)

{-
revSucc :: Succ rk a -> BinomForest (Succ rk) a -> (rk a, BinomForest rk a)
revSucc (Succ x xs) ys = (xs,Cons x ys)

deleteMin :: Ord a => a -> (a,rk a,BinomForest rk a) -> (a,rk a,BinomForest
-}

--link :: BinomTree rk a -> BinomTree rk a -> BinomTree (Succ rk) a
link x@(BinomTree v p) y@(BinomTree w q) =
    if v <= w
    then BinomTree v (Succ y p)
    else BinomTree w (Succ x q)

insertHelp :: Ord a => BinomTree rk a -> BinomForest rk a -> BinomForest rk a
insertHelp x Nil = Cons x Nil
insertHelp x (Skip ys) = Cons x ys
insertHelp x (Cons y ys) = Skip $ insertHelp (link x y) ys

tinsert x Vacant = MinQueue 1 x Nil
tinsert x (MinQueue n y ys) =
    if x <= y
    then MinQueue (n+1) x (insertHelp (BinomTree y Zero) ys)
    else MinQueue (n+1) y (insertHelp (BinomTree x Zero) ys)
{-
meldHelp :: Ord a => BinomForest rk a -> BinomForest rk a -> BinomForest rk a
meldHelp Nil y = y
meldHelp x Nil = Nil
meldHelp (Skip xs) (Skip ys) = Skip (meldHelp xs ys)
meldHelp (Skip xs) (Cons y ys) = Cons y (meldHelp xs ys)
meldHelp (Cons x xs) (Skip ys) = Cons x (meldHelp xs ys)
meldHelp (Cons x xs) (Cons y ys) = Skip $ insertHelp (link x y) (meldHelp xs ys)

tmeld :: Ord a => MinQueue a -> MinQueue a -> MinQueue a
tmeld Vacant y = y
tmeld x Vacant = x
tmeld (MinQueue n x xs) (MinQueue m y ys) =
    if x <= y
    then MinQueue (n+m) x (meldHelp xs (insertHelp (BinomTree y Zero) ys))
    else MinQueue (n+m) y (meldHelp ys (insertHelp (BinomTree x Zero) xs))
-}

{-
root (BinomTree2 _ v _) = v
rank (BinomTree2 i _ _) = i

ins x [] = [x]
ins x (y:ys) = 
    if rank x < rank y
    then x:y:ys
    else (link x y):ys

getMin t [] = (t,[])
getMin t (y:ys) =
    let (z,zs) = getMin y ys
    in if root t <= root z
       then (t,y:ys)
       else (z,t:zs)

deleteMin Empty = Empty
deleteMin (NonEmpty _ y) = 
    case deleteMinHelp y of
      Nothing -> Empty
      Just (x,xs) -> NonEmpty x xs

deleteMinHelp [] = Nothing
deleteMinHelp (x:xs) = Just $
    let (BinomTree2 i v c,ys) = getMin x xs
    in (v,meldHelp (reverse c) ys)

-}

data S n
data Z

data BinomForestG n a where
    Devoid :: BinomForestG n a
    Single :: a -> BinomTreeG n a -> BinomForestG n a
                      
data BinomTreeG n a = BinomTreeG a (BinomList n a)

data BinomList n a where
    Stop :: BinomList Z a
    More :: BinomTreeG (S n) a ->
            BinomList n a ->
            BinomList (S n) a