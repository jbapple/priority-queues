{-# LANGUAGE TypeFamilies #-}

module NestedBinom where

import Heap

instance Heap (MinQueue a) where
    type Elem (MinQueue a) = a
    empty = Vacant
    insert = tinsert
    findMin = tfindMin
    extractMin = textractMin
    meld = tmeld

data MinQueue a = Vacant | MinQueue {-# UNPACK #-} !Int a !(BinomHeap a)

type BinomHeap = BinomForest Zero

data BinomForest rk a = Nil 
                      | Skip !(BinomForest (Succ rk) a) 
                      | Cons {-# UNPACK #-} !(BinomTree rk a) !(BinomForest (Succ rk) a)

data BinomTree rk a = BinomTree a (rk a)

data Succ rk a = Succ {-# UNPACK #-} !(BinomTree rk a) (rk a)
    
data Zero a = Zero

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

incrExtract (Extract minKey (Succ kChild kChildren) ts)
    = Extract minKey kChildren (Cons kChild ts)
      
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

meldHelp :: Ord a => BinomForest rk a -> BinomForest rk a -> BinomForest rk a
meldHelp Nil y = y
meldHelp x Nil = x
meldHelp (Skip xs) (Skip ys) = Skip (meldHelp xs ys)
meldHelp (Skip xs) (Cons y ys) = Cons y (meldHelp xs ys)
meldHelp (Cons x xs) (Skip ys) = Cons x (meldHelp xs ys)
meldHelp (Cons x xs) (Cons y ys) = Skip $ insertHelp (link x y) (meldHelp xs ys)

tmeld Vacant y = y
tmeld x Vacant = x
tmeld (MinQueue n x xs) (MinQueue m y ys) =
    if x <= y
    then MinQueue (n+m) x (meldHelp xs (insertHelp (BinomTree y Zero) ys))
    else MinQueue (n+m) y (meldHelp ys (insertHelp (BinomTree x Zero) xs))