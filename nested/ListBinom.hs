{-# LANGUAGE TypeFamilies #-}

module ListBinom where

import Heap

instance Heap (BinomForest2 a) where
    type Elem (BinomForest2 a) = a
    empty = Empty
    insert = tinsert
    findMin = tfindMin
    extractMin = textractMin
    meld = tmeld

data BinomForest2 a = Empty
                    | NonEmpty a [BinomTree2 a] deriving (Show)

data BinomTree2 a = BinomTree2 {-# UNPACK #-} !Int a [BinomTree2 a] deriving (Show)

textractMin Empty = Nothing
textractMin t@(NonEmpty x _) = Just (x, deleteMin t)

tfindMin Empty = Nothing
tfindMin (NonEmpty x _) = Just x

root (BinomTree2 _ v _) = v
rank (BinomTree2 i _ _) = i

link x@(BinomTree2 i v p) y@(BinomTree2 j w q) =
    if v <= w
    then BinomTree2 (i+1) v (y:p)
    else BinomTree2 (j+1) w (x:q)

ins x [] = [x]
ins x (y:ys) = 
    if rank x < rank y
    then x:y:ys
    else ins (link x y) ys

tinsert x Empty = NonEmpty x []
tinsert x (NonEmpty y ys) =
    if x <= y
    then NonEmpty x (insertHelp y ys)
    else NonEmpty y (insertHelp x ys)
insertHelp x ys = ins (BinomTree2 0 x []) ys

tmeld Empty y = y
tmeld x Empty = x
tmeld (NonEmpty x xs) (NonEmpty y ys) =
    if x <= y
    then NonEmpty x (meldHelp xs (insertHelp y ys))
    else NonEmpty y (meldHelp ys (insertHelp x xs))

meldHelp [] y = y
meldHelp x [] = x
meldHelp (x:xs) (y:ys) =
    case compare (rank x) (rank y) of
      LT -> x:(meldHelp xs (y:ys))
      GT -> y:(meldHelp (x:xs) ys)
      EQ -> ins (link x y) (meldHelp xs ys)

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
    let (BinomTree2 _ v c,ys) = getMin x xs
    in (v,meldHelp (reverse c) ys)