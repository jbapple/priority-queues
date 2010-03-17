module ListBinom where

import Heap
import Debug.Trace

instance Heap BinomForest2 where
    empty = Empty
    insert = tinsert
    findMin = tfindMin
    extractMin = textractMin
--    meld = tmeld

data BinomForest2 a = Empty
                    | NonEmpty a [BinomTree2 Int a] deriving (Show)

data BinomTree2 v a = BinomTree2 v a [BinomTree2 Int a] deriving (Show)

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
getMin t@(BinomTree2 _ v _) (y:ys) =
    let (z@(BinomTree2 _ w _),zs) = getMin y ys
    in if v <= w
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

--------------------
{-
data Extract a = Extract a [BinomTree2 Int a] [BinomTree2 Int a] deriving (Show)

--incrExtract :: Extract a -> Extract a
incrExtract (Extract minKey (kChild:kChildren) ts)
    = Extract minKey kChildren (kChild:ts)

--incrExtract' :: Ord a => BinomTree2 Int a -> Extract a -> Extract a
incrExtract' t (Extract minKey (kChild:kChildren) ts)
    = Extract minKey kChildren (ins (t `link` kChild) ts)

data MExtract a = No | Yes {-# UNPACK #-} !(Extract a)

--extractBin :: Ord a => Int -> [BinomTree2 Int a] -> MExtract a
extractBin _ [] = No
extractBin n (t@(BinomTree2 i x ts):f) = trace "" {-(show (n,t,f))-} $
    if n > 0
    then case extractBin (n-1) (t:f) of
           No -> No
           Yes ex -> Yes (incrExtract ex)
    else Yes $ case f of
                 [] -> Extract x ts f
                 (y:ys) -> case extractBin (rank y - i) f of
                             Yes ex@(Extract minKey _ _) | minKey < x    -> trace (show (t,f,n,rank y,i,ex)) $ incrExtract' t ex
                             _                       -> Extract x ts f
{-
extractBin (Skip f) = 
    case extractBin f of
      Yes ex  -> Yes (incrExtract ex)
      No      -> No
extractBin (Cons t@(BinomTree x ts) f) = 
    Yes $ case extractBin f of
            Yes ex@(Extract minKey _ _) | minKey < x    -> incrExtract' t ex
            _                       -> Extract x ts (Skip f)
-}

--extractHeap :: Ord a => [BinomTree2 Int a] -> Maybe (a, [BinomTree2 Int a])
extractHeap [] = Nothing
extractHeap (t:ts) = 
    case extractBin (rank t) (t:ts) of
      Yes (Extract x _ ts') -> Just (x, ts')
      _                       -> Nothing


textractMin Empty = Nothing
textractMin (NonEmpty x xs) = Just (x,
    case extractHeap xs of
      Nothing -> Empty
      Just (y,ys) -> NonEmpty y ys)

{-
                 





      

                    
-}

(BinomTree2 1 (-872973571) [BinomTree2 0 2098126276 []],[BinomTree2 1 (-1464289892) [BinomTree2 0 (-944620574) []],BinomTree2 1 (-848719277) [BinomTree2 0 1272308198 []],BinomTree2 1 547563048 [BinomTree2 0 1652820443 []],BinomTree2 1 790757905 [BinomTree2 0 1854045126 []]],0,1,1,Extract (-1464289892) [BinomTree2 0 (-944620574) []] [BinomTree2 1 (-848719277) [BinomTree2 0 1272308198 []],BinomTree2 1 547563048 [BinomTree2 0 1652820443 []],BinomTree2 1 790757905 [BinomTree2 0 1854045126 []]])

(BinomTree2 1 (-1512044831) [BinomTree2 0 1213615102 []],[BinomTree2 1 (-1840619074) [BinomTree2 0 (-1797528184) []],BinomTree2 1 (-872973571) [BinomTree2 0 2098126276 []],BinomTree2 1 (-1464289892) [BinomTree2 0 (-944620574) []],BinomTree2 1 (-848719277) [BinomTree2 0 1272308198 []],BinomTree2 1 547563048 [BinomTree2 0 1652820443 []],BinomTree2 1 790757905 [BinomTree2 0 1854045126 []]],0,1,1,Extract (-1840619074) [BinomTree2 0 (-1797528184) []] [BinomTree2 1 (-872973571) [BinomTree2 0 2098126276 []],BinomTree2 1 (-1464289892) [BinomTree2 0 (-944620574) []],BinomTree2 1 (-848719277) [BinomTree2 0 1272308198 []],BinomTree2 1 547563048 [BinomTree2 0 1652820443 []],BinomTree2 1 790757905 [BinomTree2 0 1854045126 []]])

(BinomTree2 1 79061793 [BinomTree2 0 540132651 []],
  [BinomTree2 1 (-1512044831) 
     [BinomTree2 0 1213615102 []],
   BinomTree2 1 (-1840619074) 
     [BinomTree2 0 (-1797528184) []],
   BinomTree2 1 (-872973571) 
     [BinomTree2 0 2098126276 []],
   BinomTree2 1 (-1464289892) 
     [BinomTree2 0 (-944620574) []],
   BinomTree2 1 (-848719277) 
     [BinomTree2 0 1272308198 []],
   BinomTree2 1 547563048 
     [BinomTree2 0 1652820443 []],
   BinomTree2 1 790757905 
     [BinomTree2 0 1854045126 []]]
,0
,1
,1
,Extract (-1840619074) [] [BinomTree2 2 (-1797528184) [BinomTree2 1 (-872973571) [BinomTree2 0 2098126276 []],BinomTree2 1 (-1512044831) [BinomTree2 0 1213615102 []]],BinomTree2 1 (-1464289892) [BinomTree2 0 (-944620574) []],BinomTree2 1 (-848719277) [BinomTree2 0 1272308198 []],BinomTree2 1 547563048 [BinomTree2 0 1652820443 []],BinomTree2 1 790757905 [BinomTree2 0 1854045126 []]])
-}