{-# LANGUAGE FlexibleInstances, TypeFamilies #-}

module FingerTest where

import qualified Finger as F
import qualified Test.QuickCheck as Q

instance Ord t => F.MultiDim (t,t,Int) where
    dimension _ = 2
    type F.Component (t,t,Int) = t
    get (x,_,_) 1 = x
    get (_,y,_) 2 = y

instance (Q.Arbitrary t, F.MultiDim t) => Q.Arbitrary (F.KDHeap t) where
    arbitrary =
        do b <- Q.arbitrary
           (if b
            then do v <- Q.arbitrary
                    return $ F.insert v F.empty
            else do x <- Q.arbitrary
                    y <- Q.arbitrary
                    return $ F.meld x y)

--instance Show (F.MultiDim t, Show t) => Show (F.KDHeap t) where
    

findExtract :: F.KDHeap (Int,Int,Int) -> Int -> Bool
findExtract x n =
    let k = 1 + n`mod`2 in
    case (F.findMink k x, F.extractMink k x) of
      (Nothing, Nothing) -> True
      (Just x, Just (y,_)) -> x == y
      _ -> False


