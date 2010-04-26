{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables #-}

module Finger where

import qualified Data.FingerTree as F
import qualified Data.Monoid as M
import Array

class Ord (Component t) => MultiDim t where
    dimension :: t -> Int
    type Component t :: *
    get :: t -> Int -> Component t

data Least t = Least (Array Int t)
             | None deriving (Show)

arrayZipWithIndex :: Ix i => (i -> e -> e -> e) -> Array i e -> Array i e -> Array i e
arrayZipWithIndex f x y =
    let ixs = assocs x -- O(|x|)
        ys = elems y   -- O(|y|)
        g (a,b) c = f a b c -- O(|max a . f(a)|)
        ansList = zipWith g ixs ys -- O((max a . f(a)) (min |x| |y|))
        range = bounds x -- O(1)
    in listArray range ansList -- O((max a . f(a)) (min |x| |y|))

instance MultiDim t => M.Monoid (Least t) where
    mempty = None
    mappend (Least x) (Least y) = 
        let minAt i a b = if get a i <= get b i
                          then a
                          else b
        in Least (arrayZipWithIndex minAt x y) -- O(min |x| |y|)
    mappend None y = y
    mappend x None = x

newtype Dim t = Dim {unDim :: t} deriving (Show)

instance MultiDim t => F.Measured (Least t) (Dim t) where
    measure (Dim x) = 
        let k = dimension x
        in Least $ listArray (1,k) (replicate k x) -- O(k)

newtype KDHeap t = KDHeap (F.FingerTree (Least t) (Dim t)) deriving (Show)

insert :: MultiDim t => t -> KDHeap t -> KDHeap t
insert x (KDHeap y) = KDHeap ((Dim x) F.<| y) -- O(k)

empty :: MultiDim t => KDHeap t
empty = KDHeap (F.empty) -- O(1)

meld :: MultiDim t => KDHeap t -> KDHeap t -> KDHeap t
meld (KDHeap x) (KDHeap y) = KDHeap (x F.>< y) -- O(k lg(min |x| |y|))

extractMink :: MultiDim t => Int -> KDHeap t -> Maybe (t, KDHeap t)
extractMink k (KDHeap xs) =
    case F.measure xs of
      None -> Nothing
      Least top -> 
          Just $
          let leastK = get (top ! k) k
              moreK (Least y) = get (y ! k) k >= leastK
              (hd,tl) = F.split moreK xs -- O(lg |xs|)
              Dim ans F.:< rest = F.viewl tl -- O(1)
          in (ans, KDHeap (hd F.>< rest)) -- O(k lg |xs|)

findAny :: MultiDim t => KDHeap t -> Maybe t
findAny (KDHeap x) = 
    case F.viewl x of
      (Dim y) F.:< _ -> Just y -- O(1)
      _ -> Nothing

findMink :: MultiDim t => Int -> KDHeap t -> Maybe t
findMink k (KDHeap xs) =
    case F.measure xs of
      None -> Nothing
      Least top -> 
          Just $ (top ! k) -- O(1)