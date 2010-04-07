{-# LANGUAGE TypeSynonymInstances, TypeFamilies #-}

module BootWrap where

import qualified BootExtract as B
import Heap

type PQ a = B.PQ a

instance Ord a => Heap (B.PQ a) where
    type Elem (B.PQ a) = a
    empty = B.empty (<=) (B.bootPQ (<=))
    insert = B.insert (<=) (B.bootPQ (<=))
    findMin = B.findMin (<=) (B.bootPQ (<=))
    extractMin = B.extractMin (<=) (B.bootPQ (<=))
    meld = B.meld (<=) (B.bootPQ (<=))
