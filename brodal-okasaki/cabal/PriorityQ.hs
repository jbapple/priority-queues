{-# LANGUAGE TypeSynonymInstances #-}

module PriorityQ where

import qualified BootExtract as B

type PQ = B.BootWrap

class PriorityQ t where
    empty      :: Ord a => t a
    insert     :: Ord a => a -> t a -> t a
    findMin    :: Ord a => t a -> Maybe a
    extractMin :: Ord a => t a -> Maybe (a, t a)
    meld       :: Ord a => t a -> t a -> t a
    toList     :: Ord a => t a -> [a]

instance PriorityQ PQ where
    empty      = B.empty      (<=) (B.bootPQ (<=))
    insert     = B.insert     (<=) (B.bootPQ (<=))
    findMin    = B.findMin    (<=) (B.bootPQ (<=))
    extractMin = B.extractMin (<=) (B.bootPQ (<=))
    meld       = B.meld       (<=) (B.bootPQ (<=))
    toList     = B.toList     (<=) (B.bootPQ (<=))