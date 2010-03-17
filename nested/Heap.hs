module Heap where

class Heap t where
    empty :: t a
    findMin :: Ord a => t a -> Maybe a
    extractMin :: Ord a => t a -> Maybe (a,t a)
    insert :: Ord a => a -> t a -> t a
--    meld :: Ord a => t a -> t a -> t a