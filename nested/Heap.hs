{-# LANGUAGE TypeFamilies,FlexibleContexts #-}

module Heap where

class Heap t where
    type Elem t
    empty :: t
    findMin :: Ord (Elem t) => t -> Maybe (Elem t)
    extractMin :: Ord (Elem t) => t -> Maybe (Elem t,t)
    insert :: Ord (Elem t) => Elem t -> t -> t
    meld :: Ord (Elem t) => t -> t -> t