{-# OPTIONS -fglasgow-exts #-}

import qualified ListBinom as L
import qualified NestedBinom as N
import Heap
import Random
import System.CPUTime

--mkHeap :: (Ord a, Heap h) => [a] -> h a
mkHeap [] = empty
mkHeap (x:xs) = insert x (mkHeap xs)

--unHeap :: (Ord a, Heap h) => h a -> [a]
biggest d x =
    case extractMin x of
      Nothing -> d
      Just (y,ys) -> biggest y ys

many = 25000

randomInts :: IO [Int]
randomInts = 
    do u <- getCPUTime
       let g = mkStdGen $ round $ sqrt $ fromIntegral u
       return $ take many $ randoms g

time f = 
    do l <- randomInts 
       start <- getCPUTime
       f l
       end <- getCPUTime
       return $ end-start

testList l =
    do let x :: L.BinomForest2 Int = mkHeap l
       print $ biggest 0 x

testNest l =
    do let x :: N.MinQueue Int = mkHeap l
       print $ biggest 0 x

trials = 40

main =
    do ls <- sequence $ map time $ replicate trials testList
       ns <- sequence $ map time $ replicate trials testNest
       putStrLn "List:"
       print $ (fromIntegral (sum ls))/(10^9 * fromIntegral trials)
       putStrLn "Nested:"
       print $ (fromIntegral (sum ns))/(10^9 * fromIntegral trials)
