{-# LANGUAGE ScopedTypeVariables #-}

import qualified ListBinom as L
import qualified NestedBinom as N
import qualified Labor as B
import qualified ExtractedSkew as E
import qualified QuickBinom as Q
import qualified BootWrap as M
import Heap
import Random
import System.CPUTime
import System.Mem

mkHeap [] = empty
mkHeap (x:xs) = insert x (mkHeap xs)

biggestCheck d x =
    case extractMin x of
      Nothing -> d
      Just (y,ys) -> 
          if y < d
          then error "Heapsaster!"
          else biggestCheck y ys

biggestNoCheck d x =
    case extractMin x of
      Nothing -> d
      Just (y,ys) -> biggestNoCheck y ys

biggest x y = biggestNoCheck x y

many = 25000

randomInts :: IO [Int]
randomInts = 
    do u <- getCPUTime
       let g = mkStdGen $ round $ sqrt $ fromIntegral u
       return $ take many $ randoms g

time f = 
    do l <- randomInts 
       performGC
       start <- getCPUTime
       f l
       end <- getCPUTime
       return $ end-start

testList l =
    do let x :: L.BinomForest2 Int = mkHeap l
       print $ biggest minBound x

testNest l =
    do let x :: N.MinQueue Int = mkHeap l
       print $ biggest minBound x

testQuick l =
    do let x :: Q.PQueue Int = mkHeap l
       print $ biggest minBound x

testExtracted l =
    do let x :: E.PreQ Int = mkHeap l
       print $ biggest minBound x

testLabor l =
    do let x :: B.MinQueue Int = mkHeap l
       print $ biggest minBound x

testBoot l =
    do let x :: M.PQ Int = mkHeap l
       print $ biggest minBound x

trials = 40

main =
    do {-ls <- sequence $ map time $ replicate trials testList
       ns <- sequence $ map time $ replicate trials testNest
       qs <- sequence $ map time $ replicate trials testQuick
       es <- sequence $ map time $ replicate trials testExtracted-}
       bs <- sequence $ map time $ replicate trials testLabor
       ms <- sequence $ map time $ replicate trials testBoot {-
       putStrLn "List:"
       print $ (fromIntegral (sum ls))/(10^9 * fromIntegral trials)
       putStrLn "Nested:"
       print $ (fromIntegral (sum ns))/(10^9 * fromIntegral trials)
       putStrLn "Quick:"
       print $ (fromIntegral (sum qs))/(10^9 * fromIntegral trials)
       putStrLn "Extracted:"
       print $ (fromIntegral (sum es))/(10^9 * fromIntegral trials) -}
       putStrLn "Labor:"
       print $ (fromIntegral (sum bs))/(10^9 * fromIntegral trials)
       putStrLn "Boot:"
       print $ (fromIntegral (sum ms))/(10^9 * fromIntegral trials)
