-- {-# OPTIONS -fglasgow-exts #-}
-- {-# LANGUAGE KindAnnotations #-}

newtype Single t = Single t
data Empty t = Empty
newtype Unit t a = Unit (t a)
data Succ n t a = Simple (n Single a) (t a) (n Empty a)
                | SkewA (n Single a) (t a) (n Single a)
                | SkewB a (n Single a) (t a) (n Empty a)
data SkewForest f t = Uniq (UniqForest f t)
                    | Skip (SkewForest (Succ f) t)
                    | SkewForest (f Single t) (UniqForest f t)
data UniqForest f t = Nil
                    | Zero (UniqForest (Succ f) t)
                    | One (f Single t) (UniqForest (Succ f) t)
type SkewBinHeap = SkewForest Unit


insert x (Uniq Nil) = Uniq (One (Unit (Single x)) Nil)
insert x (Uniq (Zero y)) = Uniq (One (Unit (Single x)) y)
insert x (Uniq y@(One _ _)) = SkewForest (Unit (Single x)) y
insert x (Skip y) = Uniq (One (Unit (Single x)) (uniqify y))
insert x (SkewForest y ys) = 

uniqify :: Ord t => SkewForest (Succ f) t -> UniqForest (Succ f) t
uniqify (Uniq x) = x
uniqify (Skip x) = Zero (uniqify x)
uniqify (SkewForest x xs) = ins x xs

ins :: Ord a => Succ n Single a -> UniqForest (Succ n) a -> UniqForest (Succ n) a
ins x Nil = One x Nil
ins x (Zero xs) = One x xs
ins x (One y ys) = Zero (ins (link x y) ys)

meld x y = meldUniq (uniqify x) (uniqify y)

meldUniq :: Ord a => UniqForest (Succ n) a -> UniqForest (Succ n) a -> UniqForest (Succ n) a
meldUniq Nil y = y
meldUniq x Nil = x
meldUniq (Zero x) (Zero y) = Zero (meldUniq x y)
meldUniq (Zero x) (One y ys) = One y (meldUniq x ys)
meldUniq (One x xs) (Zero y) = One x (meldUniq xs y)
meldUniq (One x xs) (One y ys) = Zero (ins (link x y) (meldUniq xs ys))

empty (Simple l _ r) = Simple l Empty r
empty (SkewA l _ r) = SkewA l Empty r
empty (SkewB a l _ r) = SkewB a l Empty r

root (Simple _ (Single x) _) = x
root (SkewA _ (Single x) _) = x
root (SkewB _ _ (Single x) _) = x

link p q =
    let x = root p
        y = root q
    in if x <= y
       then Simple q (Single x) (empty p)
       else Simple p (Single y) (empty q)

skewLink v p q =
    let x = root p
        y = root q
    in if x <= v
       then if x <= y
            then SkewB v q (Single x) (empty p)
            else SkewB v p (Single y) (empty q)
       else if v <= y
            then SkewA p (Single v) q
            else SkewB v p (Single y) (empty q)

{-
data Big b s a = BigSimple (b a) a (s a)
                | BigSkewA (b a) a (b a)
                | BigSkewB a (b a) a (b a)
data Small b s a = SmallSimple (b a) (s a)
                | SmallSkewA (b a) (b a)
                | SmallSkewB a (b a) (b a)
data SizeForest b s t = Size (StepForest b s t)
                    | SizeForest (b s t) (UniqForest f t)
data StepForest f t = Nil
                    | Zero (UniqForest (Succ f) t)
                    | One (f Single t) (UniqForest (Succ f) t)
-}

{-
link p@(Simple l (Single c) r) q@(Simple x (Single y) z) =
    if c <= y
    then Simple q (Single c) (Simple l Empty r)
    else Simple p (Single y) (Simple x Empty z)
link p@(Simple l (Single c) r) q@(SkewA x (Single y) z) =
    if c <= y
    then Simple q (Single c) (Simple l Empty r)
    else Simple p (Single y) (SkewA x Empty z)
link p@(Simple l (Single c) r) q@(SkewB w x (Single y) z) =
    if c <= y
    then Simple q (Single c) (Simple l Empty r)
    else Simple p (Single y) (SkewB w x Empty z)
-}

{-
link p@(Simple l c r) q@(SkewA x y z) =
    if c <= Bogus y
    then Simple q c p
    else Simple p y q
        -}