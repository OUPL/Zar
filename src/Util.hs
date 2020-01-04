module Util where

-- import Control.Monad
import Data.Bifunctor
import Debug.Trace (trace)

-- debug = const id
debug = trace

allEq :: Eq a => [a] -> Bool
allEq [] = True
allEq (x:xs) = all (== x) xs

-- | Compose a function with itself n times. (nth rather than twice)
nTimes :: Int -> (a -> a) -> (a -> a)
nTimes 0 _ = id
nTimes 1 f = f
nTimes n f = f . nTimes (n-1) f

-- All elements which occur more than once.
doubles :: Eq a => [a] -> [a]
doubles = go []
  where
    go :: Eq a => [a] -> [a] -> [a]
    go _ [] = []
    go seen (x:xs) =
      (if x `elem` seen then [x] else []) ++ go (x:seen) xs

-- First power of 2 greater than or equal to n.
nextPow2 :: Int -> Int
nextPow2 = go 1
  where
    go :: Int -> Int -> Int
    go p n = if n <= p then p else go (p*2) n

classify :: Eq a => [a] -> [[a]]
classify = classifyBy (==)

classifyBy :: (a -> a -> Bool) -> [a] -> [[a]]
classifyBy _ []     = []
classifyBy eq (x:xs) = (x:filter (eq x) xs)
                       : classifyBy eq (filter (neq x) xs)
  where
  neq x1 x2 = not (eq x1 x2)

counts :: Eq a => [a] -> [(a,Int)]
counts = map headLength . classify

headLength :: [a] -> (a,Int)
headLength xs = (head xs, length xs)

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x:_) = Just x

bimap' :: (a -> b) -> (a, a) -> (b, b)
bimap' f = bimap f f

-- We use this with f = Tree, m = InterpM, a = St.
-- mapJoin :: (Traversable f, Monad f, Monad m) =>
--                 f a -> (a -> m (f b)) -> m (f b)
-- mapJoin x g = join <$> (mapM g x)

isSubsetOf :: Eq a => [a] -> [a] -> Bool
isSubsetOf xs ys = all (`elem` ys) xs

setEq :: Eq a => [a] -> [a] -> Bool
setEq xs ys = isSubsetOf xs ys && isSubsetOf ys xs

tupleFun :: (a -> b) -> (a -> c) -> a -> (b, c)
tupleFun f g x = (f x, g x)

modify_at :: Int -> (a -> a) -> [a] -> [a]
modify_at i f l = let (l1, x:l2) = splitAt i l in l1 ++ f x : l2

set_at :: Int -> a -> [a] -> [a]
set_at i x = modify_at i $ const x