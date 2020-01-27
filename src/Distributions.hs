module Distributions where

import Data.Ratio

-- import Lang
import Tree
import Util

-- Tree that generates the uniform distribution cotree over a given
-- list (assumed to not contain duplicates).
uniform :: (Eq a, Show a) => [a] -> Tree a
uniform dom =
  set_label 0 $ canon $ go $
  (Leaf <$> dom) ++ (Hole 0 <$ [0 .. nextPow2 n - n - 1])
  where
    n = length dom
    go :: [Tree a] -> Tree a
    go [] = error "internal error in Distributions:uniform; please report"
    go [x] = x
    go xs = let m = length xs `div` 2 in
              Split Nothing (go $ take m xs) (go $ drop m xs)

reduce_rational :: Rational -> Rational
reduce_rational r = (n `div` c) % (d `div` c)
  where
    n = numerator r
    d = denominator r
    c = gcd n d

bernoulli :: Rational -> Tree Bool
bernoulli r =
  uniform $ (True <$ [0..n-1]) ++ (False <$ [0..d-n-1])
  where
    n = numerator $ reduce_rational r
    d = denominator $ reduce_rational r

fair_coin :: Tree Bool
fair_coin = bernoulli $ 1/2


-- | Experimental

-- uniform_prim :: (Show a, Typeable a) => Val ([a] -> Tree a)
-- uniform_prim = VPrim f
--   where
--     f :: Show a => Val [a] -> InterpM (Exp (Tree a))
--     f (VList l) = do
--       lbl <- freshLbl
--       return $ EVal $ VTree $ uniform lbl $ EVal <$> l
