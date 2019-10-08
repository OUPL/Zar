{-# LANGUAGE RebindableSyntax, OverloadedStrings, GADTs, DataKinds, ScopedTypeVariables #-}

module Controller where

import Prelude hiding
  ( (>>)
  , (>>=)
  , (+)
  , (-)
  , (*)
  , (/)
  , (&&)
  , (||)
  , (==)
  , (<)
  , (<=)
  , not
  , return
  , fromRational
  , fromInteger
  , negate
  , ifThenElse
  , head
  , tail
  , map
  , sum
  , all
  , drop
  , fst
  , snd

  , pi
  )

import qualified Prelude

import Data.String( IsString(..) )
import Data.Typeable (Typeable)

import qualified Lang
import List
import Syntax
import TreeInterp (InterpM)
import TreeRepr()
import Inference
import SparseLinAlg

{- TODO: 
   * Do some more experiments with stability invariants. -}

pi :: Exp Double -> Exp Double -> Exp [Double] -> Exp Double
pi k vr vs =
  k * ( (vr - head 0.0 vs) +
        (sum (map # pair (fun ("v" :: Lang.Name Double) $ vr - "v") vs))
          / (float_of_int # (len # vs)))

plant :: Exp Double -> Exp Double
plant u = u

within_range :: Exp [Double] -> Exp Double -> Exp Double -> Exp Bool
within_range vs vr eps =
  all (map #
    pair (fun ("v" :: Lang.Name Double) $ (vr - eps <= "v") && ("v" <= vr + eps))
         vs)

main :: SyntaxM (Com (Exp Bool))
main = do
  vr <- (0.5 :: Exp Double)
  k  <- unif (cons (0.5 :: Exp Double) $ cons 1.0 $ cons 1.5 nil)
  i  <- (0 :: Exp Integer)
  v  <- (0.0 :: Exp Double)
  vs <- cons (v :: Exp Double) nil

  while (i < 20) $ do
    u     <- pi vr k vs
    dv    <- plant u
    new_v <- dv + v
    v     <-- new_v
    vs    <-- cons new_v vs
    i     <-- i + (1 :: Exp Integer)
    skip

  return $ within_range (drop # pair 5 vs) vr 0.5

t = Lang.interp Lang.initEnv $ runSyntax main

pmf :: IO [(Exp Bool, Double)]
pmf = sample_infer t (int 1000)

exact = solve_tree ((\(Lang.EVal (Lang.VBool b)) -> b) <$> t)

-- Library functions

sum :: Exp [Double] -> Exp Double
sum vs = 
  foldleft
  # pair vs 
      (pair (0 :: Exp Double)
            (fun ("p" :: Lang.Name (Double, Double))
               $ (fst ("p" :: Exp (Double, Double)))
                  + (snd ("p" :: Exp (Double, Double)))))

all :: Exp [Bool] -> Exp Bool -- Exp ([Bool] -> Bool)
all l = 
  foldleft
  # pair l 
      (pair true
            (fun ("p" :: Lang.Name (Bool, Bool))
               $ (fst ("p" :: Exp (Bool, Bool)))
                  && (snd ("p" :: Exp (Bool, Bool)))))

