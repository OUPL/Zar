{-# LANGUAGE RebindableSyntax, OverloadedStrings, GADTs, DataKinds #-}

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
        (sum (map # Lang.EPair (fun ("v" :: Lang.Name Double) $ vr - "v") vs))
          / ("float_of_int" # (len # vs)))

plant :: Exp Double -> Exp Double
plant u = u

within_range :: Exp [Double] -> Exp Double -> Exp Double -> Exp Bool
within_range vs vr eps =
  all (map #
    Lang.EPair (fun ("v" :: Lang.Name Double) $ (vr - eps <= "v") && ("v" <= vr + eps))
               vs)

main :: Com (Exp Bool)
main = do
  "vr" <-- (0.5 :: Exp Double)

  "k"  <~~ unif (val $ cons (0.5 :: Val Double) $ cons 1.0 $ cons 1.5 nil)

  "i"  <-- (0 :: Exp Integer)
  "v"  <-- (0.0 :: Exp Double)
  "vs" <-- (Lang.ECons "v" Lang.ENil :: Exp [Double])

  while ("i" < (20 :: Exp Integer)) $ do
    "u"     <-- pi "vr" "k" "vs"
    "dv"    <-- plant "u"
    "new_v" <-- "dv" + ("v" :: Exp Double)
    "v"     <-- ("new_v" :: Exp Double)
    "vs"    <-- Lang.ECons ("new_v" :: Exp Double) "vs"
    "i"     <-- "i" + (1 :: Exp Integer)

  return $ within_range (drop # Lang.EPair 5 "vs") "vr" 0.5

main2 :: Com (Exp Bool)
main2 = do
  return $ all $ Lang.ECons (Lang.EVal true) Lang.ENil

t = Lang.interp Lang.initEnv main

pmf :: IO [(Exp Bool, Double)]
pmf = sample_infer t (int 1000)

exact = solve_tree ((\(Lang.EVal (Lang.VBool b)) -> b) <$> t)

-- Library functions

sum :: Exp [Double] -> Exp Double
sum vs = 
  foldleft
  # Lang.EPair vs 
      (pair (0 :: Exp Double)
            (fun ("p" :: Lang.Name (Double, Double))
               $ (fst ("p" :: Exp (Double, Double)))
                  + (snd ("p" :: Exp (Double, Double)))))

all :: Exp [Bool] -> Exp Bool -- Exp ([Bool] -> Bool)
all l = 
  foldleft
  # Lang.EPair l 
      (pair (Lang.EVal true)
            (fun ("p" :: Lang.Name (Bool, Bool))
               $ (fst ("p" :: Exp (Bool, Bool)))
                  && (snd ("p" :: Exp (Bool, Bool)))))

