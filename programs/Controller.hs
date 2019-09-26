{-# LANGUAGE RebindableSyntax, OverloadedStrings, GADTs #-}

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
  )

import Data.String( IsString(..) )

import qualified Lang
import Syntax
import TreeInterp()
import TreeRepr()
import Inference
import SparseLinAlg

pi :: Exp Double -> Exp Double -> Exp [Double] -> Exp Double
pi k vr vs =
  k * ( (vr - head 0.0 vs) +
        (sum (map (fun ("v" :: Lang.Name Double) $ vr - "v") vs)) / len vs)

plant :: Exp Double -> Exp Double
plant u = u

ex :: Com (Exp Bool)
ex = do
  "x" <-- val (cons (3 :: Val Integer) nil);
  "y" <-- val (cons true nil);
  "z" <-- head (4 :: Exp Integer) (tail "x")
  "b" <~~ unif(val $ cons true $ cons false nil)
  return "b"

t = Lang.interp [] ex

pmf :: IO [(Exp Bool, Double)]
pmf = sample_infer t (int 1000)

exact = solve_tree ((\(Lang.EVal (Lang.VBool b)) -> b) <$> t)
