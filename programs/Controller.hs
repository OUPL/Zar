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

  , pi
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
        (sum # (map # Lang.EPair (fun ("v" :: Lang.Name Double) $ vr - "v") vs))
          / ("float_of_int" # (len # vs)))

plant :: Exp Double -> Exp Double
plant u = u

within_range :: Exp [Double] -> Exp Double -> Exp Double -> Exp Bool
within_range vs vr eps =
  all # Lang.EPair (fun ("v" :: Lang.Name Double) $ (vr - eps <= "v") && ("v" <= vr + eps)) vs

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
    "i"       <-- "i" + (1 :: Exp Integer)

  return $ within_range "vs" "vr" 0.4


t = Lang.interp Lang.initEnv main

pmf :: IO [(Exp Bool, Double)]
pmf = sample_infer t (int 1000)

exact = solve_tree ((\(Lang.EVal (Lang.VBool b)) -> b) <$> t)
