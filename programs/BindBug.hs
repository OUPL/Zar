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

main :: Com (Exp Bool)
main = do
  return $ all # Lang.ENil

exercise_bug = Lang.interp Lang.initEnv main

-- Library functions

all :: Exp ([Bool] -> Bool)
all = fun "l" $
  foldleft
  # Lang.EPair "l" 
      (Lang.EPair (Lang.EVal true)
            (fun ("p" :: Lang.Name (Bool, Bool))
               $ (fst ("p" :: Exp (Bool, Bool)))
                  && (snd ("p" :: Exp (Bool, Bool)))))

