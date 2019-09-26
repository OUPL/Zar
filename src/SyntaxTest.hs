{-# LANGUAGE RebindableSyntax #-}

module SyntaxTest where

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
  )

import Data.Proxy

import qualified Lang
import Syntax
import TreeInterp()
import TreeRepr()
import Inference

x :: Lang.Name [Integer]
x = ("x", Proxy)

ex :: Com (Exp Integer)
ex = do
  x <-- Lang.EVal (cons 3 nil);
  return (head (Lang.EVal 4) (tail (Lang.EVar x)))

t = Lang.interp [] ex

pmf :: IO [(Exp Integer, Double)]
pmf = sample_infer t (int 1000)
