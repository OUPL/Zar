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

pot :: Exp Double -> Exp Double -> Exp Double
pot r theta = r * theta

main :: SyntaxM (Com (Exp Double))
main = do
  -- pot_r: Sample uniformly the pot's unknown resistance coefficient (\in {1,2,5,10})
  pot_r  <- unif $ cons (1.0 :: Exp Double) $ cons 2.0 $ cons 5.0 $ cons 10.0 $ nil

  -- theta: Sample the (controlled) measurement angle (\in {0.25,0.5,0.75})
  theta  <- unif $ cons (0.25:: Exp Double) $ cons 0.50$ cons 0.75$ nil

  -- r_meas: Measure the resistance
  r_meas <- pot pot_r theta

  -- Perform one experiment: setting theta=0.25 gives r_meas=2.5
  observe $ (theta == (0.25 :: Exp Double)) && (r_meas == (2.5 :: Exp Double))

  -- Given the experiment, return the likelihoods of the possible resistance coefficients.
  -- (In this case, pot_r=10.0 with probability 1.)
  return pot_r

t = Lang.interp Lang.initEnv $ runSyntax main

pmf :: IO [(Exp Double, Double)]
pmf = sample_infer t (int 1000)


