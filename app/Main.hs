{-# LANGUAGE GADTs #-}
module Main where

import Control.Monad.State
import Data.Bifunctor (first, second)
import Data.List (nub, sort, (\\))
import Data.Proxy
import System.Environment (getArgs)
import System.Random
import Text.Megaparsec.Error

import Cotree
import Datatypes
import Inference
import Interp (runInterp')
import Lang (Type(..), Val(..))
import ListTree
import Parser (parse)
import Primitives
import Sample (eval_sampler, n_samples)
import Sexp
import Tree
import Tycheck (SomeCom(..), tycheck)
import Untyped
import Util


main :: IO ()
main = do
  args <- getArgs

  let (filename, api_filename) =
        case args of
          (f:a:_) -> (f, Just a)
          f:_   -> (f, Nothing)
          []    -> error "Error: no input file"

  -- Read in source file
  src <- readFile filename

  let (funcs_dists, main_com) =
        case parse filename src of
          Left err -> error $ errorBundlePretty err
          Right c -> c

  putStrLn "UNTYPED:"
  putStrLn "funcs_dists: "
  mapM_ (putStrLn . toSexp) funcs_dists
  putStrLn "main_com: "
  putStrLn $ toSexp main_com

  case tycheck funcs_dists main_com of
    Left msg -> putStrLn msg
    Right (es, SomeCom t tcom) ->
      case t of
        TSt -> do
          putStrLn "TYPED:"
          putStrLn "es: "
          mapM_ (putStrLn . show) es
          -- putStrLn $ show es
          putStrLn "tcom: "
          putStrLn $ show tcom

          let t = runInterp' (initEnv ++ es) tcom
          -- putStrLn "TREE:"
          -- putStrLn $ toSexp t
          putStrLn $ "size: " ++ (show $ tree_size t)

          let t' = canon t
          -- putStrLn "REDUCED TREE:"
          putStrLn $ toSexp t'
          putStrLn $ "size: " ++ (show $ tree_size t')
      
          -- For testing bernoulli stuff.
          -- let xt = var_tree t ("x", Proxy :: Proxy Bool)
          -- putStrLn $ toSexp xt
          -- putStrLn "exact Pr(true):"
          -- putStrLn $ show $ probOf (VBool True) xt
          -- putStrLn "exact Pr(false):"
          -- putStrLn $ show $ probOf (VBool False) xt
      
          -- -- For testing tricky coin example.
          -- let xt = canon $ var_tree t ("is_tricky_coin", Proxy :: Proxy Bool)
          -- -- putStrLn $ toSexp $ canon xt
          -- putStrLn $ toSexp $ xt
          -- putStrLn "exact Pr(true):"
          -- putStrLn $ show $ probOf (VBool True) xt
          -- putStrLn "exact Pr(false):"
          -- putStrLn $ show $ probOf (VBool False) xt

          -- let xt = canon $ var_tree t ("x", Proxy :: Proxy Bool)
          -- putStrLn $ toSexp $ xt
          -- putStrLn "exact Pr(true):"
          -- putStrLn $ show $ probOf (VBool True) xt
          -- putStrLn "exact Pr(false):"
          -- putStrLn $ show $ probOf (VBool False) xt

          -- -- Generate the cotree.
          let ct = generate t
          let ct' = generate t'

          -- Sample it.
          g <- newStdGen
          let bits = randoms g :: [Bool]
          let samples = eval_sampler (n_samples ct 10000) bits
          let samples' = eval_sampler (n_samples ct' 10000) bits

          -- Plot histogram.
          let hist = generate_histogram samples
          putStrLn "HISTOGRAM:"
          putStrLn $ show hist

          let hist' = generate_histogram samples'
          putStrLn "REDUCED HISTOGRAM:"
          putStrLn $ show hist'

          -- Compute probability mass function.
          let pmf = histogram_pmf hist
          putStrLn "PMF:"
          putStrLn $ show pmf

          let pmf' = histogram_pmf hist'
          putStrLn "REDUCED PMF:"
          putStrLn $ show pmf'

        _ ->
          putStrLn "asdf"
