{-# LANGUAGE GADTs #-}

module Main where

import           Data.List (sort)
import           Data.Proxy
-- import           Data.Typeable
import           System.Environment (getArgs)
-- import qualified Z3.Base
-- import qualified Z3.Monad as Z3

import Classes
-- import Cotree
-- import Inference
import IORepr()
import Lang (Exp(..), Type(..), Val(..), empty)
import TreeRepr()
import Sexp
-- import SparseLinAlg (solve_tree)
import Tree
import TreeRepr (c_infer)
import Tycheck (SomeKG(..), load_repr)
-- import Z3Infer (z3infer)

main :: IO ()
main = do
  args <- getArgs

  -- let (filename, api_filename) =
  let (filename, _) =
        case args of
          (f:a:_) -> (f, Just a)
          f:_   -> (f, Nothing)
          []    -> error "Error: no input file"

  -- Read in source file
  src <- readFile filename

  -- let n = 10000

  -- Load IO representation of the program.
  -- case load_repr (Proxy :: Proxy IO) filename src of
  --   Left msg -> putStrLn msg
  --   Right (SomeKG _ k) -> do
  --     -- WARNING: this can diverge if the total probability mass of
  --     -- the program is less than 1.
  --     putStrLn $ "Generating a sample.."
  --     let sampler = k empty
  --     x <- sample sampler
  --     putStrLn $ show x

  -- Load tree representation of the program.
  case load_repr (Proxy :: Proxy Tree) filename src of
    Left msg -> putStrLn msg
    Right (SomeKG ty k) -> do
      -- Choose the first inference method (the only one that
      -- exists at the moment).
      -- let infer = infers!!0
      let t = reorder $ k empty
      -- Do stuff with it (more to do).
      putStrLn "TREE:"
      putStrLn $ toSexp t
      putStrLn $ "size: " ++ (show $ tree_size t)

      -- let t' = expand t
      -- putStrLn "EXPANDED:"
      -- putStrLn $ toSexp t'
      
      let n = 10
      let ts = flip expand_n t <$> [0..n-1]
      -- putStrLn "EXPANSIONS:"
      -- putStrLn $ toSexp ts
      
      -- putStrLn "TREE SAMPLING INFERENCE:"
      -- finite_pmf <- sample_infer t n
      -- putStrLn $ show finite_pmf

      -- let t' = canon t
      -- putStrLn "REDUCED TREE:"
      -- putStrLn $ toSexp t'
      -- putStrLn $ "size: " ++ (show $ tree_size t')

      case ty of
        TExp TInteger -> do
          let t' = (\(EVal (VInteger i)) -> i) <$> t
          putStrLn "CLEANER TREE:"
          putStrLn $ toSexp t'
          -- Expected value
          let solution = (infers!!0) (\i -> fromIntegral i) t'
          putStrLn $ "expected value: " ++ show solution

          let c_solution = c_infer (\i -> fromIntegral i) t'
          putStrLn $ "c_solution: " ++ show c_solution
          -- -- Full pmf
          -- let supp = sort $ support t'
          -- let pmf =
          --       map (\n -> (n, infer t' (\m -> if m == n then 1.0 else 0.0))) supp
          -- putStrLn $ "pmf: " ++ show pmf
        TExp TFloat -> do
          let solution = (infers!!0) (\(EVal (VFloat f)) -> f) t
          putStrLn $ show $ solution
          let c_solution = c_infer (\(EVal (VFloat f)) -> f) t
          putStrLn $ "c_solution: " ++ show c_solution
        TExp TRational -> do
          let solution = (infers!!0) (\(EVal (VRational r)) -> fromRational r) t
          putStrLn $ show $ solution
          let c_solution = c_infer (\(EVal (VRational r)) -> fromRational r) t
          putStrLn $ "c_solution: " ++ show c_solution
        TExp TBool -> do
          -- let ct = generate t
          -- let t' = prefix 20 ct
          -- putStrLn "PREFIX TREE: "
          -- putStrLn $ toSexp t'
          -- putStrLn $ "mass: " ++ (show $ mass (\(EVal (VBool b)) -> if b then 1.0 else 0.0) t')
          -- let f = (\(EVal (VBool b)) -> if b then 1.0 else 0.0)
          --       :: Exp InterpM Tree Bool -> Double
          -- let m = mass f t
          -- let lm = lmass f t
          -- let ms = mass f <$> ts
          -- let lms = lmass f <$> ts
          -- putStrLn "MASS:"
          -- putStrLn $ show m
          -- putStrLn "LMASS:"
          -- putStrLn $ show lm
          -- putStrLn "MASSES:"
          -- putStrLn $ show ms
          -- putStrLn "LMASSES:"
          -- putStrLn $ show lms
          
          let solution = (infers!!0) (\(EVal (VBool b)) -> if b then 1.0 else 0.0) t
          putStrLn $ show $ solution
          let c_solution = c_infer (\(EVal (VBool b)) -> if b then 1.0 else 0.0) t
          putStrLn $ "c_solution: " ++ show c_solution

          -- let c1 = m / solution
          -- let c2 = solution / lm
          -- putStrLn $ "c1: " ++ show c1
          -- putStrLn $ "c2: " ++ show c2
          
          -- putStrLn $ show $ (infers!!0) t' (\(EVal (VBool b)) -> b)
          -- let tb = (\(EVal (VBool b)) -> b) <$> t
          -- let model = z3infer tb
          -- putStrLn $ show model

          -- Use sparse linear algebra module.
          -- let tb = (\(EVal (VBool b)) -> b) <$> t
          -- v <- solve_tree tb
          -- putStrLn $ show v
        _ ->
          -- putStrLn "expected bool tree"
          putStrLn "no expected value"

      let supp = sort $ support t
      let pmf =
            map (\x -> (x, (infers!!0) (\y -> if x == y then 1.0 else 0.0) t)) supp
      putStrLn $ "pmf: " ++ show pmf

      -- case cast t' of
      --   Just t'' -> putStrLn $ show $ (infers!!0) t'' id
      --   Nothing -> return ()
      -- putStrLn $ show $ (infers!!0) t' (\x -> case cast x of
      --                                           Just (EVal (VBool b)) -> b
      --                                           _ -> error "asd")
