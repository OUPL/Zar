{-# LANGUAGE GADTs #-}

module Main where

import           Data.Proxy
-- import           Data.Typeable
import           System.Environment (getArgs)
-- import qualified Z3.Base
-- import qualified Z3.Monad as Z3

import Classes
-- import Inference
import IORepr()
import Lang (Exp(..), Type(..), Val(..), empty)
import TreeRepr()
import Sexp
-- import SparseLinAlg (solve_tree)
import Tree
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
      let t = k empty
      -- Do stuff with it (more to do).
      putStrLn "TREE:"
      putStrLn $ toSexp $ reorder t
      putStrLn $ "size: " ++ (show $ tree_size t)

      -- putStrLn "TREE SAMPLING INFERENCE:"
      -- finite_pmf <- sample_infer t n
      -- putStrLn $ show finite_pmf

      -- let t' = canon t
      -- putStrLn "REDUCED TREE:"
      -- putStrLn $ toSexp t'
      -- putStrLn $ "size: " ++ (show $ tree_size t')

      case ty of
        TExp TBool -> do
          putStrLn $ show $ (infers!!0) t (\(EVal (VBool b)) -> b)
          -- putStrLn $ show $ (infers!!0) t' (\(EVal (VBool b)) -> b)
          -- let tb = (\(EVal (VBool b)) -> b) <$> t
          -- let model = z3infer tb
          -- putStrLn $ show model

          -- Use sparse linear algebra module.
          -- let tb = (\(EVal (VBool b)) -> b) <$> t
          -- v <- solve_tree tb
          -- putStrLn $ show v
        _ ->
          putStrLn "expected bool tree"

      -- case cast t' of
      --   Just t'' -> putStrLn $ show $ (infers!!0) t'' id
      --   Nothing -> return ()
      -- putStrLn $ show $ (infers!!0) t' (\x -> case cast x of
      --                                           Just (EVal (VBool b)) -> b
      --                                           _ -> error "asd")
