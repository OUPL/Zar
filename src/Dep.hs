{-# LANGUAGE GADTs #-}

-- | Loop data-flow analysis.

module Dep (compute_deps, dependent_vars, filter_names, sample_vars,
            self_dependent_vars) where

import Data.List (union)
import Data.Maybe (fromMaybe)

import Lang hiding (empty, get)
import Symtab (add, empty, fold, get, Id(..), Symtab)
import qualified Symtab as S (mapi)

compute_deps :: Show a => Com m g a -> Symtab [Id]
compute_deps = go empty
  where
    go :: Show a => Symtab [Id] -> Com m g a -> Symtab [Id]
    go deps Skip = deps
    go deps (Assign (x, _) e) = f deps (Id x) $ id_of_name <$> fvs e
    go deps (Sample (x, _) e) = f deps (Id x) $ id_of_name <$> fvs e
    go deps (Seq c1 c2) = go (go deps c1) c2
    go deps (Ite e c1 c2) =
      -- pass deps, free variables of e, union of deps of c1 and c2
      let c1_deps = go deps c1
          c2_deps = go deps c2
          avars = id_of_name <$> union (assigned_vars c1) (assigned_vars c2)
          deps' = g deps (id_of_name <$> fvs e) avars (union_deps c1_deps c2_deps)
      in deps'
    go deps (While e c) =
      g deps (id_of_name <$> fvs e) (id_of_name <$> assigned_vars c) (go deps c)    
    go _ _ = empty

    -- initial deps, variable being assigned to, free variables of RHS
    f :: Symtab [Id] -> Id -> [Id] -> Symtab [Id]
    f deps x ys =
      -- If there are no variables in the RHS expression, then moving
      -- forward in the analysis variable x has no deps.
      if null ys then
        add x [] deps
      else
        add x (foldl (\acc y -> union acc $ case get y deps of
                                              Just zs -> zs
                                              Nothing -> [y])
                [] ys) deps

    -- initial deps table, free variables of guard expression,
    -- variables assigned to in cases / loop body, new deps table from
    -- analyzing cases / loop body -> propagate deps of free variables
    -- to new deps table
    g :: Symtab [Id] -> [Id] -> [Id] -> Symtab [Id] -> Symtab [Id]
    g deps xs ys deps' =
      let xs_deps = foldl union
                    (concat $ (\x -> fromMaybe [x] $ get x deps) <$> xs) []
      in
        S.mapi (\y zs -> if y `elem` ys then union zs (union xs xs_deps) else zs) deps'

union_deps :: Symtab [Id] -> Symtab [Id] -> Symtab [Id]
union_deps deps1 deps2 =
  fold (\acc x x_deps ->
          add x (union x_deps $ fromMaybe [] $ get x acc) acc) deps2 deps1

-- Given a deps table and a list of variables, find all variables that
-- depend on at least one variable from the list.
dependent_vars :: Symtab [Id] -> [Id] -> [Id]
dependent_vars deps xs =
  fold (\acc y zs -> if any (`elem` xs) zs then y:acc else acc) [] deps

self_dependent_vars :: Symtab [Id] -> [Id]
self_dependent_vars =
  fold (\acc x ys -> if x `elem` ys then x:acc else acc) []

-- Collect variables that are directly assigned random values.
sample_vars :: Com m g a -> [Id]
sample_vars (Sample (x, _) _) = [Id x]
sample_vars (Seq c1 c2) = union (sample_vars c1) (sample_vars c2)
sample_vars (Ite _ c1 c2) = union (sample_vars c1) (sample_vars c2)
sample_vars (While _ c) = sample_vars c
sample_vars _ = []

filter_names :: [Id] -> [SomeName] -> [SomeName]
filter_names xs = filter (\(SomeName (x, _)) -> Id x `elem` xs)
