{-# LANGUAGE GADTs #-}

-- | Variable dependency analysis.

module Dep (dep_cycle, sample_deps, sample_vars, var_deps, loop_vars, filter_names) where

import Data.List (intersect, nub, union)
import Data.Maybe (fromJust, fromMaybe)

import Lang
import Symtab (Id(..))

-- Compute dependencies of variables in a command (possibly a sequence
-- of commands).
var_deps :: Com m g a -> [(Id, [Id])]
var_deps = iter_deps . init_deps

upd_deps :: Eq a => a -> ([b] -> [b]) -> [(a, [b])] -> [(a, [b])]
upd_deps x f ((x', y) : entries) =
  if x == x' then
    (x, f y) : entries
  else
    (x', y) : upd_deps x f entries
upd_deps x f [] = [(x, f [])]

-- Merge two sets of dependencies.
union_deps :: [(Id, [Id])] -> [(Id, [Id])] -> [(Id, [Id])]
union_deps deps [] = deps
union_deps deps ((x, ys) : deps') =
  union_deps (upd_deps x (union ys) deps) deps'

-- Initialize with direct dependencies.
init_deps :: Com m g a -> [(Id, [Id])]
init_deps (Assign (x, _) e) = [(Id x, id_of_name <$> fvs e)]
init_deps (Sample (x, _) e) = [(Id x, id_of_name <$> fvs e)]
init_deps (Seq c1 c2) = union_deps (init_deps c1) (init_deps c2)
init_deps (Ite e c1 c2) =
  union_deps (union_deps (init_deps c1) (init_deps c2)) $
  map (\x -> (id_of_name x, id_of_name <$> fvs e)) $
  assigned_vars c1 `union` assigned_vars c2
init_deps (While e c) =
  union_deps (init_deps c) $
  map (\x -> (id_of_name x, id_of_name <$> fvs e)) $ assigned_vars c
init_deps Skip = []
init_deps (Observe _) = []
init_deps (Return _) = []
init_deps Abort = []

-- Compute transitive closure (iterate until fixed point).
iter_deps :: [(Id, [Id])] -> [(Id, [Id])]
iter_deps deps =
  if deps == deps' then deps else iter_deps deps'
  where
    deps' = f deps (fst <$> deps)
    f :: [(Id, [Id])] -> [Id] -> [(Id, [Id])]
    f deps0 (x:xs) =
      let ys = fromJust $ lookup x deps0
          ys_deps = nub $ concat $ fromMaybe [] . flip lookup deps0 <$> ys
      in
        f (upd_deps x (union ys_deps) deps0) xs
    f deps0 [] = deps0


-- Collect variables that are directly assigned random values.
sample_vars :: Com m g a -> [Id]
sample_vars (Sample (x, _) _) = [Id x]
sample_vars (Seq c1 c2) = union (sample_vars c1) (sample_vars c2)
sample_vars (Ite _ c1 c2) = union (sample_vars c1) (sample_vars c2)
sample_vars (While _ c) = sample_vars c
sample_vars _ = []

filter_names :: [Id] -> [SomeName] -> [SomeName]
filter_names xs = filter (\(SomeName (x, _)) -> Id x `elem` xs)

-- is_bool :: SomeName -> Bool
-- is_bool (SomeName nm@(x, _)) =
--   case cast nm of
--     Just nm' -> nm' == (x, Proxy :: Proxy Bool)
--     Nothing -> False

-- -- Get type information of variables appearing in a command 
-- get_var_types :: [Id] -> Com m g a -> [SomeName]
-- get_var_types xs (Assign (x, proxy) _) = if Id x `elem` xs then [SomeName (x, proxy)] else []
-- get_var_types xs (Sample (x, proxy) _) = if Id x `elem` xs then [SomeName (x, proxy)] else []
-- get_var_types _ _ = []

-- Given variables that are directly assigned random values together
-- with the set of dependencies, compute the set of variables that
-- transitively depend on randomness.
sample_deps :: [Id] -> [(Id, [Id])] -> [Id]
sample_deps xs ((x, ys) : deps) =
  if x `elem` xs || not (null $ intersect xs ys) then
    x : sample_deps xs deps
  else
    sample_deps xs deps
sample_deps _ [] = []

-- Find the first variable in the input list that appears in its own
-- dependency list (it depends on itself).
dep_cycle :: [(Id, [Id])] -> Maybe Id
dep_cycle ((x, ys) : deps) = if x `elem` ys then Just x else dep_cycle deps
dep_cycle [] = Nothing

-- Find all variables that are self-dependent.
loop_vars :: [(Id, [Id])] -> [Id]
loop_vars ((x, ys) : deps) = (if x `elem` ys then [x] else []) ++ loop_vars deps
loop_vars [] = []
