{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module EffTree where

class Pred p where
  inter :: p -> p -> p
  union :: p -> p -> p

class Pred p => Eff e p where
  wp :: e -> p -> p

data EffTree e p where
  Leaf :: EffTree e p
  Node :: Eff e p => (e, EffTree e p) -> (e, EffTree e p) -> EffTree e p

type Name = String

data Exp = Id Name | Val Int | Inc Exp
  deriving (Show)

-- (TODO) This and other functions should be tail recursive.
vars :: Exp -> [Name]
vars (Id n)  = [n]
vars (Val _) = []
vars (Inc e) = vars e

ground_eval :: Exp -> Int
ground_eval (Id x)  = error $ "expected " ++ x ++ " a ground expression"
ground_eval (Val i) = i
ground_eval (Inc e) = 1 + ground_eval e

data Halfspace = Leq Exp Exp | Geq Exp Exp
  deriving (Show)

hs_vars :: Halfspace -> [Name]
hs_vars (Leq e1 e2) = vars e1 ++ vars e2
hs_vars (Geq e1 e2) = vars e1 ++ vars e2

ground_hs_sat :: Halfspace -> Bool
ground_hs_sat (Leq e1 e2) = ground_eval e1 <= ground_eval e2
ground_hs_sat (Geq e1 e2) = ground_eval e1 >= ground_eval e2

subst :: Name -> Exp -> Exp -> Exp
subst x enew (Id y) | x==y      = enew
subst x enew (Id y) | otherwise = Id y
subst x enew (Val i) = Val i
subst x enew (Inc e) = Inc $ subst x enew e

subst_hs :: Name -> Exp -> Halfspace -> Halfspace
subst_hs x enew (Leq e1 e2) = Leq (subst x enew e1) (subst x enew e2)
subst_hs x enew (Geq e1 e2) = Geq (subst x enew e1) (subst x enew e2)

-- Conjunction of halfspaces
type Region = [Halfspace]

subst_region :: [(Name, Exp)] -> Region -> Region
subst_region ss r = foldl (\r0 (x, e) -> map (subst_hs x e) r0) r ss

-- A region is satisfiable iff it has a satisfiable ground substitution
-- (TODO) The entire backend should be built against Z3; this is just an experiment.
region_sat :: Region -> Bool
region_sat r =
  any (\ss -> all ground_hs_sat $ subst_region ss r) substs
  where
    substs = [ [(x, v) | v <- vals] | x <- region_vars ]
    region_vars = concatMap hs_vars r
    vals = [ Val i | i <- [0..9] ]

-- Disjunction of regions
type Regions = [Region]

regions_sat :: Regions -> Bool
regions_sat = any region_sat 

instance Pred Regions where
  inter rs1 rs2 = [ r1 ++ r2 | r1 <- rs1, r2 <- rs2 ]
  union rs1 rs2 = rs1 ++ rs2

data Com = Assign Name Exp

instance Eff Com Regions where
  wp (Assign x e) rs = map (subst_region [(x, e)]) rs

iverson :: Bool -> Rational
iverson b = if b then 1 else 0

wpe :: EffTree Com Regions -> Regions -> Rational
wpe Leaf rs = iverson $ regions_sat rs
wpe (Node (eff1, t1) (eff2, t2)) rs = 
  (1/2)*(guard (wp eff1 rs) $ wpe t1) + (1/2)*(guard (wp eff2 rs) $ wpe t2)
  where guard rs z = if regions_sat rs then z rs else 0

ex1 :: EffTree Com Regions 
ex1 = Node (Assign x (Inc (Id x)), ex1) (Assign x (Id x), Leaf)
  where x = "x"

ex1_post :: Regions 
ex1_post = [[Leq (Id "x") (Val 3)]]
  

  
           
  
