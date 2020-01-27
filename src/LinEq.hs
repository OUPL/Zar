module LinEq where

import Data.List (sort)
import Data.Maybe (maybeToList)

import Sexp
import Tree
import Util (debug)

-- Boolean-valued trees with mandatory labels at all split nodes.
data LTree =
  LLeaf Double
  | LSplit Int LTree LTree
  | LHole Int
  deriving (Eq, Show)

instance ToSexp LTree where
  toSexp (LLeaf x) = "(" ++ show x ++ ")"
  toSexp (LSplit n t1 t2) =
    "(" ++ show n ++ " " ++ toSexp t1 ++ " " ++ toSexp t2 ++ ")"
  toSexp (LHole n) = "(Hole " ++ show n ++ ")"

type Var = Int
type Coeff = Double
type Term = (Coeff, Maybe Var)

-- A linear equation of a specific form. The LHS is a single variable,
-- and the RHS is a list of terms (taken to be summed together), each
-- comprised of a single rational coefficient and an optional
-- variable. Variables are represented by integers and correspond
-- directly to tree labels.
newtype Equation = Equation { unEquation :: (Var, [Term]) }
  deriving Eq

instance Show Equation where
  show (Equation (x, tms)) = "{ " ++ show x ++ " = " ++ show tms ++ " }"

-- Equations are ordered by their LHS integers, but in reverse.
instance Ord Equation where
  compare (Equation (x, _)) (Equation (y, _)) = compare y x

-- Convert a regular tree to an LTree by filling in labels.
ltree_of_tree :: Tree Double -> LTree
ltree_of_tree t = fst $ go (f 0 t) t
  where
    -- Copy the tree, adding fresh labels at unlabeled split nodes.
    go :: Int -> Tree Double -> (LTree, Int)
    go n (Leaf x) = (LLeaf x, n)
    go n (Split m t1 t2) =
      case m of
        Just m' ->
          let (t1', n') = go n t1
              (t2', n'') = go n' t2 in
            (LSplit m' t1' t2', n'')
        Nothing ->
          let (t1', n') = go (n+1) t1
              (t2', n'') = go n' t2 in
            (LSplit (n+1) t1' t2', n'')
    go n (Hole lbl) = (LHole lbl, n)
    -- Find the maximum label occurring in the tree.
    f :: Int -> Tree Double -> Int
    f n (Split m t1 t2) = maximum $ (maybeToList m) ++ [f n t1, f n t2]
    f n _ = n

term_of_ltree :: LTree -> (Double, Maybe Int)
term_of_ltree (LLeaf x)      = (x/2, Nothing)
term_of_ltree (LSplit x _ _) = (1/2, Just x)
term_of_ltree (LHole x)      = (1/2, Just x)

-- Generate the set of equations from a tree.
equations_of_ltree :: LTree -> [Equation]
equations_of_ltree (LSplit x t1 t2) =
    Equation (x, [term_of_ltree t1, term_of_ltree t2]) :
  (equations_of_ltree t1) ++ (equations_of_ltree t2)
equations_of_ltree _ = []

-- Look for a term containing a given variable in a set of
-- terms. Return the coefficient of the first one encountered.
lookup_term :: Maybe Var -> [Term] -> Maybe Coeff
lookup_term (Just x) ((c, Just y) : terms) =
  if x == y then Just c else lookup_term (Just x) terms
lookup_term Nothing ((c, Nothing) : _) = Just c
lookup_term x (_ : terms) = lookup_term x terms
lookup_term _ [] = Nothing

-- Look for a term containing a given variable in a set of
-- terms. Return the coefficient of the first one encountered, and the
-- list of terms with the selected one deleted.
remove_term :: Maybe Var -> [Term] -> Maybe (Coeff, [Term])
remove_term = go []
  where
    go :: [Term] -> Maybe Var -> [Term] -> Maybe (Coeff, [Term])
    go acc (Just x) (tm@(c, Just y) : terms) =
      if x == y then Just (c, acc ++ terms)
      else go (tm:acc) (Just x) terms
    go acc Nothing ((c, Nothing) : terms) = Just (c, acc ++ terms)
    go acc x (tm : terms) = go (tm:acc) x terms
    go _ _ [] = Nothing

mult_term :: Double -> Term -> Term
mult_term r (c, x) = (r*c, x)

-- Simplify an equation so that the LHS variable doesn't appear
-- anywhere in the RHS. (TODO: combine terms as well? shouldn't be
-- necessary but could improve efficiency).
simplify_equation :: Equation -> Equation
simplify_equation eq =
  let Equation (x, terms) = go eq in
    -- Here we make the choice to set the variable to 0 when it has
    -- infinitely many solutions.
    Equation (x, if null terms then [(0, Nothing)] else terms)
  where
    go (Equation (x, terms)) =
      case remove_term (Just x) terms of
        Nothing -> Equation (x, terms)
        Just (c, terms') ->
          simplify_equation $ Equation (x, mult_term (recip (1-c)) <$> terms')


-- Use remove_term and recurse until fixed point.
combine_terms :: [Term] -> [Term]
combine_terms ((a, x) : tms) =
  case remove_term x tms of
    Just (b, tms') -> combine_terms $ (a+b, x) : tms'
    Nothing -> (a, x) : combine_terms tms
combine_terms [] = []

subst_var :: Var -> [Term] -> Term -> [Term]
subst_var _ _ (c, Nothing) = [(c, Nothing)]
subst_var x tms (c, Just y) =
  if x == y then mult_term c <$> tms else [(c, Just y)]

subst_equation :: Var -> [Term] -> Equation -> Equation
subst_equation x x_tms (Equation (y, y_tms)) =
  Equation (y, concat $ subst_var x x_tms <$> y_tms)

solve_equations :: [Equation] -> Equation
solve_equations = go . sort
  where
    go :: [Equation] -> Equation
    -- Can't solve if there are no equations.
    go [] = error "internal error in LinEq:solve_equations"
    go [eq] = simplify_equation eq
    go (eq : eqs) =
      let Equation (x, terms) = simplify_equation eq in
        go $ simplify_equation . subst_equation x terms <$> eqs

-- Add up a list of terms containing no variables. Evaluates to
-- Nothing if any of the terms contains a variable.
add_terms :: [Term] -> Maybe Double
add_terms [] = Just 0
add_terms ((c, Nothing) : tms) = add_terms tms >>= return . (c +)
-- add_terms ((c, Just x) : [(d, Just y)]) =
--   if c == d && x == y then Just 0 else Nothing
-- add_terms ((_, Just _) : _) = Nothing
add_terms ((c, Just x) : tms) =
  debug "add_terms failure" $
  debug ("c: " ++ show c) $
  debug ("var: " ++ show x) $
  debug ("tms: " ++ show tms) $
  Nothing

infer :: Tree Double -> Maybe Double
infer (Leaf x) = Just x
-- If the tree has at least one split node, then the list of generated
-- equations will be non-empty and safe to pass to the solver.
infer t = add_terms tms
  where Equation (_, tms) =
          solve_equations $ equations_of_ltree $ ltree_of_tree t

-- infer :: Tree Bool -> Maybe Rational
-- infer t =
--   debug ("infer") $
--   debug ("t: " ++ toSexp t) $
--   debug ("lt: " ++ toSexp lt) $
--   debug ("eqs: " ++ show (sort eqs)) $
--   debug ("solution: " ++ show solution) $
--   add_terms tms
--   where
--     lt = ltree_of_tree t
--     eqs = equations_of_ltree lt
--     solution = solve_equations eqs
--     Equation (_, tms) = solution

infer' :: (a -> Double) ->Tree a -> Double
infer' f t  =
  case infer (f <$> t) of
    Just r -> r
    Nothing -> error "LinEq.hs infer' failure"



-- (declare-fun t0 () Real)
-- (declare-fun t1 () Real)
-- (declare-fun t2 () Real)
-- (declare-fun t3 () Real)
-- (declare-fun t4 () Real)
-- (assert (= t3 (+ (* (/ 1 2) t1) (* (/ 1 2) t0))))
-- (assert (= t4 (+ (* (/ 1 2) t2) (* (/ 1 2) t0))))
-- (assert (= t1 (* (/ 1 2) t3)))
-- (assert (= t2 (+ (/ 1 2) (* (/ 1 2) t4))))
-- (assert (= t0 (+ (* (/ 1 2) t1) (* (/ 1 2) t2))))
-- (check-sat)
-- (get-model)
