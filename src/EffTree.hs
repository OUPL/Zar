{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module EffTree where

--import           Control.Applicative
--import           Control.Monad ( join )
import           Control.Monad.State 
--import qualified Data.Traversable as T
import qualified Data.Map.Strict as M

import           Z3.Monad

data Tree eff =
    Leaf 
  | Node eff (Tree eff) eff (Tree eff)

type Name = String

data Val = VInt Integer

data Exp = EVar Name | EVal Val | EInc Exp

data Pred = PLe Exp Exp | PAnd Pred Pred

data Eff = Upd Name Exp | Skip

data Event = SatCheck String

instance Show Event where
  show (SatCheck s) = "sat: " ++ s

printEvents :: [Event] -> IO ()
printEvents es = mapM (putStrLn . show) es >> return ()

data InterpState =
  InterpState {
    -- updates(x) = i: Variable x has been updated i times.
    updates :: M.Map String Int, 
    trace :: [Event] }

initInterpState = InterpState M.empty []

type InterpM = StateT InterpState Z3

runInterpM :: InterpM a -> IO a
runInterpM m = do
  (a, s) <- evalZ3 $ runStateT m initInterpState
  printEvents $ trace s
  return a

record :: Event -> InterpM ()
record ev = modify (\s -> InterpState (updates s) (ev : trace s))

varIdx :: String -> InterpM Int
varIdx x = do
  s <- get
  case M.lookup x (updates s) of
   Nothing -> return 0
   Just n -> return n   

incVarIdx :: String -> InterpM ()
incVarIdx x =
  modify (\s -> InterpState (M.insertWith (+) x 1 (updates s)) (trace s))

identOf :: String -> InterpM String
identOf x = do 
  n <- varIdx x
  return $ x ++ if n > 0 then show n else ""

varOf :: String -> InterpM AST
varOf x = do
  _x <- identOf x
  sx <- lift $ mkStringSymbol _x
  lift $ mkIntVar sx

class ToZ3 a where
  toZ3 :: a -> InterpM AST

instance ToZ3 Val where
  toZ3 (VInt i) = lift $ mkInteger i

instance ToZ3 Exp where
  toZ3 (EVar x) = varOf x
  toZ3 (EVal v) = toZ3 v
  toZ3 (EInc e) = do
    _e <- toZ3 e
    one <- lift $ mkInteger 1
    lift $ mkAdd [_e, one]

instance ToZ3 Pred where 
  toZ3 (PLe e1 e2) = do
    _e1 <- toZ3 e1
    _e2 <- toZ3 e2
    lift $ mkLe _e1 _e2
  toZ3 (PAnd p1 p2) = do
    _p1 <- toZ3 p1
    _p2 <- toZ3 p2
    lift $ mkAnd [_p1, _p2]

printZ3 :: ToZ3 a => a -> IO ()
printZ3 a = do
  ast <- runInterpM $ toZ3 a
  s <- evalZ3 $ astToString ast
  putStrLn s

sat :: AST -> InterpM Bool
sat a = do
  _a <- lift $ astToString a
  record $ SatCheck _a
  -- START fresh Z3 context
  lift push
  lift $ assert a
  r <- lift check
  lift $ pop 1
  -- END fresh Z3 context
  case r of
   Sat -> return True
   Unsat -> return False
   Undef -> error "sat: undefined"

wp :: Eff -> Pred -> AST -> InterpM AST
wp (Upd x e) base q = do
  _e <- toZ3 e
  incVarIdx x
  _x <- toZ3 $ EVar x
  eq <- lift $ mkEq _x _e
  _base <- toZ3 base
  p <- lift $ mkAnd [eq, _base, q]
  return p
wp Skip _ q = return q  

wpe :: Tree Eff -> Pred -> AST -> InterpM Rational
wpe Leaf _ q = do
  b <- sat q
  return $ if b then 1 else 0
wpe (Node eff1 t1 eff2 t2) base q = do
  q1 <- wp eff1 base q
  q2 <- wp eff2 base q
  b1 <- sat q1
  b2 <- sat q2
  r1 <- if b1 then wpe t1 base q1 else return 0
  r2 <- if b2 then wpe t2 base q2 else return 0
  return $ (1/2)*r1 + (1/2)*r2

tree1 :: Tree Eff
tree1 = Node (Upd "x" (EInc (EVar "x"))) tree1 Skip Leaf
post1 = PAnd (PLe (EVar "x") (EVal $ VInt 3)) (PLe (EVal $ VInt 0) (EVar "x"))
ex1 = runInterpM $ toZ3 post1 >>= wpe tree1 post1
