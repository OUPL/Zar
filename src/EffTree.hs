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

data Val = VInt Integer | VArr Val

data Ty = TInt | TIntArr

instance Show Ty where
  show TInt = "i"
  show TIntArr = "iarr"

data Exp = EVar Name Ty | EVal Val | EInc Exp | EGet Exp Exp

data Pred = PLe Exp Exp | PAnd Pred Pred

-- Predicate sugar:
peq :: Exp -> Exp -> Pred
peq e1 e2 = PAnd (PLe e1 e2) (PLe e2 e1)

data Eff = Upd Name Ty Exp | Store Name Exp Exp Exp | Seq Eff Eff | Skip

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

identOf :: String -> Ty -> InterpM String
identOf x t = do 
  n <- varIdx x
  return $ '_' : show t ++ '_' : x ++ if n > 0 then show n else ""

varOf :: String -> Ty -> InterpM AST
varOf x t = do
  _x <- identOf x t
  sx <- lift $ mkStringSymbol _x
  case t of
   TInt -> lift $ mkIntVar sx
   TIntArr -> do
     isort <- lift $ mkIntSort
     asort <- lift $ mkArraySort isort isort
     lift $ mkVar sx asort

class ToZ3 a where
  toZ3 :: a -> InterpM AST

instance ToZ3 Val where
  toZ3 (VInt i) = lift $ mkInteger i
  toZ3 (VArr v) = do
    isort <- lift mkIntSort
    _v <- toZ3 v
    lift $ mkConstArray isort _v

instance ToZ3 Exp where
  toZ3 (EVar x t) = varOf x t
  toZ3 (EVal v) = toZ3 v
  toZ3 (EInc e) = do
    _e <- toZ3 e
    one <- lift $ mkInteger 1
    lift $ mkAdd [_e, one]
  toZ3 (EGet earr eidx) = do
    _earr <- toZ3 earr
    _eidx <- toZ3 eidx
    lift $ mkSelect _earr _eidx

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
wp (Upd x t e) base q = do
  _e <- toZ3 e
  incVarIdx x
  _x <- toZ3 $ EVar x t
  eq <- lift $ mkEq _x _e
  _base <- toZ3 base
  p <- lift $ mkAnd [eq, _base, q]
  return p
wp (Store x earr eidx enew) base q = do
  _earr <- toZ3 earr
  _eidx <- toZ3 eidx
  _enew <- toZ3 enew
  incVarIdx x
  _x <- toZ3 $ EVar x TIntArr
  store <- lift $ mkStore _earr _eidx _enew
  eq <- lift $ mkEq _x store
  _base <- toZ3 base
  p <- lift $ mkAnd [eq, _base, q]
  return p
wp (Seq eff1 eff2) base q = do
  q1 <- wp eff2 base q
  wp eff1 base q1
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
tree1 = Node (Upd "x" TInt (EInc (EVar "x" TInt))) tree1 Skip Leaf
post1 = PAnd (PLe (EVal $ VInt 0) (EVar "x" TInt)) (PLe (EVar "x" TInt) (EVal $ VInt 7)) 
ex1 = runInterpM $ toZ3 post1 >>= wpe tree1 post1

tree2 :: Tree Eff
tree2 =
  Node
  (Store "y" (EVal $ VArr $ VInt 0) (EVal $ VInt 0) (EVal $ VInt 1)) Leaf
  (Store "y" (EVal $ VArr $ VInt 0) (EVal $ VInt 0) (EVal $ VInt 2)) Leaf
post2 = peq (EGet (EVar "y" TIntArr) (EVal $ VInt 0)) (EVal $ VInt 1)
ex2 = runInterpM $ toZ3 post2 >>= wpe tree2 post2  

