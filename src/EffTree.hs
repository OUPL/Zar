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

data Val = VInt Integer | VBool Bool | VArr Val

data Ty = TInt | TBool | TArr Ty

instance Show Ty where
  show TInt = "int"
  show TBool = "bool"
  show (TArr t) = "(arr " ++ show t ++ ")"

data Binop = BEq | BLe

data Exp =
    EVar Name Ty
  | EVal Val
  | EInc Exp
  | EGet Exp Exp
  | ENot Exp
  | EBin Binop Exp Exp

eeq = EBin BEq     
ele = EBin BLe

data Pred = PAssert Exp | PEq Exp Exp | PLe Exp Exp | PAnd Pred Pred

data Eff = Assert Exp | Upd Name Ty Exp | Store Name Ty Exp Exp Exp | Seq Eff Eff | Skip

data Event = SatCheck String Bool

instance Show Event where
  show (SatCheck s b) = show b ++ ": " ++ s

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
   TBool -> lift $ mkBoolVar sx
   TArr TInt -> do
     isort <- lift $ mkIntSort
     asort <- lift $ mkArraySort isort isort
     lift $ mkVar sx asort
   TArr TBool -> do
     isort <- lift $ mkIntSort          
     bsort <- lift $ mkBoolSort
     asort <- lift $ mkArraySort isort bsort
     lift $ mkVar sx asort
   --FIXME(GS): generalize       
   TArr t0 -> error $ show t0 ++ " array types not supported"     

class ToZ3 a where
  toZ3 :: a -> InterpM AST

instance ToZ3 Val where
  toZ3 (VInt i) = lift $ mkInteger i
  toZ3 (VBool b) = lift $ mkBool b
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
  toZ3 (ENot e) = do
    _e <- toZ3 e
    lift $ mkNot _e
  toZ3 (EBin b e1 e2) = do
    _e1 <- toZ3 e1
    _e2 <- toZ3 e2
    lift $ mkOp b _e1 _e2
    where
      mkOp BEq = mkEq
      mkOp BLe = mkLe

instance ToZ3 Pred where
  toZ3 (PAssert e) = do
    toZ3 e
  toZ3 (PEq e1 e2) = do
    _e1 <- toZ3 e1
    _e2 <- toZ3 e2
    lift $ mkEq _e1 _e2
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
  -- START fresh Z3 context
  lift push
  lift $ assert a
  r <- lift check
  lift $ pop 1
  -- END fresh Z3 context
  case r of
   Sat -> record (SatCheck _a True) >> return True
   Unsat -> record (SatCheck _a False) >> return False
   Undef -> error "sat: undefined"

wp :: Eff -> AST -> InterpM AST
wp (Assert e) q = do
  _e <- toZ3 e
  p <- lift $ mkAnd [_e, q]
  return p
wp (Upd x t e) q = do
  _e <- toZ3 e
  incVarIdx x
  _x <- toZ3 $ EVar x t
  eq <- lift $ mkEq _x _e
  p <- lift $ mkAnd [eq, q]
  return p
wp (Store x t earr eidx enew) q = do
  _earr <- toZ3 earr
  _eidx <- toZ3 eidx
  _enew <- toZ3 enew
  incVarIdx x
  _x <- toZ3 $ EVar x t
  store <- lift $ mkStore _earr _eidx _enew
  eq <- lift $ mkEq _x store
  p <- lift $ mkAnd [eq, q]
  return p
wp (Seq eff1 eff2) q = do
  q1 <- wp eff2 q
  wp eff1 q1
wp Skip q = return q  

wpe :: Tree Eff -> AST -> InterpM Rational
wpe Leaf q = do
  b <- sat q
  return $ if b then 1 else 0
wpe (Node eff1 t1 eff2 t2) q = do
  q1 <- wp eff1 q
  q2 <- wp eff2 q
  b1 <- sat q1
  b2 <- sat q2
  r1 <- if b1 then wpe t1 q1 else return 0
  r2 <- if b2 then wpe t2 q2 else return 0
  return $ (1/2)*r1 + (1/2)*r2

tree1 :: Int -> Tree Eff
tree1 0 = Leaf
tree1 n = Node (Seq
              (Assert (ele (EVal $ VInt 0) (EVar "x" TInt)))
              (Upd "x" TInt (EInc (EVar "x" TInt)))) (tree1 $ n-1) Skip Leaf
post1 = PLe (EVar "x" TInt) (EVal $ VInt 3)
ex1 n = runInterpM $ toZ3 post1 >>= wpe (tree1 n)

tree2 :: Tree Eff
tree2 =
  Node
  (Store "y" (TArr TInt) (EVal $ VArr $ VInt 0) (EVal $ VInt 0) (EVal $ VInt 1)) Leaf
  (Store "y" (TArr TInt) (EVal $ VArr $ VInt 0) (EVal $ VInt 0) (EVal $ VInt 2)) Leaf
post2 = PEq (EGet (EVar "y" (TArr TInt)) (EVal $ VInt 0)) (EVal $ VInt 2)
ex2 = runInterpM $ toZ3 post2 >>= wpe tree2

tree3 :: Tree Eff
tree3 = Node inc tree3 Skip Leaf
  where
    inc = Store "y" (TArr TInt) (EVar "y" (TArr TInt)) (EVal $ VInt 0)
            (EInc $ EGet (EVar "y" (TArr TInt)) (EVal $ VInt 0))
post3 =
  let y0 = EGet (EVar "y" (TArr TInt)) (EVal $ VInt 0)
      n x = EVal $ VInt x
  in PAnd (PLe (n 0) y0) (PLe y0 (n 2))
ex3 = runInterpM $ toZ3 post3 >>= wpe tree3 

geom :: Tree Eff
geom =
  Node
   (Upd "i" TInt (EInc $ EVar "i" TInt)) geom 
   Skip 
     (Node
      (Assert $ ENot $ EGet (EVar "u" (TArr TBool)) (EVar "i" TInt)) Leaf
      (Assert $ EGet (EVar "u" (TArr TBool)) (EVar "i" TInt)) Leaf)

geom_post =
  let n x = EVal $ VInt x
      i = EVar "i" TInt
      u = EVar "u" (TArr TBool)
  in PEq i (n 1)-- PAnd (PAnd (PLe (n 0) i) (PLe i (n 5))) (PAssert $ EGet u (n 1))
ex_geom = runInterpM $ toZ3 geom_post >>= wpe geom 
     

