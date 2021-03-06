{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

-- | KY tree semantics. m = InterpM, g = Tree.

module TreeInterp (freshLbl, generalize_tree, InterpM, runInterp, runInterp') where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State hiding (get)
import qualified Control.Monad.State as S (get)

import Data.Bifunctor (first, second)
import Data.List (intersect, sort, union)
import Data.Maybe (fromJust)
import Data.Typeable

import           Dep
import           Distributions
import           Lang hiding (Com, Exp, St, Val, interp)
import qualified Lang (Com, Exp, St, Val)
import           Tree (labels_of_tree, set_label, subst_label, Tree(..))
import           Util (set_at)


-- Gensym counter, tree table (used when compiling loops with
-- loop-carried boolean variables).
type InterpState = (Int, [Maybe (Tree St)])

type InterpEnv = Env InterpM Tree

newtype InterpM a =
  InterpM { unInterpM :: ReaderT InterpEnv (State InterpState) a }
  deriving (Functor)

instance Applicative InterpM where
  pure = InterpM . pure
  InterpM f <*> InterpM x = InterpM $ f <*> x

instance Monad InterpM where
  InterpM m >>= g = InterpM $ m >>= (unInterpM . g)
  return = pure

instance MonadState InterpState InterpM where
  get = InterpM S.get
  put s = InterpM $ put s

instance MonadReader InterpEnv InterpM where
  ask = InterpM ask
  local f (InterpM m) = InterpM $ local f m

runInterpM :: InterpEnv -> InterpState -> InterpM a -> (a, InterpState)
runInterpM env s (InterpM f) = runIdentity $ runStateT (runReaderT f env) s

-- Kleisli composition for the monad InterpM ∘ Tree (which I think
-- forms a monad only because Tree is traversable). Used for composing
-- the interpretations of commands.
kcomp :: (a -> InterpM (Tree b)) -> (b -> InterpM (Tree c)) -> a -> InterpM (Tree c)
kcomp f g x = join <$> (join $ sequenceA <$> (fmap g <$> (f x)))


-- Here we can see that f ∘ g is a monad whenever f and g are monads
-- and g is traversable, so we could change the type of interp to use
-- Compose InterpM Tree and then automatically derive the kleisli
-- composition operation (>=>), but it's probably easier to use the
-- specialized kcomp function instead in order to avoid all the
-- boilerplate.
newtype Compose f g a = Compose { unCompose :: f (g a) }
instance (Functor f, Functor g) => Functor (Compose f g) where
  fmap f (Compose x) = Compose $ fmap f <$> x
instance (Applicative f, Applicative g) => Applicative (Compose f g) where
  pure = Compose . pure . pure
  Compose f <*> Compose x = Compose $ (<*>) <$> f <*> x
instance (Monad f, Monad g, Traversable g) => Monad (Compose f g) where
  return = Compose . return . return
  Compose x >>= k =
    Compose $ fmap join $ join $ sequenceA <$> fmap (unCompose . k) <$> x


--note(jgs): unused
-- evalInterpM :: InterpEnv -> InterpState -> InterpM a -> a
-- evalInterpM env s f = fst $ runInterpM env s f

-- execInterpM :: InterpEnv -> InterpState -> InterpM a -> InterpState
-- execInterpM env s f = snd $ runInterpM env s f


-- Set up type synonyms.
type Com = Lang.Com InterpM Tree
type Exp = Lang.Exp InterpM Tree
type St  = Lang.St  InterpM Tree
type Val = Lang.Val InterpM Tree


-- | Interpreting commands as Kleisli arrows out of St.

freshLbl :: InterpM Int
freshLbl = do
  counter <- fst <$> S.get
  modify $ first $ const $ counter + 1
  return $ counter + 1

is_true :: Exp Bool -> St -> InterpM Bool
is_true e st = do
  b <- eval e st
  case b of
    VBool b' -> return b'

generalize_tree :: (Eq a, Show a) => Tree (Exp a) -> Val (Tree a)
generalize_tree t = VDist (labels_of_tree t) t

eval :: Typeable a => Exp a -> St -> InterpM (Val a)
eval (EVal v) _ = return v
eval (EVar x) st =
  -- First try a lookup in the local state.
  case get x st of
    Just v -> return v
    Nothing -> do
      -- If that fails, try the global environment.
      env <- ask
      case envGet x env of
        Just e -> eval e st
        Nothing ->
          let (_, proxy) = x
              ty = typeOf proxy in
            error $ "eval: unbound variable: " ++ show x
            ++ " of type " ++ show ty ++ ".\nst: " ++ show st
eval (EUnop u e) st = do
  v <- eval e st
  case u of
    UNot ->
      case v of
        VBool b -> return $ VBool $ not b
        _ -> error "eval: ill-typed UNot expression"
    UFst ->
      case v of
        VPair x _ -> return x
        _ -> error "eval: ill-typed UFst expression"
    USnd ->
      case v of
        VPair _ y -> return y
        _ -> error "eval: ill-typed USnd expression"
eval (EBinop b e1 e2) st = do
  v1 <- eval e1 st
  v2 <- eval e2 st
  case b of
    BPlus ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 + r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 + f2
        (VInteger i1, VInteger i2) -> return $ VInteger $ i1 + i2
        _ -> error "eval: ill-typed BPlus expression"
    BMinus ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 - r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 - f2
        (VInteger i1, VInteger i2) -> return $ VInteger $ i1 - i2
        _ -> error "eval: ill-typed BMinus expression"
    BMult ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 * r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 * f2
        (VInteger i1, VInteger i2) -> return $ VInteger $ i1 * i2
        _ -> error "eval: ill-typed BMult expression"
    BDiv ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 / r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 / f2
        _ -> error "eval: ill-typed BDiv expression"
    BAnd ->
      case (v1, v2) of
        (VBool b1, VBool b2) -> return $ VBool $ b1 && b2
        _ -> error "eval: ill-typed BAnd expression"
    BOr ->
      case (v1, v2) of
        (VBool b1, VBool b2) -> return $ VBool $ b1 || b2
        _ -> error "eval: ill-typed BOr expression"
    BEq -> return $ VBool $ v1 == v2
    BLt ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VBool $ r1 < r2
        (VFloat f1, VFloat f2) -> return $ VBool $ f1 < f2
        (VInteger i1, VInteger i2) -> return $ VBool $ i1 < i2
        (VBool b1, VBool b2) -> return $ VBool $ b1 < b2
        _ -> error "eval: ill-typed BLt expression"

eval (EPair e1 e2) st = pure VPair <*> eval e1 st <*> eval e2 st

eval ENil _ = return VNil

eval (ECons hd tl) st = do
  hd' <- eval hd st
  tl' <- eval tl st
  return $ VCons hd' tl'

eval (EDestruct l z f) st = do
  l' <- eval l st
  case l' of
    VNil -> eval z st
    VCons v vs ->
      eval (EApp (EApp f $ EVal v) $ EVal vs) st

eval (ELam x body) _ = return $ VLam x body

eval (EApp f e) st = do
  f' <- eval f st
  v <- eval e st
  case f' of
    VLam x body ->
      -- Extend the local state with a binding for the variable.
      -- eval body (upd x v st)
      -- Substitute v for x in body, then evaluate.
      eval (subst x (EVal v) body) st
    VPrim f0 -> f0 v >>= flip eval st

eval (ECom args com) st = do
  st' <- mapM (\(SomeNameExp x e) -> SomeNameVal x <$> eval e st) args
  -- Remember gensym counter
  i <- gets fst
  modify $ first $ const 0
  t <- generalize_tree <$> interp com st'
  -- Restore gensym counter
  modify $ first $ const i
  return t

-- Need labels here?
eval (ECond b e1 e2) st = do
  b' <- is_true b st
  if b' then eval e1 st else eval e2 st

eval (EPrim x) _ = return $ VPrim x

eval (EUniform e) st = do
  v <- eval e st
  case v of
    VNil -> error "eval: empty list argument to uniform distribution"
    --note(jgs): Don't generate fresh labels in special case of singleton
    --lists. This is to address issue #8.
    VCons v1 VNil -> return $ VDist [] $ Leaf (EVal v1)
    _ -> do
      return $ generalize_tree $ uniform $ EVal <$> vlist_list v


-- | Interp. Commands are interpreted as functions from trees of
-- states to stateful tree-building computations.

interp' :: (Eq a, Show a) => Com a -> St -> InterpM (Tree a)
-- Use this for incremental reduction. Not working right though?
-- interp' c t = canon <$> interp c t
interp' = interp

interp :: (Eq a, Show a) => Com a -> St -> InterpM (Tree a)
interp Skip st = return $ Leaf st
interp (Assign x e) st = do
  v <- eval e st
  return $ Leaf $ upd x v st
interp (Sample x e) st = do
  v <- eval e st
  case v of
    VDist lbls t' -> do
      t'' <- foldM (\acc lbl -> do
                       fresh_lbl <- freshLbl
                       return $ subst_label fresh_lbl lbl acc) t' lbls
      mapM (\e' -> do
               v' <- eval e' st
               return $ upd x v' st) t''
interp (Seq c1 c2) st = kcomp (interp' c1) (interp' c2) st
interp (Ite e c1 c2) st = do
  b <- is_true e st
  if b then interp' c1 st
    else interp' c2 st

interp (While e c) st =
  let deps = compute_deps c
      svars = sample_vars c
      sdeps = dependent_vars deps svars
      sdeps_in_e = intersect (union svars sdeps) (id_of_name <$> fvs e)
  in
    if not $ null sdeps_in_e then
      -- Something in e depends on randomness.
      -- debug "DETECTED RANDOM LOOP" $
      let self_dep_vars = self_dependent_vars deps
          names = assigned_vars c
          lnames = filter_names self_dep_vars names
          lvals = map (\(SomeName nm) -> SomeVal $ fromJust $ get nm st) lnames
          all_bool = all is_bool_val lvals
      in do
        -- No loop-carried variables so straightforward loop construction.
        -- debug ("simple loop") $ do
        b <- is_true e st
        if b then do
          fresh_lbl <- freshLbl
          let kt = interp c
          let kt' = \st' -> do
                b' <- is_true e st'
                return $ if b' then Hole fresh_lbl else Leaf st'
          t' <- kcomp kt kt' st
          return $ set_label fresh_lbl t'
          else
          return $ Leaf st
    else
      -- Nothing in e depends on randomness so unfold the loop.
      -- debug "DETECTED UNROLLABLE LOOP" $
      interp' (Ite e (Seq c (While e c)) Skip) st

interp (Return e) st = Leaf . EVal <$> eval e st
interp (Observe e) st = do
  b <- is_true e st
  if b then return $ Leaf st else return $ Hole 0
interp Abort t = interp' (Observe $ EVal $ VBool False) t


runInterp :: (Eq a, Show a) => Env InterpM Tree -> Com a -> St -> (Tree a, Int)
runInterp env c st = second fst $ runInterpM env (0, []) (interp' c st)

runInterp' :: (Eq a, Show a) => Env InterpM Tree -> Com a -> St -> Tree a
runInterp' env c st = set_label 0 $ fst $ runInterp env c st


-- Given the number of loop-carried variables, initialize the tree
-- table to a list of length 2^n containing all Nothings.
initialize_treetable :: Int -> InterpM ()
initialize_treetable n = modify $ second $ const $ replicate (2^n) Nothing

-- Construct the tree for the body of a loop that contains
-- loop-carried boolean variables. Arguments: loop body, loop
-- condition expression, program state, loop-carried variables. Make
-- sure the tree table is initialized beforehand.
mkLoop :: Com St -> Exp Bool -> St -> [SomeName] -> InterpM (Tree St)
mkLoop body_com e st names =
  -- Compute the index into the tree table using the values of the
  -- loop-carried variables.
  let vals = map (\(SomeName nm) -> SomeVal $ fromJust $ get nm st) $ sort names
      i = int_of_bool_vals vals
  in do
    tree_table <- gets snd
    fresh_lbl <- freshLbl
    case tree_table !! i of
      -- If the tree at index i has already been constructed, return
      -- it (this will be a hole pointing to the original).
      Just t -> return t
      -- Otherwise we must build the tree and update the tree table.
      Nothing -> do
        -- Pre-emptively update the tree table with a hole pointing to
        -- the tree that is currently being constructed so we don't
        -- diverge.
        modify $ second $ set_at i $ Just (Hole fresh_lbl)
        let kt = interp' body_com
        let kt' = \st' -> do
              b <- is_true e st'
              if not b then
                return $ Leaf st'
                else
                mkLoop body_com e st' names
        set_label fresh_lbl <$> kcomp kt kt' st

-- Treat a list of boolean Vals as the binary encoding of an integer.
int_of_bool_vals :: [SomeVal m g] -> Int
int_of_bool_vals = go 0
  where
    go :: Int -> [SomeVal m g] -> Int
    go n (SomeVal (VBool b) : vals) = (if b then 1 else 0) * 2^n + go (n+1) vals
    go _ [] = 0
    go _ v = error $ "int_of_bool_vals: expected boolean value, got " ++ show v
