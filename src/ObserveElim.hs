{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{- Implementation of the observe elimination transformation
   from Fig. 9 of "Conditioning in Probabilistic Programming" by
   Olmedo et al., TOPLAS'18 -}

module ObserveElim where

type Var = String

type Val = Int

type State = Var -> Val

-- Instance is specialized to program "c" below.
instance Show State where
  show s = "x=" ++ show (s "x") ++ ", y=" ++ show (s "y") ++ "\n"

type Pred = State -> Rational

statesOf :: [String] -> [State]
statesOf [] = [\x -> 0]
statesOf (x : xs) =
  concatMap (\f ->
               [\y -> if x == y then 0 else f y,
                \y -> if x == y then 1 else f y])
  $ statesOf xs

-- Instance is specialized to program "c" below.
instance Show Pred where
  show p = show $ map p $ statesOf ["x","y"]

data Exp =
    ValE Val
  | VarE Var
  deriving (Show)  

data Com =
    Skip
  | Abort
  | Assign Var Exp
  | Observe Pred
  | Seq Com Com
  | Ite Pred Com Com
  | Flip Pred Com Com
  deriving (Show)

one :: Pred
one = \_ -> fromIntegral 1

zero :: Pred
zero = \_ -> fromIntegral 0

neg :: Pred -> Pred
neg p s = 1 - p s

eval :: State -> Exp -> Val
eval s (ValE v) = v
eval s (VarE x) = s x

subst_state :: Var -> Exp -> State -> State
subst_state x e s y = if x == y then eval s e else s y

subst :: Var -> Exp -> Pred -> Pred
subst x e p s = p $ subst_state x e s

pand :: Pred -> Pred -> Pred
pand p q s = p s * q s

por :: Pred -> Pred -> Pred
por p q s = p s + q s

pdiv :: Pred -> Pred -> Pred
pdiv p q s = if q s == 0 then 0 else p s / q s

elim :: (Com, Pred) -> (Com, Pred)
elim p@(Skip, f) = p
elim (Abort, f) = (Abort, one)
elim (Assign x e, f) = (Assign x e, subst x e f)
elim (Observe p, f) = (Skip, pand p f)
elim (Seq c1 c2, f) =
  let (c2', f'') = elim (c2, f)
      (c1', f') = elim (c1, f'')
  in (Seq c1' c2', f')
elim (Ite p c1 c2, f) =
  let (c1', f1) = elim (c1, f)
      (c2', f2) = elim (c2, f)
  in (Ite p c1' c2', pand p f1 `por` pand (neg p) f2)
elim (Flip p c1 c2, f) =
  let (c1', f1) = elim (c1, f)
      (c2', f2) = elim (c2, f)
      p0 = pand p f1 `por` pand (neg p) f2
      p' = pand p f1 `pdiv` p0
  in (Flip p' c1' c2', p0)

c =
  Seq
    (Flip (\_ -> 1/2)
     (Assign "x" (ValE 1)) (Assign "x" (ValE 0)))
    (Ite (\s -> fromIntegral $ s "x")
       (Seq
         (Flip (\_ -> 1/2)
          (Assign "y" (ValE 1)) (Assign "y" (ValE 0)))
         (Observe (\s -> fromIntegral $ s "y")))
       Skip)

celim =
  let (c', f') = elim (c, one)
  in show (c', f' $ \y -> if y == "x" then 1 else 0)

pir =
  let gold = ValE 0
      pir  = ValE 1
  in       
  Seq
    (Flip (\_ -> 1/2) (Assign "f1" gold) (Assign "f1" pir))
    (Seq
      (Assign "f2" pir)
      (Seq
        (Flip (\_ -> 1/2)
           (Assign "rem" (VarE "f1"))
           (Assign "rem" (VarE "f2")))
        (Observe (\s -> fromIntegral $ s "rem"))))
pirelim =    
  let (pir', f') = elim (pir, one)
  in show (pir', f' $ \_ -> 1)

