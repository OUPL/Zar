{-# LANGUAGE RebindableSyntax
           , OverloadedStrings
           , GADTs
           , TypeFamilies
           , GeneralizedNewtypeDeriving  
           , TypeSynonymInstances
           , FlexibleInstances
           , DataKinds
           , FlexibleContexts
           , MultiParamTypeClasses #-}

module Syntax where

import           Prelude hiding
  ( (>>)
  , (>>=)
  , (+)
  , (-)
  , (*)
  , (/)
  , (&&)
  , (||)
  , (==)
  , (<)
  , (<=)
  , not
  , return
  , fromRational
  , fromInteger
  , negate
  , ifThenElse
  )

import qualified Prelude

import           Control.Monad.State hiding (get)
import qualified Control.Monad.State as S (get)

import           Data.Typeable
import           Data.String( IsString(..) )

import           Lang hiding (Com, Exp, St, Val, Env, interp)
import qualified Lang (Com, Exp, St, Val)
import           Tree
import           TreeInterp

type Com = Lang.Com InterpM Tree
type Exp = Lang.Exp InterpM Tree
type St  = Lang.St  InterpM Tree
type Val = Lang.Val InterpM Tree
--type Env = [Lang.SomeNameExp InterpM Tree]

newtype SyntaxM a = SyntaxM { unSyntaxM :: State Integer a }
  deriving (Functor)

instance Applicative SyntaxM where
  pure = SyntaxM . pure
  SyntaxM f <*> SyntaxM x = SyntaxM $ f <*> x

instance Monad SyntaxM where
  (>>=) (SyntaxM m) g = SyntaxM $ (Prelude.>>=) m (unSyntaxM . g)
  return = pure

instance MonadState Integer SyntaxM where
  get = SyntaxM S.get
  put s = SyntaxM $ put s

freshVar :: String -> SyntaxM (Name a)
freshVar x =
  (Prelude.>>=) S.get $ \counter ->
  (Prelude.>>=) (put ((Prelude.+) counter 1)) $ \_ -> 
  Prelude.return $ ("_" ++ x ++ show counter, Proxy)

runSyntax :: SyntaxM a -> a
runSyntax m = Prelude.fst (runState (unSyntaxM m) 0)

{-- VALUES --}

class FromRational a where
  fromR :: Rational -> a

instance FromRational (Val Rational) where
  fromR = VRational

instance FromRational (Exp Rational) where
  fromR = EVal . fromR

instance FromRational (Val Double) where
  fromR r = VFloat (Prelude.fromRational r)

instance FromRational (Exp Double) where
  fromR = EVal . fromR

fromRational :: FromRational a => Rational -> a
fromRational = fromR

class FromInteger a where
  fromI :: Integer -> a

instance FromInteger Integer where
  fromI = Prelude.fromInteger

instance FromInteger (Val Integer) where
  fromI = VInteger

instance FromInteger (Exp Integer) where
  fromI = EVal . fromI

instance FromInteger (Exp Double) where
  fromI i = EVal $ VFloat $ Prelude.fromIntegral i

fromInteger :: FromInteger a => Integer -> a
fromInteger = fromI

dist :: (Eq a, Show a) => Tree (Exp a) -> Val (Tree a)
dist = VDist

lam :: (Show a, Typeable a, Eq b, Show b) => Name a -> Exp b -> Val (a -> b)
lam = VLam

prim :: (Show a, Typeable a) => (Val a -> InterpM (Exp b)) -> Val (a -> b)
prim = VPrim

{-- EXPRESSIONS --}

instance IsString (Name a) where
  fromString x = (x, Proxy)

instance IsString (Exp a) where
  fromString x = EVar $ fromString x

val :: Val a -> Exp a
val = EVal

true :: Exp Bool
true = val $ VBool True

false :: Exp Bool
false = val $ VBool False

destruct :: (Show a, Typeable a, Show b, Typeable b) =>
            Exp [a] -> Exp b -> Exp (a -> [a] -> b) -> Exp b
destruct = EDestruct

(+) :: (Show a, Eq a, Typeable a) => Exp a -> Exp a -> Exp (BinopResTy BTPlus a a)
(+) = EBinop BPlus

(-) :: (Show a, Eq a, Typeable a) => Exp a -> Exp a -> Exp (BinopResTy BTMinus a a)
(-) = EBinop BMinus

(*) :: (Show a, Eq a, Typeable a) => Exp a -> Exp a -> Exp (BinopResTy BTMult a a)
(*) = EBinop BMult

(/) :: (Show a, Eq a, Typeable a) => Exp a -> Exp a -> Exp (BinopResTy BTDiv a a)
(/) = EBinop BDiv

(&&) :: (Show a, Eq a, Typeable a) => Exp a -> Exp a -> Exp (BinopResTy BTAnd a a)
(&&) = EBinop BAnd

(||) :: (Show a, Eq a, Typeable a) => Exp a -> Exp a -> Exp (BinopResTy BTOr a a)
(||) = EBinop BOr

infix 3 ==
(==) :: (Show a, Eq a, Typeable a) => Exp a -> Exp a -> Exp (BinopResTy BTEq a a)
(==) = EBinop BEq

infix 3 <
(<) :: (Show a, Eq a, Typeable a) => Exp a -> Exp a -> Exp (BinopResTy BTLt a a)
(<) = EBinop BLt

infix 3 <=
(<=) :: (Show a, Eq a, Typeable a) => Exp a -> Exp a -> Exp (BinopResTy BTLt a a)
(<=) e1 e2 = (e1 < e2) || (e1 == e2)

fun :: (Show a, Typeable a, Eq b, Show b, Typeable b) => Name a -> Exp b -> Exp (a -> b)
fun = ELam

unif :: (Eq a, Show a, Typeable a) => Exp [a] -> Exp (Tree a)
unif = EUniform

pair :: (Typeable a, Eq a, Show a, Typeable b, Eq b, Show b) => 
        Exp a -> Exp b -> Exp (a,b)
pair = EPair

fst :: (Typeable a, Eq a, Show a, Typeable b, Eq b, Show b) => Exp (a, b) -> Exp a
fst = EUnop UFst

snd :: (Typeable a, Eq a, Show a, Typeable b, Eq b, Show b) => Exp (a, b) -> Exp b
snd = EUnop USnd

nil :: (Typeable a, Eq a, Show a) => Exp [a]
nil = ENil 

cons :: (Typeable a, Eq a, Show a) => Exp a -> Exp [a] -> Exp [a]
cons = ECons

{-- COMMANDS --}

skip :: SyntaxM (Com St)
skip = Prelude.return Skip

class SampleAssign a b where
  sample_assign :: Name a -> Exp b -> Com St

instance (Show a, Typeable a) => SampleAssign a (Tree a) where
  sample_assign = Sample

instance (Show a, Typeable a) => SampleAssign a a where
  sample_assign = Assign

(>>=) :: (Show a,Typeable a, Show b,Typeable b, Show c,Typeable c, SampleAssign b a) => 
         Exp a -> (Exp b -> SyntaxM (Com c)) -> SyntaxM (Com c)
(>>=) e f =
  (Prelude.>>=) (freshVar "internal") $ \x ->
  (Prelude.>>=) (f (Lang.EVar x)) $ \k -> 
  Prelude.return $ Seq (sample_assign x e) k

(>>) :: (Show a, Typeable a) => SyntaxM (Com St) -> SyntaxM (Com a) -> SyntaxM (Com a)
(>>) m1 m2 =
  (Prelude.>>=) m1 $ \c1 ->
  (Prelude.>>=) m2 $ \c2 ->  
  Prelude.return $ Seq c1 c2

infix 3 <--
(<--) :: (Show a, Typeable a) => Exp a -> Exp a -> SyntaxM (Com St)
(<--) (EVar x) e = Prelude.return $ Assign x e
(<--) x        _ = error $ "tried to assign nonvariable expression " ++ show x

ifThenElse :: (Show a, Typeable a) =>
              Exp Bool -> SyntaxM (Com a) -> SyntaxM (Com a) -> SyntaxM (Com a)
ifThenElse e m1 m2 =
  (Prelude.>>=) m1 $ \c1 ->
  (Prelude.>>=) m2 $ \c2 ->
  Prelude.return $ Ite e c1 c2

observe :: Exp Bool -> SyntaxM (Com St)
observe e = Prelude.return $ Observe e

return :: (Show a, Typeable a) => Exp a -> SyntaxM (Com (Exp a))
return e = Prelude.return $ Return e

while :: Exp Bool -> SyntaxM (Com St) -> SyntaxM (Com St)
while e m =
  (Prelude.>>=) m $ \c -> 
  Prelude.return $ While e c

{-- PRELUDE HACKS --}

int :: Val Integer -> Int
int (VInteger i) = fromIntegral i

infix 5 # -- note(jgs): Must be greater than <--, <~~
(#) :: (Show a, Typeable a, Show b) => Exp (a -> b) -> Exp a -> Exp b
(#) = EApp

{-- ZAR PRELUDE --}

head :: (Eq a, Show a, Typeable a) => Exp a -> Exp [a] -> Exp a
head def l = destruct l def (ELam "x" $ ELam "xs" "x")

tail :: (Eq a, Show a, Typeable a) => Exp [a] -> Exp [a]
tail l = destruct l ENil (ELam "x" $ ELam "xs" "xs")

float_of_int :: Exp (Integer -> Double)
float_of_int = "float_of_int"
