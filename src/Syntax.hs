{-# LANGUAGE RebindableSyntax
           , OverloadedStrings
           , GADTs
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
type Env = [Lang.SomeNameExp InterpM Tree]

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

instance FromInteger (Val Integer) where
  fromI = VInteger

instance FromInteger (Exp Integer) where
  fromI = EVal . fromI

instance FromInteger (Exp Double) where
  fromI i = EVal $ VFloat $ Prelude.fromIntegral i

fromInteger :: FromInteger a => Integer -> a
fromInteger = fromI

true :: Val Bool
true = VBool True

false :: Val Bool
false = VBool False

dist :: (Eq a, Show a) => Tree (Exp a) -> Val (Tree a)
dist = VDist

nil :: (Eq a, Show a) => Val [a]
nil = VNil

cons :: (Eq a, Show a, Typeable a) => Val a -> Val [a] -> Val [a]
cons = VCons

class HasPair a b c where
  pair :: a -> b -> c

instance (Eq a, Show a, Eq b, Show b) => HasPair (Val a) (Val b) (Val (a, b)) where
  pair = VPair

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

instance (Typeable a, Eq a, Show a, Typeable b, Eq b, Show b)
         => HasPair (Exp a) (Exp b) (Exp (a,b)) where
  pair = EPair

fst :: (Typeable a, Eq a, Show a, Typeable b, Eq b, Show b) => Exp (a, b) -> Exp a
fst = EUnop UFst

snd :: (Typeable a, Eq a, Show a, Typeable b, Eq b, Show b) => Exp (a, b) -> Exp b
snd = EUnop USnd


{-- COMMANDS --}

skip :: Com St
skip = Skip

infix 3 <-- 
(<--) :: (Show a, Typeable a) => Name a -> Exp a -> Com St
(<--) = Assign

(>>) :: Com St -> Com a -> Com a
(>>) = Seq

ifThenElse :: (Show a, Typeable a) => Exp Bool -> Com a -> Com a -> Com a
ifThenElse = Ite

infix 3 <~~ 
(<~~) :: (Show a, Typeable a) => Name a -> Exp (Tree a) -> Com St
(<~~) = Sample

observe :: Exp Bool -> Com St
observe = Observe

return :: (Show a, Typeable a) => Exp a -> Com (Exp a)
return = Return

while :: Exp Bool -> Com St -> Com St
while = While

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

