{-# LANGUAGE RebindableSyntax, GADTs #-}

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
  , not
  , return
  , fromRational
  , fromInteger
  , negate
  , ifThenElse  
  )

import           Data.Typeable

import           Lang hiding (Com, Exp, St, Val, interp)
import qualified Lang (Com, Exp, St, Val)
import           Tree
import           TreeInterp

type Com = Lang.Com InterpM Tree
type Exp = Lang.Exp InterpM Tree
type St  = Lang.St  InterpM Tree
type Val = Lang.Val InterpM Tree

{-- VALUES --}

fromRational :: Rational -> Val Rational
fromRational = VRational

fromInteger :: Integer -> Val Integer
fromInteger = VInteger

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

pair :: (Eq a, Show a, Eq b, Show b) => Val a -> Val b -> Val (a, b)
pair = VPair

lam :: (Show a, Typeable a, Eq b, Show b) => Name a -> Exp b -> Val (a -> b)
lam = VLam

prim :: (Show a, Typeable a) => (Val a -> InterpM (Exp b)) -> Val (a -> b)
prim = VPrim

{-- EXPRESSIONS --}

destruct :: (Show a, Typeable a, Show b) => Exp [a] -> Exp b -> Exp (a -> [a] -> b) -> Exp b
destruct = EDestruct

head :: (Eq a, Show a, Typeable a) => Exp a -> Exp [a] -> Exp a
head def l =
  let x  = ("x", Proxy)
      xs = ("xs", Proxy)
  in destruct l def (ELam x $ ELam xs $ EVar x)

tail :: (Eq a, Show a, Typeable a) => Exp [a] -> Exp [a]
tail l =
  let x  = ("x", Proxy)
      xs = ("xs", Proxy)
  in destruct l (EVal nil) (ELam x $ ELam xs $ EVar xs)

{-- COMMANDS --}

skip :: Com St
skip = Skip

(<--) :: (Show a, Typeable a) => Name a -> Exp a -> Com St
(<--) = Assign

(>>) :: Com St -> Com a -> Com a
(>>) = Seq

ifThenElse :: (Show a, Typeable a) => Exp Bool -> Com a -> Com a -> Com a
ifThenElse = Ite

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

  
