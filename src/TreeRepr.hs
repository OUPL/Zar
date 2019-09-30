{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}

module TreeRepr () where

import           Classes
import           Distributions
import           TreeInterp
import           Lang hiding (Exp, SomeTypeVal, Val)
import qualified Lang as L (Exp, SomeTypeVal(..), Val)
import           LinEq (infer')
import           Sample
import           Tree

type Exp         = L.Exp         InterpM Tree
type SomeTypeVal = L.SomeTypeVal InterpM Tree
type Val         = L.Val         InterpM Tree

-- | The list of predefined primitives. Used by the typechecker (name
-- and type information) and interpreter (name and value). For now
-- primitives can't be polymorphic, so the uniform distribution must
-- be built directly into the language rather than being a primitive
-- here.
prims :: [(String, SomeTypeVal)]
prims =
  [
    ("bernoulli", L.SomeTypeVal (TArrow TRational (TDist TBool)) bernoulli_prim)
  , ("float_of_int", L.SomeTypeVal (TArrow TInteger TFloat) float_of_int)    
  , ("sum_float", L.SomeTypeVal (TArrow (TList TFloat) TFloat) sum_float)
  , ("map_float", L.SomeTypeVal (TArrow (TPair (TArrow TFloat TFloat) (TList TFloat)) (TList TFloat)) map_float)
  , ("all_float", L.SomeTypeVal (TArrow (TPair (TArrow TFloat TBool) (TList TFloat)) TBool) all_float)
  ]

bernoulli_prim :: Val (Rational -> Tree Bool)
bernoulli_prim = VPrim f
  where
    f :: Val Rational -> InterpM (Exp (Tree Bool))
    f (VRational r) = do
      lbl <- freshLbl
      return $ EVal $ VDist $ EVal . VBool <$> bernoulli lbl r

float_of_int :: Val (Integer -> Double)
float_of_int = VPrim f
  where f :: Val Integer -> InterpM (Exp Double)
        f (VInteger i) = return $ EVal $ VFloat (fromIntegral i :: Double)

sum_float :: Val ([Double] -> Double)
sum_float = VPrim f
  where f :: Val [Double] -> InterpM (Exp Double)
        f VNil = return $ EVal $ VFloat 0
        f (VCons x l) = f l >>= \y -> return $ EBinop BPlus y (EVal x)

map_float :: Val ((Double -> Double, [Double]) -> [Double])
map_float = VPrim f
  where f :: Val (Double -> Double, [Double]) -> InterpM (Exp [Double])
        f (VPair _ VNil) = return $ EVal VNil
        f (VPair g (VCons x l)) = do
          l' <- f (VPair g l)
          return $ ECons (EApp (EVal g) (EVal x)) l'

all_float :: Val ((Double -> Bool, [Double]) -> Bool)
all_float = VPrim f
  where f :: Val (Double -> Bool, [Double]) -> InterpM (Exp Bool)
        f (VPair _ VNil) = return $ EVal (VBool True)
        f (VPair g (VCons x l)) = do
          b <- f (VPair g l)
          return $ EBinop BAnd (EApp (EVal g) (EVal x)) b

-- Tree instances
instance Sample Tree where
  sample = samplerIO -- in Sample.hs
deriving instance EqF Tree
deriving instance ShowF Tree
deriving instance AllF Tree

-- Here we can provide other inference methods. (TODO: exact inference)
instance Infer Tree where
  infers = [infer']

-- Representation instance for m = InterpM and g = Tree.
instance Repr InterpM Tree where
  primitives = prims
  interp     = runInterp' -- In TreeInterp.hs
