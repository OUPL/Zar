{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}

module TreeRepr (c_infer) where

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
    ("flip", L.SomeTypeVal (TArrow TRational (TDist TBool)) bernoulli_prim)
  , ("float_of_int", L.SomeTypeVal (TArrow TInteger TFloat) float_of_int)
  ]

bernoulli_prim :: Val (Rational -> Tree Bool)
bernoulli_prim = VPrim f
  where
    f :: Val Rational -> InterpM (Exp (Tree Bool))
    f (VRational r) = do
      lbl <- freshLbl
      return $ EVal $ generalize_tree $ EVal . VBool <$> bernoulli r

float_of_int :: Val (Integer -> Double)
float_of_int = VPrim f
  where f :: Val Integer -> InterpM (Exp Double)
        f (VInteger i) = return $ EVal $ VFloat (fromIntegral i :: Double)

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


-- Experimental compositional inference

c_infer :: (a -> Double) -> Tree a -> Double
c_infer f (Leaf x) = f x
c_infer _ (Hole _) = 0.0
c_infer f (Split n t1 t2) =
  case n of
    Just n' ->
      ((1/2) * c_infer f t1 + (1/2) * c_infer f t2) /
      (1 - ((1/2) * c_infer_hole n' t1 + (1/2) * c_infer_hole n' t2))
    Nothing ->
      ((1/2) * c_infer f t1 + (1/2) * c_infer f t2)

c_infer_hole :: Int -> Tree a -> Double
c_infer_hole _ (Leaf _) = 0.0
c_infer_hole n (Hole m) = if n == m then 1.0 else 0.0
c_infer_hole n (Split m t1 t2) =
  case m of
    Just m' ->
      ((1/2) * c_infer_hole n t1 + (1/2) * c_infer_hole n t2) /
      (1 - ((1/2) * c_infer_hole m' t1 + (1/2) * c_infer_hole m' t2))
    Nothing ->
      ((1/2) * c_infer_hole n t1 + (1/2) * c_infer_hole n t2)
