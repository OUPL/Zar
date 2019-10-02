{-# LANGUAGE GADTs #-}

module List where

import Data.Typeable
import Lang


-- | Generic list functions.

len :: (Show a, Typeable a, Repr m g) => Exp m g ([a] -> Integer)
len = EVal $ VPrim f
  where
    f :: Repr m g => Val m g [a] -> m (Exp m g Integer)
    f VNil = return $ EVal $ VInteger 0
    f (VCons _ l) =
      let n = EApp len $ Lang.EVal l
      in return $ EBinop BPlus n (EVal $ VInteger $ 1)
    f (VDist _) = error "len: expected list"

map :: (Show a, Typeable a, Eq b, Show b, Typeable b, Repr m g) =>
       Exp m g ((a -> b, [a]) -> [b])
map = EVal $ VPrim f
  where
    f :: (Eq b, Show b, Typeable b, Repr m g) =>
         Val m g (a -> b, [a]) -> m (Exp m g [b])
    f (VPair _ VNil) = return $ EVal VNil
    f (VPair g (VCons x l)) = do
      l' <- f (VPair g l)
      return $ ECons (EApp (EVal g) (EVal x)) l'
    f (VPair _ (VDist _)) = error "map: expected list"
    f (VDist _) = error "map: expected list"

-- Curried version of map.
map' :: (Show a, Typeable a, Eq b, Show b, Typeable b, Repr m g) =>
       Exp m g ((a -> b) -> [a] -> [b])
map' = EVal $ VPrim f
  where
    f :: (Show a, Typeable a, Eq b, Show b, Typeable b, Repr m g) =>
         Val m g (a -> b) -> m (Exp m g ([a] -> [b]))
    f g = return $ EVal $ VPrim $ h $ EVal g
    h :: (Eq b, Show b, Typeable b, Repr m g) =>
         Exp m g (a -> b) -> Val m g [a] -> m (Exp m g [b])
    h _ VNil = return $ EVal VNil
    h g (VCons x l) = ECons (EApp g $ EVal x) <$> h g l
    h _ (VDist _) = error "map: expected list"

foldleft :: (Show a, Typeable a, Show b, Typeable b, Repr m g) =>
         Exp m g (([a], (b, (b, a) -> b)) -> b)
foldleft = EVal $ VPrim f
  where
    f :: (Typeable b, Repr m g) =>
         Val m g ([a], (b, (b, a) -> b)) -> m (Exp m g b)
    f (VPair VNil (VPair z _)) = return $ EVal z
    f (VPair (VCons x l) (VPair z g)) = do
      z' <- f $ VPair l $ VPair z g
      return $ EApp (EVal g) $ EPair z' (EVal x)
    f _ = error "foldleft: expected list"

-- foldleft :: (Show a, Typeable a, Show b, Typeable b, Monad m) =>
--          Exp m g (([a], (b, b -> a -> b)) -> b)
-- foldleft = EVal $ VPrim f
--   where
--     f :: (Typeable b, Monad m) =>
--          Val m g ([a], (b, b -> a -> b)) -> m (Exp m g b)
--     f (VPair l (VPair z g)) = f' l (EVal z) (EVal g)
--     f _ = error "foldleft: expected list"

--     f' :: (Show b, Typeable b, Monad m) =>
--           Val m g [a] -> Exp m g b -> Exp m g (b -> a -> b) -> m (Exp m g b)
--     f' VNil z _ = return z
--     f' (VCons x l) z g = do
--       z' <- f' l z g
--       return $ EApp (EApp g z') (EVal x)
--     f' (VDist _) _ _ = error "foldleft: expected list"

foldright :: (Show a, Typeable a, Show b, Typeable b, Repr m g) =>
             Exp m g (([a], ((a, b) -> b, b)) -> b)
foldright = EVal $ VPrim f
  where
    f :: (Typeable b, Repr m g) =>
         Val m g ([a], ((a, b) -> b, b)) -> m (Exp m g b)
    f (VPair l (VPair g z)) = f' (EVal z) l (EVal g)
    f _ = error "foldright: expected list"
    
    f' :: (Eq b, Show b, Typeable b, Repr m g) =>
          Exp m g b -> Val m g [a] -> Exp m g ((a, b) -> b) -> m (Exp m g b)
    f' acc VNil _ = return acc
    f' acc (VCons x l) g = f' (EApp g (EPair (EVal x) acc)) l g
    f' _ (VDist _) _ = error "foldright: expected list"

-- curry' :: Exp m g ((a, b) -> c) -> Exp m g (a -> b -> c)
-- curry' = undefined

-- uncurry' :: Exp m g (a -> b -> c) -> Exp m g ((a, b) -> c)
-- uncurry' = undefined

-- flip' :: Exp m g (a -> b -> c) -> Exp m g (b -> a -> c)
-- flip' = undefined

-- all :: (Show a, Typeable a, Monad m) => Exp m g (([a], (a -> Bool)) -> Bool)
-- -- all = EApp (flip (EApp (flip' (curry' foldleft)) (EVal $ VBool True))) f

-- all = EVal $ VPrim f
--   where
--     f :: (Show a, Typeable a, Monad m) =>
--          Val m g ([a], (a -> Bool)) -> m (Exp m g Bool)
--     f (VPair l g) =
--       return $ EApp foldleft $ EVal $ VPair l (VPair (VBool True) (VPrim $ h g))
--     f (VDist _) = error "all: expected pair"

--     h :: Val m g (a -> Bool) -> Val m g (Bool -> a -> Bool)
--     h g = 
