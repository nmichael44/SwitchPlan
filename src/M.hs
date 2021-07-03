{-# LANGUAGE InstanceSigs #-}

module M where

import qualified Data.Map.Strict as Map

data Tree a = Leaf a | Node (Tree a) (Tree a)

countLeafs :: Tree a -> Int 
countLeafs (Leaf _) = 1
countLeafs (Node t0 t1) = countLeafs t0 + countLeafs t1

type State s a = s -> (a, s)

type WithCounter a = State Int a

next :: WithCounter a -> (a -> WithCounter b) -> WithCounter b
f `next` g = \i -> let (a, j) = f i in g a j

pur :: a -> WithCounter a
pur x i = (x, i)

relabel :: Tree a -> Tree (Int, a)
relabel t
  = fst $ go t 0
  where
    go :: Tree a -> WithCounter (Tree (Int, a))
    go (Leaf x) = \i -> (Leaf (i, x), i + 1)
    go (Node t0 t1) =
      go t0 `next` (\t0' ->
        go t1 `next` (\t1' ->
          pur $ Node t0' t1'))

newtype WC a = WC (Int -> (a, Int))

instance Functor WC where
  fmap :: (a -> b) -> WC a -> WC b
  fmap f (WC g) = WC (\i -> let (a, i') = g i in (f a, i'))

instance Applicative WC where

  pure :: a -> WC a
  pure x = WC (\i -> (x, i))

  (<*>) :: WC (a -> b) -> WC a -> WC b
  (<*>) (WC f) (WC g) =
    WC (\i -> let (h, i') = f i
                  (a, i'') = g i'
              in (h a, i''))

instance Monad WC where
  (>>=) :: WC a -> (a -> WC b) -> WC b
  (>>=) (WC f) g = WC (\i -> let (a, i') = f i
                                 WC h = g a
                                 (b, i'') = h i'
                             in (b, i''))

  return = pure

relabel' :: Tree a -> Tree (Int, a)
relabel' t
  = let (WC f) = go t in fst $ f 0
  where
    go :: Tree a -> WC (Tree (Int, a))
    go (Leaf x) = WC $ \i -> (Leaf (i, x), i + 1)
    go (Node t0 t1)
      = do
          t0' <- go t0
          t1' <- go t1
          return $ Node t0' t1'

insertWith' :: Ord k => (a -> b -> b) -> (a -> b) -> k -> a -> Map.Map k b -> Map.Map k b
insertWith' f g k x
  = Map.alter (\oy ->
                 Just $ case oy of
                          Just y -> f x y
                          Nothing -> g x) k
