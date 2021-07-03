{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module O where

import Data.Monoid
import Data.Profunctor
import Control.Applicative

data Tree a = Leaf a | Node (Tree a) (Tree a)
  deriving Show

countLeafs :: Tree a -> Int
countLeafs
  = go
  where
    go (Leaf _) = 1
    go (Node t0 t1) = go t0 + go t1

label :: forall a . Tree a -> Tree (Int, a)
label t
  = snd $ go t 0
  where
    go :: Tree a -> Int -> (Int, Tree (Int, a))
    go (Leaf x) i = (i + 1, Leaf (i, x))
    go (Node t0 t1) i
      = let
          (j, t0') = go t0 i
          (k, t1') = go t1 j
        in
          (k, Node t0' t1')

newtype ST s a = ST (s -> (s, a))

instance Functor (ST s) where
  fmap :: (a -> b) -> ST s a -> ST s b
  fmap f (ST g)
    = ST (\s ->
          let
            (s', a) = g s
          in
            (s', f a))

instance Applicative (ST s) where
  pure :: a -> ST s a
  pure a = ST (, a)

  (<*>) :: ST s (a -> b) -> ST s a -> ST s b
  (<*>) (ST f) (ST g)
    = ST (\s -> let
                  (s', h) = f s
                  (s'', a) = g s'
                in
                   (s'', h a))

instance Monad (ST s) where
  return :: a -> ST s a
  return = pure

  (>>=) :: ST s a -> (a -> ST s b) -> ST s b
  (>>=) (ST f) g
    = ST (\s -> let
                  (s', a) = f s
                  (ST h) = g a
                in
                  h s')

put :: s -> ST s ()
put s = ST $ const (s, ())

ask :: (ST s s)
ask = ST (\s -> (s, s))

runStateTransformer :: ST s a -> s -> a
runStateTransformer (ST f) s = snd $ f s

label' :: forall a . Tree a -> Tree (Int, a)
label' t
  = runStateTransformer (go t) 0
  where
    go :: Tree a -> ST Int (Tree (Int, a))
    go (Leaf x) = ST (\i -> (i + 1, Leaf (i, x)))
    go (Node t0 t1)
      = do
          t0' <- go t0
          t1' <- go t1
          pure $ Node t0' t1'

f1 :: Int -> Either String Int
f1 n = Right $ n + 1

f1' :: Int -> Either String Int
f1' _ = Left "f1 failed"

f2 :: String -> Either String Int
f2 s = Right (read s :: Int)

f2' :: String -> Either String Int
f2' _ = Left "f2 failed"

data A = A Int Int
  deriving Show

g :: Int -> String -> Either String A
g n s =
  do
    n1 <- f1 n
    n2 <- f2 s
    return $ A n1 n2

foo' :: (Monad m, Monoid a) => m a -> m a -> m a
foo' x y
  = do
      xx <- x
      yy <- y
      return $ xx `mappend` yy

foo :: Maybe (Sum Int)
foo = foo' (Just (Sum (10 :: Int))) (Just (Sum (11 :: Int)))

whileM :: Monad m => m Bool -> m a -> m [a]
whileM cond action
  = do
      c <- cond
      if c then
        do
          a <- action
          r <- whileM cond action
          return $ a : r
        else
           return []

whileM' :: Monad m => m Bool -> m a -> m [a]
whileM' cond action
  = do
      c <- cond
      if c then (:) <$> action <*> whileM' cond action
           else return []

inc :: ST Int Int
inc = ST (\s -> (s + 1, s))

inc' :: ST Int Int
inc' =
  do
    s <- ask
    put (s + 1)
    return s

boolCheck :: Int -> ST Int Bool
boolCheck end =
  do
    v <- ask
    return $ v < end

list1To10 :: [Int]
list1To10 =
  let
    startInc = - 11
    endExc = 21

    lessThanEnd = boolCheck endExc
    ml = whileM lessThanEnd inc'
  in
    runStateTransformer ml startInc

newtype Return a r = Re { f :: a -> r }

instance Profunctor Return where
  lmap :: (a' -> a) -> Return a r -> Return a' r
  lmap f (Re g) = Re (g . f)

  rmap :: (r -> r') -> Return a r -> Return a r'
  rmap f (Re g) = Re (f . g)

  dimap :: (a' -> a) -> (r -> r') -> Return a r -> Return a' r'
  dimap f g (Re h) = Re (g . h . f)

{-
data Ei a b = L a | R b

instance Functor (Ei a) where
  fmap :: (b -> c) -> Ei a b -> Ei a c
  fmap _ (L a) = L a
  fmap f (R b) = R $ f b

instance Applicative (Ei a) where
  pure :: b -> Ei a b
  pure = R

  (<*>) :: Ei a (b -> c) -> Ei a b -> Ei a c
  (<*>) (R f) (R b) = R $ f b
  (<*>) (L a) _ = L a
  (<*>) _ (L a) = L a

instance Monoid a => Alternative (Ei a) where
  empty :: Ei a b
  empty = L mempty

  (<|>) :: Ei a b -> Ei a b -> Ei a b
  (<|>) (R b) _ = R b
  (<|>) (L _) x = x

{-| Triple a list

>>> triple "a"
"aa"

-}

triple :: [a] -> [a]
triple x = x ++ x

rev1 :: [a] -> [a]
rev1 xs = loop xs []
  where
    loop :: [a] -> [a] -> [a]
    loop [] res = res
    loop (x : xs) res = loop xs (x : res)

rev2 :: [a] -> [a]
rev2 xs = loop xs []
  where
    loop :: [a] -> [a] -> [a]
    loop [] = id
    loop (x : xs) = loop xs . (x :)

-}
