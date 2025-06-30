-- This module introduces a monad with which it is possible to exactly evaluate the distribution
-- of randomized algorithms. This works by keeping track of the possible states with their respective
-- probabilities (using rational number arithmetic with big integers.)
module SimulationMonad where

import Data.Ratio
import Data.List.Extra (groupSort)

data Dist a = Dist { unDist :: [(a,Rational)] }

dedupe :: (Ord a) => Dist a -> Dist a
dedupe (Dist xs) = Dist $ map (\(x,vs) -> (x, sum vs)) $ groupSort xs

instance Monad Dist where
  return x = Dist [(x,1)]
  m >>= f = Dist $
    do (v,p) <- unDist m
       (w,q) <- unDist (f v)
       return (w,p*q)

instance Applicative Dist where
    pure = return
    a <*> b = do
        f <- a
        x <- b
        return (f x)
        
instance Functor Dist where
  fmap f m = m >>= (return . f)

expectation :: Dist Rational -> Rational
expectation (Dist d) = sum $ map (\(x,p) -> x * p) d

bernoulli :: Rational -> Dist Bool
bernoulli p = Dist [(True,p),(False,1-p)]

-- Sample uniformly from {0,..,n-1}
sample :: Int -> Dist Int
sample n = Dist $ map (\x -> (x,1 / fromIntegral n)) [0..n-1]



