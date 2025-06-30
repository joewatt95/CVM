module Main where

import Data.List (delete)
import SimulationMonad

threshold :: Int
threshold = 10

stream :: [Int]
stream = [0..15]

-- Remove the nth element of a list e.g. remove 1 [a,b,c] = [a,c]
remove :: Int -> [a] -> [a]
remove _ [] = error "unexpected"
remove 0 (_:xs) = xs
remove n (x:xs) = x:(remove (n-1) xs)

-- Initial state
f0_init :: ([a],Rational)
f0_init = ([],1)

-- Subsampling operation remove randomly (treshold/2 elements)
subsample :: [Int] -> Dist [Int]
subsample xs
  | length xs * 2 == threshold = return xs
  | otherwise = 
      do index <- sample (length xs)
         subsample (remove index xs)

f0_loop :: ([Int], Rational) -> [Int] -> Dist ([Int],Rational)
f0_loop (chi, p) [] = return (chi, p)
f0_loop (chi, p) (x:xs) =
  do let chi' = delete x chi
     coin <- bernoulli p
     let chi'' = (if coin then x:chi' else chi')
     if length chi'' == threshold then -- buffer full 
        do chi''' <- dedupe $ subsample chi''
           f0_loop (chi''', p / 2) xs
     else
        f0_loop (chi'', p) xs

f0_alg :: [Int] -> Dist ([Int], Rational)
f0_alg xs = f0_loop f0_init xs

test_f1 :: ([Int], Rational) -> Rational
test_f1 (chi, _) = if (length $ filter (\x -> x < 10) chi) >= 5 then 1 else 0

test_f2 :: ([Int], Rational) -> Rational
test_f2 (chi, _) = fromIntegral $ length $ filter (\x -> x >= 10) chi

-- Note: Both test_f1, test_f2 are monotone increasing and depend on disjoint indicator variables of chi.
-- If the indicator variables of chi were n.a., then we would have E test_f1 * test_f2 <= E test_f1 * E test_f2
-- I.e. the last inequality must be true. (But when we run the code, it will return False.) 
main :: IO ()
main = 
  do let state = f0_alg stream
     let x = expectation (fmap (test_f1) state)
     let y = expectation (fmap (test_f2) state)
     let z = expectation (fmap (\x -> test_f1 x * test_f2 x) state)
     putStrLn $ show $ x*y
     putStrLn $ show $ z
     putStrLn $ show $ z <= x*y

