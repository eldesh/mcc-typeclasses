-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module Combinatorial where

--- Compute any permuation of a list
permute :: [a] -> [a]
permute []     = []
permute (x:xs) = insert x (permute xs)
  where insert x []	  = [x]
	insert x ys@(_:_) = x : ys
	insert x (y:ys)	  = y : insert x ys

--- Compute any sublist of a list
subset :: [a] -> [a]
subset []     = []
subset (x:xs) = x : subset xs
subset (_:xs) = subset xs

--- Split a list into any two sublists
splitSet :: [a] -> ([a],[a])
splitSet []	= ([],[])
splitSet (x:xs) = (x:ys,zs) ? (ys,x:zs)
  where (ys,zs) = splitSet xs

--- Compute any sublist of fixed length of a list
sizedSubset :: Int -> [a] -> [a]
sizedSubset n []     | n == 0 = []
sizedSubset n (x:xs) | n > 0  = x : sizedSubset (n - 1) xs
sizedSubset n (_:xs)          = sizedSubset n xs

--- Compute any partition of a list
partition :: [a] -> [[a]]
partition []	 = []
partition (x:xs) = insert x (partition xs)
  where insert x []	  = [[x]]
	insert x (xs:xss) = (x:xs) : xss
	insert x (xs:xss) = xs : insert x xss
