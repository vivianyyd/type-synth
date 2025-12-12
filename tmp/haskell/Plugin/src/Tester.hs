module Tester where

foo :: Eq a => a -> Bool
foo x = x == x

bar :: Bool -> Bool
bar b = not b

