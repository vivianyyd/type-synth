module Simple where

{-# NOINLINE f #-}
{-# NOINLINE bottom #-}
bottom :: a
bottom = undefined

f :: Eq a => a -> a -> Bool
f x y = bottom x y 

