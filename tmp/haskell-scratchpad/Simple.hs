{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
module Simple where

a = do x <- [3..4]
       [1..2]
       return (x, 42)

inc :: Int -> Int
inc x = x + 1

{-# NOINLINE f #-}
f :: Eq a => a -> a -> Bool
f x y = (==) x y

g :: Int -> Bool
g x = f 0 x

monadd :: Monad m => m Int -> m Int
monadd mx = do
  x <- mx
  return (x + 1)

-- Becomes:
{-
ds_monadd :: DMonad m -> m Int -> m In
ds_monadd dmonad mint =
      dmonad.(>>=)
        mint 
        (\ (x :: Int) ->
           dmonad.return
             (+ x 1))
-}
-- Check if real desugared output is valid Haskell

-- Suppose monadd is the library function we wanna call...
-- Write new function
{-# LANGUAGE RankNTypes #-}
d_monadd :: Monad m => DMonad m -> m Int -> m Int
-- It's actually ok to keep the typeclass constraint in here, since we can control the
-- dictionaries we'll just only generate valid ones to expose in examples 
d_monadd dmonad mint = monadd mint
-- The only change is we take the typeclass constraints, prepend D to all typeclasses, then
--   flatten [(X a, Y b) => rest] into [DX a -> DY b -> rest]
-- How to enforce at compile-time that the dictionary passed matches the monad passed?
-- e.g. We as wrapper guys have to be able to tell if the code that calls the wrapper
--      passed the correct lookup table. That's cus we let the synthesis algo make arbitrary
--      new examples...
--     Ah, we can make the lookup tables contain the monad as a parameter like in 
--     -ddump-ds. And we control the lookup tables themselves.
data DMonad (m :: * -> *) = DMonad 
-- f is a type constructor of kind * -> *
--data MyRecord (f :: * -> *) = MyRecord
--  { value :: f Int
--  , run   :: f Bool
--  }
{- 
data DMonad m = DMonad 
  { (>>=)  :: m a -> (a -> m b) -> m b
  , (>>)   :: m a -> m b        -> m b
  , return :: a                 -> m a
}
-}

isDouble :: (Eq a, Num a) => a -> a -> Bool
isDouble x y = x == 2 * y

-- Becomes:
-- d_isDouble :: DEq a -> DNum a -> a -> a -> Bool
-- d_isDouble deq dnum x y = deq.(==) x (dnum.(*) y)


-- Need to define Eqdict 'a to be a record parameterized type w all the
-- appropriate fns. My understanding is this dictionary isn't really exposed
-- unless we reach in and get tcbinds
-- is there an easy way to get this or would they suggest working with ghc api
-- desired output is valid haskell but declasses desugared
-- want it to look similar to desugared dump
{-
isDouble_desugar :: Eqdict a -> Numdict a -> a -> a -> Bool
isDouble_desugar
  = \ (dEq_a :: Eqdict a)
      (dNum_a :: Numdict a)
      (x :: a)
      (y :: a) ->
      dEq_a.(==)
        x
        (dNum_a.(*) (fromInteger dNum_a 2) y)

isDouble_desugar :: Eqdict a -> Numdict a -> a -> a -> Bool
isDouble_desugar
  = \ (dEq_a :: Eqdict a)
      (dNum_a :: Numdict a)
      (x :: a)
      (y :: a) ->
      (==) dEq_a
        x
        ((*) dNum_a (fromInteger dNum_a 2) y)
-}

{-
I can get the input types of f_desugar easily from ddump-ds output,
but the output type requires resolving variable bindings
- Not so bad if ddump-prep, all names resolved, *should* only have variables free,
  but ideally want a nice mapping from type signature to names in definition 

f_desugar :: forall a. Eqdict a -> a -> a -> Bool
f_desugar 
  = \ (@ a)
      (dEq_a :: EqDict a)
      (x :: a)
      (y :: a) ->
      == @ a dEq_a x y


-- Need to define Eqdict 'a to be a record parameterized type w all the
-- appropriate fns 
isDouble_desugar :: forall a. Eqdict a -> Numdict a -> a -> a -> Bool
isDouble_desugar
  = \ (@ a)
      (dEq_a :: Eq a)
      (dNum_a :: Num a)
      (x :: a)
      (y :: a) ->
      ==
        @ a
        dEq_a
        x
        (* @ a dNum_a (fromInteger @ a dNum_a 2) y)

monadd :: forall (m :: * -> *). Monad m => m Int -> m Int
monadd
  = \ (@ (m :: * -> *))
      (dMonad_m :: Monad m)
      (m_Int :: m Int) ->
      >>=
        @ m
        dMonad_m
        @ Int
        @ Int
        m_Int
        (\ (x :: Int) ->
           return
             @ m
             dMonad_m
             @ Int
             (+ @ Int GHC.Num.$fNumInt x (GHC.Types.I# 1#)))

TODO what happens when there are redundant type constraints
-}
