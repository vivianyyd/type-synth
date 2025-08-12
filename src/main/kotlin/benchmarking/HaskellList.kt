package benchmarking

/**
Haskell List library functions

Included:
(:) :: a -> [a] -> [a]
null :: [a] -> Bool
length :: [a] -> Int
and :: [Bool] -> Bool
or :: [Bool] -> Bool
any :: (a -> Bool) -> [a] -> Bool
all :: (a -> Bool) -> [a] -> Bool
concat :: [[a]] -> [a]
(++) :: [a] -> [a] -> [a]
iterate :: (a -> a) -> a -> [a]
repeat :: a -> [a]
replicate :: Int -> a -> [a]
take :: Int -> [a] -> [a]
drop :: Int -> [a] -> [a]
splitAt :: Int -> [a] -> ([a] [a])
map :: (a -> b) -> [a] -> [b]
filter :: (a -> Bool) -> [a] -> [a]
takeWhile :: (a -> Bool) -> [a] -> [a]
dropWhile :: (a -> Bool) -> [a] -> [a]
span :: (a -> Bool) -> [a] -> ([a] [a])
break :: (a -> Bool) -> [a] -> ([a] [a])
reverse :: [a] -> [a]

Artificially added values:
0 :: Int
True :: Bool
IL :: [Int]
BL :: [Bool]
inc :: Int -> Int
not :: Bool -> Bool
id :: a -> a
isEven :: Int -> Bool
 */

val seedPositives = listOf(
    ""
)

val seedNegatives = listOf(
    ""
)

/**
Omitted for now:
foldr :: (a -> b -> b) -> b -> [a] -> b
foldl :: (b -> a -> b) -> b -> [a] -> b // TODO there was a forall here?
concatMap :: (a -> [b]) -> [a] -> [b]
uncons :: [a] -> Maybe (a [a])
unsnoc :: [a] -> Maybe ([a] a)
(!?) :: [a] -> Int -> Maybe a
zip :: [a] -> [b] -> [(a b)]
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
unzip :: [(a b)] -> ([a] [b])
 */