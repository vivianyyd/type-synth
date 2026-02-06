import benchmarking.parseHaskellTypes
import products.ExampleGenerator
import products.types.Assignment
import products.types.Type
import products.types.toSExpr
import products.types.toType
import query.Query
import util.SExpr
import util.SExprParser

fun Assignment.toSExprStrs() =
    this.entries.joinToString(separator = "\t") {
        "${SExpr.Lst(listOf(SExpr.Atm(it.key), it.value.toSExpr()))}"
    }

fun generate(types: List<Pair<Type, String?>>): Pair<Query, Assignment> {
    val (query, context) = ExampleGenerator(1, 2, 500, types).examples()
    println("Positive examples: ${query.posWithSubexprs.size}")
    println("Negative examples: ${query.neg.size}")
    return query to context
}

fun generateFromSExpr(types: List<Pair<String, String?>>): Pair<Query, Assignment> =
    generate(types.map { SExprParser(it.first).parse().toType() to it.second })

val toy =
    parseHaskellTypes(
        listOf(
            "cons :: a -> [a] -> [a]",
            "hd :: [a] -> a",
            "tl :: [a] -> [a]",
            //        "single :: a -> [a]",
            "0 :: Int",
            "IL :: [Int]",
            //        "FL :: List (a -> b)",
            "inc :: Int -> Int",
        )
    )

val haskellList =
    parseHaskellTypes(
        listOf(
            "(:) :: a -> [a] -> [a]",
            //        "foldr :: (a -> b -> b) -> b -> [a] -> b",
            //        "foldl :: (b -> a -> b) -> b -> [a] -> b", // TODO there was a forall here?
            "null :: [a] -> Bool",
            "length :: [a] -> Int",
            "and :: [Bool] -> Bool",
            "or :: [Bool] -> Bool",
            "any :: (a -> Bool) -> [a] -> Bool",
            "all :: (a -> Bool) -> [a] -> Bool",
            "concat :: [[a]] -> [a]",
            "concatMap :: (a -> [b]) -> [a] -> [b]",
            "map :: (a -> b) -> [a] -> [b]",
            "(++) :: [a] -> [a] -> [a]",
            "filter :: (a -> Bool) -> [a] -> [a]",
            "uncons :: [a] -> Maybe (a, [a])",
            "unsnoc :: [a] -> Maybe ([a], a)",
            "(!?) :: [a] -> Int -> Maybe a",
            "iterate :: (a -> a) -> a -> [a]",
            "repeat :: a -> [a]",
            "replicate :: Int -> a -> [a]",
            "take :: Int -> [a] -> [a]",
            "drop :: Int -> [a] -> [a]",
            "splitAt :: Int -> [a] -> ([a], [a])",
            "takeWhile :: (a -> Bool) -> [a] -> [a]",
            "dropWhile :: (a -> Bool) -> [a] -> [a]",
            "span :: (a -> Bool) -> [a] -> ([a], [a])",
            "break :: (a -> Bool) -> [a] -> ([a], [a])",
            "reverse :: [a] -> [a]",
            "zip :: [a] -> [b] -> [(a, b)]",
            "zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]",
            "unzip :: [(a, b)] -> ([a], [b])",
        ) +
                listOf(
                    "0 :: Int",
                    "True :: Bool",
                    "IL :: [Int]",
                    "BL :: [Bool]",
                    "inc :: Int -> Int",
                    "not :: Bool -> Bool",
                    "id :: a -> a",
                    "isEven :: Int -> Bool"
                )
    )

val haskellEither =
    parseHaskellTypes(
        listOf(
            "either :: (a -> c) -> (b -> c) -> Either a b -> c",
            "lefts :: [Either a b] -> [a]",
            "rights :: [Either a b] -> [b]",
            "isLeft :: Either a b -> Bool",
            "isRight :: Either a b -> Bool",
            "fromLeft :: a -> Either a b -> a",
            "fromRight :: b -> Either a b -> b",
            "partitionEithers :: [Either a b] -> ([a], [b])",
            "0 :: Int",
            "True :: Bool",
            "NilInt :: [Int]",
            "NilBool :: [Bool]"
        )
    )

val haskellMaybe =
    parseHaskellTypes(
        listOf(
            "maybe :: b -> (a -> b) -> Maybe a -> b",
            "isJust :: Maybe a -> Bool",
            "isNothing :: Maybe a -> Bool",
            "fromMaybe :: a -> Maybe a -> a",
            "listToMaybe :: [a] -> Maybe a",
            "maybeToList :: Maybe a -> [a]",
            "catMaybes :: [Maybe a] -> [a]",
            "mapMaybe :: (a -> Maybe b) -> [a] -> [b]",
            "0 :: Int",
            "True :: Bool",
            "NothingInt :: Maybe Int",
            "NothingBool :: Maybe Bool",
            "NilInt :: [Int]",
            "NilBool :: [Bool]"
        )
    )

val dict =
    listOf(
        "(i)",
        "(b)",
        "(d (i) (b))",
        "(d (b) (i))",
        "(d (i) (i))",
        "(d (b) (b))",
        "(-> (d k v) (-> k (-> v (d k v))))", // put
        "(-> (d a b) (-> (d b c) (d a c)))" // chain
    )

val small = listOf("(i)", "(b)", "(-> a (-> b a))")
