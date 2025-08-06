import benchmarking.parseHaskellTypes
import query.ExampleGenerator
import query.Query
import query.sexpsFromExamples
import types.Assignment
import types.Type
import types.toSExpr
import types.toType
import util.SExpr
import util.SExprParser
import util.writeExamples

private fun Assignment.toSExprStrs() = this.entries.joinToString(separator = "\t") {
    "${SExpr.Lst(listOf(SExpr.Atm(it.key), it.value.toSExpr()))}"
}

fun main() {
    val test = haskellEither
    val (query, context) = generate(test)
    val generatedExs =
        (sexpsFromExamples(query.posExamples, true) + sexpsFromExamples(query.negExamples, false))
            .joinToString(separator = "\n")
    writeExamples("${context.toSExprStrs()}\n$generatedExs", "haskell-either")
}

fun generate(types: List<Pair<Type, String?>>): Pair<Query, Assignment> {
    val (query, context) = ExampleGenerator(1, 2, 500, types).examples()
    println("Positive examples: ${query.posExamples.size}")
    println("Negative examples: ${query.negExamples.size}")
    return query to context
}

fun generateFromSExpr(types: List<Pair<String, String?>>): Pair<Query, Assignment> =
    generate(types.map { SExprParser(it.first).parse().toType() to it.second })

val haskellList = parseHaskellTypes(
    listOf(
        "(:) :: a -> [a] -> [a]",
        "foldr :: (a -> b -> b) -> b -> [a] -> b",
        "foldl :: (b -> a -> b) -> b -> [a] -> b", // TODO there was a forall here?
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
    )
)

val haskellEither = parseHaskellTypes(
    listOf(
        "either :: (a -> c) -> (b -> c) -> Either a b -> c",
        "lefts :: [Either a b] -> [a]",
        "rights :: [Either a b] -> [b]",
        "isLeft :: Either a b -> Bool",
        "isRight :: Either a b -> Bool",
        "fromLeft :: a -> Either a b -> a",
        "fromRight :: b -> Either a b -> b",
        "partitionEithers :: [Either a b] -> ([a], [b])"
    )
) + listOf(
    "(i)" to "0",
    "(b)" to "true",
    "(List (i))" to "NilInt", // Nil Int
    "(List (b))" to "NilBool", // Nil Bool
).map { SExprParser(it.first).parse().toType() to it.second }

val haskellMaybe = listOf(
    "(-> b (-> (-> a b) (-> (Maybe a) b)))" to "maybe", // maybe :: b -> (a -> b) -> Maybe a -> b
    "(-> (Maybe a) (b))" to "isJust", // isJust :: Maybe a -> Bool
    "(-> (Maybe a) (b))" to "isNothing", // isNothing :: Maybe a -> Bool
    "(-> a (-> (Maybe a) a))" to "fromMaybe", // fromMaybe :: a -> Maybe a -> a
    "(-> (List a) (Maybe a))" to "listToMaybe", // listToMaybe :: [a] -> Maybe a
    "(-> (Maybe a) (List a))" to "maybeToList", // maybeToList :: Maybe a -> [a]
    "(-> (List (Maybe a)) (List a))" to "catMaybes", // catMaybes :: [Maybe a] -> [a]
    "(-> (-> a (Maybe b)) (-> (List a) (List b)))" to "mapMaybe", // mapMaybe :: (a -> Maybe b) -> [a] -> [b]
) + listOf(
    "(i)" to "0",
    "(b)" to "true",
    "(Maybe (i))" to "NothingInt", // Nothing Int
    "(Maybe (b))" to "NothingBool", // Nothing Bool
    "(List (i))" to "NilInt", // Nil Int
    "(List (b))" to "NilBool", // Nil Bool
)

val dict = listOf(
    "(i)", "(b)",
    "(d (i) (b))",
    "(d (b) (i))",
    "(d (i) (i))",
    "(d (b) (b))",
    "(-> (d k v) (-> k (-> v (d k v))))", // put
    "(-> (d a b) (-> (d b c) (d a c)))" // chain
)

val small = listOf("(i)", "(b)", "(-> a (-> b a))")
