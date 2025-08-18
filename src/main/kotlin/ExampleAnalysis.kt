import benchmarking.parseHaskellTypes
import query.*
import query.App
import util.SExprParser

/** AI-generated code I was toying with */
fun main() {
    println(groundTruth.toSExprStrs())
    val oracle = oracleFromAssignment(groundTruth.toSExprStrs())
    val exs = examples.map { SExprParser(it).parse().toExpression().first }

    val (pos, neg) = exs.partition { check(it, groundTruth) != null }
    println(pos.size)
    println(neg.size)

    val query = Query(pos, neg)
    vizUndir(query)

    // Example: 12 nodes (0..11)
    val n = query.names.size
    val matrix = Array(n) { IntArray(n) { 0 } }
    val indices = query.names.withIndex().associate { (i, n) -> n to i }
    query.posExsBeforeSubexprs.filterIsInstance<App>().forEach {
        it.names.forEach { n1 ->
            it.names.forEach { n2 ->
                val i1 = indices[n1]!!
                val i2 = indices[n2]!!
                matrix[i1][i2] += 1
                matrix[i2][i1] += 1
            }
        }
    }


    val (A, B) = balancedMinCut(matrix, cushion = 3, iterations = 20)
    println("Set A: ${A.map { query.names[it] }}}")
    println("Set B: ${B.map { query.names[it] }}}")

    // Compute cut weight
    val cutWeight = A.sumOf { i -> B.sumOf { j -> matrix[i][j] } }
    println("Cut weight: $cutWeight")

//    val G = Graph(n, matrix)
//    val subset = findDenseWeaklyConnectedSubset(G)
//
//    println("Chosen subset: ${subset.map { query.names[it] }}")
//    println("Internal density = ${internalDensity(G, subset)}")
//    println("External density = ${externalDensity(G, subset)}")
}

fun balancedMinCut(
    matrix: Array<IntArray>,
    cushion: Int = 0,
    iterations: Int = 10
): Pair<Set<Int>, Set<Int>> {
    val n = matrix.size
    if (n == 0) return emptySet<Int>() to emptySet<Int>()

    // Initial random split roughly in half
    val nodes = (0 until n).toList()
    val shuffled = nodes.shuffled()
    val portion = n / 3 // TODO tunable. for half was n/2
    var A = shuffled.take(portion).toMutableSet()
    var B = shuffled.drop(portion).toMutableSet()

    fun cutWeight(): Int {
        var sum = 0
        for (i in A) for (j in B) sum += matrix[i][j]
        return sum
    }

    repeat(iterations) {
        // Compute gain for all movable nodes
        val gains = mutableListOf<Triple<Int, Int, Int>>() // node, fromSetSize, gain
        for (i in nodes) {
            val fromSet = if (A.contains(i)) A else B
            val toSet = if (fromSet === A) B else A
            if (fromSet.size - 1 < portion - cushion || fromSet.size - 1 > portion + cushion) continue

            val internal = fromSet.sumOf { j -> matrix[i][j] }
            val external = toSet.sumOf { j -> matrix[i][j] }
            val gain = external - internal
            gains.add(Triple(i, fromSet.size, gain))
        }

        if (gains.isEmpty()) return@repeat

        // Move the node with max gain
        val (nodeToMove, _, _) = gains.maxByOrNull { it.third }!!
        if (A.contains(nodeToMove)) {
            A.remove(nodeToMove)
            B.add(nodeToMove)
        } else {
            B.remove(nodeToMove)
            A.add(nodeToMove)
        }
    }

    return A to B
}

data class Graph(val n: Int, val matrix: Array<IntArray>) {
    // n = number of nodes
    // matrix[i][j] = number of edges from i -> j (undirected)

    fun edgesInside(subset: Set<Int>): Int {
        var total = 0
        val nodes = subset.toList()
        for (i in nodes.indices) {
            for (j in i + 1 until nodes.size) {
                total += matrix[nodes[i]][nodes[j]]
            }
        }
        return total
    }

    fun edgesBetween(subset: Set<Int>): Int {
        val others = (0 until n).toSet() - subset
        var total = 0
        for (u in subset) {
            for (v in others) {
                total += matrix[u][v]
            }
        }
        return total
    }
}

fun internalDensity(G: Graph, S: Set<Int>): Double {
    if (S.size <= 1) return 0.0
    val possible = S.size * (S.size - 1) / 2.0
    return G.edgesInside(S) / possible
}

fun externalDensity(G: Graph, S: Set<Int>): Double {
    val others = G.n - S.size
    if (S.isEmpty() || others == 0) return 0.0
    val possible = S.size * others.toDouble()
    return G.edgesBetween(S) / possible
}

fun findDenseWeaklyConnectedSubset(G: Graph): Set<Int> {
    var bestSet = emptySet<Int>()
    var bestScore = Double.NEGATIVE_INFINITY

    for (start in 0 until G.n) {
        var current = mutableSetOf(start)
        var improved = true
        while (improved) {
            improved = false
            val candidates = (0 until G.n).toSet() - current
            val next = candidates.maxByOrNull { v ->
                val newSet = current + v
                internalDensity(G, newSet) - externalDensity(G, newSet)
            }
            if (next != null) {
                val newSet = current + next
                val score = internalDensity(G, newSet) - externalDensity(G, newSet)
                if (score > internalDensity(G, current) - externalDensity(G, current)) {
                    current = newSet.toMutableSet()
                    improved = true
                }
            }
        }
        val score = (internalDensity(G, current) - 0.3 * externalDensity(G, current)) * Math.log(1.0 + current.size)
        val epsilon = 10 // TODO tunable
        if (score >= bestScore - epsilon) {
            bestScore = score
            bestSet = current
        }
    }
    return bestSet
}

val groundTruth = parseHaskellTypes(
    listOf(
        "cons :: a -> [a] -> [a]",
        "hd :: [a] -> a",
        "tl :: [a] -> [a]",
        "singleton :: a -> [a]",
        "0 :: Int",
        "null :: [a] -> Bool",
        "length :: [a] -> Int",
        "and :: [Bool] -> Bool",
        "or :: [Bool] -> Bool",
        "any :: (a -> Bool) -> [a] -> Bool",
        "all :: (a -> Bool) -> [a] -> Bool",
        "concat :: [[a]] -> [a]",
        "concatMap :: (a -> [b]) -> [a] -> [b]",
        "map :: (a -> b) -> [a] -> [b]",
        "++ :: [a] -> [a] -> [a]",
        "filter :: (a -> Bool) -> [a] -> [a]",
        "uncons :: [a] -> Maybe (a, [a])",
        "unsnoc :: [a] -> Maybe ([a], a)",
        "!? :: [a] -> Int -> Maybe a",  // TODO these paren get erased by sexpr parser when we make the examples, so i just omit parens here too
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
        "0 :: Int",
        "True :: Bool",
        "False :: Bool",
        "NilInt :: [Int]",
        "NilBool :: [Bool]",
        "inc :: Int -> Int",
        "not :: Bool -> Bool",
        "id :: a -> a",
        "isEven :: Int -> Bool",
        "either :: (a -> c) -> (b -> c) -> Either a b -> c",
        "lefts :: [Either a b] -> [a]",
        "rights :: [Either a b] -> [b]",
        "isLeft :: Either a b -> Bool",
        "isRight :: Either a b -> Bool",
        "fromLeft :: a -> Either a b -> a",
        "fromRight :: b -> Either a b -> b",
        "partitionEithers :: [Either a b] -> ([a], [b])",
        "maybe :: b -> (a -> b) -> Maybe a -> b  ",
        "isJust :: Maybe a -> Bool",
        "isNothing :: Maybe a -> Bool",
        "fromMaybe :: a -> Maybe a -> a ",
        "listToMaybe :: [a] -> Maybe a  ",
        "maybeToList :: Maybe a -> [a]  ",
        "catMaybes :: [Maybe a] -> [a]  ",
        "mapMaybe :: (a -> Maybe b) -> [a] -> [b]",
        "NothingInt :: Maybe Int  ",
        "NothingBool :: Maybe Bool",
        "Just :: a -> Maybe a",
    )
).map { (t, n) -> n to t }.toMap()

val examples = listOf(
    "filter not (cons True NilBool)",
    "(++) (repeat False) (singleton False)",
    "all isEven (cons 0 (cons 0 NilInt))",
    "null NilBool",
    "iterate id 0",
    "null NilInt",
    "and (cons True (cons False NilBool))",
    "any not (cons False (cons (not False) NilBool))",
    "catMaybes (cons (Just 0) (repeat (listToMaybe (cons (Just 0) NilInt))))",
    "map isEven (cons 0 NilInt)",
    "cons (hd (cons 0 NilInt)) NilInt",
    "concatMap maybeToList (repeat (Just True))",
    "cons True (replicate 0 True)",
    "cons (hd (cons 0 (cons 0 NilInt))) NilInt",
    "inc 0",
    "cons 0 (singleton 0)",
    "id 0",
    "id cons",
    "cons 0 (singleton 0)",
    "id NilInt",
    "tl (cons True NilBool)",
    "(++) (repeat True) (singleton True)",
    "inc (length (cons True NilBool))",
    "cons False (replicate 0 True)",
    "dropWhile null (singleton (Just 0))",
    "filter not (cons False NilBool)",
    "id True",
    "dropWhile null (singleton NilInt)",
    "inc (fromMaybe 0 (Just 0))",
    "id NothingInt",
    "takeWhile isEven NilInt",
    "True isEven (listToMaybe (cons 0 NilInt))",
    "catMaybes (cons NothingInt (repeat (listToMaybe NilInt)))",
    "concatMap maybeToList (repeat NothingBool)",
    "id NilBool",
    "maybeToList NothingBool",
    "inc (hd (filter isEven (cons 0 (cons 0 NilInt))))",
    "inc (length (cons False (cons True NilBool)))",
    "and (cons True NilBool)",
    "isJust NothingBool",
    "isNothing ((!?) (replicate 0 0) 0)",
    "length NilInt",
    "iterate inc 0",
    "inc 0",
    "isJust (Just True)",
    "isNothing ((!?) (repeat True) True)",
    "iterate id True",
    "mapMaybe ((!?) (cons 0 NilInt)) (repeat 0)",
    "take 0 ((++) (reverse (cons True NilBool)) (repeat True))",
    "unsnoc (repeat True)",
    "iterate inc 0",
    "iterate not False",
    "inc (hd (filter isEven (cons 0 NilInt)))",
    "length (cons 0 (cons 0 NilInt))",
    "null (cons 0 NilInt)",
    "inc (fromMaybe 0 NothingInt)",
    "uncons (cons 0 (cons 0 NilInt))",
    "map isEven (cons 0 (cons 0 NilInt))",
    "mapMaybe ((!?) (cons 0 NilInt)) (repeat 0)",
    "maybeToList (Just True)",
    "all isEven (cons 0 (cons 0 NilInt))",
    "any not (cons True (cons (not True) NilBool))",
    "iterate not True",
    "not True",
    "or (cons True NilBool)",
    "not False",
    "null (cons 0 NilInt)",
    "null (cons False NilBool)",
    "null (singleton (Just 0))",
    "or (cons False (cons True NilBool))",
    "take 0 ((++) (reverse (cons False (cons True NilBool))) (repeat False))",
    "takeWhile isEven (cons 0 (cons 0 NilInt))",
    "tl (cons False NilBool)",
    "False isEven (listToMaybe (cons 0 (cons 0 NilInt)))",
    "uncons (cons 0 (cons 0 NilInt))",
    "unsnoc (repeat False)",
    "(++) (cons True NilBool) (singleton True)",
    "all isJust (cons (Just 0) (repeat NothingInt))",
    "and (singleton False)",
    "any id (cons False (cons True NilBool))",
    "catMaybes (cons (Just 0) (cons NothingInt NilInt))",
    "concatMap id (repeat (Just 0))",
    "cons (hd (cons 0 NilInt)) (repeat 0)",
    "cons (Just 0) (singleton (Just 0))",
    "dropWhile isNothing (singleton (Just 0))",
    "filter id (cons NothingBool NilBool)",
    "id NothingBool",
    "id (repeat False)",
    "id (replicate 0 True)",
    "inc (fromMaybe 0 (Just 0))",
//    "inc (hd (filter (not . isJust) (cons (Just 0) (repeat NothingInt))))",
    "inc (length (cons False (cons False NilBool)))",
    "length (repeat True)",
    "map not (cons True (cons False NilBool))",
    "mapMaybe (listToMaybe (cons 0 (cons 0 (singleton 0)))) (repeat True)",
    "maybeToList (Just False)",
    "null (repeat True)",
    "null (singleton True)",
    "or (cons False NilBool)",
    "take 0 (repeat True)",
    "takeWhile isJust (singleton (Just 0))",
    "tl (singleton (Just False))",
    "uncons (repeat False)",
    "(++) (repeat True) (singleton False)",
    "all not (cons True (cons True NilBool))",
    "and (singleton True)",
    "any isJust (cons (Just 0) (repeat NothingInt))",
    "catMaybes (cons (Just 0) (repeat (Just 0)))",
    "concatMap maybeToList (repeat (Just False))",
    "cons (hd (filter isNothing (cons NothingInt NilInt))) (repeat 0)",
    "cons True (singleton (Just 0))",
    "dropWhile null (repeat True)",
//    "filter (not . isJust) (repeat (Just True))",
    "id (repeat True)",
    "id (filter isEven (repeat 0))",
    "id (Just 0)",
    "inc (fromMaybe True (Just True))",
    "inc (hd (filter not (cons True (repeat True))))",
    "inc (length (repeat True))",
    "isJust (Just False)",
    "isNothing ((!?) (replicate 0 False) False)",
    "iterate (not True) True",
    "iterate inc (Just 0)",
    "iterate not (Just True)",
    "length (cons False (cons False (repeat True)))",
    "map isJust (cons (Just True) (repeat NothingInt))",
    "mapMaybe ((!?) (cons True NilBool)) (repeat True)",
    "maybeToList (Just False)",
    "not (Just True)",
    "null (repeat NothingInt)",
    "null (repeat True)",
    "or (repeat (Just True))",
    "take 0 (repeat False)",
    "takeWhile isJust (repeat (Just 0))",
    "tl (repeat False)",
    "uncons (singleton False)",
).map { "($it)\n" }