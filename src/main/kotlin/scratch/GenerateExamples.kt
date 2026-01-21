import benchmarking.parseHaskellTypes

// Legacy example generation will be removed once oneast wiring is added.

fun main() {
    // Legacy pipeline disabled pending oneast support.
}

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
