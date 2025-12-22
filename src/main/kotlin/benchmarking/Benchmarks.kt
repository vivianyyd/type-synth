package benchmarking

sealed class HType {
    data class TypeVar(val name: String) : HType()

    data class TypeConstructor(val name: String, val args: List<HType> = emptyList()) : HType()

    data class Function(val from: HType, val to: HType) : HType()
}

data class Constraint(val classes: List<String>, val variable: HType.TypeVar)

data class Schema(val constraints: List<Constraint>, val type: HType)

fun parse(ty: String): Schema {
    val split = ty.split("=>").map { it.trim() }
    return if (split.size == 1) Schema(listOf(), parseType(split.first()))
    else {
        require(split.size == 2)
        Schema(parseConstraints(split.first()), parseType(split.last()))
    }
}

fun parseConstraints(cs: String): List<Constraint> {
    TODO()
}

fun parseType(t: String): HType {
    TODO()
}


// Example usage
fun main() {
    val examples =
        listOf(
            "Foldable t => (a -> [b]) -> t a -> [b]",
            "(Foldable t, Num a) => t a -> a",
            "Traversable t => (s -> a -> (s, b)) -> s -> t a -> (s, t b)",
            "HasCallStack => (a -> a -> a) -> [a] -> a",
            "[Either a b] -> [b]",
            "[Maybe a] -> [a]",
            "Either (Either a b) b")
    examples.forEach { println(parse(it)) }
}
