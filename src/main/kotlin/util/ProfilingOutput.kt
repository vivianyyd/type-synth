package util

/** @param [output] for each iteration, the time in seconds and the prettyprinted output */
fun recordOutput(output: List<Pair<Int, String>>, testName: String) {
    val out = output.mapIndexed { i, (t, s) -> "$i,$t,$s" }.joinToString(separator = "\n")
}
