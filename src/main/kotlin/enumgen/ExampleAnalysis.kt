package enumgen

class ExampleAnalysis(
    private val posExamples: Set<Application>,
    private val negExamples: Set<Application>
) {
    // TODO actually flatten the posexs, negexs so each application is named, then enum types for everything in posexs names
    fun canBeEqual(expressions: Set<Application>): Boolean {
        // For each e, search thru posExs and substitute every other e' for e when it appears. Do it through a fold and use equals since they're data classes
        return expressions.all { e ->
            posExamples.all { app ->
                expressions.all { ePrime -> works(replace(app, e, ePrime)) }
            }
        }
    }

    fun replace(a: Application, e: Application, ePrime: Application): Application = TODO()
    fun works(a: Application): Boolean = TODO()
}
