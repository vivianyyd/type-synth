package core

import core.enumerate.EnumeratorTag
import core.unification.UnificationTag
import org.junit.jupiter.api.Test
import testutil.loadQueryFromFile
import util.Configuration
import util.Logger

class CoreTest {
    @Test
    fun `run completes with simple configuration`() {
        val testFromFile = loadQueryFromFile("dictchain")

        val configuration =
            Configuration(
                query = testFromFile,
                runCVC = true,
                enumeratorTag = EnumeratorTag.DFSPriority,
                unificationTag = UnificationTag.Eager,
                finalRoundSketches = true,
                sizeBound = 10,
                depthBound = 3
            )

        val logger =
            Logger(
                configuration = configuration,
                logFilename = "tmp.log",
                logToFile = true,
                verbosity = 5
            )

        run(configuration, logger)
    }
}
