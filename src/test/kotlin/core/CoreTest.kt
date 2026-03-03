package core

import core.enumerate.EnumeratorTag
import core.unification.UnificationTag
import data.ConsTest
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import util.Configuration
import util.Logger

class CoreTest {
    @Test
    fun `run completes with simple configuration`() {
        val configuration =
            Configuration(
                query = ConsTest,
                runCVC = true,
                enumeratorTag = EnumeratorTag.DFSPriority,
                unificationTag = UnificationTag.Eager,
                finalRoundSketches = true,
                sizeBound = 10,
                depthBound = 3
            )

        val logger = Logger(configuration = configuration, logToFile = false, verbosity = 0)

        run(configuration, logger)

        assertTrue(true) // if run returns without exception, the test passes
    }
}
