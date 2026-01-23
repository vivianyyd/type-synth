package core

import core.enumerate.EnumeratorTag
import core.unification.UnificationTag
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import test.IdTest
import util.Configuration
import util.Logger

class EnumeratorsTest {
    @Test
    fun `run completes with simple configuration`() {
        val configuration =
            Configuration(
                test = IdTest,
                runCVC = false,
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
