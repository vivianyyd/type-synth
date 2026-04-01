package products

import testutil.loadQueryFromFile
import util.Logger

class Test {
    fun main() {
        val testFromFile = loadQueryFromFile("dictchain")

        val config = ConfigForOld(querySpec = testFromFile, runCVC = true, maxDepth = 4)

        val logger =
            Logger(configuration = config, logToFile = true, logFilename = "dictchain-product.log")

        run(config, logger)
    }
}
