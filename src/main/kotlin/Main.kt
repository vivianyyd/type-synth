import products.ConfigForOld
import products.run
import query.parseTest
import test.Test
import util.Logger

fun main() {
    val testFromFile: Test = parseTest("dictchain")

    val config = ConfigForOld(test = testFromFile, runCVC = true, maxDepth = 4)

    val logger =
        Logger(configuration = config, logToFile = true, logFilename = "dictchain-product.log")

    run(config, logger)
}
