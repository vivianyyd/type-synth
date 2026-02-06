import products.ConfigForOld
import products.run
import query.parseTest
import util.Logger

fun main() {
    val testFromFile = parseTest("dictchain")

    val config = ConfigForOld(querySpec = testFromFile, runCVC = true, maxDepth = 4)

    val logger =
        Logger(configuration = config, logToFile = true, logFilename = "dictchain-product.log")

    run(config, logger)
}
