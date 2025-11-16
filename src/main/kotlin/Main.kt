import query.parseTest
import test.*
import util.Logger

fun main() {
    val smallTests = listOf(IdTest, ConsTest, HOFTest, DictTest, WeirdTest)
    val smallTest = DictTest
    val testFromFile = parseTest("dictchain")

    val config = ConfigForOld(
        test = DictTest,
        runCVC = true,
        maxDepth = 4
    )

    val logger = Logger(
        configuration = config,
        logToFile = false
    )

    run(config, logger)
}
