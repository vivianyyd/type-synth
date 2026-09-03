package oneast.bench

import oneast.Type
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.condition.EnabledIfSystemProperty
import query.Example
import testutil.ocaml.OcamlTypeParser
import testutil.unsignedExample
import util.CheckingGroundTruthOracle
import util.join
import java.io.File

/**
 * Classifies every OCaml stdlib example with the hole-free type checker and digests the result, so
 * two builds can be compared exactly.
 */
class OracleDigest {
    @Test
    @EnabledIfSystemProperty(named = Bench.GATE, matches = ".+")
    fun digest() {
        val exsDir = File(join("src", "test", "input", "ocaml-stdlib", "exs"))
        val typesDir = File(join("src", "test", "input", "ocaml-stdlib", "types"))
        val parser = OcamlTypeParser()
        val types: Map<String, Type> = buildMap {
            typesDir.listFiles()!!.filter { it.extension == "types" }.sortedBy { it.name }
                .forEach { f ->
                    val text = f.readLines().filterNot { it.trim().startsWith("//") }
                    runCatching { putAll(parser.parseSignatures(text.joinToString("\n"))) }
                }
        }
        val examples = mutableListOf<Example>()
        exsDir.listFiles()!!.filter { it.extension == "exs" }.sortedBy { it.name }.forEach { f ->
            f.readLines().drop(1).forEach { line ->
                val t = line.trim()
                if (t.isNotBlank() && !t.startsWith("//")) examples.add(unsignedExample(t))
            }
        }
        val all = examples.flatMap { it.subexprs() }.toSet()
            .filter { e -> e.names.all { it in types } }
            .sortedBy { it.toString() }
        val oracle = CheckingGroundTruthOracle(types)
        var digest = 0L
        var valid = 0
        for (e in all) {
            val v = oracle.valid(e)
            if (v) valid++
            digest = digest * 1000003L + (e.toString().hashCode() * 2 + if (v) 1 else 0)
        }
        println("examples=${all.size} valid=$valid digest=$digest")
    }
}
