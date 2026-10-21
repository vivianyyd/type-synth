package testutil.ocaml

import util.GroundTruth

/**
 * The ways to ask OCaml whether an expression type-checks. They all use OCaml's own parser and type
 * checker and give the same answers (`OCamlGroundTruthTest` checks them against [Ocamlc]); they
 * differ in how they reach it, and so in speed. Per check, on the expressions the observational
 * oracle sends one at a time:
 *
 * | | per check | a batch |
 * |---|---|---|
 * | [Typer] | 0.06ms | checked one at a time, stopping at the first failure |
 * | [Toplevel] | 1.5ms | up to 100 expressions per phrase |
 * | [Ocamlc] | 13.5ms, nearly all process startup | one file, one compile |
 *
 * What else differs:
 * - [Typer] only types each expression, never binds or runs it. It needs `ocamlfind` and
 *   `compiler-libs`, and builds its server on first use.
 * - [Toplevel] runs what it is given, so it wraps each expression in `fun () -> (...)`. An
 *   expression that leaves a comment or string open would swallow everything sent after it, so it
 *   is answered without the toplevel.
 * - [Ocamlc] compiles each check in a file of its own, binding each expression to `_`: a named
 *   binding would fail on the value restriction. A compile that takes over 10 seconds counts as
 *   failing.
 */
enum class OCamlGroundTruth(val description: String) {
    Typer("a server around OCaml's type checker (compiler-libs)"),
    Toplevel("one ocaml toplevel, fed each expression as a phrase"),
    Ocamlc("ocamlc, one process per check");

    /** Asks OCaml about examples written as [source] writes them. */
    fun create(source: OCamlSource = OCamlSource()): GroundTruth =
        when (this) {
            Typer -> OCamlTyper(source = source)
            Toplevel -> OCamlToplevel(source = source)
            Ocamlc -> OCamlChecker(source = source)
        }

    companion object {
        val default = Typer
    }
}
