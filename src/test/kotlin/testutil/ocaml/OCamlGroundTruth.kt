package testutil.ocaml

import util.GroundTruth

/** The ways to ask OCaml whether an expression type-checks. They all give the same answers. */
enum class OCamlGroundTruth(val description: String) {
    Typer("a server around OCaml's type checker (compiler-libs)"),
    Toplevel("one ocaml toplevel, fed each expression as a phrase"),
    Ocamlc("ocamlc, one process per check");

    fun create(): GroundTruth =
        when (this) {
            Typer -> OCamlTyper()
            Toplevel -> OCamlToplevel()
            Ocamlc -> OCamlChecker()
        }

    companion object {
        val default = Typer
    }
}
