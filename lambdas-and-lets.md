# Lambdas and lets

Examples can be any Hindley-Milner program: names, applications, lambdas and lets. This records
how that works, what was decided, and what is left. Rules for writing examples are in
`src/test/input/ocaml-stdlib/exs/README.md`.

## How it works

- **Syntax** (`src/main/kotlin/query/Examples.kt`). `Lam(param, body)` and
  `Let(name, value, body)`. `Name` is the only variable reference; scope decides whether it is a
  component or a local, so a binder shadows a component of the same name.
  - `names` are the free names, i.e. the components an example needs typed.
  - `subexprs()` returns only closed subexpressions: in `fun x -> f x`, `f` is one, `f x` is not.
  - Lambdas and lets are equal up to renaming bound names.
  - `flatten()` keeps arguments whole, so a lambda argument still flattens; it is null when the
    head is a lambda or let.
- **Parsing** (`src/test/kotlin/testutil/SExprExample.kt`). `(fun x y -> body)` and
  `(let x = value in body)`. Binders must be OCaml variable names.
- **Type checking** (`OneUnification.build`). A lambda's parameter is one type at every use. A
  let-bound name builds its value again at each use, so each use instantiates the components in it
  afresh: Hindley-Milner's let-polymorphism, since `let x = v in b` type-checks iff v and `b[v/x]`
  do. Each copy's holes are ordinary instances, so `refine` and `rewindTo` work unchanged.
- **Reading types back** (`TypeGraph.typeAt`), which the ground-truth oracle uses to compare
  examples in the dependency analysis. It needs a graph with no holes; then a class with no
  constructor is a type variable, as the parameter of `fun x -> x` is. Variables are numbered per
  class, so separate uses of a component get separate variables: `pair nil nil` is
  `'a list * 'b list`, not `'a list * 'a list`.
- **Seeding** (`Engine.functions`). A new name is seeded as an arrow if unification makes it one
  when it starts as a hole, so a name applied only under another name counts.
- **Dependency analysis** (`Examples.flatPos`). Positives are flattened with their lets inlined
  (`Example.inlineLets`), so `let f = cons in f x l` is evidence about `cons`. Negatives are not.
- **Ground truth** (`OCamlChecker`). An example is printed for ocamlc after three rewrites:
  dummy names (`Num` to `1`), labels (`withLabels`), and, with the `thunk-lets` variant, lets as
  `let x () = v` (`thunkLets`).
- **OCaml types** (`ReadOCamlTypes.kt`). Labelled parameters are positional, with their labels
  kept for printing. Optional parameters are left out.

## Decisions

- Our type checker is pure Hindley-Milner: every let is generalized.
- ocamlc checks examples as written by default, so the examples must avoid the value
  restriction. The `thunk-lets` bench variant has ocamlc check each let as `let x () = v`, which
  makes it agree with Hindley-Milner on every let.
- Labelled parameters are positional in our types; ocamlc gets the label written at the
  argument. Labelled components must be applied up to their last labelled parameter.
- Optional parameters are left out of our types and never passed.
- The dependency analysis gets let-inlined positives.

## Checked

- Every `.exs` file loads on its own, with our checker and ocamlc agreeing, with or without
  `thunk-lets`: 2076 positives and 210 negatives; 134 positives have lambdas, 78 of them distinct
  up to bound names. None has a let yet.
- Benchmarks other than `ocaml-list` search exactly as before (same candidates).

## Left to do

- **`ocaml-list` is now a higher-order problem.** Before, every example applying `List.filter`,
  `List.exists` and 15 other higher-order functions had a lambda and was dropped, so the search
  made them labels and finished "wrong" in 22s. With those examples it must find their real types,
  and it times out, at 300s and at 1200s alike. From 300s to 1200s, candidates barely grow
  (524,859 to 536,628) while solver calls go from 55k to 221k, so the time goes to label arity
  queries. The seeding change makes no difference here: syntactic seeding times out with the same
  candidates.
- **`load all and split` still fails**, now on module qualification in the `.types` files (e.g.
  `57_option_mod.types` declares `value`, the examples use `Option.value`), not on parsing.
- **Beta reduction** for the dependency analysis, so `(fun f -> f Num Nil) List.cons` is evidence
  about `List.cons`. No example is headed by a lambda yet, so it is not done.
- **CEGIS**: `RandomExampleGenerator` makes only names and applications. CEGIS is disabled
  (`CEGISCheck.kt`), so this matters only when it comes back.
- **Outside the Hindley-Milner core**, the parser rejects `let rec`, tuple and unit patterns
  (`fun (a, b) ->`, `fun () ->`), `if`, `match` and sequencing.
