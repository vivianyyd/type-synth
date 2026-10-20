# Lambdas and lets: what's next

## Where `let-lambda-examples` leaves it

- `Example` has `Lam(param, body)` and `Let(name, value, body)` (`src/main/kotlin/query/Examples.kt`).
  `Name` is still the only variable reference. Scope decides whether it is a component or a
  local, so a binder shadows a component of the same name.
- `names` are the free names, i.e. the components an example needs typed. Everything that
  schedules or filters by `names` (Engine rounds, `takeExs`, the OCaml loader) is correct as is.
- `subexprs()` returns only closed subexpressions. In `fun x -> f x`, `f` is one, `f x` is not.
- `FlatApp` arguments are whole `Example`s, so `List.filter (fun x -> ...) xs` still flattens.
  `flatten()` is null when the head is a lambda or let, and `Examples.flat` leaves those out.
- The `.exs` parser reads `(fun x y -> body)` and `(let x = v in body)`. Binders must be OCaml
  variable names. The 111 lambda examples already in the `.exs` files now parse as lambdas.
  Before, they parsed as applications of a name `fun` and were dropped.
- Type checking throws on `Lam`/`Let` (`Unification.kt:177`). To keep that from triggering,
  `splitOCamlExamples` drops examples with binders (`ExampleLinter.kt:26`). The examples the
  search sees are byte-identical to `main` for all six `ocamlModuleGroups`.
- Rules for writing examples are in `src/test/input/ocaml-stdlib/exs/README.md`.

## Decisions

- **Our type checker is pure Hindley-Milner.** Every let is generalized.
- **ocamlc checks examples as written by default.** The examples must avoid the value
  restriction (rule in the README). The bench variant `thunk-lets` instead has ocamlc check each
  let as `let x () = v`, with each use as `x ()` (`thunkLets` in `OCamlChecker.kt`). That makes
  ocamlc agree with Hindley-Milner on every let.
- **Labelled parameters are positional** in our types, in declaration order. When printing for
  ocamlc, the label is written at that argument.
- **Optional parameters are left out** of our types.
- **The dependency analysis gets let-inlined examples.**

## Next steps, in order

### 1. Type check `Lam` and `Let` in `OneUnification` (about a day, including tests)

Give `build` a scope: a map from local name to graph node.

- `Name` bound in scope: return its node. Do not instantiate it, because lambda-bound variables
  are monomorphic.
- `Name` not in scope: instantiate the component's type, as now.
- `Lam(x, b)`: `p = graph.freshVar()`, build `b` with `x -> p`, return `graph.arrow(p, body)`.
- `Let(x, v, b)`: **build `v` again at every use of `x` in `b`**, plus once up front so an
  unused, ill-typed `v` still fails. This is Hindley-Milner's let-polymorphism without
  generalization machinery: `let x = v in b` types iff `v` types and `b[v/x]` types. It also keeps
  incremental refinement working unchanged. Each rebuild instantiates components again, so it
  creates hole instances with their own instantiation numbers, and `refine`/`rewindTo` handle them
  like any other. Variables bound by an enclosing lambda stay shared across the copies because
  the scope is shared, which is exactly the Hindley-Milner rule (no generalizing over the
  environment). Cost grows with nested lets. That is fine at example sizes.

Also needed:

- `TypeGraph.typeAt` (`TypeGraph.kt:483`) returns null for a class with no constructor and no
  rigid variable. The parameter of `fun x -> x` is such a class. So `type()` returns null, and
  `CheckingGroundTruthOracle.equal` (`GroundTruth.kt:19`) says every lambda differs from every
  other. Report those classes as fresh `Variable`s, numbered by class, when reading back the
  type of a closed example.
- Tests: `fun x -> x x` fails the occurs check. `let id = fun x -> x in pair (id Num) (id true)`
  passes. `(fun id -> pair (id Num) (id true)) (fun x -> x)` fails. Refine/rewind gives the same
  answers as rebuilding from scratch on examples with lets (extend `IncrementalRefinementTest`).

### 2. Turn on binder examples (about 2 hours)

- Delete the `hasBinders` filter in `splitOCamlExamples`. `assureEq` then checks our checker
  against ocamlc on all 111 lambda examples. That comparison is the real test of step 1.
- Run the loader both ways (default and `thunk-lets`). Any let that only `thunk-lets` accepts
  breaks the README's value restriction rule; fix the example.
- `OCamlChecker.desugar` (`OCamlChecker.kt`) rewrites `Num`, `Str`, `Char`, `Flt`, `Nil` by
  plain string replacement, so a name containing one of them is mangled. The README forbids
  such names. Replacing it with a rewrite on `Example` names would remove the rule.

### 3. Labelled and optional parameters (about half a day)

`origin/fix-ocaml-type-parser` (one commit, 2026-09-14) parses labels, but differently from the
decisions above. Before merging it:

- It drops label names. Keep them: the type stays positional, but the parser also returns,
  per component, the label of each parameter (or none).
- It turns `?label:a -> b` into a positional `a -> b`. Drop optional parameters instead, so
  `Hashtbl.create` is `int -> ('a, 'b) t`. With them positional, `(Hashtbl.create Num)` in
  `42_hashtbl_mod.exs` would be a type error.

Then `OCamlChecker` writes `~label:` before each labelled argument of a component applied
directly. The README's rule keeps labelled components directly applied up to their last
labelled parameter.

Existing examples are affected now. ocamlc omits labels only in a full application whose result
type is not a type variable. So `Option.value Option.none Num` in `57_option_mod.exs` is
accepted by ocamlc as a partial application (`Num` goes to the result), not with `Num` as the
default. Our checker, with labels dropped, types it as an `int`. Both accept it, so loading
passes. But an example that uses the result as an `int` would make them disagree. Printing
the label fixes this.

### 4. Seeding: which names are functions (about half a day)

`Engine.nameIsApplied` (`Engine.kt:73`) is syntactic. A component applied only through a binder,
as `f` is in `let g = f in g x` or `(fun h -> h x) f`, is seeded as a label-only `Blank`
(`Engine.kt:108`). Then the true solution is unreachable. Once step 1 exists, decide it by
unification instead: check the round's examples with each new name as a `TypeHole`, and seed
`Arrow(TypeHole(), TypeHole())` where `holeConstructor` says `Arrow`.

### 5. Dependency analysis input (about half a day)

`ParameterwiseDependencyAnalysis` sees only examples headed by a component name.
It marks parameter `i` "fixed" when no positive example shows it varying. Fewer witnesses
therefore means more parameters wrongly fixed, which can prune the true solution. Every
example headed by a let is a lost witness: `let f = List.cons in f Num Nil` says nothing about
`List.cons` today.

Fix: give it let-inlined positives (`let x = v in b` becomes `b[v/x]`). That preserves
typability, by Hindley-Milner's let rule. Do not inline negatives: inlining drops an unused
ill-typed value, so a negative can become positive. This needs capture-avoiding substitution
in `query`.

Examples headed by a lambda, like `(fun f -> f Num Nil) List.cons`, are still lost. Beta
reduction would recover them, the same way. Add it if lambda-headed examples turn out to be
common.

### 6. Smaller items (an hour or less each)

- Alpha-equivalence: `fun x -> x` and `fun y -> y` are unequal data classes, so `Examples`
  dedup, the Bloom filter and `ScrappyNewOracle` treat them as different. The `.exs` files
  number binders uniquely, so this rarely matters yet. Fix by renaming binders canonically
  at parse time if it does.
- `RandomExampleGenerator` makes only names and applications. CEGIS is disabled
  (`CEGISCheck.kt:24`), so this matters only when it comes back.
- Out of Hindley-Milner core, still rejected by the parser: `let rec`, tuple and unit patterns
  (`fun (a, b) ->`, `fun () ->`), `if`, `match`, sequencing.
