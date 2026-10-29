# Writing examples for the OCaml stdlib benchmarks

The search gets untyped example expressions over a set of names and finds a type for each name.
OCaml decides which examples type-check (positive) and which don't (negative); examples aren't
labelled. The search returns the smallest types consistent with the examples, so a fact about a
type that no example forces is lost. Examples have to force every part of every type.

## Files and groups

- `types/N_name.types`: the true types, in OCaml `val` syntax. A module's file (`*_mod.types`)
  names values relative to the module (`val code : char -> int` in Char); examples use the
  qualified name (`Char.code`). `//` lines are comments, except `// Module` on the first line and
  `// type ...` declarations.
- `exs/N_name.exs`: the examples. The first line is a comment listing every .types file whose names
  the examples use. Then one example per line; blank lines and `//` lines are ignored.
- `ocamlModuleGroups` (`src/test/kotlin/testutil/ocaml/OCamlStdlib.kt`): the groups of .exs files
  and what each depends on. A group's examples may only use names of its own and its dependencies'
  .types files (`OCamlStdlibTest` checks the first lines). A dependency's name is given to the group
  only if the dependency's own examples use it, as in a chain; otherwise the group has to solve it.
  How to run the benchmarks of a group is in `bench/README.md`.

## Syntax

- Prefix application in parentheses: `(f a b)`. Operators in parentheses: `((+) Num Num)`. Operators
  that start or end with `*` are spaced: `(( * ) Num Num)`.
- Constants are written by type: `Num`, `Str`, `Char`, `Flt`, `Unit`, `Nil` (`[]`), `true`, `false`.
  There are no other literals: no tuples, lists or records.
- Labelled arguments are positional, in declared order: `(Option.value o d)`. Optional arguments
  (`?limit:int`) are left out. A function with labelled parameters can't be passed as an argument.
- Partial application is fine and useful: `((+) Num)`, `(List.map succ)`.
- `fun` and `let` are dropped, keeping only the parts outside them. Pass named functions instead.
- Every example is checked against both OCaml 5.4 and the .types files, and loading fails if they
  disagree.

## What the examples must show

For each function `f`:

1. **Positive uses**, fully applied. A polymorphic parameter at three or more different types.
2. **Each parameter's type, by negatives whose last argument is wrong.** The arity analysis assumes
   a negative fails at its last argument: `((+.) Flt Num)` and `((+.) Num)`, not `((+.) Num Flt)`.
   Every subexpression of a negative must type-check.
3. **The result type, by using it**: passed to functions that need exactly that type (positive) and
   other types (negative). The cheapest way is `(=)` against a value built from known names:
   `((=) (Pair.swap (Pair.make Num Str)) (Pair.make Str Num))` vs `... (Pair.make Num Str))`.
4. **Shared type variables**, by negatives where they disagree, the disagreeing argument last:
   `(List.cons Num (List.cons Str Nil))`. A result that shares a parameter's variable, by the element
   flowing through: `(succ (Option.get (Option.some Num)))` vs `(not (Option.get (Option.some Num)))`.
5. **Type constructors' parameters**: values with several element types, and negatives where the
   container comes after an element and disagrees with it (`(Option.value (Option.some Num) Str)`).
6. **Higher-order parameters**: named functions of the right type (positive) and wrong types
   (negative, last), with results of several types.
7. **Application**: every function is the head of some positive example, not only an argument;
   a name that is never applied is taken for a constant.
8. **Constants** (`infinity`, `String.empty`) where their type is required, positive and negative.
   Polymorphic ones (`Option.none`, `Nil`, `StrMap.empty`) at several types, with several functions.

## Independence from the schedule

The search solves a few functions at a time, in rounds, and commits to each round's answer. A
round only sees examples whose names are all solved by then. Which names share a round depends on
all of the group's examples, so don't rely on it or try to steer it:

- Show every fact about `f`'s type with examples that use only `f`, constants and dependencies'
  names. For each function, think of the plausible wrong types, more general (two variables where
  there is one) and less general (one where there are two), and refute each:
  `(List.fold_left (List.fold_left (+)) Num (List.cons (List.cons Num Nil) Nil))` shows the
  accumulator and the elements differ; `(List.compare Option.value)` (negative) shows the
  comparator's arguments have one type.
- A round whose examples don't pin a result commits to a wrong type, and later rounds fail; that
  shows up as many fast failed rounds, or a timeout.
- To give a mutable container a known element type, build it from typed values:
  `(Queue.of_seq (List.to_seq (List.cons Num Nil)))`.

## Finding what's missing

`bench/analyze.py show` gives each wrong name's returned and expected type. `bench/analyze.py
rounds` gives each round's names, time and number of solutions; each `solution` event in the run's
JSON has the types that round found (`types`). A round with several solutions lacks examples that
tell them apart; a round with none may have a wrong earlier answer committed, or hit a search limit
(below).

## Known search limits

- A round's types share one size bound (30 holes). Two large higher-order types in one round
  (`equal` and `compare` of a container, `List.fold_left_map` and `List.assoc`) don't fit.
- Types deeper than the depth bound (`StrMap.merge`, `StrMap.union`) can't be found.

Don't leave examples out, or move them to another group, because the search fails on them. A group
the search can't solve is reported as failing.
