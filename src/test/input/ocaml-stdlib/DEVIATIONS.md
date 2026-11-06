# Deviations from the OCaml stdlib

Every way the benchmarks differ from the real OCaml 5.4 stdlib, or leave part of it out, and why.
When you choose a new deviation, add it here.

## How examples are written (all groups)

How to write examples under these rules is in `EXAMPLES.md`.

- **Constants are placeholders.** `Num`, `Str`, `Char`, `Flt`, `Nil` and `Unit` are names in
  `0_basics.types`. To ask OCaml, `OCamlSource` writes them as `1`, `"s"`, `'a'`, `1.`, `[]`, `()`.
  There are no other literals: no tuple, list or record syntax, and no constructors such as `Some`
  or `FP_normal` (examples use functions like `Option.some` instead).
- **No `fun`, `let` or patterns.** The loader keeps only the subexpressions outside a `fun` or
  `let`, so the 12 lambda examples in `57_option_mod.exs` and `70_string_mod.exs` add little.
- **Labelled arguments are positional**, in declared order. `OCamlSource.withLabels` adds the labels
  back when asking OCaml. Optional arguments (`?limit:`) are left out: the .types parser drops
  them, and examples never pass them (`String.edit_distance`'s `?limit`, `String.spellcheck`'s
  `?max_dist`).
- **Tuples are constructors** of their arity (`*2`, `*3`) in our types.

## Definitions that aren't in the stdlib

Both are in `stdlibSource.prelude` (`src/test/kotlin/testutil/ocaml/OCamlStdlib.kt`), which OCaml
checks before the examples. The search never sees the prelude, only .types files and examples.

- **`StrMap = Map.Make (String)`.** Examples can't apply a functor, so `51_map_mod` uses this one
  instance of `Map`. It is the only instance: no other key type is tested.
- **`Triple`** (`79_triple_mod.types`, group `triple_mod`): `make`, `fst`, `snd`, `thd` for
  3-tuples, in the style of `Pair`. Examples can't build or take apart a tuple, and the stdlib has
  no functions for 3-tuples, so without it nothing pins `StrMap.split`'s result. Approved 2026-11-06.

## Names left out

- **`List.to_seq`, `List.of_seq`** (`skippedNames` in `OCamlStdlib.kt`): examples that need the
  search to solve them are left out. Approved as temporary on 2026-10-29. Cause: `to_seq` is solved
  first, with a Seq label of no parameter, and a later round can't give the label one, so `of_seq`
  has no solution. `queue_mod` is still given `List.to_seq`'s true type. Undo by emptying the set.
- **`Result.Syntax`**: `( let* )`, `( and* )`, `( let+ )` and `( and+ )`. Examples can't name an
  operator in a submodule (operators stay unqualified), and these are `bind`, `product` and `map`
  with its arguments swapped, which `64_result_mod` already has.
- **A dependency's names that its own examples don't use** aren't given to a group; the group has
  to solve them, as a chain would.
- **Examples that use a name of no group** (`print_int` and `print_string` in `69_stack_mod.exs` and
  `64_result_mod.exs`, from `14_stdout`; `print_newline`, `flush_all` and others in
  `21_termination.exs`, from `14_stdout` and `17_out`) are in the file, but the group's query leaves them out,
  since their names aren't in the group's .types files.
- **Modules and names in no group yet**: the `// Skipped` lines in `README`, and `// Skipped`
  comments in .types files (`56_oo_mod`: object types).
- **`ref`'s `contents` field**: `'a ref` is the record `{ mutable contents : 'a }`, but examples
  have no record syntax, so `19_ref` treats `ref` as an abstract type and leaves out `r.contents`
  and `r.contents <- v`. `ref`, `(!)`, `(:=)`, `incr` and `decr` cover the same uses.
- **String**: no Bytes, Uchar, Int32 or Int64 function is given, so `bytes`, `Uchar.utf_decode`,
  `int32` and `int64` values come only from String's own functions.

## Known wrong results

None.

## Settings some groups need

`list`, `queue_mod`, `pair_mod`, `map_mod`, `either_mod` and `result_mod` are correct only on branch
`resolve-on-clash`, with `--variant names-per-round=1,depth-bound=6`. Other groups are correct with the
default settings.

## Copy in tyind

`~/project/bench/bench-examples/ocaml-stdlib` has a copy of some of these files. Its parser has no
labelled parameters and needs qualified names, so in that copy `57_option_mod.types` has no labels,
and `57_option_mod.types` and `76_pair_mod.types` write names in full (`val Option.some`). Its
`Render.prelude` declares every name from the .types files instead of using the real stdlib, and it
has no `StrMap` or `Triple`.
