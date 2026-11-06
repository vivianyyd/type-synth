# Deviations from the OCaml stdlib

Every way the benchmarks differ from the real OCaml 5.4 stdlib, or leave part of it out, and why.
When you choose a new deviation, add it here.

## How examples are written (all groups)

How to write examples under these rules is in `EXAMPLES.md`.

- **Constants are placeholders.** `Num`, `Str`, `Char`, `Flt`, `Nil` and `Unit` are names in
  `0_basics.types`. To ask OCaml, `OCamlSource` writes them as `1`, `"s"`, `'a'`, `1.`, `[]`, `()`.
  There are no other literals: no tuple, list or record syntax, and no constructors such as `Some`
  or `FP_normal` (examples use functions like `Option.some` instead), except those of `open_flag`
  (see below).
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

## Constructors that are names

- **`open_flag`'s constructors** (`Open_rdonly`, `Open_wronly`, `Open_append`, `Open_creat`,
  `Open_trunc`, `Open_excl`, `Open_binary`, `Open_text`, `Open_nonblock`) are values in
  `17_out.types`, with type `open_flag`. `open_out_gen` and `open_in_gen` take an `open_flag list`,
  and no function builds an `open_flag`. OCaml accepts the constructors as written, and examples
  build the list with `List.cons` and `Nil`.
  `In_channel.open_flag` and `Out_channel.open_flag` are the same type (`Stdlib.open_flag`), so
  their .types files declare them as a rename, and `In_channel.open_gen` and `Out_channel.open_gen`
  take these constructors too.

## Names left out

- **`List.to_seq`, `List.of_seq`** (`skippedNames` in `OCamlStdlib.kt`): examples that need the
  search to solve them are left out. Approved as temporary on 2026-10-29. Cause: `to_seq` is solved
  first, with a Seq label of no parameter, and a later round can't give the label one, so `of_seq`
  has no solution. `queue_mod` is still given `List.to_seq`'s true type. Undo by emptying the set.
- **Bigarray functions of `In_channel` and `Out_channel`**: `input_bigarray` and `really_input_bigarray`.
  `Bigarray` has no group, so no example can build the argument.
- **`Result.Syntax`**: `( let* )`, `( and* )`, `( let+ )` and `( and+ )`. Examples can't name an
  operator in a submodule (operators stay unqualified), and these are `bind`, `product` and `map`
  with its arguments swapped, which `64_result_mod` already has.
- **A dependency's names that its own examples don't use** aren't given to a group; the group has
  to solve them, as a chain would.
- **`20_result`** has no group: it declares only the type `('a, 'b) result = Ok of 'a | Error of
  'b`, and no value. Examples can't write the constructors, and `Result.ok` and `Result.error`
  (group `result_mod`) cover them.
- **Modules and names in no group yet**: the `// Skipped` lines in `README`, and `// Skipped`
  comments in .types files (`56_oo_mod`: object types).
- **`ref`'s `contents` field**: `'a ref` is the record `{ mutable contents : 'a }`, but examples
  have no record syntax, so `19_ref` treats `ref` as an abstract type and leaves out `r.contents`
  and `r.contents <- v`. `ref`, `(!)`, `(:=)`, `incr` and `decr` cover the same uses.
- **`Atomic.Loc`** (OCaml 5.4): its values come only from `[%atomic.loc r.field]`, on a record field
  declared `[@atomic]`. Examples can't declare types, build records or write that syntax, so
  `23_atomic_mod.types` leaves the submodule out. Its functions are `Atomic`'s, on `'a Atomic.Loc.t`.
- **`Complex.t`'s fields**: `Complex.t` is the record `{ re : float; im : float }`, but examples have
  no record syntax, so `re` and `im` can't be read or built. Complex values come only from
  `Complex.zero`, `one`, `i`, `polar` and the functions on them.
- **String**: no Bytes, Uchar, Int32 or Int64 function is given, so `bytes`, `Uchar.utf_decode`,
  `int32` and `int64` values come only from String's own functions.

## Known wrong results

- **`type_mod` (`72_type_mod`)**: the search returns `Type.Id.make : unit -> Id.t`, `uid : Id.t -> int`
  and `provably_equal : Id.t -> Id.t -> eq option`, with no type parameters; the true types have
  `'a Id.t` and `('a, 'b) eq`. No example can show the parameters. Only `provably_equal` relates
  them (`'a Id.t -> 'b Id.t -> ('a, 'b) eq option`), the result's parameters can be seen only by
  something that takes an `eq`, and nothing in the stdlib does (its one value is the constructor
  `Equal`, which examples can't write). Every `make ()` call is a fresh instance, so no example
  can make two `Id.t` arguments share a parameter either (that takes a `let`). The search picks
  the smallest arity, 0, for both types. Leaving `provably_equal` out would not help: `make` and
  `uid` have the same problem.

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
