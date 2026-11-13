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

All of them are in `stdlibSource.prelude` (`src/test/kotlin/testutil/ocaml/OCamlStdlib.kt`), which OCaml
checks before the examples. The search never sees the prelude, only .types files and examples.

- **`StrMap = Map.Make (String)`.** Examples can't apply a functor, so `51_map_mod` uses this one
  instance of `Map`. It is the only instance: no other key type is tested.
- **`StrSet = Set.Make (String)`.** The same for `68_set_mod`: one instance, with strings as elements, so no
  other element type is tested.
- **`IntMinQueue = Pqueue.MakeMin (Int)`.** The same for `78_pqueue_mod`: one instance, with ints as elements
  (`Int.t` is `int`). The other three functors (`MakeMax`, `MakeMinPoly`, `MakeMaxPoly`) are left out.
  `MakeMax`'s values are `MakeMin`'s with `min` in the names changed to `max` (`max_elt`, `get_max_elt`,
  `pop_max`, `remove_max`) and the same types, so it adds no type to find. The `Poly` functors take a type
  with a parameter (`'a t`), and examples can't declare one.
- **`Triple`** (`79_triple_mod.types`, group `triple_mod`): `make`, `fst`, `snd`, `thd` for
  3-tuples, in the style of `Pair`. Examples can't build or take apart a tuple, and the stdlib has
  no functions for 3-tuples, so without it nothing pins `StrMap.split`'s result. Approved 2026-11-06.

## Modules split across groups

- **`Seq` is two groups.** `80_seq_core_mod.types` (group `seq_core`) has `empty`, `return`, `cons`,
  `is_empty`, `length` and `for_all`; `67_seq_mod.types` (group `seq_mod`) has the rest. Both files
  head with `// Seq`, so both declare the same module, and `Seq.t` is one label across them.
  The reason is an ordering cycle: `Seq.t` is in the types of Option, List, String, Hashtbl, Queue,
  Stack, Map, Set, Array, Iarray, Dynarray, Bytes, Buffer, Float, Result and Format, but `Seq`'s own
  examples need lists, arrays, options and either, so `seq_mod` can only come last. Before the split,
  every earlier module saw `Seq` only as a function's result type -- `Option.to_seq : 'a option -> 'a Seq.t`
  with nothing that takes a sequence apart -- so no example could show its parameter and the search
  committed `Seq` with no parameter. `seq_core` comes before `option_mod`, the first module that
  mentions `Seq`, and depends only on `arith`, `boolean` and `comparison`. Its `for_all` examples are
  what give the label its parameter: `(Seq.for_all ((=) Num) (Seq.return Num))` is positive and
  `(Seq.for_all ((=) Num) (Seq.return Str))` is negative, and the negative type-checks if `Seq.t` has
  no parameter. Every group whose types mention `Seq` depends on `seq_core`, so the label and the six
  names are given to it. Approved 2026-11-12.

## Constructors that are names

- **`open_flag`'s constructors** (`Open_rdonly`, `Open_wronly`, `Open_append`, `Open_creat`,
  `Open_trunc`, `Open_excl`, `Open_binary`, `Open_text`, `Open_nonblock`) are values in
  `17_out.types`, with type `open_flag`. `open_out_gen` and `open_in_gen` take an `open_flag list`,
  and no function builds an `open_flag`. OCaml accepts the constructors as written, and examples
  build the list with `List.cons` and `Nil`.
  `In_channel.open_flag` and `Out_channel.open_flag` are the same type (`Stdlib.open_flag`), so
  their .types files declare them as a rename, and `In_channel.open_gen` and `Out_channel.open_gen`
  take these constructors too.
- **Exception constants** (`Not_found`, `Exit`, `End_of_file`, `Division_by_zero`) are values of type `exn` in
  `27_callback_mod.types`. `Callback.register_exception` takes an `exn`, and nothing in the stdlib builds
  one, so examples need a name for it. OCaml accepts the constructors as written. Only constructors without
  arguments are given: a bare `Failure` is not an OCaml expression, and the loader asks OCaml about every
  name on its own.
- **`Gc.Memprof.allocation_source`'s constructors** (`Normal`, `Marshal`, `Custom`, `Map_file`) are values in
  `41_gc_mod.types`, named `Gc.Memprof.Normal` and so on, with type `Gc.Memprof.allocation_source`. The only other
  source of that type is a field of `Gc.Memprof.allocation`, a record that no example can get, and
  `string_of_allocation_source` takes one.
- **`extern_flags`'s constructors** (`Marshal.No_sharing`, `Marshal.Closures`, `Marshal.Compat_32`) are values of
  type `extern_flags` in `52_marshal_mod.types`. `Marshal.to_string`, `to_bytes`, `to_buffer` and `to_channel`
  take an `extern_flags list`, and nothing builds an `extern_flags`. They are qualified, as OCaml needs.
- **`Sys`'s constructors without arguments** are values in `71_sys_mod.types`, qualified as OCaml needs:
  `Sys.Native` and `Sys.Bytecode` (type `backend_type`, the type of `Sys.backend_type`), `Sys.Signal_default` and
  `Sys.Signal_ignore` (type `signal_behavior`, taken and returned by `Sys.signal` and `Sys.set_signal`), and `Sys.Plus` and
  `Sys.Tilde` (type `extra_prefix`, which only the record `ocaml_release_info` uses, so no function takes it). `Sys.Break`
  is a value of type `exn`, so `sys_mod` depends on `callback_mod`, as `parsing_mod` does for `Parse_error`.
- **`Parsing.Parse_error`** is a value of type `exn` in `59_parsing_mod.types`, qualified as OCaml needs. Only
  `Callback.register_exception` takes an `exn`, so `parsing_mod` depends on `callback_mod`.

## Names left out

- **Nothing is in `skippedNames`** (`OCamlStdlib.kt`), the set whose names' examples are left out.
  `List.to_seq` and `List.of_seq` were in it from 2026-10-29, because `to_seq` was solved first with
  a Seq label of no parameter and a later round can't give a committed label one, so `of_seq` had no
  solution. Two changes retired it, both on 2026-11-12. The `seq_core` group (above) gives `Seq` its
  parameter before `list` runs. That alone left both names wrong (69/71 exact, cost 2): the arity was
  right but the search made a *fresh* label of one parameter, because `list`'s examples only passed a
  sequence through List's own functions and nothing tied it to `Seq` itself. `50_list_mod.exs` now
  ties it with `seq_core`'s consumers -- `(Seq.for_all ((=) Num) (List.to_seq (List.cons Num Nil)))`
  against `(Seq.for_all ((=) Num) (List.to_seq (List.cons Str Nil)))`, and `List.of_seq` applied to
  `Seq.return`, `Seq.cons` and `Seq.empty`. `ocaml-list` is then correct, 71/71 exact in 965 s with
  `--variant depth-per-round,names-per-round=1,depth-bound=6,backjump`.
- **Bigarray functions of `In_channel` and `Out_channel`**: `input_bigarray`, `really_input_bigarray`
  and `output_bigarray`. `Bigarray` has no group, so no example can build the argument.
- **`Result.Syntax`**: `( let* )`, `( and* )`, `( let+ )` and `( and+ )`. Examples can't name an
  operator in a submodule (operators stay unqualified), and these are `bind`, `product` and `map`
  with its arguments swapped, which `64_result_mod` already has.
- **`Float.ArrayLabels`**: the same functions as `Float.Array` with labelled parameters (`Array` has the
  same skip in `README`). Everything in `Float.Array` is in `38_float_mod`.
- **`Iarray.unsafe_get`**: an `external` for `get` without the bounds check; `get` covers it.
- **Ephemeron functors**: `K1.Make`, `K1.MakeSeeded`, `K2.Make`, `K2.MakeSeeded`, `Kn.Make` and `Kn.MakeSeeded`, and the
  module types `S` and `SeededS` (`Hashtbl` leaves out its functors for the same reason). `36_ephemeron_mod` has
  the other 24 values, in `K1`, `K2`, `Kn` and their `Bucket`s. Its `Kn` examples build arrays with `Array.make`, so the
  group depends on `array_mod`.
- **Records in `Gc` and `Lexing`**: `Gc.stat`, `Gc.control`, `Gc.Memprof.allocation`, `Gc.Memprof.tracker`,
  `Lexing.position`, `Lexing.lexbuf` and `Lexing.lex_tables` are records, but examples have no record syntax, so no field
  can be read or built (as with `Complex.t`'s `re` and `im`). Their values come only from functions:
  `Gc.stat`, `Gc.quick_stat`, `Gc.get`, `Lexing.dummy_pos`, `Lexing.from_string` and so on. The only tracker is
  `Gc.Memprof.null_tracker`.
- **`Lexing.engine`, `Lexing.new_engine`**: they take a `lex_tables`, which only ocamllex's output builds, so no example
  can call them.
- **Parsing**: `yyparse` (takes a `parse_tables` record), `peek_val` (takes a `parser_env`, which only the
  action functions inside a `parse_tables` receive), the types `parse_tables` and `parser_env`, and the
  constructor `YYexit of Obj.t`.
- **Scanf's functions with format strings**: `scanf`, `sscanf`, `bscanf`, `kscanf`, `ksscanf`, their `_opt` versions,
  `sscanf_format`, `bscanf_format` and `format_from_string`. The only literal for a string is `Str`, which OCaml reads
  as `"s"` and the .types files give the type `string`, so no example can pass a `format6`, and nothing in the stdlib
  returns one without taking one. `65_scanf_mod` has `Scanning`'s values (`stdin`, `open_in`, `from_string`, ...) and
  `unescaped`. `Scanf.Scan_failure` is an exception with an argument, so it is left out as other such exceptions are.
- **Effect**: only `Shallow.fiber` and `Shallow.get_callstack` are in `34_effect_mod.types` (group `effect_mod`). `fiber` takes
  an ordinary function; `get_callstack` takes the continuation it returns. The other 10 names are left out:
  - `perform` takes an `'a Effect.t`, which only an `effect E : ...` declaration builds, and examples can't declare.
    `Effect.Unhandled` (an exception with an argument) is left out for the same reason, and `Continuation_already_resumed`
    would have no use: only functions that take a handler or a continuation raise it.
  - `Deep.match_with` and `Deep.try_with` take a `handler` or `effect_handler` record, which examples can't build.
  - `Shallow.continue_with`, `discontinue_with` and `discontinue_with_backtrace` take a `Shallow.handler` record too.
  - `Deep.continue`, `discontinue`, `discontinue_with_backtrace` and `get_callstack` take a `Deep.continuation`, which
    only a handler is given (`match_with` and `try_with` pass one to `effc`).
  The only value of `Shallow.continuation` is `fiber`'s result, so the continuation's two parameters are
  shown by comparing continuations with `(=)`.
- **Printf**: no value is in `61_printf_mod.types` and the module has no group: all 13 functions (`fprintf`, `printf`,
  `eprintf`, `sprintf`, `bprintf`, `ifprintf`, `ibprintf`, `kfprintf`, `ikfprintf`, `ksprintf`, `kbprintf`,
  `ikbprintf` and `kprintf`) take a format string. The reason is the same as for Scanf and Format: no example
  can write a `format`. The .types file was missing `kprintf` and had the wrong type for `ifprintf`; both are fixed in
  its `// Left out` comments.
- **Printexc**: `location` is a record (`filename`, `line_number`, ...), so `Slot.location` returns an
  abstract `location option` that examples can only compare and pass to `Option` functions, and
  `raw_backtrace_entry` (`private int`) is abstract too. `backtrace_slot` is abstract in OCaml 5.4 (the old
  .types file had its variant, `Known_location` with a record argument). Exceptions are values only for
  `Not_found`, `Exit`, `End_of_file` and `Division_by_zero` (see "Constructors that are names"), so the exn
  arguments are those four.
- **Sys**: the constructors with arguments, `Signal_handle of (signal -> unit)` and `Other of string` (no example can
  write them, so no `signal_behavior` or `backend_type` value carries a function or a string), the fields of
  `ocaml_release_info` (a record; `Sys.ocaml_release` is a value of that type, and no field can be read), and
  `Sys.Immediate64` (`Make` is a functor, and the module types `Immediate` and `Non_immediate` have no values).
  `Sys.signal_to_string`'s and `Sys.signal_of_int`'s `signal` is `int`, as in the stdlib.
- **Weak**: the functor `Weak.Make` and the module type `Weak.S` (`Hashtbl` leaves out its functors for the same reason).
  `75_weak_mod` has the 8 values of `Weak` itself.
- **Names whose type needs a module scheduled later have no examples**, so they are left out of
  their group's benchmark, although the .types file declares them. Nothing available when the group
  runs can take the result apart, so no example can show its type. Two cases are left:
  `57_option_mod.exs` leaves out `Option.to_list` and `to_result` (16 names declared, 14 solved),
  and says so in a comment on its first lines; `50_list_mod.exs` leaves out `List.partition_map`,
  whose result needs `Either` (group `either_mod`, after `list`). The `Seq` results were in this
  list until the `seq_core` group (above) gave `Seq` its parameter before every module that uses it.
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
- **Bytes**: `compare` is in the .types file, which lacked it. The `unsafe_get`, `unsafe_set`, `unsafe_blit`,
  `unsafe_blit_string`, `unsafe_fill` and `unsafe_escape` externals are left out: they have the types of
  `get`, `set`, `blit`, `blit_string`, `fill` and `escaped`, and the stdlib documents none of them. Bytes
  values in the examples come from `String.to_bytes` (given by `string_mod`) as well as from Bytes' own
  functions.
- **`Seq.Forced_twice`**: an exception, which examples can't name or raise; `67_seq_mod.types` has values only.
- **Array**: `unsafe_get` and `unsafe_set` (the types of `get` and `set`, so examples can't tell them
  apart) and the `Floatarray` submodule (a separate float array type with its own functions) are left
  out. `Array.t` is an alias of `array`, so there is no value to give it.
- **String**: no Bytes, Uchar, Int32 or Int64 function is given, so `bytes`, `Uchar.utf_decode`,
  `int32` and `int64` values come only from String's own functions.

- **Format**:
  - The functions with format string parameters are left out: `printf`, `eprintf`, `fprintf`, `sprintf`,
    `asprintf`, `dprintf`, `ifprintf`, `kfprintf`, `kdprintf`, `ikfprintf`, `ksprintf`, `kasprintf` and
    `format_text` (the same skip as `Printf`, see `README`). The only literal for a string is `Str`, which
    OCaml reads as `"s"` and the .types files give the type `string`, so no example can pass a `format`
    (a format's type parameters also depend on the literal's contents).
  - `pp_open_stag` and `open_stag` are left out: a `stag` comes only from the constructor `String_tag of tag`,
    which has an argument, so examples can't write it. `stag` has no other value.
  - **Record types are abstract.** `formatter_out_functions`, `formatter_stag_functions` and `geometry` are
    records, but examples have no record syntax, so their fields can't be read or built (as `Complex.t`).
    Their values come only from the getters (`pp_get_formatter_out_functions`, `get_geometry`, ...), and the
    setters and `check_geometry` take them. `update_geometry` is given `Fun.id` or `Fun.const g`.
  - **`Output_flush` and `Output_newline`** (constructors of `symbolic_output_item`) are values of the .types file,
    written `Format.Output_flush`, as the constructors of `open_flag`. `Output_string`, `Output_spaces` and
    `Output_indent` have arguments and are left out, so a symbolic buffer only gets flush and newline items.
  - `pp_print_custom_break`'s `fits` and `breaks` triples are made with `Triple.make`.
  - The .types file was corrected (`pp_get_geometry` and `pp_update_geometry` use `geometry`, not `int * int`;
    `dprintf` was wrong) and completed: it now has every other value of `Format` in OCaml 5.4, including the
    functions that use the standard formatter (`print_string`, `open_box`, ...).

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
- **`iarray_mod`** times out (1800 s). With the default settings it times out at 1000 s in the rounds around
  `Iarray.fold_left_map`, which needs outer depth 3. With `names-per-round=1,depth-bound=6` on
  `resolve-on-clash` it was correct (39/39, 249 s) before it depended on `array_mod`; now `Array.make` is given
  with its `array` label, `Iarray.to_array` is solved with a new label, and the `Array.make` examples need
  the two to be equal. `resolve-on-clash` re-solves only rounds, and the given label belongs to no round, so
  it re-solves rounds 21 to 38 again and again until the time runs out.
- **`dynarray_mod` (`33_dynarray_mod`) is not solved** (1800 s, with the default settings and with
  `names-per-round=1,depth-bound=6` on `resolve-on-clash`). The time goes to rounds that hold `blit`: with
  the default settings the round of `blit`, `of_seq` and `to_array` takes 1792 s in concretize (3.1 million
  candidates). With one name per round, `fold_left`, `exists2` and the other functions with a two-parameter
  callback need outer depth 2, every name fails at depth 1 first, and the search then re-solves the names
  before it as one round; the merged round of `make`, `of_list`, `get`, `blit` and `of_seq` takes 1668 s.
  Before `dynarray_mod` depended on `array_mod`, a run with `blit`'s examples cut to a fifth also stopped at
  `append_array`, because `to_array` fixed the `array` label with no parameter; `array_mod` now gives it.

- **`ephemeron_mod`** is not solved. Two things differ from the .types file:
  - A bucket comes only from `Bucket.make`, a fresh value in every example, so only `Fun.flip`/`Fun.compose` examples
    (see EXAMPLES.md, "Parameters that no value shows") can tie its key and data types: functions of one bucket whose
    types another function fixes, compared with `(=)`. The group has these for every `Bucket` function of `K1`, `K2`
    and `Kn`. They are enough when `make` and the functions are solved in one round (a test group with `make` and
    `add` returns `Bucket.t` with the right parameters), but the search can't use them in this group. With the default
    settings the schedule puts `Bucket.make` in an earlier round than the functions of its bucket, so no example
    tells its arity in that round, it is committed as 0, and later rounds fail; the search times out (1800 s) in
    round 0. With `names-per-round=1,depth-bound=6` on `resolve-on-clash`, the clash is found, but searching the
    merged rounds again finds no solution, and each retry re-solves rounds for every order of `K1.make`'s and
    `K2.make`'s parameters; it times out (1800 s) in round 4. Before the `Bucket` examples it answered in 835 s,
    with all 18 `Bucket` names wrong (arity 0). One round of the 8 `K1` names alone also times out (1200 s).
  - `Kn.make` and `Kn.query` come back with the parameters of `Kn.t` in the other order (data, key). The benchmark
    compares a label's parameters by position, so this scores as wrong, but no example can tell the orders apart: they
    are the same abstract type with its parameters renamed, and `Kn.t` values come only from `Kn.make`.
- **`gc_mod`**: the search returns `Memprof.null_tracker : tracker` and `Memprof.start : float -> tracker -> t` with no
  type parameters; the true types have `('minor, 'major) tracker`. Only the fields of a tracker (a record, which
  examples can't use) mention the parameters, and `null_tracker` is the only tracker, so no example can show them.
  Every other name gets its true type, with either setting, in a few seconds.
## Settings some groups need

- **`buffer_mod`** is correct with `--variant depth-per-round,names-per-round=1,depth-bound=6,backjump` (40/40 exact; batch `2026-11-08_153240` at
  commit `6d9943e`, an ancestor of `constrained-needs-positive`). Why it used to be hard: it times out with the default settings (1800 s limit; stopped after 17 minutes in round 2) and with
  `--variant names-per-round=1,depth-bound=6` on `resolve-on-clash` (3000 s). Its examples agree with OCaml and the .types file. With the default 3 names per
  round, the round of `add_substitute`, `length` and `add_subbytes` has no answer in
  the time (the three types need size about 27 of the 30-hole bound). With 1 name per round, `add_substitute` is found in 35 s, but `to_seqi` (`(int * char) Seq.t`) needs
  outer depth 2 and every earlier round succeeds at depth 1, so the search resolves label clashes at depth 1
  (re-searching ever larger merged rounds) before it tries depth 2.
- **`array_mod`** is correct with `--variant depth-per-round,names-per-round=1,depth-bound=6,backjump` (48/48 exact; batch `2026-11-08_153240` at
  commit `6d9943e`, an ancestor of `constrained-needs-positive`). Why it used to be hard: it was not solved within 30 minutes, with the default settings or with
  `names-per-round=1,depth-bound=6` (also on `resolve-on-clash`). Every name up to `fold_left_map` gets
  its true type. `fold_left_map` has no solution at outer depth 2 (its type nests a pair in a function
  result in a function parameter), so the pass at depth 2 goes on to resolve clashes by re-solving a
  round of all earlier names, which takes most of the time. With only `fold_left_map` and a few other
  names, `resolve-on-clash` finds it at depth 3 in 10 minutes.
- **`format_mod`** is correct with `--variant depth-per-round,names-per-round=1,depth-bound=6,backjump` (143/143 exact; batch `2026-11-08_153240` at
  commit `6d9943e`, an ancestor of `constrained-needs-positive`). Why it used to be hard: the default settings ran out of memory (4 GB) in the outline phase of round 0 at
  outer depth 2 after 20 minutes, and `--variant names-per-round=1,depth-bound=6` on `resolve-on-clash` times out
  (1800 s). Its examples agree with OCaml and the .types file. `pp_print_iter` (`(('a -> unit) -> 'b -> unit) -> ...`)
  needs outer depth 2, so its round fails at depth 1 over and over, and each failure that clashes labels re-searches
  the earlier rounds merged (the same cause as `dynarray_mod`). The formatter's label also clashes with unit's and
  option's after the round of `pp_print_option`, which merges rounds 0 to 5 again. With only the formatter constants,
  `pp_print_int`, `pp_print_string` and `pp_print_option` (83 examples) it is correct in 380 s on `resolve-on-clash`.
`map_mod` and `seq_mod` are correct with `--variant names-per-round=1,depth-bound=6`. `list`,
`pair_mod`, `either_mod`, `result_mod` and `float_mod` are correct only on branch `resolve-on-clash`, with
that variant. `queue_mod` was in that list; with `seq_core` it is correct with the default settings
(20/20 exact in 5.4 s, measured 2026-11-12). `pair_mod`, `either_mod` and `result_mod` time out (1800 s) with the variant alone, against 30 s,
62 s and 405 s on `resolve-on-clash`; `list` and `float_mod` also time out with it alone, but that run had 7
benchmarks at once, and they take 2197 s and 1475 s on `resolve-on-clash`. Other groups are correct with the
default settings, except those under "Known wrong results". With the default settings, `float_mod` times
out in the round of `Float.Array.compare`, `find_mapi` and `map2`, and `seq_mod` in the round of
`sorted_merge`, `exists2` and `for_all2`, whose three types need more than the 30-hole bound.

## Copy in tyind

`~/project/bench/bench-examples/ocaml-stdlib` has a copy of some of these files. Its parser has no
labelled parameters and needs qualified names, so in that copy `57_option_mod.types` has no labels,
and `57_option_mod.types` and `76_pair_mod.types` write names in full (`val Option.some`). Its
`Render.prelude` declares every name from the .types files instead of using the real stdlib, and it
has no `StrMap` or `Triple`.
