# Benchmarking

```sh
./gradlew bench                                   # the sexp suite, default variant
./gradlew bench --args="hofs cons --notes 'bigger neg check' --repeat 3"
./gradlew bench --args="ocaml --variant auto3 --timeout 1200"
./gradlew bench --args=--list                     # benchmarks, suites, variants
./gradlew bench --args=--help

bench/analyze.py ls                               # every batch
bench/analyze.py show latest                      # one row per step; wrong answers in full
bench/analyze.py rounds latest hofs               # one row per search of one step
bench/analyze.py rounds latest ocaml-chained/list
bench/analyze.py compare latest~1 latest          # side by side, B/A ratios, geometric mean
bench/analyze.py latex BATCH_A BATCH_B --metrics wall,candidates --labels before,after

bench/compare-refs.sh main my-branch -- sexp      # same benchmarks at several commits

bench/dashboard/serve.py                          # all of the above in a browser, at localhost:8765
```

The dashboard is described in `bench/dashboard/README.md`.

Each run gets a JVM of its own, so that nothing carries over between runs (static id counters, the
JIT, the heap), and a crash takes down only that run. A benchmark is a list of steps, solved in
order in the run's JVM, each committing to the first solution of the step before it; most
benchmarks have one step. Unlike runs, the steps of a run share a JVM: later steps run with a warm
JIT and the static id counters the earlier steps left. Runs are one at a
time unless `--jobs N`, which is fine for checking answers but skews timings. It exits non-zero
if any run is `wrong`, `error` or `crashed`; a `timeout` or `no-solution` is a result, not a
failure.

## `./gradlew bench` options

```
./gradlew bench -q --args="[NAME ...] [OPTION ...]"
```

NAME is a benchmark or suite (default `sexp`). Any order. Quote values with spaces in single
quotes. Last occurrence of an option wins.

```
--variant NAME,...  variants from Variants.kt, in order       (default: default)
--notes TEXT        recorded with every run
--timeout SECONDS   per step, including loading it            (default: 600)
--repeat N          run each benchmark N times                (default: 1)
--jobs N            runs at once; skews timings               (default: 1)
--trace             write candidates to NAME.trace.jsonl.gz
--debug             write search progress to NAME.log
--jvm-args 'ARGS'   JVM options per run, replaces default     (default: -Xmx4g)
--out DIR           results directory                         (default: bench-results)
--list              print benchmarks, suites, variants; run nothing
--help              print options
```

Suites: `sexp`, `sexp-unsolved`, `ocaml` (each module group given the true types of the groups
before it). `ocaml-chained` is in no suite: one benchmark of six steps, `basics` to `str`, each
solving one module group given the search's own answer for the groups before it. It stops at the
first step with no solution, a timeout or an error; a wrong step is committed to, and the chain
goes on. Variants: `default`, `single-round`, `auto3`, `sound`, `observational`, `ocaml-toplevel`,
`deepen-arities=N` (any bound N, e.g. `deepen-arities=2`). Defined in
`src/test/kotlin/bench/Benchmarks.kt` and `Variants.kt`.

OCaml benchmarks ask OCaml whether examples type-check with a server around its type checker
(`src/test/ocaml/typer.ml`, built into `build/ocaml-typer/` on first use; needs `ocamlfind` and
`compiler-libs`). `ocaml-toplevel` asks one `ocaml` toplevel instead, which gives the same answers
about 25 times slower per check; see `OCamlGroundTruth.kt` for how the ways of asking compare.

System properties (via `--jvm-args`): `-Dtypesynth.debug` (same as `--debug`),
`-Dtypesynth.cvcDir=DIR` (keep solver files in a new DIR/run-*).

Example:

```
./gradlew bench -q --args="dictchain hofs --variant auto3 --repeat 3 --notes 'smaller arity queries'"
```

## What gets written

`bench-results/<date>_<commit>[+dirty]_<variant>/` (gitignored; copy batches worth keeping):

- `batch.json`: variant, notes, git commit/branch/subject, machine, options.
- `changes.patch`: uncommitted changes to the code, if there were any.
- `<benchmark>.json`: one record per run (below). With `--repeat`, `<benchmark>.<i>.json`.
- `<benchmark>.log`: the run's output, if it printed any: what the search is doing with `--debug`,
  or why it failed.
- `<benchmark>.trace.jsonl.gz`: with `--trace`, one line per candidate:
  `{step, search, phase, kind, state}`, where kind is `candidate` (passed the positive examples),
  `prunedPos`, `prunedNeg` or `relabeled`. Search ids restart with each step.

A record (`schema` 2) holds the batch, the configuration, the run's `status`, and `steps`, one per
step that ran, in order. Each step has:

- `step`: its name; a one-step benchmark's step is named like the benchmark.
- `status`: `correct`, `wrong`, `solved` when there is no expected answer, `no-solution`,
  `timeout`, or `error` (with `error`, the stack trace).
- `loadMs`: building the step's problem, which doesn't include searching.
- `groundTruth`: what answered whether examples type-check, unless the step timed out or failed.
- `names`: the names the step solved: those in its first solution that it wasn't given (not an
  earlier step's, nor a fixed group's in `ocaml`).
- `solutions`, `expected` and `scores` (below), for the step's `names` only. The whole answer after
  a step is the union of the solutions of the steps up to it.
- `stats` (below), if the search started.

The run's `status` is that of the first step that isn't `correct` or `solved`, or else of the last
step. The record is rewritten after each step, with `status: "running"` until the last, so
`analyze.py show` shows how far a run has got, and a run that stops early keeps the steps it
finished (below).

`stats` has:

- `wallMs`: from starting the search to its answer.
- `counters`: totals. `phases`: time and counts per phase (`outline`, `arity`, `concretize`,
  `cegis`). `unattributedMs`: time in no phase, which should stay small.
- `searches`: one per problem the engine hands to the search (a round, at an outer depth bound),
  with its names, number of examples, and time and counts per phase.
- `events`: each solution a search found, with the seed depth, depth and size it was found at,
  and each counterexample CEGIS added.
- `info.schedule`: the rounds the engine decided on.

Each of `scores` is `diffTo` (`src/main/kotlin/oneast/SearchStateEquivalence.kt`) from the expected
answer to that solution, up to renaming labels and variables, counting the step's names only.
`diffTo` pairs labels greedily, visiting names in the expected answer's order, so a label conflict
is charged to the later name. The bench orders it by step: the names the step was given first, then
its own, so a conflict is charged to the step that introduced it.

- `cost`: nodes that differ, summed over names; 0 when the solution is right. `expectedSize`: nodes
  in the expected answer. `ratio`: `cost / expectedSize`, which can be over 1.
- `exactNames` of `names`: how many names have a type with cost 0.
- `byName`: each name's `cost` and the `expectedSize` of its expected type.

`analyze.py show` and `compare` have a row per step, named like the benchmark when it has one step
and `benchmark/step` otherwise (e.g. `ocaml-chained/list`). They show the closest solution's `exact`
and `cost` (`--metrics diff` for the ratio), and the cost of each name of a wrong answer.

Records are self-contained JSON, so anything can read them, e.g. pandas:
`pd.DataFrame(analyze.rows(analyze.load_batch("latest")))`, or DuckDB:
`select * from read_json_auto('bench-results/*/*.json')`.

### A run that stops early keeps its finished steps

The run's JVM writes its record after every step, to a temporary file that it renames over
`<run>.json`, so the file always holds a whole record of the steps finished so far. When that JVM
exits, the bench (the parent JVM) reads the record. If its status is still `running`, the run
didn't finish: the bench sets the status to `crashed` (or `timeout`, if the bench killed it for
running past `--timeout` times the number of steps, plus a minute), adds an `error`, and keeps
every finished step. If there's no record at all, it writes one with no steps.

So a crash, the OOM killer, or killing the run yourself loses only the step in progress. That
makes it a way to cut a chain short, e.g. to skip a step you know will time out, once
`analyze.py show latest` shows the steps you want:

```sh
pkill -9 -f -- '--child ocaml-chained'    # the run's JVM, not ./gradlew bench
```

The bench then goes on to the next run, and exits non-zero, since the run is `crashed`.

## Timing lazy code

Work is charged to whichever phase is running, not to whichever phase built the sequence doing it.
`Stats.phase(search, phase) { ... }` charges an eager block, and `seq.inPhase(search, phase)` charges
each step of the sequence's iterator. Phases nest, and time is exclusive, so the per-phase times
add up to the wall-clock time.

## Changing what is measured

- A counter: add it to `Count` in `src/main/kotlin/bench/Stats.kt`, and `Stats.inc(Count.X)` where
  it happens. It goes to the phase and search running at the time. Cheap enough for hot loops.
- A phase: add it to `Phase`, and wrap the code in `Stats.phase` or `inPhase`.
- A one-off fact about the run: `Stats.note(key, value)`. Something that happens at a moment:
  `Stats.event(kind, fields)`.
- A candidate in the trace: `Stats.trace(kind) { state }`. It builds nothing unless tracing.

With no recording running (as in the tests), all of these do nothing.

## Versions to compare

There are two ways to compare versions of the search: build both into the code and pick one with
`--variant`, or keep each on its own commit or branch and run each.

**A variant** fits an alternative you will keep comparing against as the code changes, such as a
row of an ablation. Put the choice in `Configuration` (`src/main/kotlin/oneast/OneMain.kt`) and
add a variant for it in `src/test/kotlin/bench/Variants.kt`. Then any later commit can run both
sides, and alongside other variants, without merging anything:

```sh
./gradlew bench -q --args="sexp"                                  # solver picks label arities
./gradlew bench -q --args="sexp --variant deepen-arities=2"        # every arity up to 2
./gradlew bench -q --args="sexp --variant deepen-arities=2,sound"  # combined with another variant
bench/analyze.py compare latest~1 latest
```

Keep `Configuration` plain data, since it is recorded as is; that is how records from different
variants are told apart.

**A commit or branch** fits a change that replaces the old way, or a one-off experiment you won't
keep both sides of. Every run records its commit, and `compare-refs.sh` runs the same benchmarks
at several refs (e.g. `bench/compare-refs.sh main my-branch -- sexp`). A branch only compares
against the code it forked from: to compare it again after other changes, it has to be rebased
or merged.

The two combine: `compare-refs.sh main my-branch -- sexp --variant deepen-arities=2` compares two
commits under one variant.

Benchmarks and suites are in `src/test/kotlin/bench/Benchmarks.kt`.
