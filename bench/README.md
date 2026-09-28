# Benchmarking

```sh
./gradlew bench                                   # the sexp suite, default variant
./gradlew bench --args="hofs cons --notes 'bigger neg check' --repeat 3"
./gradlew bench --args="ocaml --variant auto3 --timeout 1200"
./gradlew bench --args=--list                     # benchmarks, suites, variants
./gradlew bench --args=--help

bench/analyze.py ls                               # every batch
bench/analyze.py show latest                      # one row per benchmark
bench/analyze.py rounds latest hofs               # one row per round of one run
bench/analyze.py compare latest~1 latest          # side by side, B/A ratios, geometric mean
bench/analyze.py latex BATCH_A BATCH_B --metrics wall,candidates --labels before,after

bench/compare-refs.sh main my-branch -- sexp      # same benchmarks at several commits
```

Each run gets a JVM of its own, so that nothing carries over between runs (static id counters, the
JIT, the heap), a run can be timed out, and a crash takes down only that run. Runs are one at a
time unless `--jobs N`, which is fine for checking answers but skews timings.

## What gets written

`bench-results/<date>_<commit>[+dirty]_<variant>/` (gitignored; copy batches worth keeping):

- `batch.json`: variant, notes, git commit/branch/subject, machine, options.
- `changes.patch`: uncommitted changes to the code, if there were any.
- `<benchmark>.json`: one record per run (below). With `--repeat`, `<benchmark>.<i>.json`.
- `<benchmark>.log`: the run's output. `--debug` fills it with what the search is doing.
- `<benchmark>.trace.jsonl.gz`: with `--trace`, one line per candidate:
  `{query, phase, kind, state}`, where kind is `candidate` (passed the positive examples),
  `prunedPos`, `prunedNeg` or `relabeled`.

A record holds the batch, the configuration, `status` (`correct`, `wrong`, `solved` when there is
no expected answer, `no-solution`, `timeout`, `error`, `crashed`), the solutions, the expected
answer and how each solution differs from it, and `stats`:

- `wallMs`: from starting the search to its answer; loading the benchmark is `loadMs`.
- `counters`: totals. `phases`: time and counts per phase (`outline`, `arity`, `concretize`,
  `cegis`). `unattributedMs`: time in no phase, which should stay small.
- `queries`: one per problem the engine hands to the search (a round, at an outer depth bound),
  with its names, number of examples, and time and counts per phase.
- `events`: each solution a query found, with the seed depth, depth and size it was found at,
  and each counterexample CEGIS added.
- `info.schedule`: the rounds the engine decided on.

Records are self-contained JSON, so anything can read them, e.g. pandas:
`pd.DataFrame(analyze.rows(analyze.load_batch("latest")))`, or DuckDB:
`select * from read_json_auto('bench-results/*/*.json')`.

## Timing lazy code

Work is charged to whichever phase is running, not to whichever phase built the sequence doing it.
`Stats.phase(query, phase) { ... }` charges an eager block, and `seq.inPhase(query, phase)` charges
each step of the sequence's iterator. Phases nest, and time is exclusive, so the per-phase times
add up to the wall-clock time. Never `yield` inside `Stats.phase`.

## Changing what is measured

- A counter: add it to `Count` in `src/main/kotlin/bench/Stats.kt`, and `Stats.inc(Count.X)` where
  it happens. It goes to the phase and query running at the time. Cheap enough for hot loops.
- A phase: add it to `Phase`, and wrap the code in `Stats.phase` or `inPhase`.
- A one-off fact about the run: `Stats.note(key, value)`. Something that happens at a moment:
  `Stats.event(kind, fields)`.
- A candidate in the trace: `Stats.trace(kind) { state }`. It builds nothing unless tracing.

With no recording running (as in the tests), all of these do nothing.

## Versions to compare

An alternative worth keeping side by side goes in `Configuration`
(`src/main/kotlin/oneast/OneMain.kt`), with a variant for it in
`src/test/kotlin/bench/Variants.kt`. Then one commit can run the whole ablation. Keep
`Configuration` plain data, since it is recorded as is. Anything else can just be a commit or a
branch: every run records its commit, and `compare-refs.sh` runs several.

Benchmarks and suites are in `src/test/kotlin/bench/Benchmarks.kt`.
