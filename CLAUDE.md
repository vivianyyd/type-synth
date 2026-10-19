# type-synth

## Setup

Kotlin on the JVM, built with the Gradle wrapper (`./gradlew`). Developed with OpenJDK 11. Two
external tools have to be on `PATH`: a `python3` that can import cvc5, and an OCaml 5.4 `ocamlc`.

### cvc5 (label arity solver)

`callCVC` (`src/main/kotlin/util/io/cvc/CVCFiles.kt`) writes each query as a Python script using
the cvc5 pythonic API. Long-lived workers (`src/main/python/cvc_worker.py`) run the scripts: one
query at a time per worker, one worker per concurrent call. Workers run `python3` from `PATH` with
`PYTHONPATH=src/main/python`, for `cardinality.py`. Install cvc5 in a venv outside the repo,
which isn't gitignored:

```sh
python3 -m venv ~/.venvs/type-synth
~/.venvs/type-synth/bin/pip install cvc5     # works with 1.4.2 on Python 3.10
```

`cardinality.py` supports both newer cvc5 (`Context.tm`) and older cvc5 (`Context.solver`). A query
that fails throws: with its traceback if it raised, with the worker's stderr if the worker died (for
example, cvc5 missing), and with cvc5's output if cvc5 gave up ("failed to solve"). Before that
check existed, a crash looked like a solution with no label arities, and every outline was dropped
silently (symptom: "No solution found at iteration 0").

Queries and answers are written to disk only with `-Dtypesynth.cvcDir=DIR`. `./gradlew test`
doesn't forward system properties, so pass it as `JAVA_TOOL_OPTIONS="-Dtypesynth.cvcDir=DIR"`. For
`./gradlew bench`, use `--jvm-args '-Xmx4g -Dtypesynth.cvcDir=DIR'`.

### OCaml (ground truth for the OCaml stdlib examples)

`OCamlChecker` (`src/test/kotlin/testutil/ocaml/OCamlChecker.kt`) runs `ocamlc` from `PATH`. The
examples use stdlib functions from OCaml 5.1 to 5.4 (`List.is_empty`, `find_index`, `take`, `drop`,
`singleton`), so anything older fails while loading examples with "Oracle from parsed types
disagrees with ocamlc ground truth". Set up with opam:

```sh
opam init -y --bare --no-setup --disable-sandboxing   # --no-setup leaves shell rc files alone;
                                                       # --disable-sandboxing if bubblewrap is missing
opam switch create 5.4.1 ocaml-base-compiler.5.4.1    # compiles OCaml, a few minutes
eval $(opam env --switch=5.4.1)                        # or put ~/.opam/5.4.1/bin first on PATH
```

### Running

With both on `PATH`. These were checked with `--no-daemon`; if you use a daemon, run `./gradlew --stop`
after changing `PATH`, in case it kept the old one.

```sh
export PATH=$HOME/.opam/5.4.1/bin:$HOME/.venvs/type-synth/bin:$PATH
./gradlew bench -q --args=cons                     # one quick search, end to end
./gradlew --no-daemon test
./gradlew bench -q --args="ocaml ocaml-chained"    # see bench/README.md
```

Failing on `main` for reasons unrelated to setup: `OCamlStdlibTest.load all and split` (the OCaml
type parser can't read labelled arguments; `fix-ocaml-type-parser` fixes it).

Sketch (`src/main/kotlin/util/io/sketch`) is no longer called from anywhere, so it isn't needed.
