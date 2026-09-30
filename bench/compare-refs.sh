#!/usr/bin/env bash
# Runs the same benchmarks at each of several git refs, each checked out in a worktree of its own,
# with results going to this checkout's bench-results. Each ref must have the bench harness.
#
#   bench/compare-refs.sh REF... [-- BENCH_ARGS...]
#   bench/compare-refs.sh main skolemize -- sexp --timeout 300
#
# BENCH_ARGS are passed to ./gradlew bench as they are, quoting kept. Then compare with
#   bench/analyze.py compare <batch of first ref> <batch of second ref>
set -euo pipefail

root=$(git rev-parse --show-toplevel)
refs=()
while [[ $# -gt 0 && $1 != -- ]]; do refs+=("$1"); shift; done
[[ $# -gt 0 ]] && shift
[[ ${#refs[@]} -gt 0 ]] || { sed -n '2,9p' "$0"; exit 1; }

for ref in "${refs[@]}"; do
  git cat-file -e "$ref:src/test/kotlin/bench/Main.kt" 2>/dev/null ||
    { echo "$ref has no bench harness"; exit 1; }
done

# --args is one string that Gradle splits at spaces outside quotes, with no escapes
gradle_quote() {
  if [[ $1 != *"'"* ]]; then printf "'%s'" "$1"
  elif [[ $1 != *'"'* ]]; then printf '"%s"' "$1"
  else echo "Can't pass an argument with both kinds of quote: $1" >&2; exit 1
  fi
}
args=()
for a in "$@"; do args+=("$(gradle_quote "$a")"); done

for ref in "${refs[@]}"; do
  wt=$(mktemp -d "${TMPDIR:-/tmp}/type-synth-worktree-XXXX")
  git worktree add --detach "$wt" "$ref" >/dev/null
  echo "== $ref ($(git rev-parse --short "$ref")) in $wt"
  # The first --notes is overridden by one in BENCH_ARGS
  (cd "$wt" && ./gradlew bench -q --args="--out $(gradle_quote "$root/bench-results") --notes $(gradle_quote "ref:$ref") ${args[*]}") || true
  git worktree remove --force "$wt"
done
