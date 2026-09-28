#!/usr/bin/env bash
# Runs the same benchmarks at each of several git refs, each checked out in a worktree of its own,
# with results going to this checkout's bench-results. Each ref must have the bench harness.
#
#   bench/compare-refs.sh REF... [-- BENCH_ARGS...]
#   bench/compare-refs.sh main skolemize -- sexp --timeout 300
#
# BENCH_ARGS are passed to ./gradlew bench --args, joined by spaces. Then compare with
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

for ref in "${refs[@]}"; do
  wt=$(mktemp -d "${TMPDIR:-/tmp}/type-synth-worktree-XXXX")
  git worktree add --detach "$wt" "$ref" >/dev/null
  echo "== $ref ($(git rev-parse --short "$ref")) in $wt"
  # The first --notes is overridden by one in BENCH_ARGS
  (cd "$wt" && ./gradlew bench -q --args="--out $root/bench-results --notes ref:$ref $*") || true
  git worktree remove --force "$wt"
done
