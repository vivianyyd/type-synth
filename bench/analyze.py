#!/usr/bin/env python3
"""Look at and compare benchmark results written by ./gradlew bench.

A batch is one ./gradlew bench invocation: a directory holding batch.json and one <run>.json per run.
Wherever a batch is expected, give its directory, a unique substring of its name under
bench-results, or `latest` / `latest~N`.

  analyze.py ls                         list batches
  analyze.py show BATCH                 one row per run
  analyze.py rounds BATCH BENCHMARK     one row per query (round, outer depth) of a run
  analyze.py compare BATCH_A BATCH_B    side by side, with B/A ratios
  analyze.py latex BATCH... [--metrics wall,candidates] [--labels A,B]

To work in pandas instead: pd.DataFrame(analyze.rows(analyze.load_batch("latest")))
"""

import argparse
import json
import math
import statistics
import sys
from pathlib import Path

ROOT = Path("bench-results")

# Metrics a run row has, with how to show them. Times are in seconds.
METRICS = {
    "status": ("status", str),
    "wall": ("time (s)", lambda v: f"{v:.2f}"),
    "outline": ("outline (s)", lambda v: f"{v:.2f}"),
    "arity": ("arity (s)", lambda v: f"{v:.2f}"),
    "concretize": ("concretize (s)", lambda v: f"{v:.2f}"),
    "cegis": ("cegis (s)", lambda v: f"{v:.2f}"),
    "unattributed": ("other (s)", lambda v: f"{v:.2f}"),
    "solverTime": ("solver time (s)", lambda v: f"{v:.2f}"),
    "candidates": ("candidates", str),
    "prunedPos": ("pruned +", str),
    "prunedNeg": ("pruned -", str),
    "prunedNegFinal": ("pruned - final", str),
    "relabeled": ("relabeled", str),
    "outlines": ("outlines", str),
    "seeds": ("seeds", str),
    "arityUnsat": ("arity unsat", str),
    "solverCalls": ("solver calls", str),
    "queries": ("queries", str),
    "stop": ("stopped at", str),
}
TIMES = ["wall", "outline", "arity", "concretize", "cegis", "unattributed", "solverTime"]

# ---------------------------------------------------------------------------------------------
# Loading


def batches():
    return sorted((p for p in ROOT.iterdir() if (p / "batch.json").is_file()), key=lambda p: p.name)


def find_batch(spec):
    p = Path(spec)
    if (p / "batch.json").is_file():
        return p
    all_batches = batches()
    if spec.startswith("latest"):
        back = int(spec.split("~")[1]) if "~" in spec else 0
        return all_batches[-1 - back]
    matches = [b for b in all_batches if spec in b.name]
    if len(matches) != 1:
        sys.exit(f"{spec} matches {len(matches)} batches: {[m.name for m in matches]}")
    return matches[0]


def load_batch(spec):
    """The batch's metadata, and its run records."""
    d = find_batch(spec)
    meta = json.loads((d / "batch.json").read_text())
    runs = [json.loads(p.read_text()) for p in sorted(d.glob("*.json")) if p.name != "batch.json"]
    return meta, runs


def row(record):
    """One run as a flat dict of the metrics above."""
    stats = record.get("stats") or {}
    counters = stats.get("counters", {})
    phases = stats.get("phases", {})
    r = {
        "benchmark": record["benchmark"],
        "repeat": record.get("repeat", 0),
        "status": record["status"],
        "variant": record["batch"]["variant"],
        "commit": record["batch"]["git"]["commit"][:8],
        "batch": record["batch"]["batchId"],
    }
    if stats:
        r["wall"] = stats["wallMs"] / 1000
        r["unattributed"] = stats["unattributedMs"] / 1000
        for p in ["outline", "arity", "concretize", "cegis"]:
            r[p] = phases.get(p, {}).get("ms", 0) / 1000
        r["solverTime"] = counters.get("solverMs", 0) / 1000
        for k, v in counters.items():
            if k != "solverMs":
                r[k] = v
        r["queries"] = len(stats.get("queries", []))
        sols = [e for e in stats.get("events", []) if e["kind"] == "solution"]
        if sols:
            s = sols[-1]
            q = stats["queries"][s["query"]]
            r["stop"] = (f"round {q['round']} outer depth {q['outerDepth']}: "
                         f"seed depth {s['seedDepth']}, depth {s['depth']}, size {s['size']}")
    return r


def rows(batch):
    return [row(r) for r in batch[1]]


def by_benchmark(rs):
    """Folds repeats into one row per benchmark: median times, and counts from the first repeat."""
    groups = {}
    for r in rs:
        groups.setdefault(r["benchmark"], []).append(r)
    out = {}
    for name, g in groups.items():
        g.sort(key=lambda r: r["repeat"])
        merged = dict(g[0])
        for t in TIMES:
            vals = [r[t] for r in g if t in r]
            if vals:
                merged[t] = statistics.median(vals)
        statuses = {r["status"] for r in g}
        if len(statuses) > 1:
            merged["status"] = "/".join(sorted(statuses))
        if len({r.get("candidates") for r in g}) > 1:
            merged["candidates"] = f"{g[0].get('candidates')}*"  # repeats disagree
        out[name] = merged
    return out


# ---------------------------------------------------------------------------------------------
# Output


def table(header, body):
    widths = [max(len(str(x)) for x in col) for col in zip(header, *body)]
    fmt = "  ".join(f"{{:<{w}}}" for w in widths)
    print(fmt.format(*header))
    print(fmt.format(*("-" * w for w in widths)))
    for b in body:
        print(fmt.format(*b))


def show_value(metric, value):
    if value is None:
        return "-"
    return METRICS[metric][1](value) if metric in METRICS else str(value)


def cmd_ls(args):
    body = []
    for d in batches():
        meta = json.loads((d / "batch.json").read_text())
        runs = [row(json.loads(p.read_text())) for p in d.glob("*.json") if p.name != "batch.json"]
        statuses = {}
        for r in runs:
            statuses[r["status"]] = statuses.get(r["status"], 0) + 1
        total = sum(r.get("wall", 0) for r in runs)
        git = meta["git"]
        body.append([
            d.name, git["branch"], git["commit"][:8] + ("+" if git["dirty"] else ""), meta["variant"],
            " ".join(f"{k}={v}" for k, v in sorted(statuses.items())), f"{total:.1f}", meta["notes"],
        ])
    table(["batch", "branch", "commit", "variant", "statuses", "time (s)", "notes"], body)


DEFAULT_SHOW = ["status", "wall", "outline", "arity", "concretize", "unattributed", "solverCalls",
                "candidates", "prunedPos", "prunedNeg", "stop"]


def wrong_answer(record):
    """Each solution next to the expected answer, with the names whose types differ marked."""
    expected = record["expected"]
    for i, (solution, differs) in enumerate(zip(record["solutions"], record["mismatches"])):
        if len(record["solutions"]) > 1:
            print(f"Solution {i + 1}:")
        table(["", "name", "returned", "expected"],
              [["*" if n in differs else "", n, t, expected.get(n, "-")] for n, t in solution.items()])
    print("(* differs from expected)")


def cmd_show(args):
    batch = load_batch(args.batch)
    meta = batch[0]
    print(f"{meta['batchId']}  variant={meta['variant']}  branch={meta['git']['branch']}  notes={meta['notes']!r}\n")
    metrics = args.metrics.split(",") if args.metrics else DEFAULT_SHOW
    rs = by_benchmark(rows(batch))
    table(["benchmark"] + [METRICS.get(m, (m,))[0] for m in metrics],
          [[name] + [show_value(m, r.get(m)) for m in metrics] for name, r in rs.items()])
    for record in sorted(batch[1], key=lambda r: r["runId"]):
        if record["status"] == "wrong":
            print(f"\n{record['runId']} is wrong:")
            wrong_answer(record)


def cmd_rounds(args):
    _, runs = load_batch(args.batch)
    record = next((r for r in runs if r["runId"] == args.benchmark), None) or sys.exit("No such run")
    if not record.get("stats"):
        error = (record.get("error") or "").partition("\n")[0]
        sys.exit(f"{args.benchmark} has no stats ({record['status']}) {error}".rstrip())
    body = []
    for q in record["stats"]["queries"]:
        ph = q["phases"]
        c = lambda k: sum(p.get(k, 0) for p in ph.values())
        body.append([
            q["id"], q["round"], q["outerDepth"], " ".join(q["names"]), q["numPos"], q["numNeg"],
            f"{q['ms'] / 1000:.2f}",
            *(f"{ph.get(p, {}).get('ms', 0) / 1000:.2f}" for p in ["outline", "arity", "concretize", "cegis"]),
            c("candidates"), c("prunedPos"), c("prunedNeg"), c("solverCalls"), c("solutions"),
        ])
    table(["query", "round", "outer depth", "names", "+", "-", "time (s)", "outline", "arity", "concretize",
           "cegis", "candidates", "pruned +", "pruned -", "solver calls", "solutions"], body)


DEFAULT_COMPARE = ["status", "wall", "candidates", "prunedNeg", "solverCalls"]


def cmd_compare(args):
    a, b = load_batch(args.a), load_batch(args.b)
    ra, rb = by_benchmark(rows(a)), by_benchmark(rows(b))
    print(f"A: {a[0]['batchId']}  {a[0]['notes']!r}")
    print(f"B: {b[0]['batchId']}  {b[0]['notes']!r}\n")
    metrics = args.metrics.split(",") if args.metrics else DEFAULT_COMPARE
    header, body = ["benchmark"], []
    for m in metrics:
        label = METRICS.get(m, (m,))[0]
        header += [f"A {label}", f"B {label}"] + ([] if m == "status" else ["B/A"])
    ratios = {m: [] for m in metrics}
    for name in list(ra) + [n for n in rb if n not in ra]:
        x, y = ra.get(name, {}), rb.get(name, {})
        line = [name]
        for m in metrics:
            va, vb = x.get(m), y.get(m)
            line += [show_value(m, va), show_value(m, vb)]
            if m != "status":
                if isinstance(va, (int, float)) and isinstance(vb, (int, float)) and va > 0 and vb > 0:
                    line.append(f"{vb / va:.2f}")
                    if x.get("status") == y.get("status") == "correct":
                        ratios[m].append(vb / va)
                else:
                    line.append("-")
        body.append(line)
    table(header, body)
    print("\nGeometric mean of B/A over benchmarks both got right:")
    for m, rs in ratios.items():
        if rs:
            print(f"  {METRICS.get(m, (m,))[0]}: {math.exp(sum(map(math.log, rs)) / len(rs)):.3f} ({len(rs)} benchmarks)")


def latex_escape(s):
    return str(s).replace("\\", r"\textbackslash{}").replace("_", r"\_").replace("&", r"\&").replace("%", r"\%")


def cmd_latex(args):
    loaded = [load_batch(s) for s in args.batches]
    labels = args.labels.split(",") if args.labels else [b[0]["variant"] for b in loaded]
    metrics = args.metrics.split(",")
    per = [by_benchmark(rows(b)) for b in loaded]
    names = list(dict.fromkeys(n for p in per for n in p))

    def cell(r, m):
        if not r:
            return "--"
        if r["status"] != "correct" and m in TIMES:
            return r"\textit{%s}" % latex_escape(r["status"])
        return latex_escape(show_value(m, r.get(m)))

    cols = len(loaded) * len(metrics)
    print(r"\begin{tabular}{l" + "r" * cols + "}")
    print(r"\toprule")
    if len(loaded) > 1:
        print(" & " + " & ".join(r"\multicolumn{%d}{c}{%s}" % (len(metrics), latex_escape(l)) for l in labels) + r" \\")
        rules = [f"\\cmidrule(lr){{{2 + i * len(metrics)}-{1 + (i + 1) * len(metrics)}}}" for i in range(len(loaded))]
        print(" ".join(rules))
    print("Benchmark & " + " & ".join(latex_escape(METRICS.get(m, (m,))[0]) for _ in loaded for m in metrics) + r" \\")
    print(r"\midrule")
    for n in names:
        print(latex_escape(n) + " & " + " & ".join(cell(p.get(n), m) for p in per for m in metrics) + r" \\")
    print(r"\bottomrule")
    print(r"\end{tabular}")


def main():
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", default=str(ROOT), help="where batches are (default: bench-results)")
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("ls")
    p = sub.add_parser("show")
    p.add_argument("batch")
    p.add_argument("--metrics", help=f"comma-separated, from: {', '.join(METRICS)}")
    p = sub.add_parser("rounds")
    p.add_argument("batch")
    p.add_argument("benchmark", help="the run id, e.g. cons, or cons.1 for a repeat")
    p = sub.add_parser("compare")
    p.add_argument("a")
    p.add_argument("b")
    p.add_argument("--metrics", help=f"comma-separated, from: {', '.join(METRICS)}")
    p = sub.add_parser("latex")
    p.add_argument("batches", nargs="+")
    p.add_argument("--metrics", default="wall,candidates")
    p.add_argument("--labels", help="comma-separated column group names (default: variants)")
    args = parser.parse_args()
    ROOT = Path(args.root)
    {"ls": cmd_ls, "show": cmd_show, "rounds": cmd_rounds, "compare": cmd_compare, "latex": cmd_latex}[args.cmd](args)


if __name__ == "__main__":
    main()
