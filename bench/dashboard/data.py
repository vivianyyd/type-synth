"""Reads bench-results for the dashboard: batches, run summaries, files and traces.

A run summary has the run's own fields, its totals over steps, and a row per step. Step rows are
analyze.row (so the dashboard and analyze.py agree on every metric) plus a few fields row leaves
out. Summaries are cached by (mtime, size), since a record can be tens of MB.
"""

import gzip
import json
import sys
import threading
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import analyze  # noqa: E402

GOOD = {"correct", "solved"}


class Results:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self._cache = {}  # path -> ((mtime, size), summary)
        self._lock = threading.Lock()

    # -----------------------------------------------------------------------------------------
    # Batches

    def batch_dirs(self):
        """Batches directly under the root, and one folder down (e.g. bench-results/kept/BATCH)."""
        if not self.root.is_dir():
            return []
        out = []
        for d in self.root.iterdir():
            if (d / "batch.json").is_file():
                out.append(d)
            elif d.is_dir() and not d.name.startswith("."):
                out += [e for e in d.iterdir() if (e / "batch.json").is_file()]
        # Batch names start with the date, so this is oldest first across folders
        return sorted(out, key=lambda d: (d.name, str(d)))

    def batch_dir(self, batch_id):
        d = (self.root / batch_id).resolve()
        if self.root not in d.parents or len(d.relative_to(self.root).parts) > 2 or not (d / "batch.json").is_file():
            raise KeyError(f"no batch {batch_id}")
        return d

    def batches(self):
        out = []
        for d in self.batch_dirs():
            try:
                meta = json.loads((d / "batch.json").read_text())
            except (OSError, ValueError) as e:
                meta = {"batchId": d.name, "loadError": str(e)}
            runs = [self.summary(p) for p in sorted(d.glob("*.json")) if p.name != "batch.json"]
            rel = d.relative_to(self.root)
            out.append({
                "id": rel.as_posix(),
                "folder": rel.parent.as_posix() if rel.parent != Path(".") else "",
                "meta": meta,
                "files": [{"name": f.name, "size": f.stat().st_size} for f in sorted(d.iterdir()) if f.is_file()],
                "runs": runs,
            })
        return out

    # -----------------------------------------------------------------------------------------
    # Runs

    def summary(self, path):
        st = path.stat()
        key = (st.st_mtime_ns, st.st_size)
        with self._lock:
            hit = self._cache.get(path)
        if hit and hit[0] == key:
            return hit[1]
        try:
            s = summarize(json.loads(path.read_text()))
        except Exception as e:  # a record this code can't read
            s = {"runId": path.stem, "benchmark": path.stem.split(".")[0], "status": "unreadable",
                 "errorLine": f"{type(e).__name__}: {e}", "steps": [], "numSteps": 0, "goodSteps": 0}
        s["bytes"] = st.st_size
        with self._lock:
            self._cache[path] = (key, s)
        return s

    def run_path(self, batch_id, run_id):
        p = self.batch_dir(batch_id) / f"{run_id}.json"
        if "/" in run_id or run_id == "batch" or not p.is_file():
            raise KeyError(f"no run {run_id} in {batch_id}")
        return p

    def file_path(self, batch_id, name):
        d = self.batch_dir(batch_id)
        if name not in {f.name for f in d.iterdir() if f.is_file()}:
            raise KeyError(f"no file {name} in {batch_id}")
        return d / name

    def trace(self, batch_id, run_id, step=None, kind=None, search=None, phase=None, offset=0, limit=100):
        """Lines per step over the whole trace; counts over the chosen step's lines; and the lines
        matching every filter, from offset."""
        p = self.file_path(batch_id, f"{run_id}.trace.jsonl.gz")
        counts = {"step": {}, "kind": {}, "phase": {}, "search": {}}
        lines, matched = [], 0
        with gzip.open(p, "rt") as f:
            for raw in f:
                try:
                    t = json.loads(raw)
                except ValueError:
                    continue
                s = str(t.get("step"))
                counts["step"][s] = counts["step"].get(s, 0) + 1
                if step and s != step:
                    continue
                for k in ["kind", "phase", "search"]:
                    v = str(t.get(k))
                    counts[k][v] = counts[k].get(v, 0) + 1
                if kind and t.get("kind") != kind:
                    continue
                if search is not None and str(t.get("search")) != search:
                    continue
                if phase and t.get("phase") != phase:
                    continue
                if offset <= matched < offset + limit:
                    lines.append(t)
                matched += 1
        return {"counts": counts, "matched": matched, "offset": offset, "lines": lines}


def summarize(record):
    """The run's fields, its totals over steps, and a row per step."""
    rows = [step_row(record, s, i) for i, s in enumerate(record["steps"])]
    r = {
        "runId": record["runId"],
        "benchmark": record["benchmark"],
        "repeat": record["repeat"],
        "status": record["status"],
        "config": record.get("config"),
        "steps": rows,
        "numSteps": len(rows),
        "goodSteps": sum(s["status"] in GOOD for s in rows),
    }
    if record.get("error"):
        r["errorLine"] = first_line(record["error"])
    elif rows and rows[-1].get("errorLine"):
        r["errorLine"] = rows[-1]["errorLine"]
    for k in ["wall", "load", "exactNames", "names", "cost", "expectedSize"]:
        vals = [s[k] for s in rows if isinstance(s.get(k), (int, float))]
        if vals:
            r[k] = sum(vals)
    return r


def step_row(record, step, index):
    """analyze.row, plus what it leaves out. Times in seconds, like row."""
    r = analyze.row(record, step)
    r["runId"] = record["runId"]
    r["parent"] = record["benchmark"]
    r["step"] = step["step"]
    r["stepIndex"] = index
    if step.get("loadMs") is not None:
        r["load"] = step["loadMs"] / 1000
    if r.get("names"):
        r["exactFrac"] = r["exactNames"] / r["names"]
    sols = step.get("solutions")
    if sols is not None:
        r["numSolutions"] = len(sols)
    if step.get("error"):
        r["errorLine"] = first_line(step["error"])
    stats = step.get("stats") or {}
    for phase, vals in (stats.get("phases") or {}).items():
        for k, v in vals.items():
            if k != "ms" and isinstance(v, (int, float)):
                r[f"{phase}.{k}"] = v
    searches = stats.get("searches") or []
    if searches:
        r["rounds"] = max(q.get("round", 0) for q in searches) + 1
        r["maxOuterDepth"] = max(q.get("outerDepth", 0) for q in searches)
    events = stats.get("events") or []
    r["events"] = len(events)
    schedule = (stats.get("info") or {}).get("schedule")
    if schedule is not None:
        r["scheduledRounds"] = len(schedule)
    return r


def first_line(text):
    return str(text).strip().partition("\n")[0][:300]
