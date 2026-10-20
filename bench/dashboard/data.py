"""Reads bench-results for the dashboard: batches, run summaries, files and traces.

Run summaries are analyze.row (so the dashboard and analyze.py agree on every metric) plus a few
fields row leaves out. Summaries are cached by (mtime, size), since a record can be tens of MB.
"""

import gzip
import json
import sys
import threading
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import analyze  # noqa: E402

PHASES = ["outline", "arity", "concretize", "cegis"]


class Results:
    def __init__(self, root):
        self.root = Path(root)
        self._cache = {}  # path -> ((mtime, size), summary)
        self._lock = threading.Lock()

    # -----------------------------------------------------------------------------------------
    # Batches

    def batch_dir(self, batch_id):
        d = self.root / batch_id
        if "/" in batch_id or batch_id.startswith(".") or not (d / "batch.json").is_file():
            raise KeyError(f"no batch {batch_id}")
        return d

    def batches(self):
        out = []
        if not self.root.is_dir():
            return out
        for d in sorted(p for p in self.root.iterdir() if (p / "batch.json").is_file()):
            try:
                meta = json.loads((d / "batch.json").read_text())
            except (OSError, ValueError) as e:
                meta = {"batchId": d.name, "loadError": str(e)}
            runs = []
            for p in sorted(d.glob("*.json")):
                if p.name != "batch.json":
                    runs.append(self.summary(p))
            out.append({
                "id": d.name,
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
        except Exception as e:  # a run still being written, or a record this code can't read
            s = {"runId": path.stem, "benchmark": path.stem.split(".")[0], "status": "unreadable",
                 "errorLine": f"{type(e).__name__}: {e}"}
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

    def trace(self, batch_id, run_id, kind=None, search=None, phase=None, offset=0, limit=100):
        """Counts over the whole trace, and the lines matching the filters from offset."""
        p = self.file_path(batch_id, f"{run_id}.trace.jsonl.gz")
        counts = {"kind": {}, "phase": {}, "search": {}}
        lines, matched = [], 0
        with gzip.open(p, "rt") as f:
            for raw in f:
                try:
                    t = json.loads(raw)
                except ValueError:
                    continue
                for k in counts:
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
    """analyze.row, plus what it leaves out. Times in seconds, like row."""
    r = analyze.row(record)
    r["runId"] = record.get("runId", r["benchmark"])
    if record.get("loadMs") is not None:
        r["load"] = record["loadMs"] / 1000
    if "matchesExpected" in record:
        r["matchesExpected"] = record["matchesExpected"]
    sols = record.get("solutions")
    if sols is not None:
        r["numSolutions"] = len(sols)
    mism = record.get("mismatches")
    if mism:
        r["mismatched"] = min(len(m) for m in mism)
    rounds = record.get("mismatchedRounds")
    if rounds:
        first = [x for rs in rounds for x in rs[:1]]
        if first:
            r["firstMismatchedRound"] = min(first)
    if record.get("error"):
        r["errorLine"] = str(record["error"]).strip().partition("\n")[0][:300]
    r["config"] = record.get("config")
    stats = record.get("stats") or {}
    for phase, vals in (stats.get("phases") or {}).items():
        for k, v in vals.items():
            if k != "ms" and isinstance(v, (int, float)):
                r[f"{phase}.{k}"] = v
    searches = stats.get("searches", stats.get("queries")) or []
    if searches:
        r["rounds"] = max(q.get("round", 0) for q in searches) + 1
        r["maxOuterDepth"] = max(q.get("outerDepth", 0) for q in searches)
    events = stats.get("events") or []
    r["events"] = len(events)
    schedule = (stats.get("info") or {}).get("schedule")
    if schedule is not None:
        r["scheduledRounds"] = len(schedule)
    return r
