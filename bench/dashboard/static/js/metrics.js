// What a metric is called, how to show it, and arithmetic over runs.

let LABELS = {};
let TIMES = new Set();

export function init(data) {
  LABELS = { ...data.metrics, load: "load (s)", runId: "run", numSolutions: "solutions found", mismatched: "names wrong",
    firstMismatchedRound: "first wrong round", rounds: "rounds searched", maxOuterDepth: "max outer depth",
    events: "events", scheduledRounds: "scheduled rounds", bytes: "record size", matchesExpected: "matches expected" };
  TIMES = new Set(data.times);
}

export const isTime = (m) => TIMES.has(m);
export const label = (m) => LABELS[m] || m;

// Columns that are about the run's identity rather than measurements.
const IDENTITY = new Set(["benchmark", "repeat", "variant", "commit", "batch", "runId", "config", "errorLine", "stop"]);

export function fmt(m, v) {
  if (v == null) return "–";
  if (typeof v === "number") {
    if (isTime(m)) return v.toFixed(v < 10 ? 3 : 2);
    if (m === "bytes") return fmtBytes(v);
    if (!Number.isInteger(v)) return v.toPrecision(4);
    return v.toLocaleString("en-US");
  }
  if (typeof v === "boolean") return v ? "yes" : "no";
  if (typeof v === "object") return JSON.stringify(v);
  return String(v);
}

export function fmtBytes(n) {
  return n > 1e6 ? `${(n / 1e6).toFixed(1)} MB` : n > 1e3 ? `${(n / 1e3).toFixed(1)} kB` : `${n} B`;
}

// Every numeric metric in rows: times first, then analyze.py's order, then the rest by name.
export function numericMetrics(rows) {
  const seen = new Set();
  for (const r of rows) for (const [k, v] of Object.entries(r)) if (typeof v === "number" && !IDENTITY.has(k)) seen.add(k);
  const order = [...TIMES, ...Object.keys(LABELS)];
  const rank = (k) => { const i = order.indexOf(k); return i < 0 ? 1e6 : i; };
  return [...seen].sort((a, b) => rank(a) - rank(b) || (a.includes(".") - b.includes(".")) || a.localeCompare(b));
}

// Groups for pickers: times, counters, per-phase counters, other.
export function metricOptions(rows, { includeStatus = false } = {}) {
  const ms = numericMetrics(rows);
  const opts = includeStatus ? [{ value: "status", label: "status", group: "result" }, { value: "stop", label: "stopped at", group: "result" }] : [];
  for (const m of ms) opts.push({ value: m, label: label(m), group: isTime(m) ? "times (s)" : m.includes(".") ? "per phase" : "counts" });
  return opts;
}

const median = (xs) => {
  const s = [...xs].sort((a, b) => a - b), n = s.length;
  return n % 2 ? s[(n - 1) / 2] : (s[n / 2 - 1] + s[n / 2]) / 2;
};

// Folds repeats into one row per benchmark, as analyze.by_benchmark does: median times, counts
// from the first repeat, joined statuses if repeats disagree.
export function byBenchmark(runs) {
  const groups = new Map();
  for (const r of runs) {
    if (!groups.has(r.benchmark)) groups.set(r.benchmark, []);
    groups.get(r.benchmark).push(r);
  }
  const out = new Map();
  for (const [name, g] of groups) {
    g.sort((a, b) => (a.repeat || 0) - (b.repeat || 0));
    const m = { ...g[0], repeats: g.length, runIds: g.map((r) => r.runId) };
    for (const t of TIMES) {
      const vals = g.map((r) => r[t]).filter((v) => typeof v === "number");
      if (vals.length) m[t] = median(vals);
    }
    const st = [...new Set(g.map((r) => r.status))].sort();
    if (st.length > 1) m.status = st.join("/");
    out.set(name, m);
  }
  return out;
}

export function ratio(a, b) {
  return typeof a === "number" && typeof b === "number" && a > 0 && b > 0 ? b / a : null;
}

export function geomean(xs) {
  return xs.length ? Math.exp(xs.reduce((s, x) => s + Math.log(x), 0) / xs.length) : null;
}

export const isGood = (status) => status === "correct" || status === "solved";

// For metrics where smaller is better (all of them so far), < 1 is an improvement.
export function ratioClass(r) {
  if (r == null) return "";
  return r < 0.95 ? "ratio-better" : r > 1.05 ? "ratio-worse" : "";
}
