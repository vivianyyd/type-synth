// Fetches from serve.py. Batches are fetched once (until reload); run records are kept in a
// small cache, since a record can be tens of MB.

let batchesPromise = null;
const runCache = new Map();
const RUN_CACHE_SIZE = 6;

async function getJSON(url) {
  const res = await fetch(url);
  if (!res.ok) throw new Error(`${url}: ${res.status} ${(await res.text()).slice(0, 500)}`);
  return res.json();
}

export function batches(force = false) {
  if (force || !batchesPromise) {
    if (force) runCache.clear();
    batchesPromise = getJSON("api/batches").then(index).catch((e) => { batchesPromise = null; throw e; });
  }
  return batchesPromise;
}

function index(data) {
  data.byId = new Map(data.batches.map((b) => [b.id, b]));
  data.batches.forEach((b, i) => { b.index = i; b.label = batchLabel(b); b.short = shortLabel(b); });
  data.allRuns = data.batches.flatMap((b) => b.runs);
  data.chains = chains(data.allRuns);
  // Step rows know their batch and run. A run that stopped before finishing a step gets a row for
  // that step too, with the run's status, so that a crash or a timeout shows where it happened.
  for (const b of data.batches) {
    for (const r of b.runs) {
      for (const s of r.steps) { s.batchId = b.id; s.multi = s.step !== s.parent; }
      r.pending = pendingStep(r, data.chains.get(r.benchmark));
      if (r.pending) r.pending.batchId = b.id;
    }
    b.steps = b.runs.flatMap((r) => (r.pending ? [...r.steps, r.pending] : r.steps));
  }
  data.allSteps = data.batches.flatMap((b) => b.steps);
  const rank = new Map();
  for (const s of data.allSteps) {
    const i = data.chains.get(s.parent)?.indexOf(s.step) ?? -1;
    if (!rank.has(s.benchmark)) rank.set(s.benchmark, [s.parent, i < 0 ? 1e6 : i]);
  }
  data.stepRank = rank;
  data.benchmarks = orderSteps(data, [...rank.keys()]);
  return data;
}

// Each benchmark's steps in order: the longest run of it, then any step only other runs have.
function chains(runs) {
  const out = new Map();
  const byBench = new Map();
  for (const r of runs) {
    if (!byBench.has(r.benchmark)) byBench.set(r.benchmark, []);
    byBench.get(r.benchmark).push(r.steps.map((s) => s.step));
  }
  for (const [bench, lists] of byBench) {
    lists.sort((a, b) => b.length - a.length);
    out.set(bench, [...new Set(lists.flat())]);
  }
  return out;
}

// The step a run was on when it stopped, if it stopped without recording it.
function pendingStep(r, chain = []) {
  if (r.steps.some((s) => s.status === r.status)) return null;
  const step = chain[r.steps.length] ?? (r.steps.length ? "(next)" : r.benchmark);
  const multi = step !== r.benchmark;
  return { pending: true, runId: r.runId, parent: r.benchmark, step, stepIndex: r.steps.length, multi, repeat: r.repeat,
    benchmark: multi ? `${r.benchmark}/${step}` : r.benchmark, status: r.status, errorLine: r.errorLine };
}

// Step names in chain order: by benchmark, then by place in the chain.
export function orderSteps(data, names) {
  const key = (n) => data.stepRank.get(n) || [n, 0];
  return [...names].sort((a, b) => {
    const [pa, ia] = key(a), [pb, ib] = key(b);
    return pa.localeCompare(pb, undefined, { numeric: true }) || ia - ib || a.localeCompare(b);
  });
}

export function batchLabel(b) {
  const m = b.meta, g = m.git || {};
  const when = (m.startedAt || b.id).replace("T", " ").slice(0, 16);
  return `${b.folder ? `${b.folder}/ ` : ""}${when} · ${(g.commit || "").slice(0, 8)}${g.dirty ? "+" : ""} · ${m.variant}${m.notes ? ` · ${m.notes}` : ""}`;
}

export function shortLabel(b) {
  const m = b.meta, g = m.git || {};
  const when = (m.startedAt || "").replace("T", " ").slice(5, 16);
  return `${when} ${(g.commit || "").slice(0, 7)}${g.dirty ? "+" : ""}${m.variant !== "default" ? ` ${m.variant}` : ""}`;
}

export async function run(batch, runId) {
  const key = `${batch}/${runId}`;
  if (!runCache.has(key)) {
    runCache.set(key, getJSON(`api/run?batch=${enc(batch)}&run=${enc(runId)}`).catch((e) => { runCache.delete(key); throw e; }));
    while (runCache.size > RUN_CACHE_SIZE) runCache.delete(runCache.keys().next().value);
  }
  return runCache.get(key);
}

export async function file(batch, name) {
  const res = await fetch(`api/file?batch=${enc(batch)}&name=${enc(name)}`);
  if (!res.ok) throw new Error(`${name}: ${res.status}`);
  return res.text();
}

export function trace(params) {
  return getJSON(`api/trace?${new URLSearchParams(params)}`);
}

const enc = encodeURIComponent;

// Step rows in chain order, repeats together.
export function sortSteps(data, rows) {
  const rank = new Map(orderSteps(data, [...new Set(rows.map((r) => r.benchmark))]).map((n, i) => [n, i]));
  return [...rows].sort((a, b) => rank.get(a.benchmark) - rank.get(b.benchmark) || (a.repeat || 0) - (b.repeat || 0));
}
