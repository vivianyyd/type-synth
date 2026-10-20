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
  data.benchmarks = [...new Set(data.batches.flatMap((b) => b.runs.map((r) => r.benchmark)))].sort();
  data.allRuns = data.batches.flatMap((b) => b.runs);
  return data;
}

export function batchLabel(b) {
  const m = b.meta, g = m.git || {};
  const when = (m.startedAt || b.id).replace("T", " ").slice(0, 16);
  return `${when} · ${(g.commit || "").slice(0, 8)}${g.dirty ? "+" : ""} · ${m.variant}${m.notes ? ` · ${m.notes}` : ""}`;
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
