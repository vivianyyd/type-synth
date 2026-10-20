// One run, in tabs: overview, answer, searches, events, log, trace, raw JSON.
import { h, add, card, kv, dataTable, statusChip, select, checkbox, multiPicker, tabs, loading, errorBox, jsonTree, download, clear } from "../ui.js";
import { href, setParams } from "../router.js";
import * as M from "../metrics.js";
import * as api from "../api.js";
import { plot, plotDiv, whenReady, SERIES } from "../charts.js";

const PHASES = ["outline", "arity", "concretize", "cegis"];
const KNOWN = new Set(["schema", "runId", "benchmark", "repeat", "config", "loadMs", "status", "matchesExpected", "solutions",
  "expected", "mismatches", "mismatchedRounds", "stats", "batch", "error"]);

export default {
  id: "run", title: "Run", nav: false,
  async render(el, { path, params, data }) {
    const [batchId, runId] = path;
    const b = data.byId.get(batchId);
    const summary = b?.runs.find((r) => r.runId === runId);
    if (!summary) { add(el, h("p", {}, `No run ${runId} in ${batchId}.`)); return; }
    const files = new Set(b.files.map((f) => f.name));
    const hasLog = files.has(`${runId}.log`), hasTrace = files.has(`${runId}.trace.jsonl.gz`);

    // Header: where this run is, and the same run in other batches
    const idx = b.runs.indexOf(summary), prev = b.runs[idx - 1], next = b.runs[idx + 1];
    const others = data.batches.filter((x) => x.runs.some((r) => r.runId === runId));
    add(el, 
      h("div", { class: "row" }, h("h1", {}, runId), statusChip(summary.status), h("a", { href: href("batch", [b.id]) }, b.label),
        h("span", { class: "spacer" }),
        prev ? h("a", { href: href("run", [b.id, prev.runId], { tab: params.tab }) }, `‹ ${prev.runId}`) : null,
        next ? h("a", { href: href("run", [b.id, next.runId], { tab: params.tab }) }, `${next.runId} ›`) : null),
      h("div", { class: "row small" }, "Same run in batch:",
        select(others.map((x) => [x.id, x.label]), b.id, (id) => { location.hash = href("run", [id, runId], { tab: params.tab }); }),
        h("a", { href: href("history", [], { bench: summary.benchmark }) }, "history of this benchmark")));

    const body = h("div", {}, loading(summary.bytes > 2e6 ? `Loading ${M.fmtBytes(summary.bytes)} record…` : "Loading…"));
    add(el, body);
    let rec;
    try { rec = await api.run(b.id, runId); } catch (e) { body.replaceChildren(errorBox(e)); return; }

    const stats = rec.stats || {};
    const searches = stats.searches || stats.queries || [];
    const events = stats.events || [];
    const items = [
      { id: "overview", label: "Overview" },
      { id: "answer", label: `Answer${rec.solutions ? ` (${rec.solutions.length})` : ""}` },
      { id: "searches", label: `Searches (${searches.length})` },
      { id: "events", label: `Events (${events.length})` },
      hasLog ? { id: "log", label: "Log" } : null,
      hasTrace ? { id: "trace", label: "Trace" } : null,
      { id: "raw", label: "Raw JSON" },
    ].filter(Boolean);
    let tab = items.some((t) => t.id === params.tab) ? params.tab : "overview";
    const pane = h("div", { class: "stack" });
    const draw = () => {
      body.replaceChildren(tabs(items, tab, (t) => { tab = t; setParams({ tab: t }); draw(); }), pane);
      clear(pane);
      ({ overview, answer, searches: searchesTab, events: eventsTab, log, trace, raw })[tab](pane, { rec, b, runId, searches, events, params });
    };
    draw();
  },
};

function overview(el, { rec }) {
  const stats = rec.stats || {};
  const c = stats.counters || {};
  const extra = Object.fromEntries(Object.entries(rec).filter(([k]) => !KNOWN.has(k)));
  add(el, h("div", { class: "grid" },
    card("Result", kv([["status", statusChip(rec.status)], ["matches expected", rec.matchesExpected == null ? undefined : rec.matchesExpected ? "yes" : "no"],
      ["wall (s)", stats.wallMs != null ? M.fmt("wall", stats.wallMs / 1000) : undefined], ["load (s)", rec.loadMs != null ? M.fmt("load", rec.loadMs / 1000) : undefined],
      ["not in a phase (s)", stats.unattributedMs != null ? M.fmt("wall", stats.unattributedMs / 1000) : undefined],
      ["searches", (stats.searches || stats.queries || []).length], ["events", (stats.events || []).length], ["repeat", rec.repeat], ["schema", rec.schema]])),
    card("Configuration", configView(rec.config)),
    card("Counters", kv(Object.entries(c).map(([k, v]) => [M.label(k), k === "solverMs" ? `${M.fmt("wall", v / 1000)} s` : M.fmt(k, v)]))),
  ));
  if (rec.error) add(el, card("Error", h("pre", { class: "error" }, rec.error)));
  if (Object.keys(extra).length) add(el, card("Other fields", jsonTree(extra, "fields")));

  // Phases: one row per phase, a column per count, and a chart of where time went
  const phases = stats.phases || {};
  const keys = [...new Set(Object.values(phases).flatMap((p) => Object.keys(p)))].filter((k) => k !== "ms");
  const rows = Object.entries(phases).map(([p, v]) => ({ phase: p, ...v, s: v.ms / 1000 }));
  if (stats.unattributedMs != null) rows.push({ phase: "(not in a phase)", s: stats.unattributedMs / 1000 });
  const total = rows.reduce((s, r) => s + (r.s || 0), 0);
  const pie = plotDiv(300);
  add(el, h("div", { class: "grid" },
    card("Phases", dataTable({ columns: [{ key: "phase" }, { key: "s", label: "time (s)", num: true, fmt: (v) => M.fmt("wall", v) },
      { key: "pct", label: "% of time", num: true, get: (r) => (total ? (100 * r.s) / total : null), fmt: (v) => (v == null ? "–" : v.toFixed(1)) },
      ...keys.map((k) => ({ key: k, label: M.label(k), num: true, fmt: (v) => M.fmt(k, v) }))], rows })),
    card("Where time went", pie)));
  whenReady(() => plot(pie, [{ type: "pie", labels: rows.map((r) => r.phase), values: rows.map((r) => r.s), hole: 0.45, sort: false,
    textinfo: "label+percent", hovertemplate: "%{label}: %{value:.3f}s<extra></extra>" }], { showlegend: false, margin: { l: 10, r: 10, t: 10, b: 10 } }));

  // Schedule: the rounds the engine decided on
  const schedule = stats.info?.schedule;
  if (schedule) add(el, card(`Schedule (${schedule.length} rounds)`, dataTable({
    columns: [{ key: "round", num: true }, { key: "n", label: "names", num: true }, { key: "names", label: "", wrap: true }],
    rows: schedule.map((names, i) => ({ round: i, n: names.length, names: names.join("  ") })), pageSize: 200 })));
  const info = Object.fromEntries(Object.entries(stats.info || {}).filter(([k]) => k !== "schedule"));
  if (Object.keys(info).length) add(el, card("Notes recorded by the run", jsonTree(info, "info")));
}

function configView(cfg) {
  if (!cfg) return h("span", { class: "muted" }, "none");
  return kv(Object.entries(cfg).map(([k, v]) => [k, v && typeof v === "object" ? Object.entries(v).map(([a, b]) => `${a}=${JSON.stringify(b)}`).join(", ") : String(v)]));
}

function answer(el, { rec }) {
  const sols = rec.solutions || [];
  const expected = rec.expected || {};
  if (!sols.length) {
    add(el, card("No solutions", h("p", { class: "muted" }, `Status ${rec.status}.`)));
    if (Object.keys(expected).length) add(el, card("Expected", typesTable(Object.keys(expected).map((n) => ({ name: n, expected: expected[n] })), false)));
    return;
  }
  let only = false;
  const box = h("div", { class: "stack" });
  const draw = () => {
    clear(box);
    sols.forEach((sol, i) => {
      const differs = new Set((rec.mismatches || [])[i] || []);
      const rounds = (rec.mismatchedRounds || [])[i];
      const names = [...new Set([...Object.keys(sol), ...Object.keys(expected)])];
      const rows = names.map((n) => ({ name: n, returned: sol[n], expected: expected[n], differs: differs.has(n) || !(n in sol) }))
        .filter((r) => !only || r.differs);
      box.append(card(h("span", { class: "row" }, sols.length > 1 ? `Solution ${i + 1}` : "Solution",
        h("span", { class: "muted small" }, `${differs.size} of ${Object.keys(sol).length} names differ from expected`),
        rounds && rounds.length ? h("span", { class: "small" }, `mismatched rounds: ${rounds.join(", ")} (first is where it went wrong)`) : null),
        typesTable(rows, true)));
    });
  };
  add(el, h("div", { class: "row", style: { marginBottom: "8px" } }, checkbox("only names that differ", only, (on) => { only = on; draw(); })), box);
  draw();
}

function typesTable(rows, withReturned) {
  return dataTable({ rows, pageSize: 1000, filter: rows.length > 20, rowClass: (r) => (r.differs ? "mismatch" : ""), columns: [
    ...(withReturned ? [{ key: "differs", label: "", fmt: (v) => (v ? h("span", { class: "diff-mark", title: "differs from expected" }, "≠") : "") }] : []),
    { key: "name", fmt: (v) => h("code", {}, v) },
    ...(withReturned ? [{ key: "returned", fmt: (v) => (v == null ? h("span", { class: "muted" }, "missing") : h("code", {}, v)) }] : []),
    { key: "expected", fmt: (v) => (v == null ? "–" : h("code", {}, v)) },
  ] });
}

// Flattens a search to one row: its fields, time per phase, and each count per phase and in total.
function searchRow(q) {
  const r = { id: q.id, round: q.round, outerDepth: q.outerDepth, names: (q.names || []).join(" "), numNames: (q.names || []).length,
    numPos: q.numPos, numNeg: q.numNeg, s: q.ms / 1000 };
  for (const [p, v] of Object.entries(q.phases || {})) {
    for (const [k, x] of Object.entries(v)) {
      if (k === "ms") r[`${p} (s)`] = x / 1000;
      else { r[`${p}.${k}`] = x; r[k] = (r[k] || 0) + x; }
    }
  }
  return r;
}

function searchesTab(el, { searches }) {
  if (!searches.length) { add(el, h("p", { class: "muted" }, "No searches recorded.")); return; }
  const rows = searches.map(searchRow);
  const keys = [...new Set(rows.flatMap((r) => Object.keys(r)))];
  const fixed = ["id", "round", "outerDepth", "numNames", "numPos", "numNeg", "s"];
  const phaseTimes = PHASES.map((p) => `${p} (s)`).filter((k) => keys.includes(k));
  const totals = keys.filter((k) => !fixed.includes(k) && k !== "names" && !k.includes(".") && !k.endsWith("(s)"));
  const perPhase = keys.filter((k) => k.includes("."));
  const numeric = [...fixed, ...phaseTimes, ...totals, ...perPhase];
  const label = (k) => ({ s: "time (s)", numNames: "names", numPos: "+ examples", numNeg: "− examples", outerDepth: "outer depth" })[k] || M.label(k);
  const colKey = "bench.searchCols";
  let shown;
  try { shown = JSON.parse(localStorage.getItem(colKey)); } catch {}
  if (!Array.isArray(shown)) shown = [...fixed, ...phaseTimes, ...totals];

  // Per round: time stacked by phase
  const byRound = new Map();
  for (const r of rows) {
    const g = byRound.get(r.round) || { round: r.round, searches: 0, s: 0 };
    g.searches++; g.s += r.s;
    for (const p of phaseTimes) g[p] = (g[p] || 0) + (r[p] || 0);
    for (const t of totals) g[t] = (g[t] || 0) + (r[t] || 0);
    byRound.set(r.round, g);
  }
  const rounds = [...byRound.values()].sort((a, b) => a.round - b.round);
  const roundDiv = plotDiv(340), scatterDiv = plotDiv(380);
  let y = "s", x = "id", logY = false;
  const drawScatter = () => {
    const groups = new Map();
    for (const r of rows) { if (!groups.has(r.round)) groups.set(r.round, []); groups.get(r.round).push(r); }
    plot(scatterDiv, [...groups].map(([round, rs], i) => ({
      type: rows.length > 2000 ? "scattergl" : "scatter", mode: "markers", name: `round ${round}`, x: rs.map((r) => r[x]), y: rs.map((r) => r[y] ?? null),
      marker: { size: 5, color: SERIES[i % SERIES.length] }, text: rs.map((r) => `search ${r.id}, outer depth ${r.outerDepth}<br>${r.names}`),
      hovertemplate: `%{text}<br>${label(x)}: %{x}<br>${label(y)}: %{y}<extra></extra>`,
    })), { showlegend: groups.size <= 30, xaxis: { title: label(x) }, yaxis: { title: label(y), type: logY ? "log" : "linear" } });
  };
  add(el, h("div", { class: "grid" },
    card("Time per round, by phase", roundDiv),
    card(h("span", { class: "row" }, "Each search:", select(numeric.map((k) => [k, label(k)]), y, (v) => { y = v; drawScatter(); }), "against",
      select(numeric.map((k) => [k, label(k)]), x, (v) => { x = v; drawScatter(); }), checkbox("log", logY, (on) => { logY = on; drawScatter(); })), scatterDiv)));
  whenReady(() => {
    plot(roundDiv, phaseTimes.map((p) => ({ type: "bar", name: p.replace(" (s)", ""), x: rounds.map((r) => r.round), y: rounds.map((r) => r[p]),
      hovertemplate: `round %{x}<br>${p}: %{y:.3f}<extra></extra>` })), { barmode: "stack", xaxis: { title: "round", dtick: 1 }, yaxis: { title: "seconds" } });
    drawScatter();
  });

  add(el, card(`Rounds (${rounds.length})`, dataTable({ rows: rounds, pageSize: 100, columns: [
    { key: "round", num: true }, { key: "searches", num: true }, { key: "s", label: "time (s)", num: true, fmt: (v) => M.fmt("wall", v) },
    ...phaseTimes.map((p) => ({ key: p, num: true, fmt: (v) => M.fmt("wall", v) })), ...totals.map((t) => ({ key: t, label: M.label(t), num: true, fmt: (v) => M.fmt(t, v) }))] })));

  const tableBox = h("div", {});
  const drawTable = () => tableBox.replaceChildren(dataTable({ rows, pageSize: 100, filter: true, columns: [
    ...shown.filter((k) => numeric.includes(k)).map((k) => ({ key: k, label: label(k), num: true, fmt: (v) => (k.endsWith("(s)") || k === "s" ? M.fmt("wall", v) : M.fmt(k, v)) })),
    { key: "names", wrap: true, fmt: (v) => h("code", {}, v) }] }));
  add(el, card(h("span", { class: "row" }, `Searches (${rows.length})`, columnPicker(numeric, shown, label, (v) => {
    shown = v; try { localStorage.setItem(colKey, JSON.stringify(v)); } catch {} drawTable(); }),
    h("button", { onclick: () => download("searches.csv", toCSV(rows, [...numeric, "names"]), "text/csv") }, "CSV")), tableBox));
  drawTable();
}

function columnPicker(keys, shown, label, onChange) {
  return multiPicker({ label: "Columns", selected: shown, onChange, options: keys.map((k) => ({ value: k, label: label(k),
    group: k.includes(".") ? "per phase" : k.endsWith("(s)") ? "time per phase" : undefined })) });
}

function toCSV(rows, keys) {
  const q = (v) => (v == null ? "" : /[",\n]/.test(String(v)) ? `"${String(v).replace(/"/g, '""')}"` : String(v));
  return [keys.join(","), ...rows.map((r) => keys.map((k) => q(r[k])).join(","))].join("\n");
}

function eventsTab(el, { events, searches }) {
  if (!events.length) { add(el, h("p", { class: "muted" }, "No events recorded.")); return; }
  const roundOf = new Map(searches.map((q) => [q.id, q.round]));
  const rows = events.map((e, i) => ({ i, ...e, s: e.ms != null ? e.ms / 1000 : null, round: roundOf.get(e.search ?? e.query) }));
  const keys = [...new Set(rows.flatMap((r) => Object.keys(r)))].filter((k) => k !== "ms");
  const numeric = keys.filter((k) => rows.some((r) => typeof r[k] === "number"));
  const kinds = [...new Set(rows.map((r) => r.kind))];
  const div = plotDiv(380);
  let y = numeric.includes("size") ? "size" : numeric[0];
  const lab = (k) => (k === "s" ? "time into run (s)" : k === "i" ? "event #" : k);
  const draw = () => plot(div, kinds.map((kind, j) => {
    const rs = rows.filter((r) => r.kind === kind);
    return { type: rs.length > 2000 ? "scattergl" : "scatter", mode: "markers", name: kind, x: rs.map((r) => r.s ?? r.i), y: rs.map((r) => r[y]),
      marker: { size: 5, color: SERIES[j % SERIES.length] }, text: rs.map((r) => JSON.stringify(Object.fromEntries(Object.entries(r).filter(([k]) => k !== "kind")))),
      hovertemplate: "%{text}<extra></extra>" };
  }), { xaxis: { title: lab("s") }, yaxis: { title: lab(y) } });
  add(el, card(h("span", { class: "row" }, "Events over time:", select(numeric.map((k) => [k, lab(k)]), y, (v) => { y = v; draw(); }),
    h("span", { class: "muted small" }, kinds.map((k) => `${k}: ${rows.filter((r) => r.kind === k).length}`).join(" · "))), div));
  whenReady(draw);
  add(el, card(h("span", { class: "row" }, "Events", h("button", { onclick: () => download("events.csv", toCSV(rows, keys), "text/csv") }, "CSV")),
    dataTable({ rows, pageSize: 100, filter: true, columns: keys.map((k) => ({ key: k, label: lab(k), num: numeric.includes(k), fmt: (v) => (k === "s" ? M.fmt("wall", v) : M.fmt(k, v)) })) })));
}

async function log(el, { b, runId }) {
  add(el, loading());
  try {
    const text = await api.file(b.id, `${runId}.log`);
    el.replaceChildren(h("div", { class: "row small muted", style: { marginBottom: "6px" } }, `${text.split("\n").length} lines`), h("pre", {}, text));
  } catch (e) { el.replaceChildren(errorBox(e)); }
}

function trace(el, { b, runId }) {
  const f = { kind: "", phase: "", search: "", offset: 0, limit: 100 };
  const box = h("div", { class: "stack" });
  const load = async () => {
    box.replaceChildren(loading("Reading trace…"));
    try {
      const t = await api.trace({ batch: b.id, run: runId, ...f });
      const countTable = (name) => dataTable({ pageSize: 50, sortKey: "n", sortDesc: true, rows: Object.entries(t.counts[name]).map(([v, n]) => ({ v, n })),
        columns: [{ key: "v", label: name }, { key: "n", label: "lines", num: true, fmt: (v) => M.fmt("n", v) }] });
      const sel = (name) => select([["", `any ${name}`], ...Object.keys(t.counts[name]).sort().map((v) => [v, v])], f[name], (v) => { f[name] = v; f.offset = 0; load(); });
      box.replaceChildren(
        h("div", { class: "grid" }, card("By kind", countTable("kind")), card("By phase", countTable("phase")), card("By search", countTable("search"))),
        card(h("span", { class: "row" }, "Lines", sel("kind"), sel("phase"), sel("search"),
          h("button", { disabled: f.offset === 0, onclick: () => { f.offset = Math.max(0, f.offset - f.limit); load(); } }, "‹"),
          h("span", { class: "small muted" }, `${t.matched ? f.offset + 1 : 0}–${f.offset + t.lines.length} of ${t.matched}`),
          h("button", { disabled: f.offset + f.limit >= t.matched, onclick: () => { f.offset += f.limit; load(); } }, "›")),
          dataTable({ rows: t.lines.map((l, i) => ({ n: f.offset + i, ...l })), pageSize: f.limit, columns: [
            { key: "n", label: "#", num: true }, { key: "search", num: true }, { key: "phase" }, { key: "kind" },
            { key: "state", wrap: true, fmt: (v) => h("code", {}, typeof v === "string" ? v : JSON.stringify(v)) }] })));
    } catch (e) { box.replaceChildren(errorBox(e)); }
  };
  add(el, box);
  load();
}

function raw(el, { rec, b, runId }) {
  add(el, h("div", { class: "row", style: { marginBottom: "8px" } },
    h("a", { href: `api/run?batch=${encodeURIComponent(b.id)}&run=${encodeURIComponent(runId)}`, target: "_blank" }, "open the file"),
    h("span", { class: "muted small" }, "Expand to explore; long arrays open in chunks of 100.")),
    card(null, jsonTree(rec, runId)));
}
