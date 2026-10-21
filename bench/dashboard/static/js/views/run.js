// One run: its steps in order, then tabs. Chain is about every step; overview, answer, searches and
// events are about the chosen step; log, trace and raw JSON are about the run.
import { h, add, card, kv, dataTable, statusChip, select, checkbox, multiPicker, tabs, loading, errorBox, jsonTree, download, clear } from "../ui.js";
import { href, setParams } from "../router.js";
import * as M from "../metrics.js";
import * as api from "../api.js";
import { plot, plotDiv, whenReady, series, phaseColor, barLine, statusColor } from "../charts.js";
import { strip, meter } from "../steps.js";

const PHASES = ["outline", "arity", "concretize", "cegis"];
const STEP_TABS = new Set(["overview", "answer", "searches", "events"]);
// A step's fields that have a place of their own on the page
const KNOWN = new Set(["step", "status", "loadMs", "names", "solutions", "expected", "scores", "stats", "error"]);

export default {
  id: "run", title: "Run", nav: false,
  async render(el, { path, params, data }) {
    const [batchId, runId] = path;
    const b = data.byId.get(batchId);
    const summary = b?.runs.find((r) => r.runId === runId);
    if (!summary) { add(el, h("p", {}, `No run ${runId} in ${batchId}.`)); return; }
    const files = new Set(b.files.map((f) => f.name));
    const hasLog = files.has(`${runId}.log`), hasTrace = files.has(`${runId}.trace.jsonl.gz`);
    const chain = data.chains.get(summary.benchmark) || [];
    const multi = chain.length > 1 || summary.steps.some((s) => s.multi);
    const all = summary.pending ? [...summary.steps, summary.pending] : summary.steps;
    // Without a choice, the first step that went wrong, or else the last
    let stepName = all.some((s) => s.step === params.step) ? params.step
      : (all.find((s) => !M.isGood(s.status)) || all[all.length - 1])?.step;

    // Header: where this run is, and the same run in other batches
    const idx = b.runs.indexOf(summary), prev = b.runs[idx - 1], next = b.runs[idx + 1];
    const others = data.batches.filter((x) => x.runs.some((r) => r.runId === runId));
    add(el,
      h("div", { class: "row" }, h("h1", {}, runId), statusChip(summary.status), h("a", { href: href("batch", [b.id]) }, b.label),
        h("span", { class: "spacer" }),
        prev ? h("a", { href: href("run", [b.id, prev.runId]) }, `‹ ${prev.runId}`) : null,
        next ? h("a", { href: href("run", [b.id, next.runId]) }, `${next.runId} ›`) : null),
      h("div", { class: "row small" }, "Same run in batch:",
        select(others.map((x) => [x.id, x.label]), b.id, (id) => { location.hash = href("run", [id, runId], { step: params.step, tab: params.tab }); }),
        h("a", { href: href("history", [], { bench: multi ? all.map((s) => s.benchmark) : [summary.benchmark] }) }, "history of this benchmark")));

    const stripBox = h("div", {});
    const body = h("div", {}, loading(summary.bytes > 2e6 ? `Loading ${M.fmtBytes(summary.bytes)} record…` : "Loading…"));
    add(el, stripBox, body);
    let rec;
    try { rec = await api.run(b.id, runId); } catch (e) { body.replaceChildren(errorBox(e)); return; }
    const recSteps = rec.steps;
    const stepOf = (name) => recSteps.find((s) => s.step === name) || null;

    let tab = params.tab;
    if (!(tab === "chain" ? multi : tab === "log" ? hasLog : tab === "trace" ? hasTrace : STEP_TABS.has(tab) || tab === "raw"))
      tab = multi && !params.step ? "chain" : "overview";
    const pane = h("div", { class: "stack" });
    const draw = () => {
      const step = stepOf(stepName);
      const row = all.find((s) => s.step === stepName);
      const stats = step?.stats || {};
      const ctx = { rec, recSteps, step, row, all, b, runId, multi, stepName, searches: stats.searches || [],
        events: stats.events || [], params, select: (name, t) => { stepName = name; tab = t; setParams({ step: name, tab: t }); draw(); } };
      if (multi) stripBox.replaceChildren(strip(summary, chain, { selected: tab === "chain" ? null : stepName,
        linkFor: (s) => href("run", [b.id, runId], { step: s.step, tab: STEP_TABS.has(tab) ? tab : "overview" }) }));
      const of = multi ? ` · ${stepName}` : "";
      const items = [
        multi ? { id: "chain", label: `Chain (${all.length} step${all.length === 1 ? "" : "s"})` } : null,
        { id: "overview", label: `Overview${of}` },
        { id: "answer", label: `Answer${step?.solutions ? ` (${step.solutions.length})` : ""}` },
        { id: "searches", label: `Searches (${ctx.searches.length})` },
        { id: "events", label: `Events (${ctx.events.length})` },
        hasLog ? { id: "log", label: "Log" } : null,
        hasTrace ? { id: "trace", label: "Trace" } : null,
        { id: "raw", label: "Raw JSON" },
      ].filter(Boolean);
      body.replaceChildren(...[
        rec.error ? card(h("span", { class: "row" }, "Run stopped", statusChip(rec.status)), h("pre", { class: "error" }, rec.error)) : null,
        tabs(items, tab, (t) => { tab = t; setParams({ tab: t }); draw(); }), pane].filter(Boolean));
      clear(pane);
      if (STEP_TABS.has(tab) && !step) { unfinished(pane, ctx); return; }
      ({ chain: chainTab, overview, answer, searches: searchesTab, events: eventsTab, log, trace, raw })[tab](pane, ctx);
    };
    draw();
  },
};

// A step the run stopped during, so it has no record of its own
function unfinished(el, { row, rec }) {
  add(el, card(h("span", { class: "row" }, `Step ${row?.step ?? ""} didn't finish`, statusChip(row?.status || rec.status)),
    h("p", { class: "muted" }, "The run stopped during this step, so only the steps before it were recorded."),
    rec.error ? h("pre", { class: "error" }, rec.error) : null));
}

// -----------------------------------------------------------------------------------------------
// Every step

function chainTab(el, { all, select: choose }) {
  const ran = all.filter((s) => !s.pending);
  const cols = ["exact", "cost", "expectedSize", "diff", "wall", "load", "searches", "candidates", "solverCalls"];
  add(el, card("Steps, in the order they ran", dataTable({ rows: all, pageSize: 100, onRowClick: (r) => choose(r.step, "overview"),
    columns: [
      { key: "stepIndex", label: "#", num: true, fmt: (v) => v + 1 },
      { key: "step", fmt: (v) => h("a", { href: "javascript:void 0" }, h("code", {}, v)) },
      { key: "status", fmt: (v, r) => h("span", {}, statusChip(v), r.pending ? h("span", { class: "muted small" }, " stopped here") : null) },
      ...cols.map((c) => c === "exact"
        ? { key: c, label: M.label("exactNames"), sortValue: (r) => r.exactFrac, fmt: (v, r) => (r.names ? h("span", {}, meter(r, "inline"), v) : "–") }
        : { key: c, label: M.label(c), num: true, fmt: (v) => M.fmt(c, v) }),
      { key: "stop", label: M.label("stop"), wrap: true },
    ] })));
  if (!ran.length) return;

  // Where the time went, and how many names each step got right
  const x = ran.map((s) => s.step);
  const timeDiv = plotDiv(340), namesDiv = plotDiv(340);
  const scored = ran.filter((s) => s.names);
  add(el, h("div", { class: "grid" },
    card(h("span", {}, "Time per step, by phase ", h("span", { class: "muted small" }, "searching only; loading is in the table")), timeDiv),
    scored.length ? card(h("span", {}, "Names per step ", h("span", { class: "muted small" }, "exact, or not, in the closest solution")), namesDiv) : null));
  whenReady(() => {
    plot(timeDiv, [...PHASES, "unattributed"].map((p) => ({
      type: "bar", name: p === "unattributed" ? "not in a phase" : p, x, y: ran.map((s) => s[p] ?? 0),
      marker: { color: phaseColor(p), line: barLine() }, hovertemplate: `%{x}<br>${p}: %{y:.3f}s<extra></extra>`,
    })), { barmode: "stack", xaxis: { type: "category" }, yaxis: { title: "seconds" } });
    if (scored.length) plot(namesDiv, [
      { type: "bar", name: "exact", x: scored.map((s) => s.step), y: scored.map((s) => s.exactNames), marker: { color: statusColor("correct"), line: barLine() },
        hovertemplate: "%{x}<br>%{y} names exact<extra></extra>" },
      { type: "bar", name: "not exact", x: scored.map((s) => s.step), y: scored.map((s) => s.names - s.exactNames), marker: { color: statusColor("wrong"), line: barLine() },
        customdata: scored.map((s) => s.cost), hovertemplate: "%{x}<br>%{y} names not exact, cost %{customdata}<extra></extra>" },
    ], { barmode: "stack", xaxis: { type: "category" }, yaxis: { title: "names" } });
  });
}

// -----------------------------------------------------------------------------------------------
// The chosen step

function overview(el, { rec, step, row }) {
  const stats = step.stats || {};
  const c = stats.counters || {};
  const extra = Object.fromEntries(Object.entries(step).filter(([k]) => !KNOWN.has(k)));
  add(el, h("div", { class: "grid" },
    card("Result", kv([["status", statusChip(step.status)],
      ["names exact", row?.names ? h("span", { class: "row", style: { gap: "6px" } }, meter(row, "inline"), row.exact) : undefined],
      ["cost", row?.names ? `${row.cost} of ${row.expectedSize} expected nodes (${M.fmt("diff", row.diff)})` : undefined],
      ["wall (s)", stats.wallMs != null ? M.fmt("wall", stats.wallMs / 1000) : undefined], ["load (s)", step.loadMs != null ? M.fmt("load", step.loadMs / 1000) : undefined],
      ["not in a phase (s)", stats.unattributedMs != null ? M.fmt("wall", stats.unattributedMs / 1000) : undefined],
      ["searches", (stats.searches || []).length], ["events", (stats.events || []).length],
      ["stopped at", row?.stop], ["repeat", rec.repeat], ["schema", rec.schema]])),
    card("Configuration", configView(rec.config)),
    card("Counters", Object.keys(c).length ? kv(Object.entries(c).map(([k, v]) => [M.label(k), k === "solverMs" ? `${M.fmt("wall", v / 1000)} s` : M.fmt(k, v)]))
      : h("span", { class: "muted" }, "none: the search didn't start")),
  ));
  if (step.error) add(el, card("Error", h("pre", { class: "error" }, step.error)));
  if (Object.keys(extra).length) add(el, card("Other fields", jsonTree(extra, "fields")));
  if (!stats.phases) return;

  // Phases: one row per phase, a column per count, and a chart of where time went
  const phases = stats.phases || {};
  const keys = [...new Set(Object.values(phases).flatMap((p) => Object.keys(p)))].filter((k) => k !== "ms");
  const rows = Object.entries(phases).map(([p, v]) => ({ phase: p, key: p, ...v, s: v.ms / 1000 }));
  if (stats.unattributedMs != null) rows.push({ phase: "(not in a phase)", key: "unattributed", s: stats.unattributedMs / 1000 });
  const total = rows.reduce((s, r) => s + (r.s || 0), 0);
  const pie = plotDiv(300);
  add(el, h("div", { class: "grid" },
    card("Phases", dataTable({ columns: [{ key: "phase" }, { key: "s", label: "time (s)", num: true, fmt: (v) => M.fmt("wall", v) },
      { key: "pct", label: "% of time", num: true, get: (r) => (total ? (100 * r.s) / total : null), fmt: (v) => (v == null ? "–" : v.toFixed(1)) },
      ...keys.map((k) => ({ key: k, label: M.label(k), num: true, fmt: (v) => M.fmt(k, v) }))], rows })),
    card("Where time went", pie)));
  whenReady(() => plot(pie, [{ type: "pie", labels: rows.map((r) => r.phase), values: rows.map((r) => r.s), hole: 0.5, sort: false,
    marker: { colors: rows.map((r) => phaseColor(r.key)), line: barLine() },
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

// The types of one solution of a step against the expected ones, as rows.
function typeRows(step, i, stepName) {
  const sol = step.solutions[i] || {};
  const expected = step.expected || {};
  const byName = step.scores?.[i]?.byName;
  return [...new Set([...Object.keys(sol), ...Object.keys(expected)])].map((n) => ({
    name: n, step: stepName, returned: sol[n], expected: expected[n], cost: byName?.[n]?.cost, size: byName?.[n]?.expectedSize,
    differs: !(n in sol) || (byName != null && (byName[n]?.cost ?? 1) > 0),
  }));
}

function answer(el, { step, rec, recSteps, multi, stepName }) {
  const sols = step.solutions || [];
  const expected = step.expected || {};
  if (!sols.length) {
    add(el, card("No solutions", h("p", { class: "muted" }, `Status ${step.status}.`)));
    if (Object.keys(expected).length) add(el, card("Expected", typesTable(Object.keys(expected).map((n) => ({ name: n, expected: expected[n] })), { returned: false })));
    return;
  }
  const scores = step.scores || [];
  const closest = scores.length ? scores.indexOf(scores.reduce((a, s) => (s && (!a || s.cost < a.cost) ? s : a), null)) : -1;
  const here = recSteps.indexOf(step);
  const earlier = multi ? recSteps.slice(0, here).filter((s) => s.solutions?.length) : [];
  let only = false, withEarlier = false;
  const box = h("div", { class: "stack" });
  const draw = () => {
    clear(box);
    sols.forEach((_, i) => {
      const score = scores[i];
      // The earlier steps' answers are the ones this step was given: their first solutions
      const rows = [...(withEarlier ? earlier.flatMap((s) => typeRows(s, 0, s.step)) : []), ...typeRows(step, i, stepName)]
        .filter((r) => !only || r.differs);
      box.append(card(h("span", { class: "row" }, sols.length > 1 ? `Solution ${i + 1}` : "Solution",
        i === closest && sols.length > 1 ? h("span", { class: "chip s-correct" }, "closest") : null,
        score ? h("span", { class: "row small", style: { gap: "6px" } }, meter({ names: score.names, exactNames: score.exactNames }, "inline"),
          `${score.exactNames}/${score.names} names exact · cost ${score.cost} of ${score.expectedSize}`) : null),
        typesTable(rows, { withStep: withEarlier, scored: !!score })));
    });
  };
  add(el, h("div", { class: "row", style: { marginBottom: "8px" } },
    checkbox("only names that differ", only, (on) => { only = on; draw(); }),
    earlier.length ? checkbox(`with the ${earlier.length} earlier steps' answers`, withEarlier, (on) => { withEarlier = on; draw(); },
      "the answers this step was given, as each earlier step's first solution") : null,
    step.scores ? h("span", { class: "muted small" }, "cost: nodes that differ from the expected type, up to renaming") : null), box);
  draw();
}

function typesTable(rows, { returned = true, withStep = false, scored = false } = {}) {
  return dataTable({ rows, pageSize: 1000, filter: rows.length > 20, rowClass: (r) => (r.differs ? "mismatch" : ""), columns: [
    ...(returned ? [{ key: "differs", label: "", fmt: (v) => (v ? h("span", { class: "diff-mark", title: "differs from expected" }, "≠") : "") }] : []),
    ...(withStep ? [{ key: "step", fmt: (v) => h("span", { class: "muted" }, v) }] : []),
    { key: "name", fmt: (v) => h("code", {}, v) },
    ...(scored ? [{ key: "cost", num: true, title: "nodes that differ", fmt: (v, r) => (v == null ? "–" : r.size ? `${v} / ${r.size}` : String(v)) }] : []),
    ...(returned ? [{ key: "returned", fmt: (v) => (v == null ? h("span", { class: "muted" }, "missing") : h("code", {}, v)) }] : []),
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
  // Rounds are ordered, so they get one hue, light to dark, rather than a color each
  const drawScatter = () => plot(scatterDiv, [{
    type: rows.length > 2000 ? "scattergl" : "scatter", mode: "markers", x: rows.map((r) => r[x]), y: rows.map((r) => r[y] ?? null),
    marker: { size: 8, color: rows.map((r) => r.round), colorscale: [[0, "#b7d3f2"], [1, series(0)]], showscale: true,
      colorbar: { title: { text: "round" }, thickness: 10 }, line: barLine() },
    text: rows.map((r) => `search ${r.id}, round ${r.round}, outer depth ${r.outerDepth}<br>${r.names}`),
    hovertemplate: `%{text}<br>${label(x)}: %{x}<br>${label(y)}: %{y}<extra></extra>`,
  }], { xaxis: { title: label(x) }, yaxis: { title: label(y), type: logY ? "log" : "linear" } });
  add(el, h("div", { class: "grid" },
    card("Time per round, by phase", roundDiv),
    card(h("span", { class: "row" }, "Each search:", select(numeric.map((k) => [k, label(k)]), y, (v) => { y = v; drawScatter(); }), "against",
      select(numeric.map((k) => [k, label(k)]), x, (v) => { x = v; drawScatter(); }), checkbox("log", logY, (on) => { logY = on; drawScatter(); })), scatterDiv)));
  whenReady(() => {
    plot(roundDiv, phaseTimes.map((p) => ({ type: "bar", name: p.replace(" (s)", ""), x: rounds.map((r) => r.round), y: rounds.map((r) => r[p]),
      marker: { color: phaseColor(p.replace(" (s)", "")), line: barLine() },
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
  const rows = events.map((e, i) => ({ i, ...e, s: e.ms != null ? e.ms / 1000 : null, round: roundOf.get(e.search) }));
  const keys = [...new Set(rows.flatMap((r) => Object.keys(r)))].filter((k) => k !== "ms");
  const numeric = keys.filter((k) => rows.some((r) => typeof r[k] === "number"));
  const kinds = [...new Set(rows.map((r) => r.kind))];
  const div = plotDiv(380);
  let y = numeric.includes("size") ? "size" : numeric[0];
  const lab = (k) => (k === "s" ? "time into the step (s)" : k === "i" ? "event #" : k);
  const draw = () => plot(div, kinds.map((kind, j) => {
    const rs = rows.filter((r) => r.kind === kind);
    return { type: rs.length > 2000 ? "scattergl" : "scatter", mode: "markers", name: kind, x: rs.map((r) => r.s ?? r.i), y: rs.map((r) => r[y]),
      marker: { size: 8, color: series(j), line: barLine() }, text: rs.map((r) => JSON.stringify(Object.fromEntries(Object.entries(r).filter(([k]) => k !== "kind")))),
      hovertemplate: "%{text}<extra></extra>" };
  }), { xaxis: { title: lab("s") }, yaxis: { title: lab(y) } });
  add(el, card(h("span", { class: "row" }, "Events over time:", select(numeric.map((k) => [k, lab(k)]), y, (v) => { y = v; draw(); }),
    h("span", { class: "muted small" }, kinds.map((k) => `${k}: ${rows.filter((r) => r.kind === k).length}`).join(" · "))), div));
  whenReady(draw);
  add(el, card(h("span", { class: "row" }, "Events", h("button", { onclick: () => download("events.csv", toCSV(rows, keys), "text/csv") }, "CSV")),
    dataTable({ rows, pageSize: 100, filter: true, columns: keys.map((k) => ({ key: k, label: lab(k), num: numeric.includes(k), fmt: (v) => (k === "s" ? M.fmt("wall", v) : M.fmt(k, v)) })) })));
}

// -----------------------------------------------------------------------------------------------
// The run

async function log(el, { b, runId }) {
  add(el, loading());
  try {
    const text = await api.file(b.id, `${runId}.log`);
    el.replaceChildren(h("div", { class: "row small muted", style: { marginBottom: "6px" } }, `${text.split("\n").length} lines, for every step of the run`), h("pre", {}, text));
  } catch (e) { el.replaceChildren(errorBox(e)); }
}

function trace(el, { b, runId, multi, stepName }) {
  const f = { step: multi ? stepName : "", kind: "", phase: "", search: "", offset: 0, limit: 100 };
  const box = h("div", { class: "stack" });
  const load = async () => {
    box.replaceChildren(loading("Reading trace…"));
    try {
      const t = await api.trace({ batch: b.id, run: runId, ...f });
      const countTable = (name) => dataTable({ pageSize: 50, sortKey: "n", sortDesc: true, rows: Object.entries(t.counts[name]).map(([v, n]) => ({ v, n })),
        columns: [{ key: "v", label: name }, { key: "n", label: "lines", num: true, fmt: (v) => M.fmt("n", v) }] });
      const sel = (name) => select([["", `any ${name}`], ...Object.keys(t.counts[name]).sort().map((v) => [v, v])], f[name], (v) => {
        f[name] = v; f.offset = 0; if (name === "step") f.search = ""; load(); });
      const scope = f.step ? ` in step ${f.step}` : "";
      box.replaceChildren(
        h("div", { class: "grid" }, multi ? card("By step", countTable("step")) : null, card(`By kind${scope}`, countTable("kind")),
          card(`By phase${scope}`, countTable("phase")), card(`By search${scope}`, countTable("search"))),
        card(h("span", { class: "row" }, "Lines", multi ? sel("step") : null, sel("kind"), sel("phase"), sel("search"),
          h("button", { disabled: f.offset === 0, onclick: () => { f.offset = Math.max(0, f.offset - f.limit); load(); } }, "‹"),
          h("span", { class: "small muted" }, `${t.matched ? f.offset + 1 : 0}–${f.offset + t.lines.length} of ${t.matched}`),
          h("button", { disabled: f.offset + f.limit >= t.matched, onclick: () => { f.offset += f.limit; load(); } }, "›")),
          dataTable({ rows: t.lines.map((l, i) => ({ n: f.offset + i, ...l })), pageSize: f.limit, columns: [
            { key: "n", label: "#", num: true }, ...(multi ? [{ key: "step" }] : []), { key: "search", num: true }, { key: "phase" }, { key: "kind" },
            { key: "state", wrap: true, fmt: (v) => h("code", {}, typeof v === "string" ? v : JSON.stringify(v)) }] })));
    } catch (e) { box.replaceChildren(errorBox(e)); }
  };
  add(el, box);
  load();
}

function raw(el, { rec, step, b, runId, multi, stepName }) {
  let only = false;
  const tree = h("div", {});
  const draw = () => tree.replaceChildren(only ? jsonTree(step, stepName) : jsonTree(rec, runId));
  add(el, h("div", { class: "row", style: { marginBottom: "8px" } },
    h("a", { href: `api/run?batch=${encodeURIComponent(b.id)}&run=${encodeURIComponent(runId)}`, target: "_blank" }, "open the file"),
    multi && step ? checkbox(`only step ${stepName}`, only, (on) => { only = on; draw(); }) : null,
    h("span", { class: "muted small" }, "Expand to explore; long arrays open in chunks of 100.")),
    card(null, tree));
  draw();
}
