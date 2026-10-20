// One batch: metadata, the steps of runs that have several, a table of steps with any metric as a
// column, and charts.
import { h, add, card, kv, dataTable, statusChip, statusCounts, multiPicker, select, checkbox, loading, errorBox } from "../ui.js";
import { href, setParams, list } from "../router.js";
import * as M from "../metrics.js";
import * as api from "../api.js";
import { plot, plotDiv, whenReady, statusColor, phaseColor, barLine } from "../charts.js";
import { strip, meter } from "../steps.js";

const DEFAULT_COLS = ["status", "exact", "cost", "wall", "outline", "arity", "concretize", "unattributed", "solverCalls", "candidates",
  "prunedNeg", "stop"];
const PHASE_TIMES = ["outline", "arity", "concretize", "cegis", "unattributed"];

// A step's page: its run's, with the step chosen
export const stepHref = (batchId, s, params = {}) => href("run", [batchId, s.runId], { step: s.multi ? s.step : "", ...params });

export default {
  id: "batch", title: "Batch", nav: false,
  render(el, { path, params, data }) {
    const b = data.byId.get(path[0]);
    if (!b) { add(el, h("p", {}, `No batch ${path[0]}. `, h("a", { href: href("batches") }, "All batches"))); return; }
    const m = b.meta, g = m.git || {};
    const i = b.index, prev = data.batches[i - 1], next = data.batches[i + 1];
    const files = new Set(b.files.map((f) => f.name));

    add(el, h("div", { class: "row" },
      h("h1", {}, b.id), statusCounts(b.steps), h("span", { class: "spacer" }),
      prev ? h("a", { href: href("batch", [prev.id]) }, "‹ previous batch") : null,
      next ? h("a", { href: href("batch", [next.id]) }, "next batch ›") : null,
      prev ? h("button", { onclick: () => { location.hash = href("compare", [], { b: [prev.id, b.id] }); } }, "Compare with previous") : null),
      m.notes ? h("div", { class: "muted" }, `Notes: ${m.notes}`) : null);

    // Metadata
    const planned = (m.benchmarks || []);
    const present = new Set(b.runs.map((r) => r.benchmark));
    const missing = planned.filter((n) => !present.has(n));
    const patchBox = h("div", {});
    const showPatch = files.has("changes.patch") ? h("button", { onclick: async () => {
      patchBox.replaceChildren(loading());
      try { patchBox.replaceChildren(h("pre", {}, await api.file(b.id, "changes.patch"))); } catch (e) { patchBox.replaceChildren(errorBox(e)); }
    } }, "Show changes.patch") : null;
    add(el, h("div", { class: "grid" },
      card("Git", kv([["commit", h("code", {}, g.commit)], ["branch", g.branch], ["subject", g.subject], ["dirty", g.dirty ? "yes, uncommitted changes" : "no"]]), showPatch, patchBox),
      card("Options", kv([["variant", m.variant], ["variant means", m.variantDescription], ["started", m.startedAt], ["timeout (s)", m.timeoutSec],
        ["repeat", m.repeat], ["jobs", m.jobs], ["trace", m.trace ? "yes" : "no"],
        ["benchmarks", `${planned.length} planned, ${present.size} recorded`], ["missing", missing.length ? missing.join(", ") : undefined]])),
      card("Machine", kv(m.machine || {})),
      card("Files", h("div", { class: "small" }, b.files.map((f) => h("div", {}, h("code", {}, f.name), h("span", { class: "muted" }, ` ${M.fmtBytes(f.size)}`))))),
    ));

    // Runs of benchmarks with several steps, each as its chain
    const chained = b.runs.filter((r) => data.chains.get(r.benchmark)?.length > 1);
    if (chained.length) add(el, card(h("span", {}, "Chains ", h("span", { class: "muted small" }, "each step builds on the answers of the steps before it")),
      h("div", { class: "runs-list" }, chained.map((r) => h("div", { class: "stack" },
        h("div", { class: "row" }, h("a", { href: href("run", [b.id, r.runId]) }, h("strong", {}, r.runId)), statusChip(r.status),
          h("span", { class: "muted small" }, `${r.goodSteps} of ${data.chains.get(r.benchmark).length} steps right`),
          r.names ? h("span", { class: "small row", style: { gap: "4px" } }, meter(r, "inline"), `${r.exactNames}/${r.names} names exact · cost ${r.cost}`) : null,
          r.wall != null ? h("span", { class: "muted small" }, `${M.fmt("wall", r.wall)} s searching, ${M.fmt("load", r.load || 0)} s loading`) : null,
          r.errorLine ? h("span", { class: "small error", title: r.errorLine }, r.errorLine.slice(0, 100)) : null),
        strip(r, data.chains.get(r.benchmark), { compact: true, linkFor: (s) => stepHref(b.id, s) }))))));

    // Steps table
    let cols = list(params.cols);
    if (!cols.length) cols = DEFAULT_COLS;
    const fold = params.fold === "1";
    const tableBox = h("div", {});
    const drawTable = () => {
      const rows = api.sortSteps(data, fold ? [...M.byBenchmark(b.steps).values()] : b.steps);
      const groupStart = new Set(rows.filter((r, j) => j > 0 && rows[j - 1].parent !== r.parent && (r.multi || rows[j - 1].multi)));
      const columns = [
        { key: "benchmark", label: "step", fmt: (v, r) => h("a", { href: stepHref(b.id, r) }, fold || m.repeat <= 1 ? v : `${v} #${r.repeat}`) },
        ...(fold ? [{ key: "repeats", num: true }] : []),
        ...cols.map((c) => c === "status"
          ? { key: c, fmt: (v, r) => h("span", {}, statusChip(v), r.pending ? h("span", { class: "muted small" }, " stopped here") : null,
            r.errorLine ? h("div", { class: "small muted", title: r.errorLine }, r.errorLine.slice(0, 80)) : null) }
          : c === "exact"
            ? { key: c, label: M.label("exactNames"), sortValue: (r) => r.exactFrac, fmt: (v, r) => (r.names ? h("span", {}, meter(r, "inline"), v) : "–") }
            : { key: c, label: M.label(c), num: c !== "stop", wrap: c === "stop", fmt: (v) => M.fmt(c, v) }),
        { key: "log", label: "log", sortable: false, fmt: (_, r) => files.has(`${r.runId}.log`) ? h("a", { href: stepHref(b.id, r, { tab: "log" }) }, "log") : "" },
      ];
      tableBox.replaceChildren(dataTable({ columns, rows, pageSize: 500, filter: true, rowHref: (r) => stepHref(b.id, r),
        rowClass: (r) => (groupStart.has(r) ? "group-start" : "") }));
    };
    const picker = multiPicker({ label: "Columns", options: M.metricOptions(b.steps, { includeStatus: true }), selected: cols,
      onChange: (v) => { cols = v; setParams({ cols: v }); drawTable(); } });
    add(el, card(h("span", {}, "Steps ", h("span", { class: "muted small" }, "a benchmark with one step is one row")),
      h("div", { class: "row", style: { marginBottom: "8px" } }, picker,
        m.repeat > 1 ? checkbox("fold repeats (median times)", fold, (on) => setParams({ fold: on ? "1" : "" }, { rerender: true })) : null),
      tableBox));
    drawTable();

    // Charts, a bar per step that ran
    const ran = api.sortSteps(data, b.steps.filter((s) => !s.pending));
    if (!ran.length) return;
    const phaseDiv = plotDiv(380), metricDiv = plotDiv(380);
    let chartMetric = params.chart || "wall", logY = params.log === "1";
    const names = ran.map((r) => (m.repeat > 1 ? `${r.benchmark} #${r.repeat}` : r.benchmark));
    const drawPhase = () => plot(phaseDiv, PHASE_TIMES.map((p) => ({
      type: "bar", name: p === "unattributed" ? "not in a phase" : p, x: names, y: ran.map((r) => r[p] ?? 0),
      marker: { color: phaseColor(p), line: barLine() }, hovertemplate: `%{x}<br>${p}: %{y:.3f}s<extra></extra>`,
    })), { barmode: "stack", yaxis: { title: "seconds", type: logY ? "log" : "linear" } });
    const drawMetric = () => plot(metricDiv, [{
      type: "bar", x: names, y: ran.map((r) => r[chartMetric] ?? null), marker: { color: ran.map((r) => statusColor(r.status)), line: barLine() },
      text: ran.map((r) => r.status), textposition: "none", hovertemplate: `%{x}<br>${M.label(chartMetric)}: %{y}<br>%{text}<extra></extra>`,
    }], { yaxis: { title: M.label(chartMetric), type: logY ? "log" : "linear" } });
    const metricSel = select(M.metricOptions(ran).map((o) => [o.value, o.label]), chartMetric,
      (v) => { chartMetric = v; setParams({ chart: v }); drawMetric(); });
    add(el, h("div", { class: "grid" },
      card(h("span", { class: "row" }, "Time per phase", checkbox("log scale", logY, (on) => { logY = on; setParams({ log: on ? "1" : "" }); drawPhase(); drawMetric(); })), phaseDiv),
      card(h("span", { class: "row" }, "Per step", metricSel, h("span", { class: "small muted" }, "colored by status")), metricDiv)));
    whenReady(() => { drawPhase(); drawMetric(); });
  },
};
