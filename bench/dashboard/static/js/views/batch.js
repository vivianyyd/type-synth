// One batch: metadata, a table of its runs with any metric as a column, and charts.
import { h, add, card, kv, dataTable, statusChip, statusCounts, multiPicker, select, checkbox, loading, errorBox } from "../ui.js";
import { href, setParams, list } from "../router.js";
import * as M from "../metrics.js";
import * as api from "../api.js";
import { plot, plotDiv, whenReady, statusColor } from "../charts.js";

const DEFAULT_COLS = ["status", "wall", "outline", "arity", "concretize", "unattributed", "solverCalls", "candidates", "prunedPos", "prunedNeg", "stop"];
const PHASE_TIMES = ["outline", "arity", "concretize", "cegis", "unattributed"];

export default {
  id: "batch", title: "Batch", nav: false,
  render(el, { path, params, data }) {
    const b = data.byId.get(path[0]);
    if (!b) { add(el, h("p", {}, `No batch ${path[0]}. `, h("a", { href: href("batches") }, "All batches"))); return; }
    const m = b.meta, g = m.git || {};
    const i = b.index, prev = data.batches[i - 1], next = data.batches[i + 1];
    const files = new Set(b.files.map((f) => f.name));

    add(el, h("div", { class: "row" },
      h("h1", {}, b.id), statusCounts(b.runs), h("span", { class: "spacer" }),
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

    // Runs table
    let cols = list(params.cols);
    if (!cols.length) cols = DEFAULT_COLS;
    const fold = params.fold === "1";
    const tableBox = h("div", {});
    const drawTable = () => {
      const rows = fold ? [...M.byBenchmark(b.runs).values()] : b.runs;
      const columns = [
        { key: "runId", label: fold ? "benchmark" : "run", fmt: (v, r) => h("a", { href: href("run", [b.id, r.runId]) }, fold ? r.benchmark : v) },
        ...(fold ? [{ key: "repeats", num: true }] : []),
        ...cols.map((c) => c === "status"
          ? { key: c, fmt: (v, r) => h("span", {}, statusChip(v), r.errorLine ? h("div", { class: "small muted", title: r.errorLine }, r.errorLine.slice(0, 80)) : null) }
          : { key: c, label: M.label(c), num: c !== "stop", wrap: c === "stop", fmt: (v) => M.fmt(c, v) }),
        { key: "log", label: "log", sortable: false, fmt: (_, r) => files.has(`${r.runId}.log`) ? h("a", { href: href("run", [b.id, r.runId], { tab: "log" }) }, "log") : "" },
      ];
      tableBox.replaceChildren(dataTable({ columns, rows, pageSize: 500, filter: true, rowHref: (r) => href("run", [b.id, r.runId]) }));
    };
    const picker = multiPicker({ label: "Columns", options: M.metricOptions(b.runs, { includeStatus: true }), selected: cols,
      onChange: (v) => { cols = v; setParams({ cols: v }); drawTable(); } });
    add(el, card(h("span", {}, "Runs"), h("div", { class: "row", style: { marginBottom: "8px" } }, picker,
      m.repeat > 1 ? checkbox("fold repeats (median times)", fold, (on) => setParams({ fold: on ? "1" : "" }, { rerender: true })) : null),
      tableBox));
    drawTable();

    // Charts
    const phaseDiv = plotDiv(380), metricDiv = plotDiv(380);
    let chartMetric = params.chart || "wall", logY = params.log === "1";
    const names = b.runs.map((r) => r.runId);
    const drawPhase = () => plot(phaseDiv, PHASE_TIMES.map((p) => ({
      type: "bar", name: p, x: names, y: b.runs.map((r) => r[p] ?? 0), hovertemplate: `%{x}<br>${p}: %{y:.3f}s<extra></extra>`,
    })), { barmode: "stack", yaxis: { title: "seconds", type: logY ? "log" : "linear" } });
    const drawMetric = () => plot(metricDiv, [{
      type: "bar", x: names, y: b.runs.map((r) => r[chartMetric] ?? null), marker: { color: b.runs.map((r) => statusColor(r.status)) },
      text: b.runs.map((r) => r.status), hovertemplate: `%{x}<br>${M.label(chartMetric)}: %{y}<br>%{text}<extra></extra>`,
    }], { yaxis: { title: M.label(chartMetric), type: logY ? "log" : "linear" } });
    const metricSel = select(M.metricOptions(b.runs).map((o) => [o.value, o.label]), chartMetric,
      (v) => { chartMetric = v; setParams({ chart: v }); drawMetric(); });
    add(el, h("div", { class: "grid" },
      card(h("span", { class: "row" }, "Time per phase", checkbox("log scale", logY, (on) => { logY = on; setParams({ log: on ? "1" : "" }); drawPhase(); drawMetric(); })), phaseDiv),
      card(h("span", { class: "row" }, "Per run", metricSel, h("span", { class: "small muted" }, "colored by status")), metricDiv)));
    whenReady(() => { drawPhase(); drawMetric(); });
  },
};
