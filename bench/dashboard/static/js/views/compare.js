// Two or more batches side by side, against a baseline, a row per step.
import { h, add, card, dataTable, statusChip, statusCounts, multiPicker, select, checkbox } from "../ui.js";
import { href, setParams, list, selection } from "../router.js";
import * as M from "../metrics.js";
import * as api from "../api.js";
import { plot, plotDiv, whenReady, series, statusColor, barLine } from "../charts.js";
import { meter, chip } from "../steps.js";
import { stepHref } from "./batch.js";

const DEFAULT_METRICS = ["status", "exact", "cost", "wall", "candidates", "solverCalls"];
const tag = (i) => (i === 0 ? "base" : String.fromCharCode(65 + i));
const swatch = (i) => h("span", { class: "swatch", style: { background: series(i) } });

export default {
  id: "compare", title: "Compare", nav: true,
  render(el, { params, data }) {
    let ids = list(params.b).filter((id) => data.byId.has(id));
    if (!ids.length) ids = selection.get().filter((id) => data.byId.has(id));
    if (!ids.length) ids = data.batches.slice(-2).map((b) => b.id);
    const go = (p) => { location.hash = href("compare", [], { ...params, b: ids, ...p }); };

    // Picking batches
    const addSel = select([["", "Add a batch…"], ...[...data.batches].reverse().filter((b) => !ids.includes(b.id)).map((b) => [b.id, b.label])], "",
      (v) => { if (v) go({ b: [...ids, v] }); }, { style: { maxWidth: "520px" } });
    add(el, h("div", { class: "row" }, h("h1", {}, "Compare"), h("span", { class: "muted" }, "the first batch is the baseline; times and counts as other / baseline, scores as other − baseline")));
    add(el, card("Batches", h("div", { class: "stack" },
      ids.map((id, i) => {
        const b = data.byId.get(id);
        return h("div", { class: "row" }, swatch(i), h("strong", {}, tag(i)),
          h("a", { href: href("batch", [id]) }, b.label), statusCounts(b.steps), h("span", { class: "muted small" }, b.meta.git?.subject || ""),
          i > 0 ? h("button", { onclick: () => go({ b: [id, ...ids.filter((x) => x !== id)] }) }, "make baseline") : null,
          ids.length > 1 ? h("button", { onclick: () => go({ b: ids.filter((x) => x !== id) }), title: "remove" }, "✕") : null);
      }),
      h("div", { class: "row" }, addSel, h("button", { onclick: () => { selection.set(ids); } }, "Remember as selection")))));

    const batches = ids.map((id) => data.byId.get(id));
    const folded = batches.map((b) => M.byBenchmark(b.steps));
    const names = api.orderSteps(data, new Set(folded.flatMap((f) => [...f.keys()])));
    const allSteps = batches.flatMap((b) => b.steps);
    // A step a batch has no row for: not reached if the batch ran its benchmark, else not run
    const ranBench = batches.map((b) => new Set(b.runs.map((r) => r.benchmark)));
    const parentOf = new Map(allSteps.map((s) => [s.benchmark, s.parent]));
    const statusIn = (i, n) => folded[i].get(n)?.status ?? (ranBench[i].has(parentOf.get(n)) ? "not-reached" : "not-run");
    let metrics = list(params.m);
    if (!metrics.length) metrics = DEFAULT_METRICS;
    const onlyChanged = params.changed === "1";

    // Options
    add(el, h("div", { class: "row" },
      multiPicker({ label: "Metrics", options: M.metricOptions(allSteps, { includeStatus: true }), selected: metrics, onClose: (v) => go({ m: v }) }),
      checkbox("only steps whose status changed (among steps both batches ran)", onlyChanged, (on) => go({ changed: on ? "1" : "" }))));

    // Summary. Times and counts: geometric mean of ratios over the steps every batch got right.
    // Scores: totals over the steps every batch scored, since a wrong step is where they differ.
    const numeric = metrics.filter((m) => m !== "status" && m !== "stop" && m !== "exact");
    const scoreMetrics = [...new Set([...(metrics.includes("exact") ? ["exactNames"] : []), ...numeric.filter(M.isScore)])];
    const ratioMetrics = numeric.filter((m) => !M.isScore(m));
    const allGood = names.filter((n) => folded.every((f) => f.has(n) && M.isGood(f.get(n).status)));
    const allScored = names.filter((n) => folded.every((f) => f.get(n)?.names));
    const summaryRows = batches.map((b, i) => {
      const r = { i, b, label: b.short, notes: b.meta.notes };
      for (const m of ratioMetrics) {
        const rs = allGood.map((n) => M.ratio(folded[0].get(n)[m], folded[i].get(n)[m])).filter((x) => x != null);
        r[m] = i === 0 ? null : M.geomean(rs);
        r[`${m}.total`] = allGood.reduce((s, n) => s + (folded[i].get(n)[m] || 0), 0);
      }
      for (const m of [...scoreMetrics, "names"]) r[`${m}.total`] = allScored.reduce((s, n) => s + (folded[i].get(n)[m] || 0), 0);
      return r;
    });
    const summaryCols = [
      { key: "label", label: "batch", fmt: (v, r) => h("span", { class: "row" }, swatch(r.i), h("strong", {}, tag(r.i)), v) },
      { key: "notes", wrap: true },
      { key: "statuses", sortable: false, fmt: (_, r) => statusCounts(r.b.steps) },
      ...scoreMetrics.map((m) => ({ key: `${m}.total`, label: `Σ ${M.label(m)}`, num: true, title: `over the ${allScored.length} steps every batch scored`,
        fmt: (v, r) => {
          if (!allScored.length) return "–";
          const d = r.i > 0 ? M.change(m, summaryRows[0][`${m}.total`], v) : null;
          const shown = m === "exactNames" ? h("span", {}, meter({ exactNames: v, names: r["names.total"] }, "inline"), `${v}/${r["names.total"]}`) : M.fmt(m, v);
          return h("span", {}, shown, d ? h("span", { class: `ratio ${d.cls}` }, d.text) : null);
        } })),
      ...ratioMetrics.flatMap((m) => [
        { key: `${m}.total`, label: `Σ ${M.label(m)}`, num: true, title: `over the ${allGood.length} steps every batch got right`, fmt: (v) => (allGood.length ? M.fmt(m, v) : "–") },
        { key: m, label: `× ${M.label(m)}`, num: true, fmt: (v) => (v == null ? "–" : h("span", { class: M.dirClass(M.direction(m, 1, v)) }, v.toFixed(3))) }]),
    ];
    add(el, card(h("span", {}, "Summary ", h("span", { class: "muted small" },
      `scores over the ${allScored.length} steps every batch scored; times and counts over the ${allGood.length} steps every batch got right (Σ total, × geometric mean of ratios)`)),
      dataTable({ rows: summaryRows, pageSize: 50, columns: summaryCols })));

    // Status changes against the baseline, among the steps both ran
    const changes = [];
    for (const n of names) {
      const base = statusIn(0, n);
      folded.forEach((f, i) => { if (i > 0) { const s = statusIn(i, n); if (s !== base && s !== "not-run" && base !== "not-run") changes.push({ n, i, base, s }); } });
    }
    if (changes.length) add(el, card(`Status changes (${changes.length})`, h("div", { class: "stack small" }, changes.map((c) =>
      h("div", { class: "row" }, h("code", {}, c.n), chip(c.base), "→", chip(c.s), h("span", { class: "row muted" }, "in", swatch(c.i), tag(c.i), batches[c.i].short))))));

    // Main table: step × (metric × batch)
    const changedNames = new Set(changes.map((c) => c.n));
    const rows = names.filter((n) => !onlyChanged || changedNames.has(n)).map((n) => {
      const r = { benchmark: n, parent: parentOf.get(n) };
      folded.forEach((f, i) => { const x = f.get(n); r[`run${i}`] = x; for (const m of metrics) r[`${m}@${i}`] = m === "exact" ? x?.exactFrac : x?.[m]; });
      return r;
    });
    const groupStart = new Set(rows.filter((r, j) => j > 0 && rows[j - 1].parent !== r.parent));
    const columns = [{ key: "benchmark", label: "step", fmt: (v) => h("a", { href: href("history", [], { bench: v, b: ids }) }, v) }];
    for (const m of metrics) batches.forEach((b, i) => {
      columns.push({
        key: `${m}@${i}`, label: `${m === "exact" ? M.label("exactNames") : M.label(m)} ${tag(i)}`, num: m !== "status" && m !== "stop", wrap: m === "stop",
        title: `${M.label(m)} in ${b.label}`,
        fmt: (v, r) => {
          const run = r[`run${i}`];
          if (!run) return m === "status" ? chip(statusIn(i, r.benchmark)) : h("span", { class: "muted" }, "–");
          const link = (x) => h("a", { href: stepHref(b.id, { ...run, runId: run.runIds[0] }) }, x);
          if (m === "status") return link(statusChip(v));
          if (m === "exact") {
            if (!run.names) return "–";
            const d = i > 0 && r.run0?.names ? M.change("exactNames", r.run0.exactNames, run.exactNames) : null;
            return h("span", {}, meter(run, "inline"), run.exact, d ? h("span", { class: `ratio ${d.cls}` }, d.text) : null);
          }
          const d = i > 0 ? M.change(m, r[`${m}@0`], v) : null;
          return h("span", {}, M.fmt(m, v), d ? h("span", { class: `ratio ${d.cls}` }, d.text) : null);
        },
      });
    });
    add(el, card(`Steps (${rows.length})`, dataTable({ columns, rows, pageSize: 500, filter: true, rowClass: (r) => (groupStart.has(r) ? "group-start" : "") })));

    // Charts
    const chartable = [...new Set([...(metrics.includes("exact") ? ["exactFrac"] : []), ...numeric])];
    if (!chartable.length) return;
    let chart = chartable.includes(params.chart) ? params.chart : chartable[0];
    let logY = params.log !== "0";
    const barDiv = plotDiv(420), scatDiv = plotDiv(420);
    const draw = () => {
      const log = logY && !M.isScore(chart);
      plot(barDiv, batches.map((b, i) => ({
        type: "bar", name: `${tag(i)} ${b.short}`, x: names, y: names.map((n) => folded[i].get(n)?.[chart] ?? null),
        marker: { color: series(i), line: barLine() },
        text: names.map((n) => statusIn(i, n)), textposition: "none", hovertemplate: `%{x}<br>%{y}<br>%{text}<extra>%{fullData.name}</extra>`,
      })), { barmode: "group", xaxis: { type: "category" }, yaxis: { title: M.label(chart), type: log ? "log" : "linear" } });
      const all = [];
      const traces = batches.slice(1).map((b, j) => {
        const i = j + 1, ns = names.filter((n) => folded[0].has(n) && folded[i].has(n));
        const xs = ns.map((n) => folded[0].get(n)[chart]), ys = ns.map((n) => folded[i].get(n)[chart]);
        all.push(...xs, ...ys);
        return { type: "scatter", mode: "markers", name: `${tag(i)} ${b.short}`, x: xs, y: ys, text: ns.map((n) => `${n}: ${folded[i].get(n).status}`),
          marker: { size: 10, color: series(i), symbol: ns.map((n) => (M.isGood(folded[i].get(n).status) ? "circle" : "x")), line: barLine() },
          hovertemplate: `%{text}<br>base %{x}<br>this %{y}<extra>%{fullData.name}</extra>` };
      });
      const pos = all.filter((v) => typeof v === "number" && (v > 0 || !log));
      const lo = Math.min(...pos), hi = Math.max(...pos);
      if (pos.length) traces.push({ type: "scatter", mode: "lines", x: [lo, hi], y: [lo, hi], name: "equal", line: { dash: "dot", color: "gray", width: 1 }, hoverinfo: "skip" });
      plot(scatDiv, traces, { xaxis: { title: `baseline ${M.label(chart)}`, type: log ? "log" : "linear" }, yaxis: { title: M.label(chart), type: log ? "log" : "linear" } });
    };
    add(el, card(h("span", { class: "row" }, "Chart", select(chartable.map((m) => [m, M.label(m)]), chart, (v) => { chart = v; setParams({ chart: v }); draw(); }),
      checkbox("log scale (times and counts)", logY, (on) => { logY = on; setParams({ log: on ? "" : "0" }); draw(); }),
      h("span", { class: "muted small" }, "× marks: not right in that batch")),
      h("div", { class: "grid" }, barDiv, scatDiv)));
    whenReady(draw);
  },
};
