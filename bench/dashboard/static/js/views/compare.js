// Two or more batches side by side, against a baseline.
import { h, add, card, dataTable, statusChip, statusCounts, multiPicker, select, checkbox } from "../ui.js";
import { href, setParams, list, selection } from "../router.js";
import * as M from "../metrics.js";
import { plot, plotDiv, whenReady, SERIES, statusColor } from "../charts.js";

const DEFAULT_METRICS = ["status", "wall", "candidates", "prunedNeg", "solverCalls"];

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
    add(el, h("div", { class: "row" }, h("h1", {}, "Compare"), h("span", { class: "muted" }, "the first batch is the baseline; ratios are other / baseline")));
    add(el, card("Batches", h("div", { class: "stack" },
      ids.map((id, i) => {
        const b = data.byId.get(id);
        return h("div", { class: "row" }, h("span", { class: "chip", style: { background: SERIES[i % SERIES.length], color: "#fff" } }, i === 0 ? "baseline" : String.fromCharCode(65 + i)),
          h("a", { href: href("batch", [id]) }, b.label), statusCounts(b.runs), h("span", { class: "muted small" }, b.meta.git?.subject || ""),
          i > 0 ? h("button", { onclick: () => go({ b: [id, ...ids.filter((x) => x !== id)] }) }, "make baseline") : null,
          ids.length > 1 ? h("button", { onclick: () => go({ b: ids.filter((x) => x !== id) }), title: "remove" }, "✕") : null);
      }),
      h("div", { class: "row" }, addSel, h("button", { onclick: () => { selection.set(ids); } }, "Remember as selection")))));

    const batches = ids.map((id) => data.byId.get(id));
    const folded = batches.map((b) => M.byBenchmark(b.runs));
    const names = [...new Set(folded.flatMap((f) => [...f.keys()]))].sort();
    const allRuns = batches.flatMap((b) => b.runs);
    let metrics = list(params.m);
    if (!metrics.length) metrics = DEFAULT_METRICS;
    const onlyChanged = params.changed === "1";

    // Options
    add(el, h("div", { class: "row" },
      multiPicker({ label: "Metrics", options: M.metricOptions(allRuns, { includeStatus: true }), selected: metrics, onClose: (v) => go({ m: v }) }),
      checkbox("only benchmarks whose status changed", onlyChanged, (on) => go({ changed: on ? "1" : "" }))));

    // Summary: statuses, geometric mean of ratios over benchmarks every batch got right
    const numeric = metrics.filter((m) => m !== "status" && m !== "stop");
    const allGood = names.filter((n) => folded.every((f) => f.has(n) && M.isGood(f.get(n).status)));
    const summaryRows = batches.map((b, i) => {
      const r = { i, b, label: b.short, notes: b.meta.notes };
      for (const m of numeric) {
        const rs = allGood.map((n) => M.ratio(folded[0].get(n)[m], folded[i].get(n)[m])).filter((x) => x != null);
        r[m] = i === 0 ? null : M.geomean(rs);
        r[`${m}.n`] = rs.length;
        r[`${m}.total`] = allGood.reduce((s, n) => s + (folded[i].get(n)[m] || 0), 0);
      }
      return r;
    });
    add(el, card(h("span", {}, "Summary ", h("span", { class: "muted small" }, `geometric mean of ratios over the ${allGood.length} benchmarks every batch got right; total over the same benchmarks`)),
      dataTable({ rows: summaryRows, pageSize: 50, columns: [
        { key: "label", label: "batch", fmt: (v, r) => h("span", { class: "row" }, h("span", { class: "chip", style: { background: SERIES[r.i % SERIES.length], color: "#fff" } }, r.i === 0 ? "base" : String.fromCharCode(65 + r.i)), v) },
        { key: "notes", wrap: true },
        { key: "statuses", sortable: false, fmt: (_, r) => statusCounts(r.b.runs) },
        ...numeric.flatMap((m) => [
          { key: `${m}.total`, label: `Σ ${M.label(m)}`, num: true, fmt: (v) => M.fmt(m, v) },
          { key: m, label: `× ${M.label(m)}`, num: true, fmt: (v) => (v == null ? "–" : h("span", { class: M.ratioClass(v) }, v.toFixed(3))) }]),
      ] })));

    // Status changes against the baseline
    const changes = [];
    for (const n of names) {
      const base = folded[0].get(n)?.status ?? "missing";
      folded.forEach((f, i) => { if (i > 0) { const s = f.get(n)?.status ?? "missing"; if (s !== base) changes.push({ n, i, base, s }); } });
    }
    if (changes.length) add(el, card(`Status changes (${changes.length})`, h("div", { class: "stack small" }, changes.map((c) =>
      h("div", { class: "row" }, h("code", {}, c.n), statusChip(c.base), "→", statusChip(c.s), h("span", { class: "muted" }, `in ${String.fromCharCode(65 + c.i)} ${batches[c.i].short}`))))));

    // Main table: benchmark × (metric × batch)
    const changedNames = new Set(changes.map((c) => c.n));
    const rows = names.filter((n) => !onlyChanged || changedNames.has(n)).map((n) => {
      const r = { benchmark: n };
      folded.forEach((f, i) => { const x = f.get(n); r[`run${i}`] = x; for (const m of metrics) r[`${m}@${i}`] = x?.[m]; });
      return r;
    });
    const columns = [{ key: "benchmark", fmt: (v) => h("a", { href: href("history", [], { bench: v, b: ids }) }, v) }];
    for (const m of metrics) batches.forEach((b, i) => {
      const tag = i === 0 ? "base" : String.fromCharCode(65 + i);
      columns.push({
        key: `${m}@${i}`, label: `${M.label(m)} ${tag}`, num: m !== "status" && m !== "stop", wrap: m === "stop",
        title: `${M.label(m)} in ${b.label}`,
        fmt: (v, r) => {
          const run = r[`run${i}`];
          if (!run) return h("span", { class: "muted" }, "–");
          const link = (x) => h("a", { href: href("run", [b.id, run.runIds[0]]) }, x);
          if (m === "status") return link(statusChip(v));
          const ratio = i > 0 ? M.ratio(r[`${m}@0`], v) : null;
          return h("span", {}, M.fmt(m, v), ratio != null ? h("span", { class: `ratio ${M.ratioClass(ratio)}` }, `×${ratio.toFixed(2)}`) : null);
        },
      });
    });
    add(el, card(`Benchmarks (${rows.length})`, dataTable({ columns, rows, pageSize: 500, filter: true })));

    // Charts
    if (!numeric.length) return;
    let chart = numeric.includes(params.chart) ? params.chart : numeric[0];
    let logY = params.log !== "0";
    const barDiv = plotDiv(420), scatDiv = plotDiv(420);
    const draw = () => {
      plot(barDiv, batches.map((b, i) => ({
        type: "bar", name: `${i === 0 ? "base" : String.fromCharCode(65 + i)} ${b.short}`, x: names, y: names.map((n) => folded[i].get(n)?.[chart] ?? null),
        marker: { color: SERIES[i % SERIES.length], line: { width: names.map((n) => (M.isGood(folded[i].get(n)?.status) ? 0 : 2)), color: names.map((n) => statusColor(folded[i].get(n)?.status)) } },
        text: names.map((n) => folded[i].get(n)?.status ?? "missing"), hovertemplate: `%{x}<br>%{y}<br>%{text}<extra>%{fullData.name}</extra>`,
      })), { barmode: "group", yaxis: { title: M.label(chart), type: logY ? "log" : "linear" } });
      const all = [];
      const traces = batches.slice(1).map((b, j) => {
        const i = j + 1, ns = names.filter((n) => folded[0].has(n) && folded[i].has(n));
        const xs = ns.map((n) => folded[0].get(n)[chart]), ys = ns.map((n) => folded[i].get(n)[chart]);
        all.push(...xs, ...ys);
        return { type: "scatter", mode: "markers", name: `${String.fromCharCode(65 + i)} ${b.short}`, x: xs, y: ys, text: ns,
          marker: { size: 9, color: SERIES[i % SERIES.length], symbol: ns.map((n) => (M.isGood(folded[i].get(n).status) ? "circle" : "x")) },
          hovertemplate: `%{text}<br>base %{x}<br>this %{y}<extra>%{fullData.name}</extra>` };
      });
      const pos = all.filter((v) => typeof v === "number" && v > 0);
      const lo = Math.min(...pos), hi = Math.max(...pos);
      if (pos.length) traces.push({ type: "scatter", mode: "lines", x: [lo, hi], y: [lo, hi], name: "equal", line: { dash: "dot", color: "gray" }, hoverinfo: "skip" });
      plot(scatDiv, traces, { xaxis: { title: `baseline ${M.label(chart)}`, type: logY ? "log" : "linear" }, yaxis: { title: M.label(chart), type: logY ? "log" : "linear" } });
    };
    add(el, card(h("span", { class: "row" }, "Chart", select(numeric.map((m) => [m, M.label(m)]), chart, (v) => { chart = v; setParams({ chart: v }); draw(); }),
      checkbox("log scale", logY, (on) => { logY = on; setParams({ log: on ? "" : "0" }); draw(); }),
      h("span", { class: "muted small" }, "outlined bars and × marks: not correct")),
      h("div", { class: "grid" }, barDiv, scatDiv)));
    whenReady(draw);
  },
};
