// Steps across batches: a grid of statuses and values, and a line chart over time.
import { h, add, card, multiPicker, select, checkbox, statusChip } from "../ui.js";
import { href, setParams, list } from "../router.js";
import * as M from "../metrics.js";
import * as api from "../api.js";
import { plot, plotDiv, whenReady, series, statusColor } from "../charts.js";
import { stepHref } from "./batch.js";

export default {
  id: "history", title: "History", nav: true,
  render(el, { params, data }) {
    const go = (p) => { location.hash = href("history", [], { ...params, ...p }); };
    const metric = params.m || "wall";
    const variant = params.variant || "";
    let ids = list(params.b).filter((id) => data.byId.has(id));
    let benches = list(params.bench).filter((n) => data.benchmarks.includes(n));
    let batches = ids.length ? ids.map((id) => data.byId.get(id)).sort((a, b) => a.index - b.index) : data.batches;
    if (variant) batches = batches.filter((b) => b.meta.variant === variant);
    // Without a choice of benchmarks, show the ones these batches ran; with one, only batches that ran them
    if (benches.length) batches = batches.filter((b) => b.steps.some((r) => benches.includes(r.benchmark)));
    const folded = batches.map((b) => M.byBenchmark(b.steps));
    const rowsNames = api.orderSteps(data, benches.length ? benches : new Set(folded.flatMap((f) => [...f.keys()])));
    const parentOf = new Map(data.allSteps.map((s) => [s.benchmark, s.parent]));
    const variants = [...new Set(data.batches.map((b) => b.meta.variant))];

    add(el, h("div", { class: "row" }, h("h1", {}, "History"),
      h("span", { class: "muted" }, `${rowsNames.length} steps × ${batches.length} batches, oldest first`)));
    add(el, h("div", { class: "row" },
      "Metric", select(M.metricOptions(data.allSteps).map((o) => [o.value, o.label]), metric, (v) => go({ m: v })),
      multiPicker({ label: "Steps", options: data.benchmarks.map((n) => ({ value: n, label: n })), selected: benches, onClose: (v) => go({ bench: v }) }),
      multiPicker({ label: "Batches", options: [...data.batches].reverse().map((b) => ({ value: b.id, label: b.label })), selected: ids, onClose: (v) => go({ b: v }) }),
      "Variant", select([["", "any"], ...variants.map((v) => [v, v])], variant, (v) => go({ variant: v })),
      ids.length || benches.length || variant ? h("button", { onclick: () => { location.hash = href("history", [], { m: metric }); } }, "Show everything") : null));

    if (!batches.length) { add(el, h("p", { class: "muted" }, "No batches match.")); return; }

    // Grid: cell color is status, text is the metric; a cell links to its run
    const vals = rowsNames.flatMap((n) => folded.map((f) => f.get(n)?.[metric])).filter((v) => typeof v === "number" && v > 0);
    // Times and counts span orders of magnitude, so they shade on a log scale; scores don't
    const scale = M.isScore(metric) ? (v) => v : Math.log;
    const lo = scale(Math.min(...vals)), hi = scale(Math.max(...vals));
    const shade = (v) => (typeof v === "number" && v > 0 && hi > lo ? (scale(v) - lo) / (hi - lo) : 0);
    const table = h("table", { class: "heat" },
      h("thead", {}, h("tr", {}, h("th", {}, "benchmark"), batches.map((b) => h("th", { class: "rot", title: b.label },
        h("a", { href: href("batch", [b.id]) }, b.short))))),
      h("tbody", {}, rowsNames.map((n, j) => h("tr", { class: j > 0 && parentOf.get(rowsNames[j - 1]) !== parentOf.get(n) ? "group-start" : "" },
        h("td", {}, h("a", { href: href("history", [], { ...params, bench: [n] }) }, n)),
        folded.map((f, i) => {
          const r = f.get(n);
          if (!r) return h("td", { class: "cell muted", title: batches[i].runs.some((x) => x.benchmark === parentOf.get(n)) ? "not reached" : "not run" },
            batches[i].runs.some((x) => x.benchmark === parentOf.get(n)) ? "·" : "");
          const v = r[metric];
          const color = statusColor(r.status.split("/")[0]);
          return h("td", { class: "cell", title: `${n} in ${batches[i].label}\n${r.status}\n${M.label(metric)}: ${M.fmt(metric, v)}${r.repeats > 1 ? `\nmedian of ${r.repeats}` : ""}`,
            style: { background: `color-mix(in srgb, ${color} ${Math.round(12 + 38 * shade(v))}%, transparent)`, borderLeft: `3px solid ${color}` },
            onclick: () => { location.hash = stepHref(batches[i].id, { ...r, runId: r.runIds[0] }); } }, M.fmt(metric, v));
        })))));
    add(el, card(h("span", { class: "row" }, `${M.label(metric)} per step and batch`,
      h("span", { class: "row small" }, ["correct", "wrong", "no-solution", "timeout"].map((s) => statusChip(s))),
      h("span", { class: "muted small" }, `darker is larger${M.isScore(metric) ? "" : " (log scale)"}; · not reached; click a cell for its step`)),
      h("div", { class: "table-wrap", style: { maxHeight: "70vh" } }, table)));

    // Line chart over batches
    let logY = params.log !== "0";
    const div = plotDiv(440);
    // One color per step, in a fixed order, so at most eight
    const chartNames = rowsNames.slice(0, 8);
    const xs = batches.map((b) => b.short);
    const draw = () => plot(div, chartNames.map((n, j) => ({
      type: "scatter", mode: "lines+markers", name: n, x: xs, y: folded.map((f) => f.get(n)?.[metric] ?? null), connectgaps: false,
      line: { color: series(j), width: 2 },
      marker: { size: 9, color: folded.map((f) => statusColor((f.get(n)?.status || "").split("/")[0])), line: { color: series(j), width: 2 } },
      text: folded.map((f, i) => `${f.get(n)?.status ?? "not run"}<br>${batches[i].meta.notes || ""}`),
      hovertemplate: `${n}<br>%{x}<br>%{y}<br>%{text}<extra></extra>`,
    })), { xaxis: { type: "category", tickangle: -40 }, yaxis: { title: M.label(metric), type: logY && !M.isScore(metric) ? "log" : "linear" } });
    add(el, card(h("span", { class: "row" }, `${M.label(metric)} over batches`, checkbox("log scale", logY, (on) => { logY = on; setParams({ log: on ? "" : "0" }); draw(); }),
      h("span", { class: "muted small" }, chartNames.length < rowsNames.length ? `first ${chartNames.length} steps; pick up to 8 above` : "marker color is status")), div));
    whenReady(draw);
  },
};
