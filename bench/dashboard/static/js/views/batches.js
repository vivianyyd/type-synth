// Every batch, newest first. Tick batches to compare them or follow them in History.
import { h, add, card, dataTable, statusCounts, checkbox } from "../ui.js";
import { href, selection, rerender } from "../router.js";
import { fmt } from "../metrics.js";
import { meter } from "../steps.js";

const sum = (rows, k) => rows.reduce((s, r) => s + (typeof r[k] === "number" ? r[k] : 0), 0);

export default {
  id: "batches", title: "Batches", nav: true,
  render(el, { data }) {
    const sel = new Set(selection.get().filter((id) => data.byId.has(id)));
    const chosen = () => [...sel].sort((a, b) => data.byId.get(a).index - data.byId.get(b).index); // oldest first: the baseline
    const count = h("span", {});
    const compareBtn = h("button", { class: "primary", onclick: () => { location.hash = href("compare", [], { b: chosen() }); } }, "Compare selected");
    const historyBtn = h("button", { onclick: () => { location.hash = href("history", [], { b: chosen() }); } }, "History of selected");
    const update = () => {
      selection.set([...sel]);
      count.textContent = `${sel.size} selected`;
      compareBtn.disabled = sel.size < 2;
      historyBtn.disabled = sel.size < 1;
    };
    update();

    const rows = data.batches.map((b) => {
      const g = b.meta.git || {};
      return {
        b, id: b.id, started: b.meta.startedAt, branch: g.branch, commit: (g.commit || "").slice(0, 8) + (g.dirty ? "+" : ""),
        subject: g.subject, variant: b.meta.variant, notes: b.meta.notes, runs: b.runs.length, steps: b.steps.length, folder: b.folder,
        planned: (b.meta.benchmarks || []).length * (b.meta.repeat || 1),
        wall: b.runs.reduce((s, r) => s + (r.wall || 0), 0),
        correct: b.steps.filter((r) => r.status === "correct" || r.status === "solved").length,
        exactNames: sum(b.steps, "exactNames"), names: sum(b.steps, "names"), cost: sum(b.steps, "cost"),
        options: `timeout ${b.meta.timeoutSec}s · jobs ${b.meta.jobs} · repeat ${b.meta.repeat}${b.meta.trace ? " · trace" : ""}`,
      };
    });

    const columns = [
      { key: "sel", label: "", sortable: false, fmt: (_, r) => checkbox("", sel.has(r.id), (on) => { on ? sel.add(r.id) : sel.delete(r.id); update(); }) },
      { key: "started", label: "started", fmt: (v, r) => h("a", { href: href("batch", [r.id]) }, (v || r.id).replace("T", " ").slice(0, 19)) },
      ...(data.batches.some((b) => b.folder) ? [{ key: "folder" }] : []),
      { key: "commit", label: "commit", fmt: (v) => h("code", {}, v) },
      { key: "branch" },
      { key: "subject", wrap: true },
      { key: "variant" },
      { key: "notes", wrap: true },
      { key: "runs", num: true, fmt: (v, r) => (v < r.planned ? `${v} / ${r.planned}` : String(v)), title: "runs recorded (of planned, if fewer)" },
      { key: "steps", num: true, title: "steps of all runs, counting the one a run stopped on" },
      { key: "correct", label: "step statuses", sortValue: (r) => r.correct, fmt: (_, r) => statusCounts(r.b.steps), title: "statuses of the steps" },
      { key: "exactNames", label: "names exact", num: true, sortValue: (r) => (r.names ? r.exactNames / r.names : null),
        title: "over every step with an expected answer, its closest solution",
        fmt: (v, r) => (r.names ? h("span", {}, meter(r, "inline"), `${v}/${r.names}`) : "–") },
      { key: "cost", label: "Σ cost", num: true, fmt: (v, r) => (r.names ? fmt("cost", v) : "–") },
      { key: "wall", label: "total time (s)", num: true, fmt: (v) => fmt("wall", v) },
      { key: "options", label: "options", fmt: (v) => h("span", { class: "muted small" }, v) },
    ];

    add(el, 
      h("div", { class: "row" }, h("h1", {}, "Batches"), h("span", { class: "muted" }, `${data.batches.length} batches, ${data.allRuns.length} runs, ${data.allSteps.length} steps`),
        h("span", { class: "spacer" }), count, compareBtn, historyBtn,
        h("button", { onclick: () => { sel.clear(); update(); rerender(); } }, "Clear")),
      dataTable({ columns, rows, sortKey: "started", sortDesc: true, filter: true, pageSize: 200, rowHref: (r) => href("batch", [r.id]) }),
    );
  },
};
