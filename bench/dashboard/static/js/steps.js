// A run's steps: tiles in chain order, and how close each answer came to the expected one.
import { h, statusChip } from "./ui.js";
import * as M from "./metrics.js";

const STATUS_VAR = { correct: "--good", solved: "--good", wrong: "--bad", error: "--bad", crashed: "--bad", unreadable: "--bad",
  "no-solution": "--warn", timeout: "--other", running: "--info" };
export const statusVar = (s) => `var(${STATUS_VAR[s] || "--none"})`;

export const chip = (status) => (status === "not-reached" || status === "not-run" ? statusChip(status, status.replace("-", " ")) : statusChip(status));

// Names exact against names not, as a bar. Nothing for a step without scores.
export function meter(s, cls = "") {
  if (!s.names) return null;
  const miss = s.names - s.exactNames;
  return h("span", { class: `meter ${cls}`, title: `${s.exactNames} of ${s.names} names exact` },
    s.exactNames ? h("span", { class: "fill", style: `flex: ${s.exactNames}` }) : null,
    miss ? h("span", { class: "miss", style: `flex: ${miss}` }) : null);
}

// "20/22 exact · cost 3 · 4.78 s"
export function facts(s) {
  const out = [];
  if (s.names) out.push(`${s.exactNames}/${s.names} exact`);
  if (s.cost) out.push(`cost ${s.cost}`);
  if (s.wall != null) out.push(`${M.fmt("wall", s.wall)} s`);
  return out.join(" · ");
}

export function tile(s, { link, selected = false, compact = false } = {}) {
  const ghost = s.pending || s.status === "not-reached";
  return h(link ? "a" : "div", {
    class: `tile${selected ? " selected" : ""}${ghost ? " ghost" : ""}`, href: link, style: `--st: ${statusVar(s.status)}`,
    title: [s.benchmark, s.pending ? "the run stopped during this step" : "", s.errorLine || ""].filter(Boolean).join("\n"),
  },
    h("span", { class: "name" }, s.step),
    h("span", { class: "row", style: { gap: "4px" } }, chip(s.status)),
    meter(s),
    facts(s) ? h("span", { class: "facts" }, facts(s)) : null,
    s.errorLine && !compact ? h("span", { class: "err" }, s.errorLine) : null);
}

// The run's steps, then the step it stopped on, if it didn't record it, then the steps of the
// chain it didn't reach. linkFor(step) gives each tile's link.
export function chainSteps(run, chain = []) {
  const done = run.pending ? [...run.steps, run.pending] : [...run.steps];
  const seen = new Set(done.map((s) => s.step));
  const rest = chain.filter((n) => !seen.has(n)).map((n, i) => ({
    step: n, status: "not-reached", benchmark: `${run.benchmark}/${n}`, stepIndex: done.length + i, parent: run.benchmark,
  }));
  return [...done, ...rest];
}

export function strip(run, chain, { linkFor, selected, compact = false } = {}) {
  const kids = [];
  chainSteps(run, chain).forEach((s, i) => {
    if (i) kids.push(h("span", { class: "link" }));
    const reachable = s.status !== "not-reached";
    kids.push(tile(s, { link: reachable && linkFor ? linkFor(s) : null, selected: selected === s.step, compact }));
  });
  return h("div", { class: `chain${compact ? " compact" : ""}` }, kids);
}
