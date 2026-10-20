// Plotly wrappers that pick up the page's theme. Any Plotly trace or layout option works.
import { h } from "./ui.js";

const css = (v) => getComputedStyle(document.documentElement).getPropertyValue(v).trim();

export const STATUS_COLORS = () => ({
  correct: css("--good"), solved: css("--good"), wrong: css("--bad"), error: css("--bad"), crashed: css("--bad"),
  unreadable: css("--bad"), "no-solution": css("--warn"), timeout: css("--other"),
});
export const statusColor = (s) => STATUS_COLORS()[s] || css("--none");

// Categorical series colors, chosen to stay apart in light and dark themes.
export const SERIES = ["#4e79a7", "#f28e2b", "#59a14f", "#e15759", "#76b7b2", "#edc948", "#b07aa1", "#ff9da7", "#9c755f", "#bab0ac"];

export function plot(el, traces, layout = {}, config = {}) {
  if (!window.Plotly) {
    el.replaceChildren(h("div", { class: "plot-missing" }, "Charts need Plotly, loaded from cdn.jsdelivr.net. Is the browser offline?"));
    return;
  }
  const fg = css("--fg"), grid = css("--border"), muted = css("--muted");
  const axis = (a = {}) => ({ gridcolor: grid, zerolinecolor: grid, linecolor: grid, tickfont: { color: muted }, automargin: true, ...a,
    title: typeof a.title === "string" ? { text: a.title, font: { color: muted } } : a.title });
  const base = {
    paper_bgcolor: "rgba(0,0,0,0)", plot_bgcolor: "rgba(0,0,0,0)", font: { family: css("--font"), color: fg, size: 12 },
    margin: { l: 60, r: 20, t: layout.title ? 40 : 16, b: 60 }, colorway: SERIES, hovermode: "closest",
    legend: { orientation: "h", y: -0.25, font: { color: fg } },
  };
  const merged = { ...base, ...layout, xaxis: axis(layout.xaxis), yaxis: axis(layout.yaxis) };
  if (typeof layout.title === "string") merged.title = { text: layout.title, font: { size: 14 }, x: 0 };
  window.Plotly.react(el, traces, merged, { responsive: true, displaylogo: false, ...config });
}

export function plotDiv(height = 360) {
  return h("div", { class: "plot", style: { height: `${height}px` } });
}

// Plots once Plotly has loaded (it is deferred) and the element is in the page.
export function whenReady(fn) {
  if (window.Plotly) requestAnimationFrame(fn);
  else window.addEventListener("load", () => requestAnimationFrame(fn), { once: true });
}
