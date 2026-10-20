// Plotly wrappers that pick up the page's theme. Any Plotly trace or layout option works.
import { h } from "./ui.js";

const css = (v) => getComputedStyle(document.documentElement).getPropertyValue(v).trim();

export const STATUS_COLORS = () => ({
  correct: css("--good"), solved: css("--good"), wrong: css("--bad"), error: css("--bad"), crashed: css("--bad"),
  unreadable: css("--bad"), "no-solution": css("--warn"), timeout: css("--other"), running: css("--info"),
});
export const statusColor = (s) => STATUS_COLORS()[s] || css("--none");

// Categorical colors, in a fixed order (from the CSS, so they follow the theme).
export const series = (i) => css(`--series-${(i % 8) + 1}`);

// Phases keep their color in every chart; time in no phase is gray.
const PHASE_SLOT = { outline: 0, arity: 1, concretize: 2, cegis: 3 };
export const phaseColor = (p) => (p in PHASE_SLOT ? series(PHASE_SLOT[p]) : css("--none"));

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
    margin: { l: 60, r: 20, t: layout.title ? 64 : 40, b: 60 }, colorway: [0, 1, 2, 3, 4, 5, 6, 7].map(series), hovermode: "closest",
    bargap: 0.3, barcornerradius: 3, hoverlabel: { bgcolor: css("--panel"), bordercolor: grid, font: { color: fg } },
    // Above the plot, so long tick labels can't run into it
    legend: { orientation: "h", x: 0, y: 1.02, yanchor: "bottom", traceorder: "normal", font: { color: fg } },
  };
  const merged = { ...base, ...layout, xaxis: axis(layout.xaxis), yaxis: axis(layout.yaxis) };
  if (typeof layout.title === "string") merged.title = { text: layout.title, font: { size: 14 }, x: 0 };
  window.Plotly.react(el, traces, merged, { responsive: true, displaylogo: false, ...config });
}

// Bars with a thin surface-colored outline, so stacked segments and neighbors stay apart.
export const barLine = () => ({ color: css("--panel"), width: 1 });

export function plotDiv(height = 360) {
  return h("div", { class: "plot", style: { height: `${height}px` } });
}

// Plots once Plotly has loaded (it is deferred) and the element is in the page.
export function whenReady(fn) {
  if (window.Plotly) requestAnimationFrame(fn);
  else window.addEventListener("load", () => requestAnimationFrame(fn), { once: true });
}
