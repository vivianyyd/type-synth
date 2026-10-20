// Hash router: #/VIEW/PATH...?key=value. Each view module exports
// {id, title, nav (show in the top bar), render(el, {path, params, data})}.
import * as api from "./api.js";
import * as metrics from "./metrics.js";
import { h, clear, loading, errorBox } from "./ui.js";
import { parseHash, href } from "./router.js";
import batches from "./views/batches.js";
import batch from "./views/batch.js";
import run from "./views/run.js";
import compare from "./views/compare.js";
import history from "./views/history.js";

const VIEWS = [batches, compare, history, batch, run];
const byId = new Map(VIEWS.map((v) => [v.id, v]));

let renderToken = 0;
async function render(force = false) {
  const token = ++renderToken;
  const route = parseHash();
  const view = byId.get(route.view) || batches;
  const nav = document.getElementById("nav");
  clear(nav).append(...VIEWS.filter((v) => v.nav).map((v) =>
    h("a", { href: href(v.id), class: v === view ? "active" : "" }, v.title)));
  const el = document.getElementById("view");
  clear(el).append(loading());
  try {
    const data = await api.batches(force);
    if (token !== renderToken) return;
    metrics.init(data);
    document.getElementById("root").textContent = data.root;
    document.title = `${view.title} · Bench Dashboard`;
    const container = h("div", { class: "stack" });
    clear(el).append(container);
    await view.render(container, { ...route, data });
  } catch (e) {
    if (token === renderToken) clear(el).append(errorBox(e));
    console.error(e);
  }
}

window.addEventListener("hashchange", () => render());
document.getElementById("reload").addEventListener("click", () => render(true));
render();
