// URLs are #/VIEW/PATH...?key=value, so every view's state can be bookmarked and shared.

export function parseHash() {
  const [p, q = ""] = location.hash.replace(/^#\/?/, "").split("?");
  const parts = p.split("/").filter(Boolean).map(decodeURIComponent);
  return { view: parts[0] || "batches", path: parts.slice(1), params: Object.fromEntries(new URLSearchParams(q)) };
}

export function href(view, path = [], params = {}) {
  const q = new URLSearchParams(Object.entries(params)
    .filter(([, v]) => v != null && v !== "" && v !== false && !(Array.isArray(v) && !v.length))
    .map(([k, v]) => [k, Array.isArray(v) ? v.join(",") : v])).toString();
  return `#/${[view, ...path].map(encodeURIComponent).join("/")}${q ? `?${q}` : ""}`;
}

// Records params of the current view in the URL. Without rerender, the view has already drawn
// the change, so this adds no history entry and does not re-render.
export function setParams(params, { rerender = false } = {}) {
  const cur = parseHash();
  const next = href(cur.view, cur.path, { ...cur.params, ...params });
  if (rerender) location.hash = next;
  else history.replaceState(null, "", next);
}

export const list = (s) => (s ? s.split(",").filter(Boolean) : []);

export function rerender() { window.dispatchEvent(new HashChangeEvent("hashchange")); }

// Batches picked for comparison, kept across views and reloads.
export const selection = {
  get() { try { return JSON.parse(localStorage.getItem("bench.selection") || "[]"); } catch { return []; } },
  set(ids) { try { localStorage.setItem("bench.selection", JSON.stringify(ids)); } catch {} },
};
