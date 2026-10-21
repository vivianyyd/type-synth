// Small DOM helpers and reusable widgets. No framework: each widget returns an element.

export function h(tag, attrs = {}, ...kids) {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs || {})) {
    if (v == null || v === false) continue;
    if (k === "class") el.className = v;
    else if (k === "style" && typeof v === "object") Object.assign(el.style, v);
    else if (k.startsWith("on")) el.addEventListener(k.slice(2), v);
    else if (k in el && typeof v !== "string") el[k] = v;
    else el.setAttribute(k, v === true ? "" : v);
  }
  append(el, kids);
  return el;
}

function append(el, kids) {
  for (const k of kids.flat(Infinity)) {
    if (k == null || k === false) continue;
    el.append(k instanceof Node ? k : document.createTextNode(String(k)));
  }
}

export const clear = (el) => { el.replaceChildren(); return el; };

// Like el.append, but skips null/false (native append would show them as text).
export function add(el, ...kids) { append(el, kids); return el; }

export function card(title, ...kids) {
  return h("section", { class: "card" }, title ? h("h2", {}, title) : null, ...kids);
}

export function kv(pairs) {
  const dl = h("dl", { class: "kv" });
  for (const [k, v] of Array.isArray(pairs) ? pairs : Object.entries(pairs)) {
    if (v === undefined) continue;
    dl.append(h("dt", {}, k), h("dd", {}, v instanceof Node ? v : v === null ? "–" : typeof v === "object" ? JSON.stringify(v) : String(v)));
  }
  return dl;
}

export function statusChip(status, text) {
  return h("span", { class: `chip s-${status}`, title: status }, text ?? status);
}

export function statusCounts(runs) {
  const c = {};
  for (const r of runs) c[r.status] = (c[r.status] || 0) + 1;
  return h("span", { class: "row", style: { gap: "4px" } },
    Object.entries(c).sort().map(([s, n]) => statusChip(s, `${s} ${n}`)));
}

export function loading(text = "Loading…") { return h("div", { class: "loading" }, text); }
export function errorBox(e) { return h("pre", { class: "error" }, String(e && e.stack || e)); }

export function select(options, value, onChange, attrs = {}) {
  const el = h("select", { ...attrs, onchange: () => onChange(el.value) },
    options.map((o) => {
      const [v, l] = Array.isArray(o) ? o : typeof o === "object" ? [o.value, o.label] : [o, o];
      return h("option", { value: v, selected: String(v) === String(value) }, l);
    }));
  return el;
}

export function checkbox(label, checked, onChange, title) {
  const input = h("input", { type: "checkbox", checked, onchange: () => onChange(input.checked) });
  return h("label", { class: "check", title }, input, label);
}

// A dropdown of checkboxes with a search box. options: [{value, label, group?}]
// onClose(values) runs when the menu closes after a change, for views that re-render on a change.
export function multiPicker({ label, options, selected, onChange = () => {}, onClose, searchable = true }) {
  const sel = new Set(selected);
  let changed = false;
  const changedTo = (values) => { changed = true; onChange(values); };
  const summary = h("summary", {});
  const refresh = () => { summary.textContent = `${label} (${sel.size}) ▾`; };
  const list = h("div", {});
  const search = searchable ? h("input", { type: "search", placeholder: "filter", style: { width: "100%", marginBottom: "6px" },
    oninput: () => draw() }) : null;
  const draw = () => {
    const q = (search?.value || "").toLowerCase();
    clear(list);
    let group = null;
    for (const o of options) {
      if (q && !`${o.label} ${o.value}`.toLowerCase().includes(q)) continue;
      if (o.group && o.group !== group) { group = o.group; list.append(h("div", { class: "muted small", style: { marginTop: "6px" } }, group)); }
      const input = h("input", { type: "checkbox", checked: sel.has(o.value), onchange: () => {
        input.checked ? sel.add(o.value) : sel.delete(o.value);
        refresh();
        changedTo(options.map((x) => x.value).filter((v) => sel.has(v)));
      } });
      list.append(h("label", {}, input, o.label));
    }
  };
  const buttons = h("div", { class: "row small", style: { marginBottom: "6px" } },
    h("a", { href: "javascript:void 0", onclick: () => { options.forEach((o) => sel.add(o.value)); draw(); refresh(); changedTo([...sel]); } }, "all"),
    h("a", { href: "javascript:void 0", onclick: () => { sel.clear(); draw(); refresh(); changedTo([]); } }, "none"));
  refresh(); draw();
  const el = h("details", { class: "picker" }, summary, h("div", { class: "menu" }, search, buttons, list));
  el.addEventListener("toggle", () => { if (!el.open && changed && onClose) { changed = false; onClose(options.map((x) => x.value).filter((v) => sel.has(v))); } });
  const outside = (e) => { if (!el.isConnected) document.removeEventListener("click", outside); else if (!el.contains(e.target)) el.open = false; };
  document.addEventListener("click", outside);
  return el;
}

export function tabs(items, active, onChange) {
  return h("div", { class: "tabs" }, items.map(({ id, label }) =>
    h("a", { href: "javascript:void 0", class: id === active ? "active" : "", onclick: () => onChange(id) }, label)));
}

// Sortable, filterable, paginated table.
// columns: [{key, label, get?(row), fmt?(value,row) -> string|Node, num?, wrap?, title?, sortable?}]
export function dataTable({ columns, rows, pageSize = 100, sortKey, sortDesc = false, onRowClick, rowClass, filter = false, rowHref }) {
  let key = sortKey, desc = sortDesc, page = 0, q = "";
  const wrap = h("div", {});
  const value = (c, r) => (c.get ? c.get(r) : r[c.key]);
  const draw = () => {
    let rs = rows;
    if (q) rs = rs.filter((r) => columns.some((c) => String(value(c, r) ?? "").toLowerCase().includes(q)));
    if (key != null) {
      const c = columns.find((c) => c.key === key);
      if (c) {
        const sv = c.sortValue || ((r) => value(c, r));
        rs = [...rs].sort((a, b) => cmp(sv(a), sv(b)) * (desc ? -1 : 1));
      }
    }
    const pages = Math.max(1, Math.ceil(rs.length / pageSize));
    page = Math.min(page, pages - 1);
    const shown = rs.slice(page * pageSize, (page + 1) * pageSize);
    const thead = h("thead", {}, h("tr", {}, columns.map((c) => h("th", {
      class: c.num ? "num" : "", title: c.title || c.key,
      onclick: c.sortable === false ? null : () => { if (key === c.key) desc = !desc; else { key = c.key; desc = !!c.num; } draw(); },
    }, c.label ?? c.key, key === c.key ? h("span", { class: "arrow" }, desc ? " ▼" : " ▲") : ""))));
    const tbody = h("tbody", {}, shown.map((r) => {
      const tr = h("tr", { class: [onRowClick || rowHref ? "clickable" : "", rowClass ? rowClass(r) : ""].join(" ") },
        columns.map((c) => {
          const v = value(c, r);
          const out = c.fmt ? c.fmt(v, r) : v == null ? "–" : typeof v === "object" ? JSON.stringify(v) : v;
          return h("td", { class: [c.num ? "num" : "", c.wrap ? "wrap" : ""].join(" ") }, out);
        }));
      if (onRowClick || rowHref) tr.addEventListener("click", (e) => {
        if (e.target.closest("a, input, button, select")) return;
        if (rowHref) location.hash = rowHref(r); else onRowClick(r, e);
      });
      return tr;
    }));
    const pager = rs.length > pageSize ? h("div", { class: "pager" },
      h("button", { disabled: page === 0, onclick: () => { page--; draw(); } }, "‹"),
      `${page * pageSize + 1}–${page * pageSize + shown.length} of ${rs.length}`,
      h("button", { disabled: page >= pages - 1, onclick: () => { page++; draw(); } }, "›")) :
      h("div", { class: "pager" }, `${rs.length} rows`);
    add(clear(wrap),
      filter ? h("div", { class: "pager" }, h("input", { type: "search", placeholder: "filter rows", value: q,
        oninput: (e) => { q = e.target.value.toLowerCase(); page = 0; draw(); const i = wrap.querySelector("input[type=search]"); i.focus(); i.setSelectionRange(q.length, q.length); } })) : null,
      h("div", { class: "table-wrap", style: { maxHeight: "75vh" } }, h("table", {}, thead, tbody)), pager);
  };
  draw();
  return wrap;
}

export function cmp(a, b) {
  if (a == null && b == null) return 0;
  if (a == null) return 1;
  if (b == null) return -1;
  if (typeof a === "number" && typeof b === "number") return a - b;
  return String(a).localeCompare(String(b), undefined, { numeric: true });
}

// A collapsible JSON tree that only builds children when opened, so 60k-element arrays are fine.
export function jsonTree(value, name = "record") {
  const ul = h("ul", { class: "tree" });
  ul.append(treeNode(name, value, true));
  return ul;
}

const CHUNK = 100;
function treeNode(key, v, open = false) {
  const keyEl = key == null ? null : h("span", { class: "k" }, `${key}: `);
  if (v !== null && typeof v === "object") {
    const isArr = Array.isArray(v);
    const n = isArr ? v.length : Object.keys(v).length;
    const details = h("details", { open }, h("summary", {}, keyEl, isArr ? `[${n}]` : `{${n}}`));
    let built = false;
    const build = () => {
      if (built) return; built = true;
      const ul = h("ul", {});
      if (isArr && n > CHUNK) {
        for (let i = 0; i < n; i += CHUNK) ul.append(treeNode(`[${i}…${Math.min(n, i + CHUNK) - 1}]`, Object.fromEntries(v.slice(i, i + CHUNK).map((x, j) => [i + j, x]))));
      } else {
        for (const [k, x] of Object.entries(v)) ul.append(treeNode(k, x));
      }
      details.append(ul);
    };
    details.addEventListener("toggle", build);
    if (open) build();
    return h("li", {}, details);
  }
  const cls = typeof v === "string" ? "s" : "n";
  return h("li", {}, keyEl, h("span", { class: cls }, JSON.stringify(v)));
}

export function download(name, text, type = "text/plain") {
  const a = h("a", { href: URL.createObjectURL(new Blob([text], { type })), download: name });
  document.body.append(a); a.click(); a.remove();
}
