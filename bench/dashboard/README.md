# Benchmark dashboard

A browser view of everything `./gradlew bench` writes to `bench-results/`.

```sh
bench/dashboard/serve.py                 # http://localhost:8765
bench/dashboard/serve.py --port 9000 --root other-results
```

Only Python 3's standard library is needed. Charts use Plotly, which the page loads from jsDelivr,
so the browser needs internet. On a remote machine, forward the port:
`ssh -L 8765:localhost:8765 HOST`, then open http://localhost:8765 locally.

The server reads `bench-results/` on every request (summaries are cached by file mtime), so new
batches show up on reload, including a batch still running.

## Views

Every view's state is in the URL (`#/compare?b=...&m=...`), so back/forward work and a view can be
bookmarked or pasted to someone.

| View | Shows |
|---|---|
| **Batches** | Every batch: date, git commit/branch/subject, variant, notes, status counts, total time. Filter; tick batches to compare. |
| **Batch** | One batch's metadata (git, machine, options, `changes.patch`), a table of runs with any metric as a column, and charts: time per phase per run, and any metric per run. |
| **Run** | One run, in tabs: overview (config, counters, phases, schedule, error), answer (each solution against the expected types, mismatches marked, mismatched rounds), searches (every search, sortable, with charts), events, log, trace (`--trace`), raw JSON. |
| **Compare** | Two or more batches side by side. Pick the baseline and the metrics; ratios against the baseline, geometric means over benchmarks every batch got right, status changes, a grouped bar chart and a baseline-vs-other scatter. |
| **History** | Benchmarks × batches: a grid of statuses with a metric in each cell, and a line chart of the metric across batches for the chosen benchmarks. |

## Layout

```
serve.py            HTTP server: the JSON API below, and static/
data.py             reads bench-results: batch list, run summaries (cached), files, traces
static/index.html   shell: nav and the view container
static/style.css    light and dark themes via CSS variables
static/js/
  app.js            hash router and view registry
  api.js            fetches the API, caches responses
  metrics.js        metric labels, formatting, folding repeats, ratios, geometric mean
  ui.js             DOM helpers: h(), sortable/paginated table, pickers, tabs
  charts.js         Plotly wrappers that follow the theme
  views/*.js        one module per view
```

Run summaries come from `analyze.row` in `bench/analyze.py`, so the dashboard and the command line
agree on what a metric means. `data.py` adds what `row` leaves out (per-phase counts, load time,
number of solutions and mismatches, error line).

### API

| Endpoint | Returns |
|---|---|
| `GET /api/batches` | `{metrics, times, batches: [{id, meta, files, runs: [summary]}]}` |
| `GET /api/run?batch=B&run=R` | The run's record, as written |
| `GET /api/file?batch=B&name=N` | A text file in the batch (`.log`, `changes.patch`) |
| `GET /api/trace?batch=B&run=R&kind=K&search=S&offset=O&limit=L` | Counts per kind/phase/search, and one page of trace lines |

## Extending

- **A metric**: anything new in the run records' `stats.counters` or `stats.phases` appears on its
  own. For a derived one, add it to `summarize` in `data.py`. For a nicer label, add it to `METRICS`
  in `analyze.py`.
- **A view**: add `static/js/views/NAME.js` exporting `{id, title, nav, render(el, params)}` and
  list it in `app.js`. Link to it with `#/NAME?key=value`.
- **A chart**: `charts.js` wraps Plotly; any `Plotly.newPlot` trace and layout works.
- **A plot from Python** (matplotlib, pandas): add an endpoint in `serve.py` that returns SVG, and
  show it with `<img src="/api/...">`. Not built yet.

## Plan

Built first (above): the five views over the existing record format.

Next, roughly in order of value:

1. **Run-to-run diff**: the same benchmark in two batches, with solutions, searches and per-phase
   counts side by side.
2. **Repeat spread**: with `--repeat N`, show the spread of times (box plots) instead of only the median.
3. **Python plots**: matplotlib endpoints for figures meant for a paper, sharing styles with
   `analyze.py latex`.
4. **Batch tags and hiding**: name batches and hide bad ones, kept in a small JSON file next to
   `bench-results`.
5. **Static export**: write one self-contained HTML file with the data inlined, for sharing without a server.
