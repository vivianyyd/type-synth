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
batches show up on reload, including a batch still running. Batches can also sit one folder down
(`bench-results/kept/BATCH`), to keep some apart; the folder is shown with the batch.

## Steps

A benchmark is a list of steps (`bench/README.md`), so the dashboard's unit is a step, named as
`analyze.py` names it: `cons` for a one-step benchmark, `ocaml-chained/list` for a step of one with
several. Tables, comparisons and history have a row per step, in chain order, and every step links
to its run with the step chosen.

A run that stopped during a step (crashed, killed, or still running) didn't record that step, so
the dashboard adds a row for it with the run's status, named after the step that comes next in the
longest run of the same benchmark it has seen (`(next)` if none got that far). Steps after it are
"not reached". In Compare, a step a batch didn't run at all is "not run", and isn't counted as a
status change.

Scores (`scores` in the record) appear as **names exact** (`exact`: a bar of exact names in green and
the rest in red, with `n/m`), **diff cost** (`cost`), **diff ratio** (`diff`) and **fraction exact**
(`exactFrac`), all of the closest solution. Compare shows scores as a difference from the baseline,
not a ratio, since they are often 0.

## Views

Every view's state is in the URL (`#/compare?b=...&m=...`), so back/forward work and a view can be
bookmarked or pasted to someone.

| View | Shows |
|---|---|
| **Batches** | Every batch: date, folder, git commit/branch/subject, variant, notes, runs and steps, step statuses, names exact and total cost over every scored step, total time. Filter; tick batches to compare. |
| **Batch** | One batch's metadata (git, machine, options, `changes.patch`); each run with several steps as a strip of tiles, one per step (status, names exact, cost, time); a table of steps with any metric as a column; charts of time per phase and any metric per step. |
| **Run** | The run's steps as tiles; click one to choose it. Tabs: chain (every step in a table, time per step by phase, names exact per step), and for the chosen step overview (scores, config, counters, phases, schedule, error), answer (each solution against the expected types, with each name's cost, optionally with the earlier steps' answers it was given), searches, events; and for the run log, trace (`--trace`, filtered to the chosen step) and raw JSON. With no step chosen, it opens on the first step that isn't right. |
| **Compare** | Two or more batches side by side, a row per step. Pick the baseline and the metrics: ratios against the baseline for times and counts, differences for scores. Summary: total scores over the steps every batch scored, geometric means of ratios over the steps every batch got right. Status changes, a grouped bar chart and a baseline-vs-other scatter. |
| **History** | Steps × batches: a grid of statuses with a metric in each cell, and a line chart of the metric across batches for up to 8 chosen steps. |

## Layout

```
serve.py            HTTP server: the JSON API below, and static/
data.py             reads bench-results: batch list, run summaries (cached), files, traces
static/index.html   shell: nav and the view container
static/style.css    light and dark themes via CSS variables
static/js/
  app.js            hash router and view registry
  api.js            fetches the API, caches responses; indexes steps, chains, steps a run stopped on
  metrics.js        metric labels, formatting, folding repeats, ratios and differences, geometric mean
  steps.js          a run's steps as tiles, the names-exact bar
  ui.js             DOM helpers: h(), sortable/paginated table, pickers, tabs
  charts.js         Plotly wrappers that follow the theme
  views/*.js        one module per view
```

A run summary is the run's own fields, its totals over steps, and a row per step. Step rows come
from `analyze.row` in `bench/analyze.py`, so the dashboard and the command line agree on what a
metric means. `data.py` adds what `row` leaves out (the step's name and place, per-phase counts,
load time, fraction exact, number of solutions, error line).

### API

| Endpoint | Returns |
|---|---|
| `GET /api/batches` | `{metrics, times, batches: [{id, folder, meta, files, runs: [{...run, steps: [step row]}]}]}` |
| `GET /api/run?batch=B&run=R` | The run's record, as written |
| `GET /api/file?batch=B&name=N` | A text file in the batch (`.log`, `changes.patch`) |
| `GET /api/trace?batch=B&run=R&step=T&kind=K&search=S&offset=O&limit=L` | Lines per step, counts per kind/phase/search within step T, and one page of trace lines |

## Extending

- **A metric**: anything new in a step's `stats.counters` or `stats.phases` appears on its own. For a
  derived one, add it to `step_row` in `data.py`. For a nicer label, add it to `METRICS` in
  `analyze.py`. A score (compared by difference, not ratio) goes in `SCORES` in `metrics.js`, and in
  `HIGHER` if larger is better.
- **A view**: add `static/js/views/NAME.js` exporting `{id, title, nav, render(el, params)}` and
  list it in `app.js`. Link to it with `#/NAME?key=value`.
- **A chart**: `charts.js` wraps Plotly; any `Plotly.newPlot` trace and layout works.
- **A plot from Python** (matplotlib, pandas): add an endpoint in `serve.py` that returns SVG, and
  show it with `<img src="/api/...">`. Not built yet.

## Plan

Built first (above): the five views over the record format with steps and scores (schema 2).
Records from before steps show as unreadable.

Next, roughly in order of value:

1. **Run-to-run diff**: the same step in two batches, with solutions, searches and per-phase
   counts side by side.
2. **Planned steps in the record**: the record lists only the steps that ran, so a chain that stops
   early names the step it stopped on only if another run got further. Recording the benchmark's
   step names would fix that.
3. **Repeat spread**: with `--repeat N`, show the spread of times (box plots) instead of only the median.
4. **Python plots**: matplotlib endpoints for figures meant for a paper, sharing styles with
   `analyze.py latex`.
5. **Batch tags and hiding**: name batches and hide bad ones, kept in a small JSON file next to
   `bench-results`.
6. **Static export**: write one self-contained HTML file with the data inlined, for sharing without a server.
