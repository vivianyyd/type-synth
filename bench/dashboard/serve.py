#!/usr/bin/env python3
"""Serves the benchmark dashboard: bench/dashboard/serve.py [--port 8765] [--root bench-results]"""

import argparse
import json
import mimetypes
import shutil
import sys
import traceback
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

from data import Results, analyze

STATIC = Path(__file__).resolve().parent / "static"


class Handler(BaseHTTPRequestHandler):
    results: Results = None  # set in main

    def log_message(self, fmt, *args):
        if not getattr(self, "quiet", False):
            sys.stderr.write("%s\n" % (fmt % args))

    # -----------------------------------------------------------------------------------------

    def do_GET(self):
        url = urlparse(self.path)
        q = {k: v[0] for k, v in parse_qs(url.query).items()}
        try:
            route = ROUTES.get(url.path)
            if route:
                route(self, q)
            else:
                self.static(url.path)
        except KeyError as e:
            self.send_json({"error": str(e.args[0] if e.args else e)}, 404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:
            traceback.print_exc()
            self.send_json({"error": f"{type(e).__name__}: {e}"}, 500)

    def send_bytes(self, body, ctype, status=200):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, obj, status=200):
        self.send_bytes(json.dumps(obj).encode(), "application/json", status)

    def send_file(self, path, ctype):
        size = path.stat().st_size
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(size))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        with path.open("rb") as f:
            shutil.copyfileobj(f, self.wfile)

    def static(self, path):
        rel = "index.html" if path in ("", "/") else path.lstrip("/")
        p = (STATIC / rel).resolve()
        if STATIC not in p.parents or not p.is_file():
            raise KeyError(f"not found: {path}")
        ctype = mimetypes.guess_type(p.name)[0] or "application/octet-stream"
        if p.suffix == ".js":
            ctype = "text/javascript"
        self.send_file(p, ctype + ("; charset=utf-8" if ctype.startswith("text/") else ""))

    # -----------------------------------------------------------------------------------------
    # API

    def api_batches(self, q):
        self.send_json({
            "root": str(self.results.root.resolve()),
            "metrics": {k: v[0] for k, v in analyze.METRICS.items()},
            "times": analyze.TIMES + ["load"],
            "batches": self.results.batches(),
        })

    def api_run(self, q):
        self.send_file(self.results.run_path(q["batch"], q["run"]), "application/json")

    def api_file(self, q):
        self.send_file(self.results.file_path(q["batch"], q["name"]), "text/plain; charset=utf-8")

    def api_trace(self, q):
        self.send_json(self.results.trace(
            q["batch"], q["run"], kind=q.get("kind") or None, search=q.get("search") or None,
            phase=q.get("phase") or None, offset=int(q.get("offset", 0)), limit=int(q.get("limit", 100))))


ROUTES = {
    "/api/batches": Handler.api_batches,
    "/api/run": Handler.api_run,
    "/api/file": Handler.api_file,
    "/api/trace": Handler.api_trace,
}


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(here.parent.parent / "bench-results"),
                        help="where batches are (default: bench-results of this checkout)")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--host", default="127.0.0.1", help="0.0.0.0 to serve other machines")
    parser.add_argument("--quiet", action="store_true", help="don't log requests")
    args = parser.parse_args()
    Handler.results = Results(args.root)
    Handler.quiet = args.quiet
    server = ThreadingHTTPServer((args.host, args.port), Handler)
    print(f"Serving {Path(args.root).resolve()} at http://{args.host}:{args.port}  (Ctrl-C to stop)")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
