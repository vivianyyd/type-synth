#!/usr/bin/env python3
import os
import re
import subprocess
import sys

EXS_DIR = os.path.join(os.path.dirname(__file__), "exs")

edges = set()
nodes = set()

for fname in sorted(os.listdir(EXS_DIR)):
    if not fname.endswith(".exs"):
        continue
    src = fname[: -len(".exs")]
    nodes.add(src)
    with open(os.path.join(EXS_DIR, fname)) as f:
        first_line = f.readline().strip()
    # strip leading //
    first_line = re.sub(r"^//\s*", "", first_line)
    refs = [r.strip() for r in first_line.split(",") if r.strip()]
    for ref in refs:
        # strip extension
        dst = re.sub(r"\.\w+$", "", ref)
        nodes.add(dst)
        if dst != src:
            edges.add((src, dst))

dot_lines = ["digraph deps {", "    rankdir=LR;", '    size="40,40!";', '    ratio=1;', '    dpi=150;', '    node [shape=box fontname="monospace"];']
for n in sorted(nodes):
    dot_lines.append(f'    "{n}";')
for src, dst in sorted(edges):
    dot_lines.append(f'    "{src}" -> "{dst}";')
dot_lines.append("}")

dot_src = "\n".join(dot_lines)
dot_file = os.path.join(os.path.dirname(__file__), "deps.dot")
png_file = os.path.join(os.path.dirname(__file__), "deps.png")

with open(dot_file, "w") as f:
    f.write(dot_src)

subprocess.run(["dot", "-Tpng", dot_file, "-o", png_file], check=True)
print(f"Written {dot_file} and {png_file}")

# dependents: reverse edges (who depends on this node)
from collections import defaultdict
immediate = defaultdict(set)  # node -> set of nodes that directly depend on it
for src, dst in edges:
    immediate[dst].add(src)

# transitive dependents via BFS
def transitive_dependents(node):
    visited = set()
    queue = list(immediate[node])
    while queue:
        n = queue.pop()
        if n in visited:
            continue
        visited.add(n)
        queue.extend(immediate[n])
    return visited

csv_file = os.path.join(os.path.dirname(__file__), "deps.csv")
with open(csv_file, "w") as f:
    f.write("node,immediate_dependents,transitive_dependents\n")
    for n in sorted(nodes):
        f.write(f"{n},{len(immediate[n])},{len(transitive_dependents(n))}\n")
print(f"Written {csv_file}")
