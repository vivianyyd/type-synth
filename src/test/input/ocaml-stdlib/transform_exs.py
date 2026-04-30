#!/usr/bin/env python3
"""Transform *_mod.exs files to add module qualifications to function names."""

import os
import re
import sys

TYPES_DIR = "/home/vivianyyd/type-synth/src/test/input/ocaml-stdlib/types"
EXS_DIR = "/home/vivianyyd/type-synth/src/test/input/ocaml-stdlib/exs"

# Module names for files that don't have a // ModuleName comment
FALLBACK_MODULE_NAMES = {
    "22_array_mod": "Array",
    "24_bool_mod": "Bool",
}


def get_module_name(types_base):
    """Get the OCaml module name for a mod.types file."""
    if types_base in FALLBACK_MODULE_NAMES:
        return FALLBACK_MODULE_NAMES[types_base]
    types_path = os.path.join(TYPES_DIR, types_base + ".types")
    with open(types_path) as f:
        first_line = f.readline().strip()
    if first_line.startswith("// ") and not first_line.startswith("// type") and not first_line.startswith("// TODO"):
        return first_line[3:].strip()
    return None


def extract_names_from_types(types_base):
    """Extract non-operator val names from a types file. Returns list of names."""
    types_path = os.path.join(TYPES_DIR, types_base + ".types")
    names = []
    with open(types_path) as f:
        for line in f:
            line = line.strip()
            if not line.startswith("val "):
                continue
            # Extract name: val <name> :
            rest = line[4:]  # after "val "
            # Skip operator names like (&&), (+), etc.
            if rest.startswith("("):
                continue
            # Name is everything up to " :"
            name_match = re.match(r"([A-Za-z_][A-Za-z0-9_.'']*)\s*:", rest)
            if name_match:
                names.append(name_match.group(1))
    return names


def get_lambda_params(line):
    """Extract lambda parameter names from a line (fun x1 -> ...)."""
    params = set()
    for m in re.finditer(r'\bfun\s+((?:[a-z][a-z0-9_]*\s+)+)->',  line):
        for p in m.group(1).split():
            params.add(p)
    return params


def transform_line(line, replacements, lambda_params):
    """Apply replacements to a single line, skipping lambda params."""
    # Apply replacements in order (longest names first to avoid partial matches)
    for old, new in replacements:
        if old in lambda_params:
            continue
        # Replace whole-word occurrences only
        # Use negative lookbehind/lookahead to avoid replacing inside dotted names
        # We want to replace `sqrt` but not `Float.sqrt` (already qualified)
        line = re.sub(r'(?<![A-Za-z0-9_.\'])' + re.escape(old) + r'(?![A-Za-z0-9_.\'])', new, line)
    return line


def process_file(exs_path, batch=None):
    """Process a single *_mod.exs file."""
    with open(exs_path) as f:
        lines = f.readlines()

    if not lines:
        return

    # Parse first line to get types files
    header = lines[0].strip()
    if not header.startswith("//"):
        return

    types_files = [t.strip() for t in header[2:].split(",")]

    # Find mod.types files and build replacement map
    # name -> (module_name, qualified_name)
    # Longest names first to avoid partial replacements
    name_to_module = {}

    for tf in types_files:
        # Handle typo in 75_weak_mod.exs: "75_weak_mod.exs" should be "75_weak_mod.types"
        tf = tf.replace(".exs", ".types")
        if not tf.endswith("_mod.types"):
            continue
        types_base = tf[:-6]  # remove ".types"
        module_name = get_module_name(types_base)
        if module_name is None:
            print(f"  WARNING: Could not determine module name for {types_base}")
            continue
        names = extract_names_from_types(types_base)
        for name in names:
            # Qualify: "sqrt" -> "Float.sqrt", "Array.make" -> "Float.Array.make"
            qualified = module_name + "." + name
            name_to_module[name] = qualified

    if not name_to_module:
        return

    # Sort replacements: longest names first to avoid partial matches
    replacements = sorted(name_to_module.items(), key=lambda x: -len(x[0]))

    # Transform lines
    new_lines = []
    for i, line in enumerate(lines):
        # Skip comment lines and first line
        stripped = line.strip()
        if i == 0 or stripped.startswith("//"):
            new_lines.append(line)
            continue
        lambda_params = get_lambda_params(line)
        new_line = transform_line(line, replacements, lambda_params)
        new_lines.append(new_line)

    with open(exs_path, "w") as f:
        f.writelines(new_lines)
    print(f"  Transformed {os.path.basename(exs_path)}")


def main():
    exs_files = sorted(f for f in os.listdir(EXS_DIR) if f.endswith("_mod.exs"))

    # Determine batch
    batch_start = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    batch_end = int(sys.argv[2]) if len(sys.argv) > 2 else len(exs_files)
    batch = exs_files[batch_start:batch_end]

    print(f"Processing files {batch_start} to {batch_end}: {[b for b in batch]}")
    for fname in batch:
        exs_path = os.path.join(EXS_DIR, fname)
        print(f"Processing {fname}...")
        process_file(exs_path)


if __name__ == "__main__":
    main()
