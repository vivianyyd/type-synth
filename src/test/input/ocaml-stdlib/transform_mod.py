#!/usr/bin/env python3
"""
Transform *_mod.exs files to add module qualifications to function/value names.

For each name in the exs file:
  - If from a *_mod.types file only -> prefix with ModuleName.
  - If from a non-mod types file only -> leave as-is.
  - If ambiguous -> type inference based on arguments.
  - Sub-module names like "Array.make" in Float types -> "Float.Array.make"
  - Sub-module names like "K1.make" in Ephemeron types -> "Ephemeron.K1.make"
"""

import re
import sys
from pathlib import Path

TYPES_DIR = Path("/home/vivianyyd/type-synth/src/test/input/ocaml-stdlib/types")
EXS_DIR = Path("/home/vivianyyd/type-synth/src/test/input/ocaml-stdlib/exs")

MODULE_OVERRIDES = {
    "22_array_mod.types": "Array",
    "24_bool_mod.types": "Bool",
}


def get_module_name(types_filename):
    if types_filename in MODULE_OVERRIDES:
        return MODULE_OVERRIDES[types_filename]
    filepath = TYPES_DIR / types_filename
    if not filepath.exists():
        return None
    with open(filepath) as f:
        first_line = f.readline().strip()
    if first_line.startswith("//"):
        name = first_line[2:].strip()
        parts = name.split()
        return parts[0] if parts else None
    return None


def parse_names_from_types_file(types_filename):
    filepath = TYPES_DIR / types_filename
    if not filepath.exists():
        return []
    names = []
    with open(filepath) as f:
        for line in f:
            line = line.strip()
            if line.startswith("val "):
                rest = line[4:]
                colon_idx = rest.find(" : ")
                if colon_idx >= 0:
                    name = rest[:colon_idx].strip()
                    type_sig = rest[colon_idx + 3:].strip()
                    names.append((name, type_sig))
    return names


def is_operator(name):
    return name.startswith("(") and name.endswith(")")


def tokenize(s):
    tokens = []
    i = 0
    while i < len(s):
        c = s[i]
        if c in ' \t\n\r':
            i += 1
        elif c == '(':
            j = i + 1
            while j < len(s) and s[j] != ')' and s[j] != '(':
                j += 1
            if j < len(s) and s[j] == ')':
                inner = s[i+1:j]
                if inner and all(c2 in '=<>+-*/^&|!@#%~. ' for c2 in inner):
                    tokens.append(('atom', s[i:j+1]))
                    i = j + 1
                    continue
            tokens.append(('open', '('))
            i += 1
        elif c == ')':
            tokens.append(('close', ')'))
            i += 1
        else:
            j = i
            while j < len(s) and s[j] not in ' \t\n\r()':
                j += 1
            tokens.append(('atom', s[i:j]))
            i = j
    return tokens


def parse_sexp(tokens, pos):
    if pos >= len(tokens):
        return None, pos
    kind, val = tokens[pos]
    if kind == 'atom':
        return val, pos + 1
    elif kind == 'open':
        children = []
        pos += 1
        while pos < len(tokens) and tokens[pos][0] != 'close':
            child, pos = parse_sexp(tokens, pos)
            if child is not None:
                children.append(child)
        if pos < len(tokens):
            pos += 1
        return children, pos
    return None, pos + 1


def sexp_to_str(sexp):
    if isinstance(sexp, str):
        return sexp
    return "(" + " ".join(sexp_to_str(c) for c in sexp) + ")"


# Type tags
T_FLOAT = "float"
T_INT = "int"
T_STR = "str"
T_BOOL = "bool"
T_CHAR = "char"
T_MOD = "mod"      # module-specific type (like Complex.t, Array.t, etc.)
T_UNIT = "unit"
T_UNK = "unknown"

def sig_return_type_str(sig):
    """Extract the return type string from a type sig, handling nested parens."""
    depth = 0
    last_arrow = -1
    i = 0
    while i < len(sig):
        if sig[i] == '(':
            depth += 1
        elif sig[i] == ')':
            depth -= 1
        elif sig[i:i+2] == '->' and depth == 0:
            last_arrow = i
            i += 2
            continue
        i += 1
    if last_arrow >= 0:
        return sig[last_arrow+2:].strip()
    return sig.strip()


def classify_ret(ret_str):
    ret = ret_str.strip()
    if ret == 'float' or ret.startswith('float ') or ret == 'float option':
        return T_FLOAT
    if ret == 'int' or ret == 'int option':
        return T_INT
    if ret == 'string' or ret == 'string option':
        return T_STR
    if ret == 'bool':
        return T_BOOL
    if ret == 'char':
        return T_CHAR
    if ret == 'unit':
        return T_UNIT
    # Module-specific types
    return T_MOD


def first_param_type_str(sig):
    """Get the first parameter's type string."""
    # If no arrow, it's a value
    depth = 0
    i = 0
    while i < len(sig):
        if sig[i] == '(':
            depth += 1
        elif sig[i] == ')':
            depth -= 1
        elif sig[i:i+2] == '->' and depth == 0:
            return sig[:i].strip()
        i += 1
    return None  # no arrow = value


class ModuleQualifier:
    def __init__(self, exs_file):
        self.exs_file = Path(exs_file)
        self.exs_filename = self.exs_file.name

        with open(self.exs_file) as f:
            first_line = f.readline().strip()

        types_files = []
        if first_line.startswith("//"):
            parts = first_line[2:].strip().split(",")
            for p in parts:
                p = p.strip()
                if p.endswith(".exs"):
                    p = p[:-4] + ".types"
                if p.endswith(".types"):
                    types_files.append(p)

        self.types_files = types_files
        self.mod_types_files = [f for f in types_files if f.endswith("_mod.types")]
        self.nonmod_types_files = [f for f in types_files if not f.endswith("_mod.types")]

        exs_stem = self.exs_filename.replace(".exs", "")
        primary_mod_file = exs_stem + ".types"
        self.primary_mod_file = primary_mod_file if primary_mod_file in self.mod_types_files else None
        self.primary_module = get_module_name(primary_mod_file) if self.primary_mod_file else None

        # name -> list of (module_name, type_sig)
        self.name_to_module = {}
        # name -> type_sig for non-mod names
        self.nonmod_name_types = {}
        self.nonmod_names = set()

        for tf in self.nonmod_types_files:
            for name, type_sig in parse_names_from_types_file(tf):
                self.nonmod_names.add(name)
                self.nonmod_name_types[name] = type_sig

        for tf in self.mod_types_files:
            mod_name = get_module_name(tf)
            if mod_name is None:
                continue
            for name, type_sig in parse_names_from_types_file(tf):
                if name not in self.name_to_module:
                    self.name_to_module[name] = []
                self.name_to_module[name].append((mod_name, type_sig))

        self.ambiguous_names = set(self.name_to_module.keys()) & self.nonmod_names

        # Submodule-prefixed names (e.g. "Array.make" in Float, "K1.make" in Ephemeron)
        # These appear as atoms in the exs file and need the parent module prepended
        self.submod_names = {}
        for name, mods in self.name_to_module.items():
            if "." in name:
                mod_name = mods[0][0]
                self.submod_names[name] = f"{mod_name}.{name}"

        # Build set of all names from mod types (without dots) for type inference
        # i.e. names whose return type is T_MOD (module-specific)
        self.mod_returning_names = set()
        for name, mods in self.name_to_module.items():
            if "." not in name:
                _, sig = mods[0]
                ret = sig_return_type_str(sig)
                if classify_ret(ret) == T_MOD:
                    self.mod_returning_names.add(name)

        # Constants of type T_MOD (no arguments)
        self.mod_constants = set()
        for name, mods in self.name_to_module.items():
            if "." not in name:
                _, sig = mods[0]
                if first_param_type_str(sig) is None:
                    ret = classify_ret(sig_return_type_str(sig))
                    if ret == T_MOD:
                        self.mod_constants.add(name)

    def infer_type(self, sexp):
        """
        Infer the output type of an sexp.
        Returns one of T_FLOAT, T_INT, T_STR, T_BOOL, T_MOD, T_UNIT, T_UNK.
        """
        if isinstance(sexp, str):
            atom = sexp
            if atom == "Flt":
                return T_FLOAT
            if atom == "Num":
                return T_INT
            if atom == "Str":
                return T_STR
            if atom in ("true", "false"):
                return T_BOOL
            if atom == "Char":
                return T_CHAR
            if atom in ("Unit", "[]"):
                return T_UNK
            if re.match(r'^[a-z][a-zA-Z0-9_]*\d+$', atom):
                return T_UNK
            if is_operator(atom):
                return T_UNK

            # Check mod constants first (e.g. Complex.zero -> T_MOD)
            if atom in self.mod_constants:
                return T_MOD
            # Check non-mod constants
            if atom in self.nonmod_name_types and atom not in self.name_to_module:
                sig = self.nonmod_name_types[atom]
                if first_param_type_str(sig) is None:
                    return classify_ret(sig_return_type_str(sig))
            # Module constants that aren't in nonmod
            if atom in self.name_to_module and atom not in self.nonmod_names:
                _, sig = self.name_to_module[atom][0]
                if first_param_type_str(sig) is None:
                    return classify_ret(sig_return_type_str(sig))
            return T_UNK

        if isinstance(sexp, list) and len(sexp) >= 1:
            head = sexp[0]
            args = sexp[1:]

            if isinstance(head, str) and head == "fun":
                return T_UNK

            if isinstance(head, str):
                return self.infer_call_type(head, args)

        return T_UNK

    def infer_call_type(self, funcname, args):
        """Infer the return type of a function call."""
        if is_operator(funcname):
            # Comparison operators return bool, arithmetic return int
            if funcname in ('(=)', '(<>)', '(<)', '(>)', '(<=)', '(>=)', '(==)', '(!=)', '(&&)', '(||)'):
                return T_BOOL
            return T_UNK

        # For submodule names like "Array.make" -> return type from sig
        if funcname in self.name_to_module:
            _, sig = self.name_to_module[funcname][0]
            return classify_ret(sig_return_type_str(sig))

        # Look up in nonmod types
        if funcname in self.nonmod_name_types:
            sig = self.nonmod_name_types[funcname]
            return classify_ret(sig_return_type_str(sig))

        return T_UNK

    def is_mod_type_arg(self, sexp):
        """Check if sexp is likely a module-specific type (not float/int/str/bool)."""
        t = self.infer_type(sexp)
        return t == T_MOD

    def resolve_name(self, name, args):
        """Given a name and its call arguments, return the qualified name."""
        # Already dotted: submodule name
        if "." in name:
            if name in self.submod_names:
                return self.submod_names[name]
            return name

        # Not in any mod types -> leave as-is
        if name not in self.name_to_module:
            return name

        # Only in mod types (unambiguous) -> always qualify
        if name not in self.ambiguous_names:
            mods = self.name_to_module[name]
            mod_name = mods[0][0]
            return f"{mod_name}.{name}"

        # Ambiguous: need type inference
        return self.disambiguate(name, args)

    def disambiguate(self, name, args):
        """Disambiguate an ambiguous name using argument type inference."""
        mod_entries = self.name_to_module[name]
        mod_name = mod_entries[0][0]
        mod_type_sig = mod_entries[0][1]

        # Infer arg types
        arg_types = [self.infer_type(a) for a in args]

        # Get what type the mod version's first param expects
        first_param = first_param_type_str(mod_type_sig)

        if first_param is None:
            # It's a constant - if in mod_constants, return qualified
            if name in self.mod_constants:
                return f"{mod_name}.{name}"
            return name

        # Check if mod version expects a float (concrete, not polymorphic)
        mod_expects_float = ("float" in first_param) and ("'a" not in first_param)
        # Check if mod version expects char
        mod_expects_char = (first_param.strip() in ('char', 't')) and ("char" in mod_type_sig or "char" in (TYPES_DIR / self.primary_mod_file).read_text() if self.primary_mod_file else False)
        # Check if mod version expects a module-specific type (like Complex.t, t)
        # Heuristic: if first_param is short like "t" or contains no common stdlib types
        mod_expects_modtype = (
            first_param in ('t', "'k", "'d") or
            (first_param not in ('int', 'float', 'string', 'bool', 'char', 'unit', "'a", "'b", "'c") and
             "int" not in first_param and "float" not in first_param and
             "string" not in first_param and "bool" not in first_param and
             "char" not in first_param and "'a" not in first_param)
        )

        # Check if nonmod version is polymorphic
        nonmod_sig = self.nonmod_name_types.get(name, "")
        nonmod_is_polymorphic = "'a" in nonmod_sig

        has_float_arg = T_FLOAT in arg_types
        has_char_arg = T_CHAR in arg_types
        has_mod_arg = T_MOD in arg_types

        if mod_expects_float:
            # Use mod version only if we have float args
            if has_float_arg:
                return f"{mod_name}.{name}"
            else:
                return name
        elif mod_expects_modtype:
            # Use mod version if we have a mod-type arg or a char arg (for Char module 't' = char)
            if has_mod_arg or has_char_arg:
                return f"{mod_name}.{name}"
            else:
                return name
        else:
            # Both are polymorphic (e.g. compare in Array vs 1_comparison)
            # For array-style compare: first arg is a comparator function
            # If first arg is a function (lambda or function name), use mod version
            # We'll check if the mod sig has a higher-order parameter
            has_higher_order = "-> " in (first_param or "") and "->" in first_param
            if has_higher_order and args:
                first_arg = args[0]
                # If first arg is a function (starts with fun or is a known function name)
                if isinstance(first_arg, list) and first_arg and first_arg[0] == "fun":
                    return f"{mod_name}.{name}"
                if isinstance(first_arg, str) and (
                    first_arg in self.nonmod_name_types or
                    first_arg in self.name_to_module or
                    is_operator(first_arg)
                ):
                    return f"{mod_name}.{name}"
            # Default: leave unqualified
            return name

    def transform_sexp(self, sexp, parent_func=None, arg_position=None):
        """Recursively transform an s-expression."""
        if isinstance(sexp, str):
            return self.resolve_name(sexp, [])

        if not isinstance(sexp, list) or len(sexp) == 0:
            return sexp

        head = sexp[0]
        rest = sexp[1:]

        # (fun param -> body): don't transform params
        if isinstance(head, str) and head == "fun" and "->" in rest:
            arrow_idx = rest.index("->")
            params = rest[:arrow_idx]
            body_parts = rest[arrow_idx+1:]
            new_body = [self.transform_sexp(b) for b in body_parts]
            return ["fun"] + params + ["->"] + new_body

        # Transform head with knowledge of args (for disambiguation)
        if isinstance(head, str):
            new_head = self.resolve_name(head, rest)
        else:
            new_head = self.transform_sexp(head)

        # Determine if head is a higher-order function whose func-args
        # need context to qualify properly.
        # For float_mod context, function arguments like `abs`, `sqrt`, `succ`
        # passed to Float.Array.map/iter/etc. should be Float-qualified IF
        # the higher-order function works on floats.
        hof_expects_float_func = self.head_hof_expects_float_func(head, new_head, rest)

        new_args = []
        for i, a in enumerate(rest):
            if i == 0 and hof_expects_float_func and isinstance(a, str):
                # This arg is a function expected to be float->* or float->float
                # Qualify it as a Float function if it's ambiguous
                new_a = self.qualify_as_float_func(a)
            else:
                new_a = self.transform_sexp(a)
            new_args.append(new_a)

        return [new_head] + new_args

    def head_hof_expects_float_func(self, head_orig, head_qualified, args):
        """
        Check if the (qualified) head is a higher-order function expecting float->* as first arg.
        E.g. Float.Array.map expects (float -> float) as first arg.
        """
        if not isinstance(head_orig, str):
            return False
        # Look up the type sig of head_orig in mod types (use the qualified name's module)
        name = head_orig
        if name in self.name_to_module:
            _, sig = self.name_to_module[name][0]
            first_param = first_param_type_str(sig)
            if first_param and "float" in first_param and "->" in first_param:
                return True
        return False

    def qualify_as_float_func(self, name):
        """If name is ambiguous and has a Float version, return Float.name."""
        if is_operator(name):
            return name
        if name in self.ambiguous_names:
            mods = self.name_to_module[name]
            mod_name = mods[0][0]
            return f"{mod_name}.{name}"
        if name in self.name_to_module and name not in self.nonmod_names:
            mods = self.name_to_module[name]
            mod_name = mods[0][0]
            return f"{mod_name}.{name}"
        return name


def transform_line(line, qualifier):
    stripped = line.rstrip("\n")
    if not stripped.strip() or stripped.strip().startswith("//"):
        return line

    tokens = tokenize(stripped)
    pos = 0
    result_parts = []

    while pos < len(tokens):
        sexp, pos = parse_sexp(tokens, pos)
        if sexp is None:
            break
        transformed = qualifier.transform_sexp(sexp)
        result_parts.append(sexp_to_str(transformed))

    if result_parts:
        return " ".join(result_parts) + "\n"
    return line


def transform_file(exs_path, dry_run=False):
    qualifier = ModuleQualifier(exs_path)

    with open(exs_path) as f:
        lines = f.readlines()

    result = []
    if lines:
        result.append(lines[0])

    for i, line in enumerate(lines[1:], 1):
        stripped = line.strip()
        if stripped.startswith("//") or not stripped:
            result.append(line)
        else:
            result.append(transform_line(line, qualifier))

    if not dry_run:
        with open(exs_path, "w") as f:
            f.writelines(result)

    return qualifier, result


TARGET_FILES = [
    "22_array_mod.exs",
    "23_atomic_mod.exs",
    "24_bool_mod.exs",
    "25_buffer_mod.exs",
    "26_bytes_mod.exs",
    "27_callback_mod.exs",
    "28_char_mod.exs",
    "29_complex_mod.exs",
    "30_condition_mod.exs",
    "31_digest_mod.exs",
    "32_domain_mod.exs",
    "33_dynarray_mod.exs",
    "34_effect_mod.exs",
    "35_either_mod.exs",
    "36_ephemeron_mod.exs",
    "37_filename_mod.exs",
    "38_float_mod.exs",
    "39_format_mod.exs",
    "40_fun_mod.exs",
    "41_gc_mod.exs",
]


if __name__ == "__main__":
    dry_run = "--dry-run" in sys.argv

    for filename in TARGET_FILES:
        exs_path = EXS_DIR / filename
        if not exs_path.exists():
            print(f"SKIP (not found): {filename}")
            continue
        qualifier, result = transform_file(exs_path, dry_run=dry_run)
        print(f"{'[DRY] ' if dry_run else ''}Transformed {filename}: module={qualifier.primary_module}, "
              f"ambiguous={qualifier.ambiguous_names}")
