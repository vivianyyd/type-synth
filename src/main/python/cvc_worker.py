"""
Runs solver queries for callCVC (CVCFiles.kt), so cvc5 is imported once per worker, not once per
query.

Input on stdin: a Python script, then a line QUERY_END. Repeats.
Output on stdout: a line "ok" or "error", the script's output (on error, also its stderr and
traceback), then a line ANSWER_END.

Each script runs as __main__ in a fresh namespace and a fresh cvc5 context.
"""
import contextlib
import io
import sys
import traceback

import cvc5.pythonic.cvc5_pythonic as pythonic

# Must match CVCFiles.kt
QUERY_END = "#--- end of query ---"
ANSWER_END = "#--- end of answer ---"


def answer(script):
    # The context caches constants by name, so a reused one would hand out the last query's terms
    pythonic._main_ctx = None
    out = io.StringIO()
    err = io.StringIO()
    try:
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            exec(compile(script, "<query>", "exec"), {"__name__": "__main__"})
        return "ok", out.getvalue()
    except BaseException:
        return "error", out.getvalue() + err.getvalue() + traceback.format_exc()


def main():
    lines = []
    for line in sys.stdin:
        if line.rstrip("\n") != QUERY_END:
            lines.append(line)
            continue
        status, text = answer("".join(lines))
        lines = []
        # ANSWER_END has to start a line
        if text and not text.endswith("\n"):
            text += "\n"
        sys.stdout.write(f"{status}\n{text}{ANSWER_END}\n")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
