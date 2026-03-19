#!/usr/bin/env python3
"""Streaming detector for large timestamp gaps in dictchain logs."""
import argparse
import datetime as dt
import re
from typing import List, Optional, Tuple

TIMESTAMP_PATTERN = re.compile(r"\[(\d{2}:\d{2}:\d{2}(?:\.\d{1,6})?)\]")


def _parse_timestamp(ts: str) -> dt.datetime:
    if "." in ts:
        head, frac = ts.split(".", 1)
        frac = (frac + "000000")[:6]
        ts = f"{head}.{frac}"
    else:
        ts = f"{ts}.000000"
    return dt.datetime.strptime(ts, "%H:%M:%S.%f")


def find_gaps(
    path: str,
    sample_step: int,
    threshold_seconds: float,
    max_results: Optional[int] = None,
) -> List[Tuple[int, dt.datetime, str, int, dt.datetime, str, float]]:
    previous = None
    gaps = []

    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        for line_no, line in enumerate(handle, 1):
            if (line_no - 1) % sample_step != 0:
                continue

            match = TIMESTAMP_PATTERN.search(line)
            if not match:
                continue

            current_ts = _parse_timestamp(match.group(1))
            if previous is not None:
                diff_seconds = (current_ts - previous[1]).total_seconds()
                if diff_seconds >= threshold_seconds:
                    gaps.append(
                        (
                            previous[0],
                            previous[1],
                            previous[2],
                            line_no,
                            current_ts,
                            line.strip(),
                            diff_seconds,
                        )
                    )
            previous = (line_no, current_ts, line.strip())
    gaps.sort(key=lambda item: item[-1], reverse=True)
    if max_results is not None:
        gaps = gaps[:max_results]
    return gaps


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "path",
        nargs="?",
        default="dictchain-willBeOverwritten.log",
        help="Path to the log file",
    )
    parser.add_argument(
        "--sample-step",
        type=int,
        default=10,
        help="Inspect every Nth line (default: 10)",
    )
    parser.add_argument(
        "--threshold-hours",
        type=float,
        default=1.0,
        help="Gap threshold in hours (default: 1)",
    )
    parser.add_argument(
        "--max-results",
        type=int,
        default=5,
        help="Maximum number of gaps to report (default: 5, 0 = unlimited)",
    )
    args = parser.parse_args()

    if args.sample_step <= 0:
        raise SystemExit("sample step must be positive")
    if args.max_results < 0:
        raise SystemExit("max-results must be zero or positive")

    threshold_seconds = args.threshold_hours * 3600
    max_results = args.max_results or None
    gaps = find_gaps(args.path, args.sample_step, threshold_seconds, max_results)

    if not gaps:
        print(
            f"No gaps >= {args.threshold_hours:.2f}h found using sample step {args.sample_step}."
        )
        return

    print(
        "Sampled gaps >= {thr:.2f}h (showing {count}{limit})".format(
            thr=args.threshold_hours,
            count=len(gaps),
            limit="" if max_results is None else f" of max {args.max_results}",
        )
    )
    for idx, (
        start_line,
        start_ts,
        start_text,
        end_line,
        end_ts,
        end_text,
        diff_seconds,
    ) in enumerate(gaps, 1):
        hours = diff_seconds / 3600
        print(f"- Gap #{idx}: {diff_seconds:.0f}s (~{hours:.2f}h)")
        print(
            f"    Start line {start_line}: {start_ts.time()} (sample text: {start_text[:120]})"
        )
        print(
            f"    End line {end_line}: {end_ts.time()} (sample text: {end_text[:120]})"
        )
        print(f"    Sample step: {args.sample_step}")


if __name__ == "__main__":
    main()
