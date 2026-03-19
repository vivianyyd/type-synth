#!/usr/bin/env python3
import sys
from collections import defaultdict

def analyze(file_path, normalize=False):
    lines = defaultdict(list)

    with open(file_path, encoding="utf-8") as f:
        for i, line in enumerate(f, 1):
            # if 'BEG' in line or 'END' in line or 'Elapsed' in line or 'Counts' in line:
            if 'BEG' in line or 'Elapsed' in line or 'Counts' in line:
                continue
            text = line.rstrip("\n")
            before, sep, after = text.partition('\t')
            after_tab = after if sep else line
            if after_tab:
                lines[after_tab].append(i)

    return lines


def main():
    if len(sys.argv) < 3:
        print("Usage: script.py <file> [unique|dups|count]")
        sys.exit(1)

    file, mode = sys.argv[1], sys.argv[2]
    data = analyze(file)

    if mode == "count":
        print(len(data))

    elif mode == "unique":
        for line, nums in data.items():
            if len(nums) == 1:
                print(f"{line!r} at line {nums[0]}")

    elif mode == "dups":
        for line, nums in data.items():
            if len(nums) > 1:
                print(f"{line!r} → lines {nums}")

    else:
        print("Unknown mode")


if __name__ == "__main__":
    main()
