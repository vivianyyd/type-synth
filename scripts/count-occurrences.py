import sys

target = "chain: L1[V0, V1] -> L1[V1, V2] -> L1[V0, V2], dbb: L1[L0[], L0[]], dbi: L1[L0[], L8[]], dib: L1[L8[], L0[]], dii: L1[L8[], L8[]], i: L8[], put: L1[V0, V1] -> V0 -> V1 -> L1[V0, V1"
count = 0
lines = 0

with open(sys.argv[1], encoding="utf-8") as f:
    for i, line in enumerate(f, 1):
        lines += 1
        n = line.count(target)
        if n:
            print(f"Line {i}: {n} occurrence(s)")
            print(line.rstrip())
            count += n

print(f"\nTotal lines: {lines}")
print(f"Total occurrences: {count}")

