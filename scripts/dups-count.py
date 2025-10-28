import sys
# sys.argv[1]


from collections import defaultdict

filename = sys.argv[1] 

line_map = defaultdict(list)

# Read file and record line numbers
with open(filename, "r") as f:
    for i, line in enumerate(f, start=1):
        line = line.rstrip("\n")
        line_map[line].append(i)

# Find and display duplicates
print("Duplicated lines (unique):\n")
for line, nums in line_map.items():
    if len(nums) > 1:
        print(f"{line!r}  →  lines {nums}")

