import sys
import re

def main(filename):
    with open(filename, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    # Ignore the first line
    lines = lines[1:]

    # Regex to extract sign and content inside "(+ ...)" or "(- ...)"
    pattern = re.compile(r'^\(\s*([+-])\s\(*(.*?)\s*\)\)$')

    parsed = []
    plus_contents = set()

    for line in lines:
        line = line.strip()
        m = pattern.match(line)
        if not m:
            continue  # skip malformed lines
        sign, content = m.groups()
        parsed.append((line, sign, content))
        if sign == '+':
            plus_contents.add(content)

    # Filter: remove any line whose content is strictly contained
    # in some (+ ...) content
    results = []
    for line, sign, content in parsed:
        if any(content != pc and content in pc for pc in plus_contents):
            continue
        results.append(line)

    for r in results:
        print(r)

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <filename>")
        sys.exit(1)
    main(sys.argv[1])

