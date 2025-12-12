import sys

def print_unique_lines(filename):
    seen = {}
    with open(filename, 'r', encoding='utf-8') as file:
        for lineno, line in enumerate(file, start=1):
            clean_line = line.replace('<', '').replace('>', '').strip()
            if clean_line:
                seen.setdefault(clean_line, []).append(lineno)

    for line_text, lines in seen.items():
        if len(lines) == 1:
            print(f"Unique line: '{line_text}' at line {lines[0]}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python script.py <filename>")
        sys.exit(1)
    print_unique_lines(sys.argv[1])

