import sys

def print_context(filename, line_number, context=10):
    with open(filename, 'r') as file:
        lines = file.readlines()
        
    start = max(line_number - context - 1, 0)
    end = min(line_number + context, len(lines))
    
    for i in range(start, end):
        print(lines[i], end='')

if len(sys.argv) != 3:
    print(f"Usage: python {sys.argv[0]} <filename> <line_number>")
    sys.exit(1)

filename = sys.argv[1]
line_number = int(sys.argv[2])

print_context(filename, line_number)

