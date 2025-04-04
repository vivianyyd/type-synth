import sys
import re

def extract_blocks(filename):
    with open(filename, 'r', encoding='utf-8') as file:
        content = file.read()
    
    blocks = re.findall(r'// FUNCTION START(.*?)// FUNCTION END', content, re.DOTALL)
    block_dict = {}
    for block in blocks:
        block = block.replace(';', '')  # Remove semicolons
        lines = block.strip().split('\n')  # Split into lines
        if lines and lines[0].startswith("void "):
            name = lines[0].split()[1]  # Extract block name
            block_dict[name] = lines
    
    return block_dict

if __name__ == "__main__":
    filename = sys.argv[1]
    blocks = extract_blocks(filename)
    
    with open("src/main/sketch/concretize/concretetypes.sk", 'r', encoding='utf-8') as file:
        lib = file.read()
    
    blocks = {name: lines for name, lines in blocks.items() if name not in lib and name != "_main"}    
    for name, lines in blocks.items():
        print("\n".join(lines))
        print()

