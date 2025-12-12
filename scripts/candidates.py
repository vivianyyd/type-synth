def filter_lines(input_path, output_path):
    with open(input_path, "r", encoding="utf-8") as infile, \
         open(output_path, "w", encoding="utf-8") as outfile:
        
        for line in infile:
            # Find first occurrence of ']'
            
            if line.find('[') != 0:
                outfile.write(line)
                continue

            idx = line.find(']')
            if idx == -1:
                continue  # skip lines without ']'
            
            # Extract substring after it and trim
            substring = line[idx+1:].strip()
            
            # Check if it starts with "b:"
            if not substring.startswith("b:"):
                outfile.write(substring + "\n")


# Example usage:
filter_lines("tmp.log", "chain-plus-dummy-var")

