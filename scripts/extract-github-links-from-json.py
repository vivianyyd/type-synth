import json
import sys

# json from https://api.github.com/search/repositories?q=language:Haskell&sort=stars&order=desc&per_page=30

def extract_urls(json_file):
    with open(json_file, 'r') as f:
        data = json.load(f)
    for item in data.get("items", []):
        url = item.get("html_url")
        if url:
            print(url)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <github_json_file>")
        sys.exit(1)
    extract_urls(sys.argv[1])

