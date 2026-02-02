import sys
from haskell_to_python import *

def clean(s: str) -> str:
    return '\n'.join(line.rstrip() for line in s.strip().splitlines())

if len(sys.argv) < 2:
    print("Usage: python haskell_to_python.py input.hs > output.py", file=sys.stderr)
    print("Or: import translate_haskell_to_python from this module.", file=sys.stderr)
    sys.exit(1)
with open(sys.argv[1], 'r') as f:
    src = f.read()
    src = clean(src)
    src = src.split("\n\n")
    py = ["from dataclasses import dataclass"]
    for chunk in src:
        if chunk.startswith("import") or chunk.startswith("module"):
            continue
        parsed = apply_safe_names(parse_hs_top_level(chunk))
        py.append(translate_top_level(parsed))
    py = "\n\n".join(py)
    print(py)