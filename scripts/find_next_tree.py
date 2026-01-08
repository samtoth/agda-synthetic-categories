#!/usr/bin/env python3
"""
Utility to determine the next available Forester URI with a specified gap.
"""

import json
import subprocess
import re
import argparse

BASE36 = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"

def base36_to_int(s: str) -> int:
    n = 0
    for c in s:
        n = n * 36 + BASE36.index(c.upper())
    return n

def int_to_base36(n: int, width=4) -> str:
    if n == 0:
        return "0".zfill(width)
    out = ""
    while n:
        n, r = divmod(n, 36)
        out = BASE36[r] + out
    return out.zfill(width)

def get_forester_json() -> list:
    """Run `forester query all` and parse JSON output."""
    try:
        result = subprocess.run(
            ["forester", "query", "all"],
            capture_output=True,
            text=True,
            check=True
        )
    except subprocess.CalledProcessError as e:
        print("Error running `forester query all`:", e)
        exit(1)

    # Skip any leading info lines
    stdout = result.stdout
    json_start = stdout.find("[{")
    if json_start == -1:
        print("No JSON array found in forester output", file=sys.stderr)
        exit(1)
    json_text = stdout[json_start:]

    try:
        return json.loads(json_text)
    except json.JSONDecodeError as e:
        print("Failed to parse JSON from forester output:", e)
        exit(1)

def find_next_tree(prefix, all_trees: list, gap: int) -> int:
    """Return the next available STT number as int."""
    stt_re = re.compile(rf"{prefix}-(\w{{4}})$", re.IGNORECASE)
    stt_numbers = []

    for tree in all_trees:
        uri = tree.get("uri", "")
        m = stt_re.match(uri)
        if m:
            stt_numbers.append(base36_to_int(m.group(1)))

    if not stt_numbers:
        return 0

    stt_numbers.sort()
    # Find the first gap that is at least `gap` long
    i = 1
    while i < len(stt_numbers) and (stt_numbers[i] - stt_numbers[i-1] < gap):
        i += 1

    next_val = stt_numbers[i-1] + 1
    return next_val




def main():
    parser = argparse.ArgumentParser(
        description="Find the next usable tree ID with optional gap."
    )
    parser.add_argument(
        "-g", "--gap",
        type=int,
        default=50,
        help="Number of empty slots to leave before next treeID (default: 50)"
    )
    parser.add_argument(
        "-p", "--prefix",
	default="stt",
        help="The tree prefix to search for (absent = stt)"
    )
    args = parser.parse_args()

    all_trees = get_forester_json()
    next_val = find_next_tree(args.prefix, all_trees, args.gap)

    print(f"{args.prefix}-{int_to_base36(next_val)}")

if __name__ == "__main__":
    main()
