#!/usr/bin/env python3

import re
import sys
import argparse
import json
import subprocess
from pathlib import Path
from find_next_tree import get_forester_json, find_next_tree, int_to_base36, BASE36

EXT   = ".tree"


# ----------------------------
# Argument parsing
# ----------------------------

parser = argparse.ArgumentParser(
    description="Rename author-prefixed tree files to STT-XXXX using forester JSON."
)
parser.add_argument(
    "author",
    help="Author prefix to replace (e.g. smi)"
)
parser.add_argument(
    "-c", "--cannonical",
    default="STT",
    help="The cannonical URL to insert onto, default=STT"
)

parser.add_argument(
    "dirs",
    nargs="+",
    help="Directories to scan recursively for .tree files"
)
parser.add_argument(
    "-n", "--dry-run",
    action="store_true",
    help="Show what would change, but do not modify anything"
)
parser.add_argument(
    "--gap",
    type=int,
    default=100,
    help="Number of new tree IDs needed"
)

args = parser.parse_args()

AUTHOR = args.author.lower()
DIRS = [Path(d) for d in args.dirs]
DRY_RUN = args.dry_run
GAP = args.gap
CANNON = args.cannonical

# ----------------------------
# Find first tree
# ----------------------------
all_trees = get_forester_json()
next_val = find_next_tree(CANNON, all_trees, GAP)
print(f"Starting STT value: {int_to_base36(next_val)}")


# ----------------------------
# Build rename map
# ----------------------------
rename_map = {}

auth_re = re.compile(rf"{AUTHOR}-(\w{{4}})$", re.IGNORECASE)

author_trees = [auth_re.search(tree["uri"]).group(1)
                for tree in all_trees
                if auth_re.search(tree.get("uri", ""))]

author_trees.sort(key=lambda x: int(x, 36))

print("\nBuilding a remaping: \n")

for tid in author_trees:
    new_num = int_to_base36(next_val)
    old_key = f"{AUTHOR}-{tid}"
    new_key = f"{CANNON}-{new_num}"
    rename_map[old_key.lower()] = new_key
    print(f"{old_key} → {new_key}")
    next_val += 1

# ----------------------------
# Collect .tree files
# ----------------------------
tree_files = []
for d in DIRS:
    tree_files.extend(d.rglob("*.tree"))

auth_re = re.compile(rf"{AUTHOR}-(\w{{4}})\.tree$", re.IGNORECASE)
author_files = [(p, m.group(1).upper())
                for p in tree_files if (m := auth_re.search(p.name))]

author_files.sort(key=lambda x: int(x[1], 36))


# ----------------------------
# Update references in files
# ----------------------------

print("\nUpdating references in files:\n")

subtree_re = re.compile(rf"(\\subtree\[)({AUTHOR}-\w{{4}})(\])", re.IGNORECASE)
link_re = re.compile(rf"{AUTHOR}-\w{{4}}", re.IGNORECASE)

for tree in tree_files:
    text = tree.read_text(encoding="utf-8")
    updated = subtree_re.sub(lambda m: m.group(1) + rename_map.get(m.group(2).lower(), m.group(2)) + m.group(3), text)
    if updated != text:
        print(f"Updating references in {tree}")
        if not DRY_RUN:
            tree.write_text(updated, encoding="utf-8")



# ----------------------------
# Rename files
# ----------------------------

print("\nRenaming files:\n")

for path, num in author_files:
    new_path = path.with_name(f"{rename_map[f'{AUTHOR}-{num}'.lower()]}.tree")
    print(f"Renaming {path} → {new_path}")
    if not DRY_RUN:
        path.rename(new_path)
