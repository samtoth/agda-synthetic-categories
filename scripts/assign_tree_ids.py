#!/usr/bin/env python3

import re
import sys
import argparse
import json
import subprocess
from pathlib import Path
from find_next_tree import list_all_trees, find_next_tree, int_to_base36, BASE36

EXT = ".tree"


# ----------------------------
# Argument parsing
# ----------------------------

parser = argparse.ArgumentParser(
    description="Rename prefixed tree files to stt-XXXX using forester JSON."
)
parser.add_argument("prefix", help="Prefix to replace (e.g. smi)")
parser.add_argument(
    "-c",
    "--canonical",
    default="stt",
    help="The canonical prefix to insert onto, default=stt",
)

parser.add_argument(
    "dirs", nargs="+", help="Directories to scan recursively for .tree files"
)
parser.add_argument(
    "-n",
    "--dry-run",
    action="store_true",
    help="Show what would change, but do not modify anything",
)
parser.add_argument("--gap", type=int, default=50, help="Number of new tree IDs needed")

args = parser.parse_args()

PREFIX = args.prefix
DIRS = [Path(d) for d in args.dirs]
DRY_RUN = args.dry_run
GAP = args.gap
CANON = args.canonical

# ----------------------------
# Find first tree
# ----------------------------
all_trees = list_all_trees()
next_val = find_next_tree(CANON, all_trees, GAP)
print(f"Starting STT value: {int_to_base36(next_val)}")

# ----------------------------
# Build rename map
# ----------------------------
rename_map = {}

prefix_re = re.compile(rf"{PREFIX}-(\w{{4}})$", re.IGNORECASE)

prefix_trees = [
    prefix_re.search(tree).group(1) for tree in all_trees if prefix_re.search(tree)
]

prefix_trees.sort(key=lambda x: int(x, 36))

print("\nBuilding a remapping: \n")

for tid in prefix_trees:
    new_num = int_to_base36(next_val)
    old_key = f"{PREFIX}-{tid}"
    new_key = f"{CANON}-{new_num}"
    rename_map[old_key] = new_key
    print(f"{old_key} → {new_key}")
    next_val += 1

# ----------------------------
# Collect .tree files
# ----------------------------
tree_files = []
for d in DIRS:
    tree_files.extend(d.rglob("*.tree"))

prefix_file_re = re.compile(rf"{PREFIX}-(\w{{4}})\.tree$")
prefix_files = [(p, m.group(1)) for p in tree_files if (m := prefix_file_re.search(p.name))]

prefix_files.sort(key=lambda x: int(x[1], 36))


# ----------------------------
# Update references in files
# ----------------------------

print("\nUpdating references in files:\n")

# subtree_re = re.compile(rf"(\\subtree\[)({PREFIX}-\w{{4}})(\])", re.IGNORECASE)
link_re = re.compile(rf"({PREFIX}-\w{{4}})", re.IGNORECASE)

for tree in tree_files:
    text = tree.read_text(encoding="utf-8")
    updated = link_re.sub(lambda m: rename_map.get(m.group(1)), text)
    if updated != text:
        print(f"Updating references in {tree}")
        if not DRY_RUN:
            tree.write_text(updated, encoding="utf-8")


# ----------------------------
# Rename files
# ----------------------------

print("\nRenaming files:\n")

for path, num in prefix_files:
    new_path = path.with_name(f"{rename_map[f'{PREFIX}-{num}']}.tree")
    print(f"Renaming {path} → {new_path}")
    if not DRY_RUN:
        path.rename(new_path)
