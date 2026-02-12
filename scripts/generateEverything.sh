#!/bin/bash
set -euo pipefail

tmp_file="$(mktemp)"
trap 'rm -f "$tmp_file"' EXIT

echo "module Everything where" > "$tmp_file"

find src -type f -name '*.lagda.tree' | \
  grep -v "Everything" | sort | \
  sed -re 's@src/@@g;s@.lagda.tree@@g;s@/@.@g;s@^@open import @g;s@$@@g' \
  >> "$tmp_file"

find src -type f -name '*.agda' | \
  grep -v "Everything" | sort | \
  sed -re 's@src/@@g;s@.agda@@g;s@/@.@g;s@^@open import @g;s@$@@g' \
  >> "$tmp_file"

if [ ! -f src/Everything.agda ] || ! cmp -s "$tmp_file" src/Everything.agda; then
  mv "$tmp_file" src/Everything.agda
else
  rm -f "$tmp_file"
fi
