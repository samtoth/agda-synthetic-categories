#!/usr/bin/env bash

DIR="${1:-.}"

PATTERN='subtree\[stt-[0-9A-Z]{4}\]'

grep --include='*.lagda.tree' -rnoP "$PATTERN" "$DIR" \
  | awk -F: '
    {
      match($0, /(stt-[0-9A-Z]{4})/, m)
      if (m[1] != "") {
        id = m[1]
        occurrences[id] = occurrences[id] "\n  " $1 ":" $2
        counts[id]++
      }
    }
    END {
      for (id in counts) {
        if (counts[id] > 1) {
          printf "DUPLICATE %s (%d occurrences):\n%s\n\n", id, counts[id], occurrences[id]
        }
      }
    }
  '
