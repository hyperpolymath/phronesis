#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail

if [ "$#" -ne 3 ] || [ ! -d "$1" ]; then
  echo "Usage: $0 WORKSPACE RESULTS_FILE BLOCKING_FILE" >&2
  exit 2
fi

workspace=$1
results_file=$2
blocking_file=$3
file_list=$(mktemp)
trap 'rm -f "$file_list"' EXIT

: > "$results_file"
: > "$blocking_file"

# Match the source extensions and excluded directories in dogfood-gate.yml.
find "$workspace" \
  \( -type d \( -name .git -o -name node_modules -o -name .deno -o -name target \
    -o -name _build -o -name deps -o -name external_corpora -o -name .lake \) -prune \) -o \
  \( -type f \( -name '*.rs' -o -name '*.ex' -o -name '*.exs' -o -name '*.res' \
    -o -name '*.js' -o -name '*.ts' -o -name '*.json' -o -name '*.toml' \
    -o -name '*.yml' -o -name '*.yaml' -o -name '*.md' -o -name '*.adoc' \
    -o -name '*.idr' -o -name '*.zig' -o -name '*.v' -o -name '*.jl' \
    -o -name '*.gleam' -o -name '*.hs' -o -name '*.ml' -o -name '*.sh' \) -print0 \) > "$file_list"

# Search UTF-8 byte sequences so invalid UTF-8 cannot hide C0 or NUL bytes.
c0='[\x00-\x08\x0b\x0c\x0e-\x1f]'
invisible="$c0|\\xc2[\\xa0\\xad]|\\xe2\\x80[\\x8b-\\x8f\\xaa-\\xaf]|\\xe2\\x81[\\xa0\\xa6-\\xa9]|\\xef\\xbb\\xbf"
while IFS= read -r -d '' file; do
  if LC_ALL=C grep -aP "$invisible" -- "$file" > /dev/null; then
    printf '%s\0' "$file" >> "$results_file"
  else
    status=$?
    if [ "$status" -ne 1 ]; then exit "$status"; fi
  fi
  if LC_ALL=C grep -aP "$c0" -- "$file" > /dev/null; then
    printf '%s\0' "$file" >> "$blocking_file"
  else
    status=$?
    if [ "$status" -ne 1 ]; then exit "$status"; fi
  fi
done < "$file_list"
