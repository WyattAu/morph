#!/usr/bin/env bash
# Differential verdicts: Lean `morph` vs Rust `morph`.
#
# Usage: tests/differential/diff.sh [lean_bin] [rust_bin]
#   lean_bin defaults to .lake/build/bin/morph (repo root)
#   rust_bin defaults to ./target/debug/morph (repo root, `cargo build -p morph`)
#
# For each manifest row, runs both binaries and normalizes the exit code to a
# verdict (0 = ok, anything else = fail). Any mismatch against the manifest
# is reported; the script exits nonzero if any case mismatches.
set -u

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
LEAN_BIN=${1:-"$ROOT/.lake/build/bin/morph"}
RUST_BIN=${2:-"$ROOT/target/debug/morph"}
DIR=$(cd "$(dirname "$0")" && pwd)

total=0
bad=0
while read -r file lcmd lwant rcmd rwant; do
  case "$file" in \#*|"") continue ;; esac
  total=$((total + 1))
  "$LEAN_BIN" "$lcmd" "$DIR/$file" >/dev/null 2>&1
  if [ $? -eq 0 ]; then lact=ok; else lact=fail; fi
  "$RUST_BIN" "$rcmd" "$DIR/$file" >/dev/null 2>&1
  if [ $? -eq 0 ]; then ract=ok; else ract=fail; fi
  if [ "$lact" != "$lwant" ] || [ "$ract" != "$rwant" ]; then
    bad=$((bad + 1))
    echo "MISMATCH $file: lean $lact (want $lwant), rust $ract (want $rwant)"
  else
    echo "ok       $file: lean $lact, rust $ract"
  fi
done < "$DIR/manifest.tsv"

echo "---"
echo "$((total - bad))/$total cases match the manifest"
[ "$bad" -eq 0 ]
