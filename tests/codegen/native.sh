# Usage: tests/codegen/native.sh [morph_clif_bin] [morph_bin]
#
# The stage B differential (item B8), over the accepted corpus:
#
#   .hum --morph build--> .clif --morph-clif--> .o --cc--> native -> stdout
#                                                                    |
#   .hum --morph run------------------------------------------> value
#
# The Lean value is the oracle: it is recorded in manifest.tsv, produced by the
# verified evaluator, and compared against what the *native* program prints. Any
# mismatch is a divergence between the proved-relative pipeline and the trusted
# Cranelift path, which is the one thing this stage can measure.
set -u

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
DIR=$(cd "$(dirname "$0")" && pwd)
LEAN_BIN=${2:-"$ROOT/.lake/build/bin/morph"}

if [ $# -ge 1 ]; then
  CLIF_BIN=$1
else
  TGT=$(cd "$ROOT" && cargo metadata --format-version 1 --no-deps 2>/dev/null |
    sed -n 's/.*"target_directory": *"\([^"]*\)".*/\1/p')
  CLIF_BIN="$TGT/debug/morph-clif"
fi

if [ ! -x "$CLIF_BIN" ]; then
  echo "no morph-clif at $CLIF_BIN (cargo build -p morph-codegen)" >&2
  exit 1
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

total=0
bad=0

while IFS=$'\t' read -r file want; do
  case "$file" in \#*|"") continue ;; esac
  total=$((total + 1))
  cp "$DIR/corpus/$file" "$TMP/$file"

  if ! "$LEAN_BIN" build --codegen=cranelift "$TMP/$file" >/dev/null 2>&1; then
    bad=$((bad + 1)); echo "MISMATCH $file: morph build rejected it"; continue
  fi
  if ! "$CLIF_BIN" "$TMP/${file%.hum}.clif" >/dev/null 2>&1; then
    bad=$((bad + 1)); echo "MISMATCH $file: morph-clif failed on the artifact"; continue
  fi
  exe="$TMP/${file%.hum}-native"
  if [ ! -x "$exe" ]; then
    bad=$((bad + 1)); echo "MISMATCH $file: no native executable"; continue
  fi
  got=$("$exe")
  if [ "$got" != "$want" ]; then
    bad=$((bad + 1)); echo "MISMATCH $file: native printed '$got', lean says '$want'"
    continue
  fi
  echo "ok       $file: native $got = lean $want"
done < "$DIR/manifest.tsv"

echo "---"
echo "$((total - bad))/$total programs agree natively"
[ "$bad" -eq 0 ]
