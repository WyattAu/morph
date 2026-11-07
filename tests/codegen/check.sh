# Usage: tests/codegen/check.sh [morph_bin]
#
# Accept: `morph run` prints the manifest value, `morph build --codegen=cranelift`
# exits 0, writes the artifact, and the artifact never returns the prologue's
# register (loop 151: `%v0` is undefined in the text).
#
# Reject: `morph build` exits 1, prints exactly the recorded message, and writes
# no artifact.
set -u

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
BIN=${1:-"$ROOT/.lake/build/bin/morph"}
DIR=$(cd "$(dirname "$0")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

total=0
bad=0

fail() {
  bad=$((bad + 1))
  echo "MISMATCH $1: $2"
}

while IFS=$'\t' read -r file want; do
  case "$file" in \#*|"") continue ;; esac
  total=$((total + 1))
  cp "$DIR/corpus/$file" "$TMP/$file"
  got=$("$BIN" run "$TMP/$file" 2>&1)
  if [ $? -ne 0 ] || [ "$got" != "$want" ]; then
    fail "corpus/$file" "run printed '$got', want '$want'"
    continue
  fi
  if ! "$BIN" build --codegen=cranelift "$TMP/$file" >/dev/null 2>&1; then
    fail "corpus/$file" "build rejected an in-subset program"
    continue
  fi
  af="$TMP/${file%.hum}.clif"
  if [ ! -f "$af" ]; then
    fail "corpus/$file" "build exited 0 but wrote no artifact"
    continue
  fi
  if grep -q 'return %v0' "$af"; then
    fail "corpus/$file" "artifact returns %v0, which no instruction defines"
    continue
  fi
  echo "ok       corpus/$file: $want"
done < "$DIR/manifest.tsv"

while IFS=$'\t' read -r file want; do
  case "$file" in \#*|"") continue ;; esac
  total=$((total + 1))
  cp "$DIR/rejects/$file" "$TMP/$file"
  got=$("$BIN" build --codegen=cranelift "$TMP/$file" 2>&1 >/dev/null)
  if [ $? -ne 1 ]; then
    fail "rejects/$file" "expected exit 1"
    continue
  fi
  if [ "$got" != "$want" ]; then
    fail "rejects/$file" "printed '$got', want '$want'"
    continue
  fi
  if [ -f "$TMP/${file%.hum}.clif" ]; then
    fail "rejects/$file" "wrote an artifact while rejecting"
    continue
  fi
  echo "ok       rejects/$file: rejected with the recorded message"
done < "$DIR/rejects.tsv"

echo "---"
echo "$((total - bad))/$total cases match the corpus"
[ "$bad" -eq 0 ]
