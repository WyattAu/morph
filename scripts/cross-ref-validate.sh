#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PASS=0
FAIL=0

pass() { PASS=$((PASS + 1)); echo "  PASS: $1"; }
fail() { FAIL=$((FAIL + 1)); echo "  FAIL: $1"; }

echo "=== Cross-Reference Validation ==="
echo "Repo root: $REPO_ROOT"
echo ""

echo "--- 1. Lean Import Resolution ---"
while IFS='|' read -r file import; do
  [ -z "$import" ] && continue

  dots_to_slashes="${import//./\/}"
  candidate="${REPO_ROOT}/${dots_to_slashes}.lean"

  if [ -f "$candidate" ]; then
    pass "${file}: import ${import}"
  else
    fail "${file}: import ${import} -> ${candidate} not found"
  fi
done < <(grep -rn '^import Morph\.' --include="*.lean" "$REPO_ROOT/Morph" "$REPO_ROOT/TestVars.lean" "$REPO_ROOT/Morph.lean" 2>/dev/null | sed 's/^\([^:]*:[^:]*\):.*import \(Morph[^ ]*\).*/\1|\2/' || true)

echo ""
echo "--- 2. Markdown Link Validation (spec/ docs/) ---"
while IFS='|' read -r file link_path; do
  [ -z "$link_path" ] && continue

  if [[ "$link_path" == http://* ]] || [[ "$link_path" == https://* ]] || [[ "$link_path" == "#"* ]]; then
    continue
  fi

  link_dir="$(dirname "$file")"
  target="${link_dir}/${link_path}"

  if [ -f "$target" ] || [ -d "$target" ]; then
    pass "${file}: [text](${link_path})"
  else
    fail "${file}: [text](${link_path}) -> ${target} not found"
  fi
done < <(grep -rn '\[.*\]([^)]*)' --include="*.md" "$REPO_ROOT/spec" "$REPO_ROOT/docs" 2>/dev/null | sed 's/^\([^:]*:[^:]*\):.*\](\([^)]*\)).*/\1|\2/' || true)

echo ""
echo "--- 3. ADR Reference Validation ---"
while IFS='|' read -r file_line ref; do
  [ -z "$ref" ] && continue

  adr_dir="$REPO_ROOT/.specs/02_adrs"
  found=0
  for f in "$adr_dir"/${ref}-*.md; do
    if [ -f "$f" ]; then
      found=1
      break
    fi
  done

  if [ "$found" -eq 1 ]; then
    pass "${file_line}: ${ref} -> $(basename "$f")"
  else
    fail "${file_line}: ${ref} -> no matching ADR file in .specs/02_adrs/"
  fi
done < <(grep -rn 'ADR-[0-9]\{3\}' --include="*.md" "$REPO_ROOT/spec" "$REPO_ROOT/docs" "$REPO_ROOT/.specs" 2>/dev/null | sed 's/^\([^:]*:[^:]*\):.*\(ADR-[0-9]\{3\}\).*/\1|\2/' | sort -u -t'|' -k2,2 -k1,1 || true)

echo ""
echo "=== Summary ==="
TOTAL=$((PASS + FAIL))
echo "Total: ${TOTAL}  PASS: ${PASS}  FAIL: ${FAIL}"

if [ "$FAIL" -gt 0 ]; then
  exit 1
fi
exit 0
