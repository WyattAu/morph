#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
REPORT_DIR="$PROJECT_ROOT/.reports/regression"
BUILD_LOG="/tmp/morph_regression_build.log"

mkdir -p "$REPORT_DIR"

TIMESTAMP=$(date +%Y%m%d-%H%M%S)
ISO_TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%S")
SNAPSHOT="$REPORT_DIR/snapshot-$TIMESTAMP.json"

LEAN_VERSION=$(lean --version 2>/dev/null | grep -oP 'version \K[^,]+' || echo "unknown")

echo "=== Morph Regression Snapshot ==="
echo "  timestamp : $ISO_TIMESTAMP"
echo "  lean      : $LEAN_VERSION"
echo ""

echo "Building Morph..."
LAKE_BUILD_OUTPUT=$(lake build Morph 2>&1 || true)
echo "$LAKE_BUILD_OUTPUT" > "$BUILD_LOG"

BUILD_ERRORS=$(grep -c "^error:" "$BUILD_LOG" 2>/dev/null || true)
BUILD_ERRORS="${BUILD_ERRORS:-0}"
BUILD_WARNINGS=$(grep -c "warning:" "$BUILD_LOG" 2>/dev/null || true)
BUILD_WARNINGS="${BUILD_WARNINGS:-0}"
echo "  build errors   : $BUILD_ERRORS"
echo "  build warnings : $BUILD_WARNINGS"

echo "Counting sorries..."
SORRY_COUNT=$(grep -r "sorry" "$PROJECT_ROOT/Morph/" --include="*.lean" \
  | grep -v "\.olean" \
  | grep -v "/--" \
  | wc -l | tr -d ' ')
echo "  sorry count    : $SORRY_COUNT"

echo "Counting spec stubs..."
STUB_COUNT=$(grep -r "example : True := trivial" "$PROJECT_ROOT/Morph/Specs/" --include="*.lean" 2>/dev/null \
  | wc -l | tr -d ' ' || true)
STUB_COUNT="${STUB_COUNT:-0}"
echo "  stub count     : $STUB_COUNT"

echo "Running Python tests..."
VENV_PYTHON="$PROJECT_ROOT/.venv/bin/python"
if [ ! -f "$VENV_PYTHON" ]; then
  VENV_PYTHON="python"
fi
PYTEST_OUTPUT=$("$VENV_PYTHON" -m pytest "$PROJECT_ROOT/scripts/tests/" -q --tb=no 2>&1 || true)
PY_PASSED=$(echo "$PYTEST_OUTPUT" | grep -oP '\d+ passed' | grep -oP '\d+' || echo 0)
PY_FAILED=$(echo "$PYTEST_OUTPUT" | grep -oP '\d+ failed' | grep -oP '\d+' || echo 0)
echo "  python passed  : $PY_PASSED"
echo "  python failed  : $PY_FAILED"

COVERAGE_PCT="null"
if "$VENV_PYTHON" -c "import coverage" &>/dev/null; then
  COVERAGE_OUTPUT=$("$VENV_PYTHON" -m coverage report 2>/dev/null || echo "")
  if [ -n "$COVERAGE_OUTPUT" ]; then
    COVERAGE_PCT=$(echo "$COVERAGE_OUTPUT" | grep "^TOTAL" | awk '{print $NF}' | tr -d '%' || echo "null")
  fi
fi
echo "  coverage       : ${COVERAGE_PCT}%"

LEAN_MODULES=$(find "$PROJECT_ROOT/Morph" -name "*.lean" | wc -l | tr -d ' ')
echo "  lean modules   : $LEAN_MODULES"

SPEC_MODULES=$(find "$PROJECT_ROOT/Morph/Specs" -name "*.lean" | wc -l | tr -d ' ')
echo "  spec modules   : $SPEC_MODULES"

cat > "$SNAPSHOT" <<EOF
{
  "timestamp": "$ISO_TIMESTAMP",
  "lean_version": "$LEAN_VERSION",
  "metrics": {
    "build_errors": $BUILD_ERRORS,
    "build_warnings": $BUILD_WARNINGS,
    "sorry_count": $SORRY_COUNT,
    "stub_count": $STUB_COUNT,
    "python_tests_passed": $PY_PASSED,
    "python_tests_failed": $PY_FAILED,
    "python_coverage_pct": $COVERAGE_PCT,
    "lean_modules": $LEAN_MODULES,
    "spec_modules": $SPEC_MODULES
  }
}
EOF

echo ""
echo "Snapshot saved to $SNAPSHOT"

PREV_SNAPSHOT=$(ls -t "$REPORT_DIR"/snapshot-*.json 2>/dev/null | head -2 | tail -1 || true)
if [ -n "$PREV_SNAPSHOT" ] && [ "$PREV_SNAPSHOT" != "$SNAPSHOT" ]; then
  echo ""
  echo "=== Comparison with previous snapshot ==="
  echo "  previous: $(basename "$PREV_SNAPSHOT")"
  echo ""

  REGRESSIONS=0
  IMPROVEMENTS=0

  for METRIC in build_errors build_warnings sorry_count stub_count python_tests_failed; do
    PREV_VAL=$("$VENV_PYTHON" -c "import json; print(json.load(open('$PREV_SNAPSHOT'))['metrics']['$METRIC'])" 2>/dev/null || echo "?")
    CURR_VAL=$("$VENV_PYTHON" -c "import json; print(json.load(open('$SNAPSHOT'))['metrics']['$METRIC'])" 2>/dev/null || echo "?")

    if [ "$PREV_VAL" = "?" ] || [ "$CURR_VAL" = "?" ]; then
      echo "  $METRIC: $CURR_VAL (prev: $PREV_VAL)"
      continue
    fi

    if [ "$CURR_VAL" -gt "$PREV_VAL" ]; then
      echo "  $METRIC: $CURR_VAL (prev: $PREV_VAL) *** REGRESSION ***"
      REGRESSIONS=$((REGRESSIONS + 1))
    elif [ "$CURR_VAL" -lt "$PREV_VAL" ]; then
      echo "  $METRIC: $CURR_VAL (prev: $PREV_VAL) (improved)"
      IMPROVEMENTS=$((IMPROVEMENTS + 1))
    else
      echo "  $METRIC: $CURR_VAL (unchanged)"
    fi
  done

  for METRIC in python_tests_passed python_coverage_pct lean_modules spec_modules; do
    PREV_VAL=$("$VENV_PYTHON" -c "import json; print(json.load(open('$PREV_SNAPSHOT'))['metrics']['$METRIC'])" 2>/dev/null || echo "?")
    CURR_VAL=$("$VENV_PYTHON" -c "import json; print(json.load(open('$SNAPSHOT'))['metrics']['$METRIC'])" 2>/dev/null || echo "?")

    if [ "$PREV_VAL" = "?" ] || [ "$CURR_VAL" = "?" ]; then
      echo "  $METRIC: $CURR_VAL (prev: $PREV_VAL)"
      continue
    fi

    if [ "$CURR_VAL" -lt "$PREV_VAL" ]; then
      echo "  $METRIC: $CURR_VAL (prev: $PREV_VAL) *** REGRESSION ***"
      REGRESSIONS=$((REGRESSIONS + 1))
    elif [ "$CURR_VAL" -gt "$PREV_VAL" ]; then
      echo "  $METRIC: $CURR_VAL (prev: $PREV_VAL) (improved)"
      IMPROVEMENTS=$((IMPROVEMENTS + 1))
    else
      echo "  $METRIC: $CURR_VAL (unchanged)"
    fi
  done

  echo ""
  if [ "$REGRESSIONS" -gt 0 ]; then
    echo "  RESULT: $REGRESSIONS regression(s) detected!"
  else
    echo "  RESULT: No regressions. All clear."
  fi
  if [ "$IMPROVEMENTS" -gt 0 ]; then
    echo "  IMPROVEMENTS: $IMPROVEMENTS metric(s) improved."
  fi
else
  echo "  No previous JSON snapshot found for comparison."
fi

echo ""
echo "Done."
