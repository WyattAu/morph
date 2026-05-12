#!/usr/bin/env bash
set -euo pipefail

REPORT_DIR=".reports/regression"
mkdir -p "$REPORT_DIR"
TIMESTAMP=$(date +%Y%m%d-%H%M%S)
REPORT="$REPORT_DIR/snapshot-$TIMESTAMP.txt"

echo "Morph Regression Snapshot - $(date)" | tee "$REPORT"
echo "================================" | tee -a "$REPORT"

echo "" | tee -a "$REPORT"
lake build Morph 2>&1 | tee /tmp/morph_regression_build.log
ERRORS=$(grep -c "^error:" /tmp/morph_regression_build.log 2>/dev/null || echo "0")
WARNINGS=$(grep -c "warning:" /tmp/morph_regression_build.log 2>/dev/null || echo "0")
echo "errors: $ERRORS" | tee -a "$REPORT"
echo "warnings: $WARNINGS" | tee -a "$REPORT"

SORRIES=$(grep -r "sorry" Morph/ --include="*.lean" | grep -v "\.olean" | grep -v "/--" | wc -l)
echo "sorries: $SORRIES" | tee -a "$REPORT"

STUBS=$(grep -r "example : True := trivial" Morph/Specs/ --include="*.lean" 2>/dev/null | wc -l)
echo "stubs: $STUBS" | tee -a "$REPORT"

echo "" | tee -a "$REPORT"
lake build Morph.Tests 2>&1 | tee -a "$REPORT" | tail -1

echo "" | tee -a "$REPORT"
echo "Snapshot saved to $REPORT"
