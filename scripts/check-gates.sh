#!/usr/bin/env bash
# Build-quality gates for Morph.
#
# Every gate here is blocking: a non-zero exit means the tree must not be
# committed or pushed. The same rules run in CI, so a local pass means a CI
# pass on these steps.
#
# Gates:
#   1. Lean build has no errors, no warnings in Morph sources, no compiler-
#      reported `sorry`, and no spec stubs.
#   2. `scripts/cross-ref-validate.sh` passes: every `import Morph.*`
#      resolves, every markdown link in `spec/` and `docs/` resolves, every
#      ADR reference resolves.
#   3. `spec-tools check-links spec/` reports zero broken links (skipped when
#      spec-tools is not installed).
#
# Usage:
#   scripts/check-gates.sh                # run the build, then the link gates
#   scripts/check-gates.sh BUILD_LOG      # reuse an existing lake build log
#
# Reusing a log is what the pre-commit hook does: it has just built, and
# rebuilding would double the hook's cost.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT" || exit 1

FAILED=0
TMP_LOG=""

note() { printf '%s\n' "$*"; }
fail() {
    FAILED=1
    printf 'GATE FAILED: %s\n' "$*"
}

cleanup() {
    if [ -n "$TMP_LOG" ] && [ -f "$TMP_LOG" ]; then
        rm -f "$TMP_LOG"
    fi
}
trap cleanup EXIT

# --- Gate 1: build ----------------------------------------------------------
BUILD_LOG="${1:-}"
if [ -n "$BUILD_LOG" ] && [ -f "$BUILD_LOG" ]; then
    note "[1/3] Using build log $BUILD_LOG"
else
    note "[1/3] Building Morph and Morph.Tests..."
    TMP_LOG=$(mktemp /tmp/morph_gates_build_XXXXXX.log)
    BUILD_LOG="$TMP_LOG"
    if ! timeout 900 lake build Morph Morph.Tests > "$BUILD_LOG" 2>&1; then
        note "Build output (tail):"
        tail -20 "$BUILD_LOG"
        fail "lake build Morph Morph.Tests"
    fi
fi

if grep -q '^error:' "$BUILD_LOG"; then
    note "First 10 errors:"
    grep '^error:' "$BUILD_LOG" | head -10
    fail "build errors"
fi

# Warnings in Morph sources are a gate (loop 81). Compiler-reported `sorry`
# is excluded here and covered on its own so the message names the cause.
MORPH_WARNINGS=$(grep 'Morph/.*warning:' "$BUILD_LOG" \
    | grep -v "warning: declaration uses 'sorry'" || true)
if [ -n "$MORPH_WARNINGS" ]; then
    note "Warnings:"
    printf '%s\n' "$MORPH_WARNINGS" | head -20
    fail "Morph sources contain $(printf '%s\n' "$MORPH_WARNINGS" | wc -l) build warning(s)"
fi

if grep -q "declaration uses 'sorry'" "$BUILD_LOG"; then
    grep "declaration uses 'sorry'" "$BUILD_LOG" | head -20
    fail "compiler-reported 'sorry'"
fi

# Prose mentions of `sorry` (quotations in doc comments) are filtered the way
# CI filters them, so "0 \`sorry\`" in a status comment is not a failure.
SORRY_HITS=$(grep -rn "sorry" Morph/ --include="*.lean" 2>/dev/null \
    | grep -v "no \`sorry\`" \
    | grep -v "sorry placeholders" \
    | grep -v "requires.*sorry" || true)
if [ -n "$SORRY_HITS" ]; then
    printf '%s\n' "$SORRY_HITS" | head -20
    fail "'sorry' token found in Morph sources"
fi

STUB_HITS=$(grep -rn "example : True := trivial" Morph/Specs/ --include="*.lean" 2>/dev/null || true)
if [ -n "$STUB_HITS" ]; then
    printf '%s\n' "$STUB_HITS" | head -10
    fail "spec stubs ('example : True := trivial')"
fi

# --- Gate 2: cross-references ----------------------------------------------
note "[2/3] Validating imports, markdown links, and ADR references..."
XREF_LOG=$(mktemp /tmp/morph_gates_xref_XXXXXX.log)
if bash scripts/cross-ref-validate.sh > "$XREF_LOG" 2>&1; then
    note "      $(grep -E '^Total:' "$XREF_LOG" | tail -1)"
else
    grep -E '^  FAIL' "$XREF_LOG" | head -20
    grep -E '^Total:' "$XREF_LOG" | tail -1
    fail "cross-reference validation"
fi
rm -f "$XREF_LOG"

# --- Gate 3: spec link checker ---------------------------------------------
SPEC_TOOLS=""
if [ -x ".venv/bin/spec-tools" ]; then
    SPEC_TOOLS=".venv/bin/spec-tools"
elif command -v spec-tools >/dev/null 2>&1; then
    SPEC_TOOLS="spec-tools"
fi

if [ -n "$SPEC_TOOLS" ]; then
    note "[3/3] Checking spec links with spec-tools..."
    LINK_LOG=$(mktemp /tmp/morph_gates_links_XXXXXX.log)
    if timeout 300 "$SPEC_TOOLS" check-links spec/ > "$LINK_LOG" 2>&1; then
        BROKEN=$(grep '^Broken links:' "$LINK_LOG" | awk '{print $3}')
        if [ "${BROKEN:-0}" != "0" ]; then
            grep -A2 '^Broken Links:' "$LINK_LOG" | head -20
            fail "spec-tools reports ${BROKEN} broken link(s)"
        else
            note "      0 broken links"
        fi
    else
        tail -5 "$LINK_LOG"
        fail "spec-tools check-links"
    fi
    rm -f "$LINK_LOG"
else
    note "[3/3] spec-tools not installed (skipped; gate 2 still covers links)."
fi

# --- Summary ---------------------------------------------------------------
if [ "$FAILED" -ne 0 ]; then
    note ""
    note "Gates FAILED."
    exit 1
fi

note ""
note "All gates passed."
exit 0
