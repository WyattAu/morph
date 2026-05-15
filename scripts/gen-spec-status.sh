#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
SPECS_DIR="$ROOT_DIR/Morph/Specs"
REPORT_DIR="$ROOT_DIR/.reports"
REPORT_FILE="$REPORT_DIR/spec-status.md"

mkdir -p "$REPORT_DIR"

DATE="$(date +%Y-%m-%d)"

count_lines() {
    if [ -f "$1" ]; then
        wc -l < "$1" | tr -d ' '
    else
        echo "-"
    fi
}

count_matches() {
    local file="$1"
    local pattern="$2"
    local n
    n="$(grep -cE "$pattern" "$file" 2>/dev/null)" || n=0
    echo "$n"
}

echo "# Spec Module Status"
echo ""
echo "Generated: $DATE"
echo ""
echo "| Module | Spec | Lemmas | Examples | Theorems | Sorries | Status |"
echo "|--------|------|--------|----------|----------|---------|--------|"

while IFS= read -r dir; do
    module="$(basename "$dir")"
    [ "$module" = "README" ] && continue

    spec_file="$dir/Spec.lean"
    lemmas_file="$dir/Lemmas.lean"
    examples_file="$dir/Examples.lean"

    has_spec=false; has_lemmas=false; has_examples=false

    if [ -f "$spec_file" ]; then
        has_spec=true
        spec_lines="$(count_lines "$spec_file")"
    else
        spec_lines="-"
    fi

    if [ -f "$lemmas_file" ]; then
        has_lemmas=true
        lemmas_lines="$(count_lines "$lemmas_file")"
        theorems="$(count_matches "$lemmas_file" '^\s*(theorem|lemma) ')"
        sorry_count="$(count_matches "$lemmas_file" 'sorry')"
    else
        lemmas_lines="-"
        theorems=0
        sorry_count=0
    fi

    if [ -f "$examples_file" ]; then
        has_examples=true
        examples_lines="$(count_lines "$examples_file")"
        examples_sorry="$(count_matches "$examples_file" 'sorry')"
    else
        examples_lines="-"
        examples_sorry=0
    fi

    if $has_spec && $has_lemmas; then
        total_sorries="$((sorry_count + examples_sorry))"
        if [ "$total_sorries" -eq 0 ]; then
            status="Complete"
        else
            status="Partial"
        fi
        sorries="$total_sorries"
    elif $has_spec && ! $has_lemmas; then
        status="Stub"
        sorries="-"
        theorems="-"
    else
        status="Empty"
        sorries="-"
        theorems="-"
    fi

    spec_display="$spec_lines lines"
    lemmas_display="$lemmas_lines lines"
    examples_display="$examples_lines lines"

    echo "| $module | $spec_display | $lemmas_display | $examples_display | $theorems | $sorries | $status |"

done < <(find "$SPECS_DIR" -mindepth 1 -maxdepth 1 -type d | sort) | tee "$REPORT_FILE"
