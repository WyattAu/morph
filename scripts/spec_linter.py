#!/usr/bin/env python3
"""
Specification Linter for Morph Project

Validates specification documents against the specification convention defined in
docs/conventions/specification_convention.md

Usage:
    python scripts/spec_linter.py [options] <file_or_directory>

Examples:
    python scripts/spec_linter.py spec/language/ast_graph_spec.md
    python scripts/spec_linter.py --fix spec/
    python scripts/spec_linter.py --verbose --strict spec/
"""

import argparse
import os
import re
import sys
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import List, Dict, Set, Tuple, Optional
from datetime import datetime


class Severity(Enum):
    """Error severity levels"""
    ERROR = "ERROR"
    WARNING = "WARNING"
    INFO = "INFO"


@dataclass
class LintError:
    """Represents a linting error or warning"""
    file_path: str
    line_number: int
    severity: Severity
    rule_id: str
    message: str
    suggestion: Optional[str] = None

    def __str__(self) -> str:
        location = f"{self.file_path}:{self.line_number}"
        severity_str = f"[{self.severity.value}]"
        result = f"{location} {severity_str} {self.rule_id}: {self.message}"
        if self.suggestion:
            result += f"\n  Suggestion: {self.suggestion}"
        return result


@dataclass
class LintResult:
    """Result of linting a file"""
    file_path: str
    errors: List[LintError] = field(default_factory=list)
    passed: bool = True

    @property
    def error_count(self) -> int:
        return sum(1 for e in self.errors if e.severity == Severity.ERROR)

    @property
    def warning_count(self) -> int:
        return sum(1 for e in self.errors if e.severity == Severity.WARNING)

    @property
    def info_count(self) -> int:
        return sum(1 for e in self.errors if e.severity == Severity.INFO)


class SpecLinter:
    """Main linter class for specification files"""

    # Valid status values
    VALID_STATUSES = {"Draft", "Active", "Deprecated"}

    # Mandatory sections
    MANDATORY_SECTIONS = [
        "Introduction",
        "Formal Definitions",
        "Requirements",
        "Design",
        "Correctness Properties",
        "Examples"
    ]

    # EARS pattern keywords
    EARS_KEYWORDS = {
        "THE system SHALL",
        "WHEN",
        "WHILE",
        "WHERE"
    }

    # Valid Mermaid diagram types
    VALID_MERMAID_TYPES = {
        "sequenceDiagram",
        "stateDiagram-v2",
        "flowchart",
        "erDiagram",
        "classDiagram",
        "gantt",
        "pie",
        "gitGraph"
    }

    def __init__(self, strict: bool = False, verbose: bool = False):
        self.strict = strict
        self.verbose = verbose
        self.errors: List[LintError] = []
        self.requirement_ids: Set[str] = set()

    def lint_file(self, file_path: str) -> LintResult:
        """Lint a single specification file"""
        result = LintResult(file_path=file_path)
        self.errors = []
        self.requirement_ids = set()

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
        except Exception as e:
            result.errors.append(LintError(
                file_path=file_path,
                line_number=0,
                severity=Severity.ERROR,
                rule_id="FILE-001",
                message=f"Failed to read file: {e}"
            ))
            result.passed = False
            return result

        # Run all validation checks
        self._validate_document_header(file_path, lines)
        self._validate_section_structure(file_path, lines)
        self._validate_requirements(file_path, lines)
        self._validate_mathematical_notation(file_path, lines)
        self._validate_cross_references(file_path, lines)
        self._validate_mermaid_diagrams(file_path, lines)
        self._validate_change_log(file_path, lines)
        self._validate_markdown_formatting(file_path, lines)

        result.errors = self.errors
        result.passed = all(e.severity != Severity.ERROR for e in self.errors)
        return result

    def _validate_document_header(self, file_path: str, lines: List[str]) -> None:
        """Validate the document header"""
        if not lines:
            self.errors.append(LintError(
                file_path=file_path,
                line_number=1,
                severity=Severity.ERROR,
                rule_id="HDR-001",
                message="File is empty"
            ))
            return

        # Check for title (first line should be # Title)
        if not lines[0].strip().startswith("# "):
            self.errors.append(LintError(
                file_path=file_path,
                line_number=1,
                severity=Severity.ERROR,
                rule_id="HDR-002",
                message="First line must be a title (# Title)",
                suggestion="Add a title line: # [Specification Title]"
            ))

        # Check for header block (lines 2-20 should contain header fields)
        header_fields = {
            "File": r"\* File:\s*\`spec/[^\`]+\`",
            "Version": r"\* Version:\s*\d+\.\d+\.\d+",
            "Context": r"\* Context:\s*Layer \d+",
            "Formalism": r"\* Formalism:",
            "Status": r"\* Status:\s*(Draft|Active|Deprecated)",
            "Last Modified": r"\* Last Modified:\s*\d{4}-\d{2}-\d{2}",
            "Author": r"\* Author:",
            "Reviewers": r"\* Reviewers:"
        }

        header_text = ''.join(lines[:20])
        filename = os.path.basename(file_path)

        for field_name, pattern in header_fields.items():
            if not re.search(pattern, header_text):
                self.errors.append(LintError(
                    file_path=file_path,
                    line_number=2,
                    severity=Severity.ERROR,
                    rule_id=f"HDR-{field_name.upper()[0:3]}",
                    message=f"Missing or invalid header field: {field_name}",
                    suggestion=f"Add: * {field_name}: [value]"
                ))

        # Validate version format (Semantic Versioning)
        version_match = re.search(r"\* Version:\s*(\d+\.\d+\.\d+)", header_text)
        if version_match:
            version = version_match.group(1)
            try:
                major, minor, patch = map(int, version.split('.'))
                if major < 0 or minor < 0 or patch < 0:
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=2,
                        severity=Severity.ERROR,
                        rule_id="HDR-VER",
                        message="Version numbers must be non-negative integers"
                    ))
            except ValueError:
                self.errors.append(LintError(
                    file_path=file_path,
                    line_number=2,
                    severity=Severity.ERROR,
                    rule_id="HDR-VER",
                    message="Invalid version format (must be MAJOR.MINOR.PATCH)"
                ))

        # Validate file path matches actual filename
        file_match = re.search(r"\* File:\s*\`spec/([^\`]+)\`", header_text)
        if file_match:
            expected_filename = file_match.group(1)
            if expected_filename != filename:
                self.errors.append(LintError(
                    file_path=file_path,
                    line_number=2,
                    severity=Severity.ERROR,
                    rule_id="HDR-PATH",
                    message=f"File path in header ({expected_filename}) does not match actual filename ({filename})",
                    suggestion=f"Update header to: * File: `spec/{filename}`"
                ))

        # Validate status
        status_match = re.search(r"\* Status:\s*(\w+)", header_text)
        if status_match:
            status = status_match.group(1)
            if status not in self.VALID_STATUSES:
                self.errors.append(LintError(
                    file_path=file_path,
                    line_number=2,
                    severity=Severity.ERROR,
                    rule_id="HDR-STS",
                    message=f"Invalid status: {status}. Must be one of: {', '.join(self.VALID_STATUSES)}"
                ))

    def _validate_section_structure(self, file_path: str, lines: List[str]) -> None:
        """Validate section structure and hierarchy"""
        sections = {}
        section_numbers = set()

        # Extract all sections
        for i, line in enumerate(lines, 1):
            match = re.match(r'^(#{1,4})\s+(\d+(?:\.\d+)*)\.\s+(.+)$', line)
            if match:
                level = len(match.group(1))
                number = match.group(2)
                title = match.group(3).strip()
                sections[i] = {
                    'level': level,
                    'number': number,
                    'title': title
                }
                section_numbers.add(number)

        # Check for mandatory sections
        found_sections = {s['title'] for s in sections.values()}
        for mandatory in self.MANDATORY_SECTIONS:
            if mandatory not in found_sections:
                self.errors.append(LintError(
                    file_path=file_path,
                    line_number=1,
                    severity=Severity.ERROR,
                    rule_id="SEC-MAN",
                    message=f"Missing mandatory section: {mandatory}",
                    suggestion=f"Add section: ## 1. {mandatory}"
                ))

        # Validate section numbering
        sorted_sections = sorted(sections.items())
        for i, (line_num, section) in enumerate(sorted_sections):
            # Check that section numbers are sequential
            expected_num = str(i + 1)
            if section['number'] != expected_num:
                self.errors.append(LintError(
                    file_path=file_path,
                    line_number=line_num,
                    severity=Severity.WARNING,
                    rule_id="SEC-NUM",
                    message=f"Section number {section['number']} does not match expected {expected_num}"
                ))

            # Check heading level hierarchy
            if i > 0:
                prev_section = sorted_sections[i - 1][1]
                if section['level'] > prev_section['level'] + 1:
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=line_num,
                        severity=Severity.WARNING,
                        rule_id="SEC-HIE",
                        message=f"Heading level skipped (from {prev_section['level']} to {section['level']})"
                    ))

    def _validate_requirements(self, file_path: str, lines: List[str]) -> None:
        """Validate requirements using EARS pattern"""
        in_requirements_section = False
        requirement_pattern = re.compile(r'\*\s+([A-Z]{3,4}-[A-Z]{3}-\d{3}):\s*\*\*\s*(.+?)(?:\s*\*\*)?$')

        for i, line in enumerate(lines, 1):
            # Check if we're in the Requirements section
            if re.match(r'^##\s+3\.\s+Requirements', line):
                in_requirements_section = True
            elif re.match(r'^##\s+\d+\.\s+', line) and not re.match(r'^##\s+3\.', line):
                in_requirements_section = False

            if not in_requirements_section:
                continue

            # Check for requirement identifiers
            req_match = requirement_pattern.match(line)
            if req_match:
                req_id = req_match.group(1)
                req_text = req_match.group(2)

                # Check for duplicate requirement IDs
                if req_id in self.requirement_ids:
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=i,
                        severity=Severity.ERROR,
                        rule_id="REQ-DUP",
                        message=f"Duplicate requirement ID: {req_id}"
                    ))
                self.requirement_ids.add(req_id)

                # Validate requirement ID format
                if not re.match(r'^[A-Z]{3,4}-[A-Z]{3}-\d{3}$', req_id):
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=i,
                        severity=Severity.ERROR,
                        rule_id="REQ-IDF",
                        message=f"Invalid requirement ID format: {req_id}. Expected: XXX-REQ-NNN"
                    ))

                # Check for EARS pattern
                has_ears = any(keyword in req_text for keyword in self.EARS_KEYWORDS)
                if not has_ears:
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=i,
                        severity=Severity.WARNING,
                        rule_id="REQ-EARS",
                        message=f"Requirement {req_id} does not follow EARS pattern",
                        suggestion="Use patterns like: THE system SHALL..., WHEN..., WHILE..., WHERE..."
                    ))

                # Check for required attributes (Priority, Verification Method, etc.)
                # Look ahead for attributes in next few lines
                next_lines = lines[i:i+10]
                has_priority = any("Priority:" in l for l in next_lines)
                has_verification = any("Verification Method:" in l for l in next_lines)

                if not has_priority:
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=i,
                        severity=Severity.WARNING,
                        rule_id="REQ-PRIO",
                        message=f"Requirement {req_id} missing Priority attribute"
                    ))

                if not has_verification:
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=i,
                        severity=Severity.WARNING,
                        rule_id="REQ-VER",
                        message=f"Requirement {req_id} missing Verification Method attribute"
                    ))

    def _validate_mathematical_notation(self, file_path: str, lines: List[str]) -> None:
        """Validate mathematical notation (LaTeX syntax)"""
        in_math_block = False
        math_block_start = 0

        for i, line in enumerate(lines, 1):
            # Check for inline math ($...$)
            inline_matches = re.finditer(r'\$([^$]+)\$', line)
            for match in inline_matches:
                content = match.group(1)
                # Check for unbalanced braces
                if content.count('{') != content.count('}'):
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=i,
                        severity=Severity.ERROR,
                        rule_id="MATH-BAL",
                        message="Unbalanced braces in inline math expression"
                    ))

            # Check for block math ($$...$$)
            if '$$' in line:
                if not in_math_block:
                    in_math_block = True
                    math_block_start = i
                else:
                    in_math_block = False
                    # Validate the block content
                    block_content = ''.join(lines[math_block_start:i])
                    if block_content.count('{') != block_content.count('}'):
                        self.errors.append(LintError(
                            file_path=file_path,
                            line_number=math_block_start,
                            severity=Severity.ERROR,
                            rule_id="MATH-BAL",
                            message="Unbalanced braces in math block"
                        ))

        # Check for unclosed math blocks
        if in_math_block:
            self.errors.append(LintError(
                file_path=file_path,
                line_number=math_block_start,
                severity=Severity.ERROR,
                rule_id="MATH-UNC",
                message="Unclosed math block (missing closing $$)"
            ))

    def _validate_cross_references(self, file_path: str, lines: List[str]) -> None:
        """Validate cross-references and links"""
        base_dir = os.path.dirname(file_path)

        for i, line in enumerate(lines, 1):
            # Check for markdown links [text](path)
            link_matches = re.finditer(r'\[([^\]]+)\]\(([^)]+)\)', line)
            for match in link_matches:
                link_text = match.group(1)
                link_path = match.group(2)

                # Skip external links
                if link_path.startswith(('http://', 'https://', 'mailto:')):
                    continue

                # Validate relative file paths
                if link_path.endswith('.md'):
                    # Resolve the path
                    if link_path.startswith('/'):
                        # Absolute path from project root
                        full_path = os.path.join(os.getcwd(), link_path[1:])
                    else:
                        # Relative path
                        full_path = os.path.normpath(os.path.join(base_dir, link_path))

                    if not os.path.exists(full_path):
                        self.errors.append(LintError(
                            file_path=file_path,
                            line_number=i,
                            severity=Severity.ERROR,
                            rule_id="XREF-BRK",
                            message=f"Broken link: {link_path} (file not found)",
                            suggestion=f"Check if the file exists at: {full_path}"
                        ))

                # Check for section references (#section)
                if '#' in link_path and link_path.endswith('.md'):
                    # This is a section reference - we can't validate it easily
                    # but we can check the format
                    if not re.match(r'^[a-zA-Z0-9_-]+$', link_path.split('#')[-1]):
                        self.errors.append(LintError(
                            file_path=file_path,
                            line_number=i,
                            severity=Severity.WARNING,
                            rule_id="XREF-FMT",
                            message=f"Section reference may have invalid characters: {link_path}",
                            suggestion="Use lowercase letters, numbers, hyphens, and underscores only"
                        ))

    def _validate_mermaid_diagrams(self, file_path: str, lines: List[str]) -> None:
        """Validate Mermaid diagram syntax"""
        in_mermaid = False
        mermaid_start = 0
        mermaid_content = []

        for i, line in enumerate(lines, 1):
            if line.strip().startswith('```mermaid'):
                in_mermaid = True
                mermaid_start = i
                mermaid_content = []
                continue

            if in_mermaid:
                if line.strip().startswith('```'):
                    in_mermaid = False
                    # Validate the diagram
                    self._validate_mermaid_content(file_path, mermaid_start, mermaid_content)
                    continue

                mermaid_content.append(line)

        # Check for unclosed mermaid blocks
        if in_mermaid:
            self.errors.append(LintError(
                file_path=file_path,
                line_number=mermaid_start,
                severity=Severity.ERROR,
                rule_id="MRD-UNC",
                message="Unclosed Mermaid diagram block (missing closing ```)"
            ))

    def _validate_mermaid_content(self, file_path: str, start_line: int, content: List[str]) -> None:
        """Validate the content of a Mermaid diagram"""
        if not content:
            self.errors.append(LintError(
                file_path=file_path,
                line_number=start_line,
                severity=Severity.ERROR,
                rule_id="MRD-EMP",
                message="Empty Mermaid diagram"
            ))
            return

        # Check for valid diagram type
        first_line = content[0].strip()
        valid_type = False
        for diagram_type in self.VALID_MERMAID_TYPES:
            if first_line.startswith(diagram_type):
                valid_type = True
                break

        if not valid_type:
            self.errors.append(LintError(
                file_path=file_path,
                line_number=start_line + 1,
                severity=Severity.ERROR,
                rule_id="MRD-TYP",
                message=f"Invalid or missing Mermaid diagram type: {first_line}",
                suggestion=f"Valid types: {', '.join(self.VALID_MERMAID_TYPES)}"
            ))

        # Check for common syntax errors
        diagram_text = '\n'.join(content)

        # Check for unbalanced parentheses
        if diagram_text.count('(') != diagram_text.count(')'):
            self.errors.append(LintError(
                file_path=file_path,
                line_number=start_line,
                severity=Severity.WARNING,
                rule_id="MRD-SYN",
                message="Mermaid diagram may have unbalanced parentheses"
            ))

        # Check for unbalanced brackets
        if diagram_text.count('[') != diagram_text.count(']'):
            self.errors.append(LintError(
                file_path=file_path,
                line_number=start_line,
                severity=Severity.WARNING,
                rule_id="MRD-SYN",
                message="Mermaid diagram may have unbalanced brackets"
            ))

    def _validate_change_log(self, file_path: str, lines: List[str]) -> None:
        """Validate change log format"""
        found_change_log = False
        in_change_log = False
        table_started = False

        for i, line in enumerate(lines, 1):
            if re.match(r'^##\s+Change\s+Log', line, re.IGNORECASE):
                found_change_log = True
                in_change_log = True
                continue

            if in_change_log:
                if line.strip().startswith('|'):
                    table_started = True
                    # Check table header
                    if 'Version' in line and 'Date' in line and 'Author' in line and 'Changes' in line:
                        continue  # Valid header
                elif line.strip() and not line.strip().startswith('|') and table_started:
                    in_change_log = False

        if not found_change_log:
            self.errors.append(LintError(
                file_path=file_path,
                line_number=len(lines),
                severity=Severity.WARNING,
                rule_id="CHG-MIS",
                message="Missing Change Log section",
                suggestion="Add a Change Log section at the end of the document"
            ))

    def _validate_markdown_formatting(self, file_path: str, lines: List[str]) -> None:
        """Validate general markdown formatting"""
        for i, line in enumerate(lines, 1):
            # Check line length (max 120 characters, except for code blocks and URLs)
            if len(line) > 120 and not line.strip().startswith('```') and not 'http' in line:
                self.errors.append(LintError(
                    file_path=file_path,
                    line_number=i,
                    severity=Severity.WARNING,
                    rule_id="FMT-LNG",
                    message=f"Line too long ({len(line)} characters, max 120)",
                    suggestion="Break long lines or use code blocks"
                ))

            # Check for trailing whitespace
            if line.rstrip() != line.rstrip('\n').rstrip('\r'):
                self.errors.append(LintError(
                    file_path=file_path,
                    line_number=i,
                    severity=Severity.WARNING,
                    rule_id="FMT-TWS",
                    message="Trailing whitespace"
                ))

            # Check heading spacing (exactly one space after #)
            heading_match = re.match(r'^(#+)\s*(.+)$', line)
            if heading_match:
                hashes = heading_match.group(1)
                rest = heading_match.group(2)
                if rest and not rest.startswith(' '):
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=i,
                        severity=Severity.WARNING,
                        rule_id="FMT-HSP",
                        message="Heading should have exactly one space after # characters",
                        suggestion=f"Change to: {hashes} {rest}"
                    ))

            # Check for proper list formatting
            if line.strip().startswith(('-', '*')):
                # Check for space after list marker
                if not re.match(r'^\s*[-*]\s+.+$', line):
                    self.errors.append(LintError(
                        file_path=file_path,
                        line_number=i,
                        severity=Severity.WARNING,
                        rule_id="FMT-LST",
                        message="List item should have a space after the marker",
                        suggestion="Add a space after - or *"
                    ))


def find_spec_files(directory: str) -> List[str]:
    """Find all specification files in a directory"""
    spec_files = []
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.endswith('.md'):
                spec_files.append(os.path.join(root, file))
    return spec_files


def print_results(results: List[LintResult], verbose: bool = False) -> None:
    """Print linting results"""
    total_errors = 0
    total_warnings = 0
    total_info = 0
    failed_files = 0

    for result in results:
        if result.errors:
            print(f"\n{'='*80}")
            print(f"File: {result.file_path}")
            print(f"{'='*80}")

            for error in result.errors:
                if verbose or error.severity == Severity.ERROR:
                    print(error)
                    print()

            total_errors += result.error_count
            total_warnings += result.warning_count
            total_info += result.info_count

            if not result.passed:
                failed_files += 1

    # Print summary
    print(f"\n{'='*80}")
    print("SUMMARY")
    print(f"{'='*80}")
    print(f"Files checked: {len(results)}")
    print(f"Files passed: {len(results) - failed_files}")
    print(f"Files failed: {failed_files}")
    print(f"Total errors: {total_errors}")
    print(f"Total warnings: {total_warnings}")
    print(f"Total info: {total_info}")
    print(f"{'='*80}\n")


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Specification Linter for Morph Project",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s spec/language/ast_graph_spec.md
  %(prog)s --verbose spec/
  %(prog)s --strict spec/
  %(prog)s --fix spec/
        """
    )

    parser.add_argument(
        'path',
        help='Path to specification file or directory'
    )

    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='Show all warnings and info messages'
    )

    parser.add_argument(
        '-s', '--strict',
        action='store_true',
        help='Treat warnings as errors'
    )

    parser.add_argument(
        '--fix',
        action='store_true',
        help='Automatically fix some issues (experimental)'
    )

    args = parser.parse_args()

    # Determine what to lint
    if os.path.isfile(args.path):
        files_to_lint = [args.path]
    elif os.path.isdir(args.path):
        files_to_lint = find_spec_files(args.path)
    else:
        print(f"Error: Path not found: {args.path}", file=sys.stderr)
        sys.exit(1)

    if not files_to_lint:
        print("No specification files found.", file=sys.stderr)
        sys.exit(1)

    # Create linter and run
    linter = SpecLinter(strict=args.strict, verbose=args.verbose)
    results = []

    for file_path in files_to_lint:
        if args.verbose:
            print(f"Linting: {file_path}")
        result = linter.lint_file(file_path)
        results.append(result)

    # Print results
    print_results(results, verbose=args.verbose)

    # Exit with appropriate code
    if args.strict:
        # In strict mode, any error or warning causes failure
        if any(r.error_count > 0 or r.warning_count > 0 for r in results):
            sys.exit(1)
    else:
        # Normal mode: only errors cause failure
        if any(r.error_count > 0 for r in results):
            sys.exit(1)

    sys.exit(0)


if __name__ == '__main__':
    main()
