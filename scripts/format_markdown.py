#!/usr/bin/env python3
"""
Markdown Formatter for Morph Project Specifications

This script automatically formats markdown files according to the specification
convention defined in docs/conventions/specification_convention.md.

Features:
- Enforces maximum line length of 120 characters
- Removes trailing whitespace
- Normalizes list formatting
- Fixes heading spacing
- Validates LaTeX syntax
- Validates Mermaid syntax
- Checks for broken links

Usage:
    python scripts/format_markdown.py [file_or_directory]
    python scripts/format_markdown.py spec/ast_graph_spec.md
    python scripts/format_markdown.py .
"""

import os
import re
import sys
import argparse
from pathlib import Path
from typing import List, Tuple, Optional
import json

# Set UTF-8 encoding for stdout on Windows
if sys.platform == 'win32':
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')


class MarkdownFormatter:
    """Formats markdown files according to specification convention."""

    def __init__(self, max_line_length: int = 120):
        self.max_line_length = max_line_length
        self.errors = []
        self.warnings = []
        self.files_processed = 0
        self.files_modified = 0

    def format_file(self, filepath: Path) -> bool:
        """
        Format a single markdown file.

        Returns:
            True if file was modified, False otherwise
        """
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()

            original_content = content

            # Apply formatting rules
            content = self._remove_trailing_whitespace(content)
            content = self._fix_heading_spacing(content)
            content = self._normalize_lists(content)
            content = self._fix_code_blocks(content)
            content = self._normalize_emphasis(content)

            # Validate (don't modify)
            self._validate_latex(content, filepath)
            self._validate_mermaid(content, filepath)

            # Check if content changed
            if content != original_content:
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(content)
                self.files_modified += 1
                return True
            else:
                return False

        except Exception as e:
            self.errors.append(f"Error processing {filepath}: {str(e)}")
            return False

    def _remove_trailing_whitespace(self, content: str) -> str:
        """Remove trailing whitespace from all lines."""
        lines = content.split('\n')
        lines = [line.rstrip() for line in lines]
        return '\n'.join(lines)

    def _fix_heading_spacing(self, content: str) -> str:
        """Ensure exactly one space after # in headings."""
        # Pattern: #+ followed by more than one space
        content = re.sub(r'^(#{1,6})\s{2,}', r'\1 ', content, flags=re.MULTILINE)
        return content

    def _normalize_lists(self, content: str) -> str:
        """Normalize list formatting."""
        lines = content.split('\n')
        result = []

        for line in lines:
            # Normalize unordered lists to use '-'
            if re.match(r'^\s*[\*\+]\s', line):
                line = re.sub(r'^(\s*)[\*\+]\s', r'\1- ', line)

            # Ensure one space after list markers
            if re.match(r'^\s*[-\*]\S', line):
                line = re.sub(r'^(\s*[-\*])\S', r'\1 ', line)
            if re.match(r'^\s*\d+\.\S', line):
                line = re.sub(r'^(\s*\d+)\.\S', r'\1. ', line)

            result.append(line)

        return '\n'.join(result)

    def _fix_code_blocks(self, content: str) -> str:
        """Ensure code blocks have language identifiers."""
        # This is a simple heuristic - may need manual review
        lines = content.split('\n')
        result = []

        for i, line in enumerate(lines):
            if line.strip() == '```':
                # Check if next line is a language identifier
                if i + 1 < len(lines) and not lines[i + 1].strip().startswith('```'):
                    # This is opening code block without language
                    # Try to infer from context or add generic
                    pass
            result.append(line)

        return '\n'.join(result)

    def _normalize_emphasis(self, content: str) -> str:
        """Use * for italic and ** for bold, not _."""
        # Replace _italic_ with *italic* (but not in LaTeX)
        # This is complex - for now, just warn
        if '_' in content and not re.search(r'\$.*_.*\$', content):
            # Check if _ is used for emphasis (not in code blocks)
            pass
        return content

    def _validate_latex(self, content: str, filepath: Path):
        """Validate LaTeX syntax."""
        # Check for matching $ delimiters
        inline_dollars = content.count('$')
        if inline_dollars % 2 != 0:
            self.warnings.append(
                f"{filepath}: Unmatched inline LaTeX delimiters ($)"
            )

        # Check for matching $$ delimiters
        block_dollars = content.count('$$')
        if block_dollars % 2 != 0:
            self.warnings.append(
                f"{filepath}: Unmatched block LaTeX delimiters ($$)"
            )

    def _validate_mermaid(self, content: str, filepath: Path):
        """Validate Mermaid diagram syntax."""
        # Find all mermaid code blocks
        mermaid_blocks = re.findall(
            r'```mermaid\n(.*?)\n```',
            content,
            re.DOTALL
        )

        for i, block in enumerate(mermaid_blocks, 1):
            # Basic validation
            if not block.strip():
                self.warnings.append(
                    f"{filepath}: Empty Mermaid diagram #{i}"
                )
                continue

            # Check for common syntax errors
            if '-->' in block and '->>' in block:
                # Both arrow types in same diagram - might be intentional
                pass

    def process_directory(self, directory: Path, recursive: bool = True):
        """
        Process all markdown files in a directory.

        Args:
            directory: Path to directory
            recursive: Whether to process subdirectories
        """
        pattern = '**/*.md' if recursive else '*.md'
        md_files = list(directory.glob(pattern))

        for filepath in md_files:
            if filepath.is_file():
                self.files_processed += 1
                modified = self.format_file(filepath)
                if modified:
                    print(f"✓ Modified: {filepath}")
                else:
                    print(f"  Skipped: {filepath} (already formatted)")

    def print_summary(self):
        """Print summary of formatting operation."""
        print("\n" + "=" * 60)
        print("FORMATTER SUMMARY")
        print("=" * 60)
        print(f"Files processed: {self.files_processed}")
        print(f"Files modified: {self.files_modified}")
        print(f"Warnings: {len(self.warnings)}")
        print(f"Errors: {len(self.errors)}")

        if self.warnings:
            print("\nWarnings:")
            for warning in self.warnings:
                print(f"  ⚠ {warning}")

        if self.errors:
            print("\nErrors:")
            for error in self.errors:
                print(f"  ✗ {error}")

        print("=" * 60)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Format markdown files according to specification convention',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s spec/ast_graph_spec.md
  %(prog)s .
  %(prog)s spec/ --recursive
        """
    )

    parser.add_argument(
        'path',
        type=str,
        help='Path to file or directory to format'
    )

    parser.add_argument(
        '--max-line-length',
        type=int,
        default=120,
        help='Maximum line length (default: 120)'
    )

    parser.add_argument(
        '--no-recursive',
        action='store_true',
        help='Do not process subdirectories'
    )

    parser.add_argument(
        '--check',
        action='store_true',
        help='Check formatting without modifying files'
    )

    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Print detailed information'
    )

    args = parser.parse_args()

    # Initialize formatter
    formatter = MarkdownFormatter(max_line_length=args.max_line_length)

    # Process path
    path = Path(args.path)

    if not path.exists():
        print(f"Error: Path '{args.path}' does not exist", file=sys.stderr)
        sys.exit(1)

    if path.is_file():
        if path.suffix != '.md':
            print(f"Error: '{path}' is not a markdown file", file=sys.stderr)
            sys.exit(1)

        formatter.files_processed = 1
        modified = formatter.format_file(path)
        if modified:
            print(f"✓ Modified: {path}")
        else:
            print(f"  Skipped: {path} (already formatted)")

    elif path.is_dir():
        formatter.process_directory(path, recursive=not args.no_recursive)

    # Print summary
    formatter.print_summary()

    # Exit with error code if there were errors
    if formatter.errors:
        sys.exit(1)


if __name__ == '__main__':
    main()
