#!/usr/bin/env python3
"""
Specification Link Checker

Validates all cross-references in Morph specification files.

This tool checks:
- Markdown links: [Text](path/to/file.md)
- Section references: [Text](path/to/file.md#section)
- File references: path/to/file.md
- Broken links: File doesn't exist
- Orphaned references: Section doesn't exist
- Duplicate references: Same link multiple times
- Self-references: References to same file

Usage:
    python scripts/spec_link_checker.py [options]
    python scripts/spec_link_checker.py --spec-dir spec/
    python scripts/spec_link_checker.py --output report.json
    python scripts/spec_link_checker.py --verbose
"""

import argparse
import json
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple


@dataclass
class LinkInfo:
    """Information about a single link."""
    text: str
    url: str
    line_number: int
    file_path: Path
    link_type: str  # 'markdown', 'section', 'file', 'external'
    is_valid: bool = False
    error_message: Optional[str] = None


@dataclass
class FileReport:
    """Report for a single file."""
    file_path: Path
    total_links: int = 0
    valid_links: int = 0
    broken_links: List[LinkInfo] = field(default_factory=list)
    orphaned_sections: List[LinkInfo] = field(default_factory=list)
    duplicate_links: List[Tuple[str, int]] = field(default_factory=list)
    self_references: List[LinkInfo] = field(default_factory=list)


@dataclass
class CheckerReport:
    """Complete report from link checker."""
    total_files: int = 0
    total_links: int = 0
    valid_links: int = 0
    broken_links: int = 0
    orphaned_sections: int = 0
    duplicate_links: int = 0
    self_references: int = 0
    file_reports: List[FileReport] = field(default_factory=list)
    all_links: List[LinkInfo] = field(default_factory=list)
    link_frequency: Dict[str, int] = field(default_factory=dict)


class SpecLinkChecker:
    """Link checker for specification files."""
    
    def __init__(self, spec_dir: str = 'spec', verbose: bool = False):
        self.spec_dir = Path(spec_dir)
        self.verbose = verbose
        self.report = CheckerReport()
        
        # Regex patterns for different link types
        self.markdown_link_pattern = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
        self.section_pattern = re.compile(r'^#+\s+(.+)$')
        self.file_ref_pattern = re.compile(r'(?<!\]\()spec/[a-zA-Z0-9_\-/]+\.md(?![^\)]*\))')
        
        # Cache for section headers
        self.section_cache: Dict[Path, Set[str]] = {}
        
    def check_all(self) -> CheckerReport:
        """Check all specification files."""
        if not self.spec_dir.exists():
            print(f"Error: Spec directory '{self.spec_dir}' does not exist", file=sys.stderr)
            sys.exit(1)
        
        spec_files = list(self.spec_dir.rglob('*.md'))
        self.report.total_files = len(spec_files)
        
        if self.verbose:
            print(f"Found {len(spec_files)} specification files")
        
        for spec_file in spec_files:
            self.check_file(spec_file)
        
        # Calculate statistics
        self._calculate_statistics()
        
        return self.report
    
    def check_file(self, file_path: Path) -> FileReport:
        """Check a single specification file."""
        if self.verbose:
            print(f"Checking: {file_path.relative_to(self.spec_dir.parent)}")
        
        content = file_path.read_text(encoding='utf-8')
        lines = content.split('\n')
        
        file_report = FileReport(file_path=file_path)
        
        # Extract section headers for validation
        sections = self._extract_sections(content)
        self.section_cache[file_path] = sections
        
        # Find all markdown links
        links = self._find_markdown_links(content, file_path)
        
        # Find file references (not in markdown links)
        file_refs = self._find_file_references(content, file_path, lines)
        
        # Combine all links
        all_links = links + file_refs
        
        file_report.total_links = len(all_links)
        
        # Validate each link
        link_counts: Dict[str, int] = defaultdict(int)
        
        for link in all_links:
            link_counts[link.url] += 1
            self.report.all_links.append(link)
            
            # Check for self-references
            if self._is_self_reference(link, file_path):
                link.is_valid = True  # Self-references are valid
                file_report.self_references.append(link)
                if self.verbose:
                    print(f"  Self-reference: {link.url}")
                continue
            
            # Validate link
            validation_result = self._validate_link(link, sections)
            link.is_valid = validation_result['valid']
            link.error_message = validation_result.get('error')
            
            if link.is_valid:
                file_report.valid_links += 1
            else:
                if 'section' in validation_result.get('error', '').lower():
                    file_report.orphaned_sections.append(link)
                else:
                    file_report.broken_links.append(link)
        
        # Check for duplicate links
        for url, count in link_counts.items():
            if count > 1:
                file_report.duplicate_links.append((url, count))
        
        self.report.file_reports.append(file_report)
        
        return file_report
    
    def _find_markdown_links(self, content: str, file_path: Path) -> List[LinkInfo]:
        """Find all markdown links in content."""
        links = []
        lines = content.split('\n')
        
        for line_num, line in enumerate(lines, 1):
            matches = self.markdown_link_pattern.finditer(line)
            for match in matches:
                text = match.group(1)
                url = match.group(2)
                
                # Determine link type
                link_type = 'external'
                if url.startswith('spec/'):
                    link_type = 'markdown'
                elif url.startswith('#'):
                    link_type = 'section'
                elif url.startswith('http://') or url.startswith('https://'):
                    link_type = 'external'
                elif url.endswith('.md'):
                    link_type = 'file'
                
                links.append(LinkInfo(
                    text=text,
                    url=url,
                    line_number=line_num,
                    file_path=file_path,
                    link_type=link_type
                ))
        
        return links
    
    def _find_file_references(self, content: str, file_path: Path, lines: List[str]) -> List[LinkInfo]:
        """Find file references not in markdown links."""
        links = []
        
        # Remove markdown links from content to avoid double-counting
        content_without_links = self.markdown_link_pattern.sub('', content)
        
        for line_num, line in enumerate(lines, 1):
            matches = self.file_ref_pattern.finditer(line)
            for match in matches:
                url = match.group(0)
                links.append(LinkInfo(
                    text=url,
                    url=url,
                    line_number=line_num,
                    file_path=file_path,
                    link_type='file'
                ))
        
        return links
    
    def _extract_sections(self, content: str) -> Set[str]:
        """Extract all section headers from content."""
        sections = set()
        lines = content.split('\n')
        
        for line in lines:
            match = self.section_pattern.match(line)
            if match:
                # Normalize section name: lowercase, replace spaces with hyphens, remove special chars
                section_name = match.group(1).strip()
                # Remove special characters except hyphens and alphanumeric
                normalized = ''.join(c.lower() if c.isalnum() or c in '-_' else '-' for c in section_name)
                # Replace multiple consecutive hyphens with single hyphen
                normalized = '-'.join(filter(None, normalized.split('-')))
                sections.add(normalized)
        
        return sections
    
    def _is_self_reference(self, link: LinkInfo, file_path: Path) -> bool:
        """Check if link is a self-reference."""
        if link.url.startswith('#'):
            # Section reference within same file
            return True
        
        if link.url.startswith('spec/'):
            # Check if it references the same file
            # Remove section anchor if present
            url_without_anchor = link.url.split('#')[0]
            target_path = self.spec_dir / url_without_anchor
            try:
                return target_path.resolve() == file_path.resolve()
            except:
                return False
        
        return False
    
    def _validate_link(self, link: LinkInfo, sections: Set[str]) -> Dict[str, any]:
        """Validate a single link."""
        result = {'valid': True, 'error': None}
        
        # Skip external links
        if link.link_type == 'external':
            return result
        
        # Handle section references within same file
        if link.url.startswith('#'):
            section_name = link.url[1:].lower()
            # Normalize section name same way as extraction
            normalized = ''.join(c.lower() if c.isalnum() or c in '-_' else '-' for c in section_name)
            normalized = '-'.join(filter(None, normalized.split('-')))
            if normalized not in sections:
                result['valid'] = False
                result['error'] = f"Section '{section_name}' not found in file"
            return result
        
        # Handle file references
        if link.url.startswith('spec/'):
            # Split file and section
            parts = link.url.split('#', 1)
            file_path = parts[0]
            section_name = parts[1].lower() if len(parts) > 1 else None
            
            # Check if file exists
            target_path = self.spec_dir / file_path
            if not target_path.exists():
                result['valid'] = False
                result['error'] = f"File '{file_path}' does not exist"
                return result
            
            # Check if section exists (if specified)
            if section_name:
                if target_path not in self.section_cache:
                    # Load and cache sections
                    content = target_path.read_text(encoding='utf-8')
                    self.section_cache[target_path] = self._extract_sections(content)
                
                # Normalize section name same way as extraction
                normalized = ''.join(c.lower() if c.isalnum() or c in '-_' else '-' for c in section_name)
                normalized = '-'.join(filter(None, normalized.split('-')))
                
                if normalized not in self.section_cache[target_path]:
                    result['valid'] = False
                    result['error'] = f"Section '{section_name}' not found in '{file_path}'"
        
        return result
    
    def _calculate_statistics(self):
        """Calculate overall statistics."""
        for file_report in self.report.file_reports:
            self.report.total_links += file_report.total_links
            self.report.valid_links += file_report.valid_links
            self.report.broken_links += len(file_report.broken_links)
            self.report.orphaned_sections += len(file_report.orphaned_sections)
            self.report.duplicate_links += len(file_report.duplicate_links)
            self.report.self_references += len(file_report.self_references)
        
        # Calculate link frequency
        for link in self.report.all_links:
            self.report.link_frequency[link.url] = self.report.link_frequency.get(link.url, 0) + 1
    
    def print_report(self, output_format: str = 'text'):
        """Print the check report."""
        if output_format == 'json':
            self._print_json_report()
        else:
            self._print_text_report()
    
    def _print_text_report(self):
        """Print report in text format."""
        print("=" * 80)
        print("SPECIFICATION LINK CHECKER REPORT")
        print("=" * 80)
        print()
        
        # Summary
        print("SUMMARY")
        print("-" * 80)
        print(f"Total Files Checked:  {self.report.total_files}")
        print(f"Total Links Found:    {self.report.total_links}")
        print(f"Valid Links:         {self.report.valid_links}")
        print(f"Broken Links:        {self.report.broken_links}")
        print(f"Orphaned Sections:   {self.report.orphaned_sections}")
        print(f"Duplicate Links:     {self.report.duplicate_links}")
        print(f"Self-References:     {self.report.self_references}")
        print()
        
        # Broken links
        if self.report.broken_links > 0:
            print("BROKEN LINKS")
            print("-" * 80)
            for file_report in self.report.file_reports:
                if file_report.broken_links:
                    print(f"\n{file_report.file_path.relative_to(self.spec_dir.parent)}:")
                    for link in file_report.broken_links:
                        print(f"  Line {link.line_number}: [{link.text}]({link.url})")
                        print(f"    Error: {link.error_message}")
            print()
        
        # Orphaned sections
        if self.report.orphaned_sections > 0:
            print("ORPHANED SECTION REFERENCES")
            print("-" * 80)
            for file_report in self.report.file_reports:
                if file_report.orphaned_sections:
                    print(f"\n{file_report.file_path.relative_to(self.spec_dir.parent)}:")
                    for link in file_report.orphaned_sections:
                        print(f"  Line {link.line_number}: [{link.text}]({link.url})")
                        print(f"    Error: {link.error_message}")
            print()
        
        # Duplicate links
        if self.report.duplicate_links > 0:
            print("DUPLICATE LINKS")
            print("-" * 80)
            for file_report in self.report.file_reports:
                if file_report.duplicate_links:
                    print(f"\n{file_report.file_path.relative_to(self.spec_dir.parent)}:")
                    for url, count in file_report.duplicate_links:
                        print(f"  {url} (used {count} times)")
            print()
        
        # Self-references
        if self.report.self_references > 0 and self.verbose:
            print("SELF-REFERENCES")
            print("-" * 80)
            for file_report in self.report.file_reports:
                if file_report.self_references:
                    print(f"\n{file_report.file_path.relative_to(self.spec_dir.parent)}:")
                    for link in file_report.self_references:
                        print(f"  Line {link.line_number}: {link.url}")
            print()
        
        # Most referenced files
        if self.report.link_frequency and self.verbose:
            print("MOST REFERENCED FILES")
            print("-" * 80)
            sorted_links = sorted(self.report.link_frequency.items(), key=lambda x: x[1], reverse=True)
            for url, count in sorted_links[:10]:
                print(f"  {url}: {count} references")
            print()
        
        # Final status
        print("=" * 80)
        if self.report.broken_links == 0 and self.report.orphaned_sections == 0:
            print("[OK] ALL LINKS ARE VALID")
        else:
            print("[ERROR] FOUND ISSUES")
        print("=" * 80)
    
    def _print_json_report(self):
        """Print report in JSON format."""
        report_dict = {
            'summary': {
                'total_files': self.report.total_files,
                'total_links': self.report.total_links,
                'valid_links': self.report.valid_links,
                'broken_links': self.report.broken_links,
                'orphaned_sections': self.report.orphaned_sections,
                'duplicate_links': self.report.duplicate_links,
                'self_references': self.report.self_references
            },
            'files': []
        }
        
        for file_report in self.report.file_reports:
            file_dict = {
                'path': str(file_report.file_path.relative_to(self.spec_dir.parent)),
                'total_links': file_report.total_links,
                'valid_links': file_report.valid_links,
                'broken_links': [
                    {
                        'line': link.line_number,
                        'text': link.text,
                        'url': link.url,
                        'error': link.error_message
                    }
                    for link in file_report.broken_links
                ],
                'orphaned_sections': [
                    {
                        'line': link.line_number,
                        'text': link.text,
                        'url': link.url,
                        'error': link.error_message
                    }
                    for link in file_report.orphaned_sections
                ],
                'duplicate_links': [
                    {'url': url, 'count': count}
                    for url, count in file_report.duplicate_links
                ],
                'self_references': [
                    {'line': link.line_number, 'url': link.url}
                    for link in file_report.self_references
                ]
            }
            report_dict['files'].append(file_dict)
        
        print(json.dumps(report_dict, indent=2))
    
    def save_report(self, output_path: str):
        """Save report to file."""
        output_file = Path(output_path)
        
        if output_file.suffix == '.json':
            # Save JSON report
            report_dict = {
                'summary': {
                    'total_files': self.report.total_files,
                    'total_links': self.report.total_links,
                    'valid_links': self.report.valid_links,
                    'broken_links': self.report.broken_links,
                    'orphaned_sections': self.report.orphaned_sections,
                    'duplicate_links': self.report.duplicate_links,
                    'self_references': self.report.self_references
                },
                'files': []
            }
            
            for file_report in self.report.file_reports:
                file_dict = {
                    'path': str(file_report.file_path.relative_to(self.spec_dir.parent)),
                    'total_links': file_report.total_links,
                    'valid_links': file_report.valid_links,
                    'broken_links': [
                        {
                            'line': link.line_number,
                            'text': link.text,
                            'url': link.url,
                            'error': link.error_message
                        }
                        for link in file_report.broken_links
                    ],
                    'orphaned_sections': [
                        {
                            'line': link.line_number,
                            'text': link.text,
                            'url': link.url,
                            'error': link.error_message
                        }
                        for link in file_report.orphaned_sections
                    ],
                    'duplicate_links': [
                        {'url': url, 'count': count}
                        for url, count in file_report.duplicate_links
                    ],
                    'self_references': [
                        {'line': link.line_number, 'url': link.url}
                        for link in file_report.self_references
                    ]
                }
                report_dict['files'].append(file_dict)
            
            output_file.write_text(json.dumps(report_dict, indent=2), encoding='utf-8')
        else:
            # Save text report (capture stdout)
            from io import StringIO
            old_stdout = sys.stdout
            sys.stdout = StringIO()
            self._print_text_report()
            report_text = sys.stdout.getvalue()
            sys.stdout = old_stdout
            output_file.write_text(report_text, encoding='utf-8')
        
        print(f"\nReport saved to: {output_path}")


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Validate cross-references in Morph specification files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s                              Check all spec files
  %(prog)s --spec-dir spec/             Check files in custom directory
  %(prog)s --output report.json          Save report to JSON file
  %(prog)s --verbose                    Show detailed output
  %(prog)s --format json                Output in JSON format
        """
    )
    
    parser.add_argument(
        '--spec-dir',
        default='spec',
        help='Directory containing specification files (default: spec)'
    )
    
    parser.add_argument(
        '--output', '-o',
        help='Output file path for report (default: stdout)'
    )
    
    parser.add_argument(
        '--format', '-f',
        choices=['text', 'json'],
        default='text',
        help='Output format (default: text)'
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Show verbose output'
    )
    
    args = parser.parse_args()
    
    # Run checker
    checker = SpecLinkChecker(spec_dir=args.spec_dir, verbose=args.verbose)
    checker.check_all()
    
    # Output report
    if args.output:
        checker.save_report(args.output)
    else:
        checker.print_report(output_format=args.format)
    
    # Exit with error code if issues found
    if checker.report.broken_links > 0 or checker.report.orphaned_sections > 0:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == '__main__':
    main()
