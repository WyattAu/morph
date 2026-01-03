#!/usr/bin/env python3
"""
Unit tests for Specification Link Checker

Tests cover:
- Link detection (markdown, section, file references)
- Link validation (file existence, section existence)
- Self-reference detection
- Duplicate link detection
- Orphaned section detection
- Report generation
"""

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

# Add parent directory to path for imports
import sys
sys.path.insert(0, str(Path(__file__).parent.parent))

from scripts.spec_link_checker import (
    SpecLinkChecker,
    LinkInfo,
    FileReport,
    CheckerReport
)


class TestLinkDetection(unittest.TestCase):
    """Test link detection functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.spec_dir = Path(self.temp_dir) / 'spec'
        self.spec_dir.mkdir()
    
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_detect_markdown_links(self):
        """Test detection of markdown links."""
        test_file = self.spec_dir / 'test.md'
        test_file.write_text("""
# Test Document

This is a [link to another file](spec/other.md).
This is a [link with section](spec/other.md#section).
This is an [external link](https://example.com).
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        links = checker._find_markdown_links(test_file.read_text(), test_file)
        
        self.assertEqual(len(links), 3)
        self.assertEqual(links[0].text, 'link to another file')
        self.assertEqual(links[0].url, 'spec/other.md')
        self.assertEqual(links[0].link_type, 'markdown')
        
        self.assertEqual(links[1].text, 'link with section')
        self.assertEqual(links[1].url, 'spec/other.md#section')
        self.assertEqual(links[1].link_type, 'markdown')
        
        self.assertEqual(links[2].text, 'external link')
        self.assertEqual(links[2].url, 'https://example.com')
        self.assertEqual(links[2].link_type, 'external')
    
    def test_detect_section_references(self):
        """Test detection of section references within same file."""
        test_file = self.spec_dir / 'test.md'
        test_file.write_text("""
# Test Document

See [Introduction](#introduction) for details.
Also see [Section 2](#section-2).
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        links = checker._find_markdown_links(test_file.read_text(), test_file)
        
        self.assertEqual(len(links), 2)
        self.assertEqual(links[0].url, '#introduction')
        self.assertEqual(links[0].link_type, 'section')
        self.assertEqual(links[1].url, '#section-2')
        self.assertEqual(links[1].link_type, 'section')
    
    def test_detect_file_references(self):
        """Test detection of file references not in markdown links."""
        test_file = self.spec_dir / 'test.md'
        test_file.write_text("""
# Test Document

See spec/other.md for more information.
Also check spec/nested/file.md.
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        lines = test_file.read_text().split('\n')
        links = checker._find_file_references(test_file.read_text(), test_file, lines)
        
        self.assertEqual(len(links), 2)
        self.assertEqual(links[0].url, 'spec/other.md')
        self.assertEqual(links[0].link_type, 'file')
        self.assertEqual(links[1].url, 'spec/nested/file.md')
        self.assertEqual(links[1].link_type, 'file')
    
    def test_extract_sections(self):
        """Test extraction of section headers."""
        content = """
# Main Title

## Section 1

### Subsection 1.1

## Section 2

### Subsection 2.1
"""
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        sections = checker._extract_sections(content)
        
        self.assertIn('main-title', sections)
        self.assertIn('section-1', sections)
        self.assertIn('subsection-1.1', sections)
        self.assertIn('section-2', sections)
        self.assertIn('subsection-2.1', sections)


class TestLinkValidation(unittest.TestCase):
    """Test link validation functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.spec_dir = Path(self.temp_dir) / 'spec'
        self.spec_dir.mkdir()
        
        # Create test files
        self.target_file = self.spec_dir / 'target.md'
        self.target_file.write_text("""
# Target Document

## Section 1

Content of section 1.

## Section 2

Content of section 2.
""")
        
        self.source_file = self.spec_dir / 'source.md'
        self.source_file.write_text("""
# Source Document

Link to [target](spec/target.md).
Link to [section 1](spec/target.md#section-1).
""")
    
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_validate_existing_file(self):
        """Test validation of existing file link."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        link = LinkInfo(
            text='target',
            url='spec/target.md',
            line_number=5,
            file_path=self.source_file,
            link_type='markdown'
        )
        
        result = checker._validate_link(link, set())
        
        self.assertTrue(result['valid'])
        self.assertIsNone(result['error'])
    
    def test_validate_nonexistent_file(self):
        """Test validation of non-existent file link."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        link = LinkInfo(
            text='nonexistent',
            url='spec/nonexistent.md',
            line_number=5,
            file_path=self.source_file,
            link_type='markdown'
        )
        
        result = checker._validate_link(link, set())
        
        self.assertFalse(result['valid'])
        self.assertIn('does not exist', result['error'])
    
    def test_validate_existing_section(self):
        """Test validation of existing section link."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        link = LinkInfo(
            text='section 1',
            url='spec/target.md#section-1',
            line_number=6,
            file_path=self.source_file,
            link_type='markdown'
        )
        
        result = checker._validate_link(link, set())
        
        self.assertTrue(result['valid'])
        self.assertIsNone(result['error'])
    
    def test_validate_nonexistent_section(self):
        """Test validation of non-existent section link."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        link = LinkInfo(
            text='nonexistent section',
            url='spec/target.md#nonexistent-section',
            line_number=6,
            file_path=self.source_file,
            link_type='markdown'
        )
        
        result = checker._validate_link(link, set())
        
        self.assertFalse(result['valid'])
        self.assertIn('not found', result['error'])
    
    def test_validate_external_link(self):
        """Test validation of external link (always valid)."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        link = LinkInfo(
            text='external',
            url='https://example.com',
            line_number=5,
            file_path=self.source_file,
            link_type='external'
        )
        
        result = checker._validate_link(link, set())
        
        self.assertTrue(result['valid'])
        self.assertIsNone(result['error'])


class TestSelfReferenceDetection(unittest.TestCase):
    """Test self-reference detection."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.spec_dir = Path(self.temp_dir) / 'spec'
        self.spec_dir.mkdir()
        
        self.test_file = self.spec_dir / 'test.md'
        self.test_file.write_text("""
# Test Document

See [Introduction](#introduction) for details.
""")
    
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_detect_section_self_reference(self):
        """Test detection of section self-reference."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        link = LinkInfo(
            text='Introduction',
            url='#introduction',
            line_number=5,
            file_path=self.test_file,
            link_type='section'
        )
        
        self.assertTrue(checker._is_self_reference(link, self.test_file))
    
    def test_detect_file_self_reference(self):
        """Test detection of file self-reference."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        link = LinkInfo(
            text='self',
            url='spec/test.md',
            line_number=5,
            file_path=self.test_file,
            link_type='markdown'
        )
        
        self.assertTrue(checker._is_self_reference(link, self.test_file))


class TestDuplicateDetection(unittest.TestCase):
    """Test duplicate link detection."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.spec_dir = Path(self.temp_dir) / 'spec'
        self.spec_dir.mkdir()
        
        # Create target file
        target_file = self.spec_dir / 'target.md'
        target_file.write_text("# Target\n\nContent.")
        
        # Create source file with duplicate links
        self.source_file = self.spec_dir / 'source.md'
        self.source_file.write_text("""
# Source Document

First link to [target](spec/target.md).
Second link to [target](spec/target.md).
Third link to [target](spec/target.md).
""")
    
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_detect_duplicate_links(self):
        """Test detection of duplicate links."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        file_report = checker.check_file(self.source_file)
        
        self.assertEqual(len(file_report.duplicate_links), 1)
        self.assertEqual(file_report.duplicate_links[0][0], 'spec/target.md')
        self.assertEqual(file_report.duplicate_links[0][1], 3)


class TestReportGeneration(unittest.TestCase):
    """Test report generation."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.spec_dir = Path(self.temp_dir) / 'spec'
        self.spec_dir.mkdir()
        
        # Create test files
        target_file = self.spec_dir / 'target.md'
        target_file.write_text("""
# Target

## Section 1

Content.
""")
        
        source_file = self.spec_dir / 'source.md'
        source_file.write_text("""
# Source

Link to [target](spec/target.md).
Link to [section](spec/target.md#section-1).
Broken link to [nonexistent](spec/nonexistent.md).
""")
    
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_generate_text_report(self):
        """Test text report generation."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        checker.check_all()
        
        # Capture output
        from io import StringIO
        old_stdout = sys.stdout
        sys.stdout = StringIO()
        checker.print_report(output_format='text')
        output = sys.stdout.getvalue()
        sys.stdout = old_stdout
        
        self.assertIn('SUMMARY', output)
        self.assertIn('Total Files Checked', output)
        self.assertIn('Total Links Found', output)
        self.assertIn('BROKEN LINKS', output)
    
    def test_generate_json_report(self):
        """Test JSON report generation."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        checker.check_all()
        
        # Capture output
        from io import StringIO
        old_stdout = sys.stdout
        sys.stdout = StringIO()
        checker.print_report(output_format='json')
        output = sys.stdout.getvalue()
        sys.stdout = old_stdout
        
        report = json.loads(output)
        
        self.assertIn('summary', report)
        self.assertIn('files', report)
        self.assertEqual(report['summary']['total_files'], 2)
        self.assertGreater(report['summary']['broken_links'], 0)
    
    def test_save_report_to_file(self):
        """Test saving report to file."""
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        checker.check_all()
        
        output_file = Path(self.temp_dir) / 'report.json'
        checker.save_report(str(output_file))
        
        self.assertTrue(output_file.exists())
        
        report = json.loads(output_file.read_text())
        self.assertIn('summary', report)
        self.assertIn('files', report)


class TestIntegration(unittest.TestCase):
    """Integration tests for complete workflow."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.spec_dir = Path(self.temp_dir) / 'spec'
        self.spec_dir.mkdir()
    
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_check_all_valid_links(self):
        """Test checking all valid links."""
        # Create target file
        target_file = self.spec_dir / 'target.md'
        target_file.write_text("""
# Target Document

## Section 1

Content of section 1.

## Section 2

Content of section 2.
""")
        
        # Create source file with valid links
        source_file = self.spec_dir / 'source.md'
        source_file.write_text("""
# Source Document

Link to [target](spec/target.md).
Link to [section 1](spec/target.md#section-1).
Link to [section 2](spec/target.md#section-2).
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        report = checker.check_all()
        
        self.assertEqual(report.total_files, 2)
        self.assertEqual(report.broken_links, 0)
        self.assertEqual(report.orphaned_sections, 0)
    
    def test_check_broken_links(self):
        """Test checking broken links."""
        # Create source file with broken links
        source_file = self.spec_dir / 'source.md'
        source_file.write_text("""
# Source Document

Link to [nonexistent](spec/nonexistent.md).
Link to [broken section](spec/source.md#nonexistent-section).
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        report = checker.check_all()
        
        self.assertEqual(report.total_files, 1)
        self.assertGreater(report.broken_links, 0)
        self.assertGreater(report.orphaned_sections, 0)
    
    def test_check_with_duplicates(self):
        """Test checking with duplicate links."""
        # Create target file
        target_file = self.spec_dir / 'target.md'
        target_file.write_text("# Target\n\nContent.")
        
        # Create source file with duplicates
        source_file = self.spec_dir / 'source.md'
        source_file.write_text("""
# Source

Link to [target](spec/target.md).
Link to [target](spec/target.md).
Link to [target](spec/target.md).
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        report = checker.check_all()
        
        self.assertGreater(report.duplicate_links, 0)
    
    def test_check_with_self_references(self):
        """Test checking with self-references."""
        # Create file with self-references
        test_file = self.spec_dir / 'test.md'
        test_file.write_text("""
# Test Document

## Introduction

See [Introduction](#introduction) for details.
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        report = checker.check_all()
        
        self.assertGreater(report.self_references, 0)


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and special scenarios."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.spec_dir = Path(self.temp_dir) / 'spec'
        self.spec_dir.mkdir()
    
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_empty_file(self):
        """Test checking empty file."""
        test_file = self.spec_dir / 'empty.md'
        test_file.write_text("")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        file_report = checker.check_file(test_file)
        
        self.assertEqual(file_report.total_links, 0)
    
    def test_file_with_no_links(self):
        """Test checking file with no links."""
        test_file = self.spec_dir / 'nolinks.md'
        test_file.write_text("""
# Document

This document has no links.
Just plain text.
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        file_report = checker.check_file(test_file)
        
        self.assertEqual(file_report.total_links, 0)
    
    def test_nested_directory_structure(self):
        """Test checking nested directory structure."""
        # Create nested directories
        nested_dir = self.spec_dir / 'nested' / 'deep'
        nested_dir.mkdir(parents=True)
        
        # Create files in nested directories
        deep_file = nested_dir / 'deep.md'
        deep_file.write_text("# Deep\n\nContent.")
        
        root_file = self.spec_dir / 'root.md'
        root_file.write_text("""
# Root

Link to [deep file](spec/nested/deep/deep.md).
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        report = checker.check_all()
        
        self.assertEqual(report.broken_links, 0)
    
    def test_special_characters_in_sections(self):
        """Test sections with special characters."""
        test_file = self.spec_dir / 'test.md'
        test_file.write_text("""
# Test Document

## Section with Special Characters!

Content.

## Section-with-Dashes

Content.
""")
        
        checker = SpecLinkChecker(spec_dir=str(self.spec_dir))
        sections = checker._extract_sections(test_file.read_text())
        
        # Sections should be normalized
        self.assertIn('section-with-special-characters', sections)
        self.assertIn('section-with-dashes', sections)


def run_tests():
    """Run all tests."""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestLinkDetection))
    suite.addTests(loader.loadTestsFromTestCase(TestLinkValidation))
    suite.addTests(loader.loadTestsFromTestCase(TestSelfReferenceDetection))
    suite.addTests(loader.loadTestsFromTestCase(TestDuplicateDetection))
    suite.addTests(loader.loadTestsFromTestCase(TestReportGeneration))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    suite.addTests(loader.loadTestsFromTestCase(TestEdgeCases))
    
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == '__main__':
    success = run_tests()
    sys.exit(0 if success else 1)
