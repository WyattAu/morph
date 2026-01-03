#!/usr/bin/env python3
"""
Unit tests for Specification Version Validator

Tests version parsing, compatibility checking, and validation logic
according to spec/conventions/version_compatibility_spec.md

Author: Kilo Code
Date: 2026-01-02
Version: 1.0.0
"""

import unittest
import tempfile
import shutil
from pathlib import Path
from scripts.spec_version_validator import (
    Version,
    VersionErrorType,
    SpecInfo,
    VersionError,
    VersionValidator,
)


class TestVersion(unittest.TestCase):
    """Test Version class functionality"""

    def test_version_parsing_basic(self):
        """Test basic version parsing"""
        v = Version(1, 2, 3)
        self.assertEqual(v.major, 1)
        self.assertEqual(v.minor, 2)
        self.assertEqual(v.patch, 3)
        self.assertEqual(str(v), "1.2.3")

    def test_version_parsing_with_prerelease(self):
        """Test version parsing with prerelease"""
        v = Version(1, 2, 3, "alpha.1")
        self.assertEqual(v.prerelease, "alpha.1")
        self.assertEqual(str(v), "1.2.3-alpha.1")

    def test_version_parsing_with_build(self):
        """Test version parsing with build metadata"""
        v = Version(1, 2, 3, None, "20230101")
        self.assertEqual(v.build, "20230101")
        self.assertEqual(str(v), "1.2.3+20230101")

    def test_version_parsing_master(self):
        """Test MASTER version parsing"""
        v = Version(2, 0, 0, "MASTER")
        self.assertTrue(v.is_master())
        self.assertEqual(str(v), "2.0.0-MASTER")

    def test_version_is_prerelease(self):
        """Test prerelease detection"""
        v1 = Version(1, 0, 0, "alpha")
        self.assertTrue(v1.is_prerelease())
        
        v2 = Version(1, 0, 0, "MASTER")
        self.assertFalse(v2.is_prerelease())
        
        v3 = Version(1, 0, 0)
        self.assertFalse(v3.is_prerelease())

    def test_version_comparison_equal(self):
        """Test version equality"""
        v1 = Version(1, 2, 3)
        v2 = Version(1, 2, 3)
        self.assertEqual(v1, v2)
        self.assertFalse(v1 < v2)
        self.assertFalse(v1 > v2)
        self.assertTrue(v1 <= v2)
        self.assertTrue(v1 >= v2)

    def test_version_comparison_major(self):
        """Test version comparison by MAJOR"""
        v1 = Version(1, 2, 3)
        v2 = Version(2, 0, 0)
        self.assertTrue(v1 < v2)
        self.assertFalse(v2 < v1)

    def test_version_comparison_minor(self):
        """Test version comparison by MINOR"""
        v1 = Version(1, 2, 3)
        v2 = Version(1, 3, 0)
        self.assertTrue(v1 < v2)
        self.assertFalse(v2 < v1)

    def test_version_comparison_patch(self):
        """Test version comparison by PATCH"""
        v1 = Version(1, 2, 3)
        v2 = Version(1, 2, 4)
        self.assertTrue(v1 < v2)
        self.assertFalse(v2 < v1)

    def test_version_comparison_prerelease(self):
        """Test version comparison with prerelease"""
        v1 = Version(1, 0, 0, "alpha")
        v2 = Version(1, 0, 0, "beta")
        v3 = Version(1, 0, 0, "rc.1")
        v4 = Version(1, 0, 0)
        
        self.assertTrue(v1 < v2)
        self.assertTrue(v2 < v3)
        self.assertTrue(v3 < v4)
        self.assertTrue(v1 < v4)

    def test_version_comparison_master(self):
        """Test MASTER version has higher precedence"""
        v1 = Version(2, 0, 0)
        v2 = Version(2, 0, 0, "MASTER")
        self.assertTrue(v1 < v2)

    def test_version_comparison_transitivity(self):
        """Test version comparison transitivity"""
        v1 = Version(1, 0, 0)
        v2 = Version(1, 1, 0)
        v3 = Version(2, 0, 0)
        
        self.assertTrue(v1 < v2)
        self.assertTrue(v2 < v3)
        self.assertTrue(v1 < v3)

    def test_version_hash(self):
        """Test version hashing"""
        v1 = Version(1, 2, 3)
        v2 = Version(1, 2, 3)
        v3 = Version(1, 2, 4)
        
        self.assertEqual(hash(v1), hash(v2))
        self.assertNotEqual(hash(v1), hash(v3))


class TestVersionValidator(unittest.TestCase):
    """Test VersionValidator functionality"""

    def setUp(self):
        """Set up test fixtures"""
        self.temp_dir = tempfile.mkdtemp()
        self.spec_dir = Path(self.temp_dir) / "spec"
        self.spec_dir.mkdir()

    def tearDown(self):
        """Clean up test fixtures"""
        shutil.rmtree(self.temp_dir)

    def create_spec_file(self, name: str, version: str) -> Path:
        """Create a test specification file"""
        content = f"""# Test Specification

**File:** `spec/{name}`
**Version:** {version}
**Context:** Test
**Status:** Active

## Content

Test content.
"""
        file_path = self.spec_dir / name
        file_path.write_text(content)
        return file_path

    def test_parse_version_valid(self):
        """Test parsing valid version strings"""
        validator = VersionValidator(self.spec_dir)
        
        # Basic version
        v = validator.parse_version("1.2.3")
        self.assertIsNotNone(v)
        self.assertEqual(v.major, 1)
        self.assertEqual(v.minor, 2)
        self.assertEqual(v.patch, 3)
        
        # With prerelease
        v = validator.parse_version("1.0.0-alpha")
        self.assertIsNotNone(v)
        self.assertEqual(v.prerelease, "alpha")
        
        # With build
        v = validator.parse_version("1.0.0+20230101")
        self.assertIsNotNone(v)
        self.assertEqual(v.build, None)  # Build is ignored in parsing
        
        # MASTER
        v = validator.parse_version("2.0.0-MASTER")
        self.assertIsNotNone(v)
        self.assertTrue(v.is_master())

    def test_parse_version_invalid(self):
        """Test parsing invalid version strings"""
        validator = VersionValidator(self.spec_dir)
        
        # Invalid format
        self.assertIsNone(validator.parse_version("1.2"))
        self.assertIsNone(validator.parse_version("v1.2.3"))
        self.assertIsNone(validator.parse_version("1.2.3.4"))
        self.assertIsNone(validator.parse_version("invalid"))

    def test_extract_version_from_file(self):
        """Test extracting version from specification file"""
        validator = VersionValidator(self.spec_dir)
        
        # Create test file
        file_path = self.create_spec_file("test_spec.md", "1.2.3")
        
        # Extract version
        result = validator.extract_version_from_file(file_path)
        self.assertIsNotNone(result)
        
        version, line_number = result
        self.assertEqual(version.major, 1)
        self.assertEqual(version.minor, 2)
        self.assertEqual(version.patch, 3)
        self.assertEqual(line_number, 4)  # Version is on line 4 in the test template

    def test_load_specifications(self):
        """Test loading all specifications"""
        validator = VersionValidator(self.spec_dir)
        
        # Create test files
        self.create_spec_file("spec1.md", "1.0.0")
        self.create_spec_file("spec2.md", "2.0.0")
        self.create_spec_file("spec3.md", "1.2.3")
        
        # Load specifications
        validator.load_specifications()
        
        # Check loaded specs
        self.assertEqual(len(validator.specs), 3)
        self.assertIn("spec1.md", validator.specs)
        self.assertIn("spec2.md", validator.specs)
        self.assertIn("spec3.md", validator.specs)

    def test_check_compatibility_same_major(self):
        """Test compatibility check with same MAJOR version"""
        validator = VersionValidator(self.spec_dir)
        
        v1 = Version(1, 0, 0)
        v2 = Version(1, 2, 3)
        
        self.assertTrue(validator.check_compatibility(v1, v2))
        self.assertTrue(validator.check_compatibility(v2, v1))

    def test_check_compatibility_different_major(self):
        """Test compatibility check with different MAJOR versions"""
        validator = VersionValidator(self.spec_dir)
        
        v1 = Version(1, 0, 0)
        v2 = Version(2, 0, 0)
        
        self.assertFalse(validator.check_compatibility(v1, v2))
        self.assertFalse(validator.check_compatibility(v2, v1))

    def test_validate_compatibility_no_errors(self):
        """Test compatibility validation with compatible versions"""
        validator = VersionValidator(self.spec_dir)
        
        # Create compatible specs
        self.create_spec_file("spec1.md", "1.0.0")
        self.create_spec_file("spec2.md", "1.2.3")
        
        validator.load_specifications()
        validator.validate_compatibility()
        
        # Should have no compatibility errors
        compat_errors = [e for e in validator.errors 
                        if e.error_type == VersionErrorType.INCOMPATIBLE_VERSIONS]
        self.assertEqual(len(compat_errors), 0)

    def test_validate_compatibility_with_errors(self):
        """Test compatibility validation with incompatible versions"""
        validator = VersionValidator(self.spec_dir)
        
        # Create incompatible specs
        self.create_spec_file("spec1.md", "1.0.0")
        self.create_spec_file("spec2.md", "2.0.0")
        
        validator.load_specifications()
        validator.validate_compatibility()
        
        # Should have compatibility errors
        compat_errors = [e for e in validator.errors 
                        if e.error_type == VersionErrorType.INCOMPATIBLE_VERSIONS]
        self.assertEqual(len(compat_errors), 1)

    def test_validate_synchronization_groups(self):
        """Test synchronization group validation"""
        validator = VersionValidator(self.spec_dir)
        
        # Create specs in core group with different MAJOR versions
        self.create_spec_file("morph_language_spec.md", "2.0.0")
        self.create_spec_file("type_system_spec.md", "1.0.0")
        
        validator.load_specifications()
        validator.validate_synchronization_groups()
        
        # Should have sync group errors
        sync_errors = [e for e in validator.errors 
                       if e.error_type == VersionErrorType.SYNC_GROUP_MISMATCH]
        self.assertGreater(len(sync_errors), 0)

    def test_validate_dependencies(self):
        """Test dependency validation"""
        validator = VersionValidator(self.spec_dir)
        
        # Create specs with dependency mismatch
        self.create_spec_file("type_system_spec.md", "1.0.0")
        self.create_spec_file("memory_model_spec.md", "2.0.0")
        
        validator.load_specifications()
        validator.validate_dependencies()
        
        # Should have dependency errors
        dep_errors = [e for e in validator.errors 
                     if e.error_type == VersionErrorType.DEPENDENCY_MISMATCH]
        self.assertGreater(len(dep_errors), 0)

    def test_check_eol_versions(self):
        """Test EOL version checking"""
        validator = VersionValidator(self.spec_dir)
        
        # Create spec with EOL version
        self.create_spec_file("test_spec.md", "1.0.0")
        
        validator.load_specifications()
        validator.check_eol_versions()
        
        # Should have EOL errors
        eol_errors = [e for e in validator.errors 
                     if e.error_type == VersionErrorType.EOL_VERSION]
        self.assertGreater(len(eol_errors), 0)

    def test_generate_text_report(self):
        """Test text report generation"""
        validator = VersionValidator(self.spec_dir)
        
        # Create test specs
        self.create_spec_file("spec1.md", "1.0.0")
        self.create_spec_file("spec2.md", "2.0.0")
        
        validator.load_specifications()
        validator.validate()
        
        report = validator.generate_report("text")
        
        # Check report contains expected sections
        self.assertIn("SPECIFICATION VERSION VALIDATION REPORT", report)
        self.assertIn("SUMMARY", report)
        self.assertIn("VERSION INVENTORY", report)
        self.assertIn("COMPATIBILITY MATRIX", report)

    def test_generate_json_report(self):
        """Test JSON report generation"""
        validator = VersionValidator(self.spec_dir)
        
        # Create test specs
        self.create_spec_file("spec1.md", "1.0.0")
        
        validator.load_specifications()
        validator.validate()
        
        report = validator.generate_report("json")
        
        # Check report is valid JSON
        import json
        data = json.loads(report)
        
        # Check structure
        self.assertIn("summary", data)
        self.assertIn("specifications", data)
        self.assertIn("errors", data)
        self.assertIn("warnings", data)
        
        # Check summary
        self.assertEqual(data["summary"]["total_specs"], 1)

    def test_validate_integration(self):
        """Test full validation integration"""
        validator = VersionValidator(self.spec_dir)
        
        # Create test specs
        self.create_spec_file("spec1.md", "1.0.0")
        self.create_spec_file("spec2.md", "2.0.0")
        self.create_spec_file("spec3.md", "1.2.3")
        
        # Run validation
        errors, warnings = validator.validate()
        
        # Should have errors (incompatible versions)
        self.assertGreater(len(errors), 0)
        
        # Should have loaded all specs
        self.assertEqual(len(validator.specs), 3)


class TestVersionError(unittest.TestCase):
    """Test VersionError class"""

    def test_version_error_creation(self):
        """Test creating version errors"""
        spec1 = SpecInfo(
            path=Path("spec1.md"),
            name="spec1.md",
            version=Version(1, 0, 0),
            line_number=1
        )
        
        error = VersionError(
            error_type=VersionErrorType.INVALID_FORMAT,
            spec1=spec1,
            spec2=None,
            message="Invalid version format"
        )
        
        self.assertEqual(error.error_type, VersionErrorType.INVALID_FORMAT)
        self.assertEqual(error.message, "Invalid version format")
        self.assertIsNone(error.spec2)
        self.assertEqual(error.severity, "ERROR")

    def test_version_error_string_representation(self):
        """Test version error string representation"""
        spec1 = SpecInfo(
            path=Path("spec1.md"),
            name="spec1.md",
            version=Version(1, 0, 0),
            line_number=1
        )
        
        error = VersionError(
            error_type=VersionErrorType.INVALID_FORMAT,
            spec1=spec1,
            spec2=None,
            message="Invalid version format"
        )
        
        error_str = str(error)
        self.assertIn("ERROR", error_str)
        self.assertIn("Invalid version format", error_str)
        self.assertIn("spec1.md", error_str)


class TestSpecInfo(unittest.TestCase):
    """Test SpecInfo class"""

    def test_spec_info_creation(self):
        """Test creating spec info"""
        spec_info = SpecInfo(
            path=Path("spec/test_spec.md"),
            name="test_spec.md",
            version=Version(1, 2, 3),
            line_number=5,
            status="Active",
            layer="L2",
            domain="Type System"
        )
        
        self.assertEqual(spec_info.name, "test_spec.md")
        self.assertEqual(spec_info.version.major, 1)
        self.assertEqual(spec_info.version.minor, 2)
        self.assertEqual(spec_info.version.patch, 3)
        self.assertEqual(spec_info.line_number, 5)
        self.assertEqual(spec_info.status, "Active")
        self.assertEqual(spec_info.layer, "L2")
        self.assertEqual(spec_info.domain, "Type System")


if __name__ == "__main__":
    unittest.main()
