#!/usr/bin/env python3
"""
Unit tests for the specification linter

Run with: python tests/test_spec_linter.py
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path

# Add parent directory to path to import the linter
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from scripts.spec_linter import SpecLinter, LintError, Severity, LintResult


class TestSpecLinter(unittest.TestCase):
    """Test cases for the specification linter"""

    def setUp(self):
        """Set up test fixtures"""
        self.linter = SpecLinter(strict=False, verbose=False)
        self.temp_dir = tempfile.mkdtemp()

    def tearDown(self):
        """Clean up test fixtures"""
        # Clean up temporary files
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def _create_temp_file(self, content: str, filename: str = "test_spec.md") -> str:
        """Create a temporary file with given content"""
        filepath = os.path.join(self.temp_dir, filename)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        return filepath

    def test_valid_specification(self):
        """Test that a valid specification passes all checks"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test Component)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test Author
* Reviewers: Reviewer 1, Reviewer 2

---

## 1. Introduction

### 1.1 Purpose

This is a test specification.

### 1.2 Scope

Test scope.

### 1.3 Definitions, Acronyms, and Abbreviations

| Term | Definition |
|------|------------|
| Test | A test term |

### 1.4 References

- Reference 1

---

## 2. Formal Definitions

Let $S = \\{x \\in \\mathbb{Z} \\mid x > 0\\}$.

---

## 3. Requirements

### 3.1 Functional Requirements

* TST-REQ-001:** THE system SHALL do something.

* Priority: Critical
* Verification Method: Test
* Rationale: Test rationale
* Dependencies: None
* Traceability: Section 2

---

## 4. Design

### 4.1 Architecture

```mermaid
flowchart TD
    A[Start] --> B[End]
```

---

## 5. Correctness Properties

### 5.1 Invariants

1. $\\forall x \\in S, x > 0$

---

## 6. Examples

### 6.1 Example 1

Example content.

---

## Change Log

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-01-01 | Test Author | Initial version |
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should pass with no errors
        self.assertTrue(result.passed)
        self.assertEqual(result.error_count, 0)

    def test_missing_header_fields(self):
        """Test detection of missing header fields"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0

---

## 1. Introduction

Test content.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should fail with errors
        self.assertFalse(result.passed)
        self.assertGreater(result.error_count, 0)

        # Check for specific errors
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Context" in msg for msg in error_messages))
        self.assertTrue(any("Formalism" in msg for msg in error_messages))
        self.assertTrue(any("Status" in msg for msg in error_messages))

    def test_invalid_version_format(self):
        """Test detection of invalid version format"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should fail with version error
        self.assertFalse(result.passed)
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("version" in msg.lower() for msg in error_messages))

    def test_invalid_status(self):
        """Test detection of invalid status value"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: InvalidStatus
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should fail with status error
        self.assertFalse(result.passed)
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Invalid status" in msg for msg in error_messages))

    def test_missing_mandatory_sections(self):
        """Test detection of missing mandatory sections"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should fail with missing sections
        self.assertFalse(result.passed)
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Formal Definitions" in msg for msg in error_messages))
        self.assertTrue(any("Requirements" in msg for msg in error_messages))
        self.assertTrue(any("Design" in msg for msg in error_messages))

    def test_duplicate_requirement_ids(self):
        """Test detection of duplicate requirement IDs"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

* TST-REQ-001:** THE system SHALL do something.

* Priority: Critical
* Verification Method: Test

* TST-REQ-001:** THE system SHALL do something else.

* Priority: High
* Verification Method: Test

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should fail with duplicate ID error
        self.assertFalse(result.passed)
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Duplicate requirement ID" in msg for msg in error_messages))

    def test_missing_ears_pattern(self):
        """Test detection of missing EARS pattern in requirements"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

* TST-REQ-001:** The system should do something.

* Priority: Critical
* Verification Method: Test

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should warn about missing EARS pattern
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("EARS pattern" in msg for msg in error_messages))

    def test_unbalanced_math_braces(self):
        """Test detection of unbalanced braces in math expressions"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

Let $S = \\{x \\in \\mathbb{Z} \\mid x > 0$.

---

## 3. Requirements

Test.

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should fail with unbalanced braces error
        self.assertFalse(result.passed)
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Unbalanced braces" in msg for msg in error_messages))

    def test_unclosed_math_block(self):
        """Test detection of unclosed math blocks"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

$$
\\sum_{i=1}^{n} x_i = \\mu

---

## 3. Requirements

Test.

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should fail with unclosed math block error
        self.assertFalse(result.passed)
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Unclosed math block" in msg for msg in error_messages))

    def test_invalid_mermaid_diagram_type(self):
        """Test detection of invalid Mermaid diagram type"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

Test.

---

## 4. Design

```mermaid
invalidDiagramType
    A --> B
```

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should fail with invalid diagram type error
        self.assertFalse(result.passed)
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Invalid or missing Mermaid diagram type" in msg for msg in error_messages))

    def test_unclosed_mermaid_block(self):
        """Test detection of unclosed Mermaid diagram blocks"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

Test.

---

## 4. Design

```mermaid
flowchart TD
    A[Start] --> B[End]

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should fail with unclosed mermaid block error
        self.assertFalse(result.passed)
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Unclosed Mermaid diagram block" in msg for msg in error_messages))

    def test_missing_change_log(self):
        """Test detection of missing change log"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

Test.

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should warn about missing change log
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Change Log" in msg for msg in error_messages))

    def test_line_too_long(self):
        """Test detection of lines that are too long"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

This is a very long line that exceeds the maximum allowed length of 120 characters and should trigger a warning from the linter about line length violations.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

Test.

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should warn about long line
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Line too long" in msg for msg in error_messages))

    def test_trailing_whitespace(self):
        """Test detection of trailing whitespace"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test   

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

Test.

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should warn about trailing whitespace
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Trailing whitespace" in msg for msg in error_messages))

    def test_heading_spacing(self):
        """Test detection of incorrect heading spacing"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

##1. Introduction

Test.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

Test.

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should warn about heading spacing
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Heading should have exactly one space" in msg for msg in error_messages))

    def test_missing_requirement_attributes(self):
        """Test detection of missing requirement attributes"""
        content = """# Test Specification

* File: `spec/test_spec.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

* TST-REQ-001:** THE system SHALL do something.

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content)
        result = self.linter.lint_file(filepath)

        # Should warn about missing attributes
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("Priority" in msg for msg in error_messages))
        self.assertTrue(any("Verification Method" in msg for msg in error_messages))

    def test_file_path_mismatch(self):
        """Test detection of file path mismatch in header"""
        content = """# Test Specification

* File: `spec/wrong_name.md`
* Version: 1.0.0
* Context: Layer 1 (Test)
* Formalism: Set Theory
* Status: Draft
* Last Modified: 2026-01-01
* Author: Test
* Reviewers: Test

---

## 1. Introduction

Test.

---

## 2. Formal Definitions

Test.

---

## 3. Requirements

Test.

---

## 4. Design

Test.

---

## 5. Correctness Properties

Test.

---

## 6. Examples

Test.
"""
        filepath = self._create_temp_file(content, "test_spec.md")
        result = self.linter.lint_file(filepath)

        # Should fail with path mismatch error
        self.assertFalse(result.passed)
        error_messages = [e.message for e in result.errors]
        self.assertTrue(any("does not match actual filename" in msg for msg in error_messages))


class TestLintError(unittest.TestCase):
    """Test cases for LintError class"""

    def test_error_string_representation(self):
        """Test string representation of LintError"""
        error = LintError(
            file_path="test.md",
            line_number=10,
            severity=Severity.ERROR,
            rule_id="TEST-001",
            message="Test error message",
            suggestion="Fix it like this"
        )

        error_str = str(error)
        self.assertIn("test.md:10", error_str)
        self.assertIn("[ERROR]", error_str)
        self.assertIn("TEST-001", error_str)
        self.assertIn("Test error message", error_str)
        self.assertIn("Suggestion:", error_str)
        self.assertIn("Fix it like this", error_str)

    def test_error_without_suggestion(self):
        """Test LintError without suggestion"""
        error = LintError(
            file_path="test.md",
            line_number=10,
            severity=Severity.WARNING,
            rule_id="TEST-002",
            message="Test warning"
        )

        error_str = str(error)
        self.assertIn("[WARNING]", error_str)
        self.assertNotIn("Suggestion:", error_str)


class TestLintResult(unittest.TestCase):
    """Test cases for LintResult class"""

    def test_empty_result(self):
        """Test LintResult with no errors"""
        result = LintResult(file_path="test.md")
        self.assertTrue(result.passed)
        self.assertEqual(result.error_count, 0)
        self.assertEqual(result.warning_count, 0)
        self.assertEqual(result.info_count, 0)

    def test_result_with_errors(self):
        """Test LintResult with errors"""
        result = LintResult(file_path="test.md")
        result.errors = [
            LintError("test.md", 1, Severity.ERROR, "ERR-001", "Error 1"),
            LintError("test.md", 2, Severity.WARNING, "WRN-001", "Warning 1"),
            LintError("test.md", 3, Severity.INFO, "INF-001", "Info 1")
        ]
        # Update passed status based on errors
        result.passed = all(e.severity != Severity.ERROR for e in result.errors)

        self.assertFalse(result.passed)
        self.assertEqual(result.error_count, 1)
        self.assertEqual(result.warning_count, 1)
        self.assertEqual(result.info_count, 1)

    def test_result_with_only_warnings(self):
        """Test LintResult with only warnings (should pass)"""
        result = LintResult(file_path="test.md")
        result.errors = [
            LintError("test.md", 1, Severity.WARNING, "WRN-001", "Warning 1"),
            LintError("test.md", 2, Severity.WARNING, "WRN-002", "Warning 2")
        ]
        # Update passed status based on errors
        result.passed = all(e.severity != Severity.ERROR for e in result.errors)

        self.assertTrue(result.passed)
        self.assertEqual(result.error_count, 0)
        self.assertEqual(result.warning_count, 2)


if __name__ == '__main__':
    unittest.main()
