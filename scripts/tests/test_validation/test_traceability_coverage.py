"""Additional tests for TraceabilityCheck to improve coverage."""

from pathlib import Path

from spec_tools.validation.checks.traceability import TraceabilityCheck


class TestTraceabilityCheckCoverage:
    def test_missing_traceability_section(self):
        check = TraceabilityCheck()
        content = "# Specification\n\n## Requirements\n\nREQ-001 text\n"
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].rule_id == "TRACEABILITY-001"

    def test_missing_table(self):
        check = TraceabilityCheck()
        content = "## Traceability Matrix\n\nNo table here.\n"
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].rule_id == "TRACEABILITY-002"

    def test_table_only_header_row(self):
        check = TraceabilityCheck()
        content = "## Traceability Matrix\n\n| Requirement | Design | Test |\n"
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "TRACEABILITY-003" for e in errors)

    def test_table_missing_required_columns(self):
        check = TraceabilityCheck()
        content = "## Traceability Matrix\n\n| Name | Value |\n|------|-------|\n| REQ-001 | something |\n"
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "TRACEABILITY-004" for e in errors)

    def test_untraced_requirements(self):
        check = TraceabilityCheck()
        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL do something.

### REQ-002: Another Requirement

The system SHALL do another thing.

## Traceability Matrix

| Requirement | Design | Test |
|-------------|--------|------|
| REQ-001 | DESIGN-001 | TEST-001 |
"""
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "TRACEABILITY-005" for e in errors)
        assert "REQ-002" in errors[0].message

    def test_missing_design_trace(self):
        check = TraceabilityCheck()
        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL do something.

## Traceability Matrix

| Requirement | Design | Test |
|-------------|--------|------|
| REQ-001 |        | TEST-001 |
"""
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "TRACEABILITY-006" for e in errors)

    def test_missing_test_trace(self):
        check = TraceabilityCheck()
        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL do something.

## Traceability Matrix

| Requirement | Design | Test |
|-------------|--------|------|
| REQ-001 | DESIGN-001 |  |
"""
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "TRACEABILITY-007" for e in errors)

    def test_complete_traceability_no_warnings(self):
        check = TraceabilityCheck()
        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL do something.

## Traceability Matrix

| Requirement | Design | Test |
|-------------|--------|------|
| REQ-001     | DESIGN-001 | TEST-001 |
"""
        errors = check.validate(content, Path("test.md"))
        warning_errors = [e for e in errors if "missing" in e.message.lower()]
        assert len(warning_errors) == 0

    def test_section_line_none_fallback(self):
        check = TraceabilityCheck()
        content = "## Traceability Matrix\n\n| Requirement | Design | Test |\n|-------------|--------|------|\n| REQ-001 | DESIGN-001 | TEST-001 |\n"
        errors = check.validate(content, Path("test.md"))
        assert isinstance(errors, list)
