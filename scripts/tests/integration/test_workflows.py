"""
Integration tests for end-to-end workflows.
"""

from pathlib import Path

from spec_tools.cli.main import main
from spec_tools.config import ConfigManager
from spec_tools.formatting.formatter import MarkdownFormatter
from spec_tools.linting.linter import SpecLinter
from spec_tools.validation.validator import SpecValidator
from spec_tools.link_checker.checker import SpecLinkChecker
from spec_tools.models import Config


class TestIntegrationWorkflows:
    """Test cases for end-to-end workflows."""

    def test_format_lint_validate_workflow(self, temp_dir):
        """Test format → lint → validate workflow."""
        # Create a spec file with issues
        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# 1. Purpose and Scope

This specification defines the requirements for the system.

## 2. Definitions

| Term | Definition |
|------|-----------|
| System | The software being specified |

## 3. Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

**Traceability:**
- Design: DESIGN-001
- Implementation: IMPL-001
- Test: TEST-001

## Verification Plan

### Verification Methods

- Unit tests
- Integration tests

### Verification Criteria

- All requirements shall be verified

### Acceptance Criteria

- All tests pass

## Risk Assessment

### Identified Risks

| Risk | Probability | Impact |
|------|-------------|--------|
| Database failure | Medium | High |

### Mitigation Strategies

- Implement database replication

## Security Specifications

### STRIDE Threat Modeling

| Threat | Category |
|--------|----------|
| Spoofing | Spoofing |

### Security Controls

- Authentication
- Authorization

## Performance Specifications

### Performance Metrics

| Metric | Target |
|--------|--------|
| Response time | < 200ms |

### Measurement Methods

- Load testing

## Maintainability Specifications

### Code Quality Metrics

| Metric | Target |
|--------|--------|
| Code coverage | > 80% |

### Documentation Standards

- All public APIs documented

### Evolution Strategy

- Semantic versioning

## Traceability Matrix

| Requirement | Design | Test |
|-------------|--------|------|
| REQ-001 | DESIGN-001 | TEST-001 |

## Change Log

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2024-01-01 | John Doe | Initial version |
"""
        spec_file = temp_dir / "spec.md"
        spec_file.write_text(content, encoding="utf-8")

        # Step 1: Format
        config = ConfigManager.get_default_config()
        formatter = MarkdownFormatter(config.formatting)
        formatter.format_file(spec_file)

        # Step 2: Lint
        linter = SpecLinter(config.linting)
        lint_result = linter.lint_file(spec_file)

        # Step 3: Validate
        validator = SpecValidator(config.validation)
        validate_result = validator.validate_file(spec_file)

        # Verify workflow completed
        assert lint_result.passed is True
        assert validate_result.passed is True

    def test_check_all_workflow(self, temp_dir):
        """Test check-all command workflow."""
        # Create a spec file
        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# 1. Purpose and Scope

This specification defines the requirements for the system.

## 2. Definitions

| Term | Definition |
|------|-----------|
| System | The software being specified |

## 3. Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

**Traceability:**
- Design: DESIGN-001
- Implementation: IMPL-001
- Test: TEST-001

## Verification Plan

### Verification Methods

- Unit tests
- Integration tests

### Verification Criteria

- All requirements shall be verified

### Acceptance Criteria

- All tests pass

## Risk Assessment

### Identified Risks

| Risk | Probability | Impact |
|------|-------------|--------|
| Database failure | Medium | High |

### Mitigation Strategies

- Implement database replication

## Security Specifications

### STRIDE Threat Modeling

| Threat | Category |
|--------|----------|
| Spoofing | Spoofing |

### Security Controls

- Authentication
- Authorization

## Performance Specifications

### Performance Metrics

| Metric | Target |
|--------|--------|
| Response time | < 200ms |

### Measurement Methods

- Load testing

## Maintainability Specifications

### Code Quality Metrics

| Metric | Target |
|--------|--------|
| Code coverage | > 80% |

### Documentation Standards

- All public APIs documented

### Evolution Strategy

- Semantic versioning

## Traceability Matrix

| Requirement | Design | Test |
|-------------|--------|------|
| REQ-001 | DESIGN-001 | TEST-001 |

## Change Log

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2024-01-01 | John Doe | Initial version |
"""
        spec_file = temp_dir / "spec.md"
        spec_file.write_text(content, encoding="utf-8")

        # Run all checks
        config = ConfigManager.get_default_config()
        
        formatter = MarkdownFormatter(config.formatting)
        formatter.format_file(spec_file)

        linter = SpecLinter(config.linting)
        lint_result = linter.lint_file(spec_file)

        validator = SpecValidator(config.validation)
        validate_result = validator.validate_file(spec_file)

        checker = SpecLinkChecker(config.link_checking)
        link_result = checker.check_file(spec_file)

        # All checks should pass
        assert lint_result.passed is True
        assert validate_result.passed is True
        assert link_result.passed is True

    def test_ci_cd_integration(self, temp_dir):
        """Test CI/CD integration workflow."""
        # Create multiple spec files
        for i in range(3):
            content = f"""Title: Specification {i}
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# 1. Purpose and Scope

This specification defines the requirements for the system.

## 2. Definitions

| Term | Definition |
|------|-----------|
| System | The software being specified |

## 3. Requirements

### REQ-00{i}: Basic Requirement

The system SHALL provide basic functionality.

**Traceability:**
- Design: DESIGN-00{i}
- Implementation: IMPL-00{i}
- Test: TEST-00{i}

## Verification Plan

### Verification Methods

- Unit tests
- Integration tests

### Verification Criteria

- All requirements shall be verified

### Acceptance Criteria

- All tests pass

## Risk Assessment

### Identified Risks

| Risk | Probability | Impact |
|------|-------------|--------|
| Database failure | Medium | High |

### Mitigation Strategies

- Implement database replication

## Security Specifications

### STRIDE Threat Modeling

| Threat | Category |
|--------|----------|
| Spoofing | Spoofing |

### Security Controls

- Authentication
- Authorization

## Performance Specifications

### Performance Metrics

| Metric | Target |
|--------|--------|
| Response time | < 200ms |

### Measurement Methods

- Load testing

## Maintainability Specifications

### Code Quality Metrics

| Metric | Target |
|--------|--------|
| Code coverage | > 80% |

### Documentation Standards

- All public APIs documented

### Evolution Strategy

- Semantic versioning

## Traceability Matrix

| Requirement | Design | Test |
|-------------|--------|------|
| REQ-00{i} | DESIGN-00{i} | TEST-00{i} |

## Change Log

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2024-01-01 | John Doe | Initial version |
"""
            spec_file = temp_dir / f"spec{i}.md"
            spec_file.write_text(content, encoding="utf-8")

        # Run checks on all files
        config = ConfigManager.get_default_config()
        
        formatter = MarkdownFormatter(config.formatting)
        formatter.format_directory(temp_dir, recursive=True)

        linter = SpecLinter(config.linting)
        lint_results = linter.lint_directory(temp_dir, recursive=True)

        validator = SpecValidator(config.validation)
        validate_results = validator.validate_directory(temp_dir, recursive=True)

        checker = SpecLinkChecker(config.link_checking)
        link_results = checker.check_directory(temp_dir, recursive=True)

        # All files should pass all checks
        assert len(lint_results) == 3
        assert all(r.passed for r in lint_results)
        assert len(validate_results) == 3
        assert all(r.passed for r in validate_results)
        assert link_results.passed is True

    def test_workflow_with_errors(self, temp_dir):
        """Test workflow handles errors gracefully."""
        # Create a spec file with errors
        content = """Title: Sample Specification
Version: 1.0
Status: Invalid
Author: John Doe

# Content

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.
"""
        spec_file = temp_dir / "spec.md"
        spec_file.write_text(content, encoding="utf-8")

        # Run checks
        config = ConfigManager.get_default_config()
        
        linter = SpecLinter(config.linting)
        lint_result = linter.lint_file(spec_file)

        validator = SpecValidator(config.validation)
        validate_result = validator.validate_file(spec_file)

        # Should have errors
        assert lint_result.passed is False
        assert validate_result.passed is False
        assert len(lint_result.errors) > 0
        assert len(validate_result.errors) > 0

    def test_workflow_preserves_content(self, temp_dir):
        """Test workflow preserves file content."""
        # Create a spec file
        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# 1. Purpose and Scope

## 2. Definitions

## 3. Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

**Traceability:**
- Design: DESIGN-001
- Implementation: IMPL-001
- Test: TEST-001

## Verification Plan

1. Unit tests

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|-------|-------------|--------|------------|
| Database failure | Medium | High | Replication |

## Security Specifications

The system SHALL implement authentication.

## Performance Specifications

The system SHALL respond within 200ms.

## Maintainability Specifications

The system SHALL maintain 80% code coverage.

## Change Log

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0.0 | 2024-01-01 | John Doe | Initial version |
"""
        spec_file = temp_dir / "spec.md"
        spec_file.write_text(content, encoding="utf-8")

        # Run format
        config = ConfigManager.get_default_config()
        formatter = MarkdownFormatter(config.formatting)
        formatter.format_file(spec_file)

        # Content should be preserved (only formatting changes)
        formatted_content = spec_file.read_text(encoding="utf-8")
        assert "1. Purpose and Scope" in formatted_content
        assert "REQ-001: Basic Requirement" in formatted_content
        assert "DESIGN-001" in formatted_content
