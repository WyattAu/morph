"""Tests for security spec check."""

from pathlib import Path

from spec_tools.validation.checks.security import SecuritySpecCheck
from spec_tools.models import Severity


class TestSecuritySpecCheck:
    def test_description(self):
        check = SecuritySpecCheck()
        assert "security" in check.description.lower()

    def test_missing_section(self):
        check = SecuritySpecCheck()
        errors = check.validate("# Spec\n\nNothing here.\n", Path("test.md"))
        assert len(errors) == 1
        assert errors[0].rule_id == "SECURITY-001"
        assert errors[0].severity == Severity.ERROR

    def test_missing_stride_threat_modeling(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-002" for e in errors)

    def test_empty_stride_threats(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-003" for e in errors)

    def test_stride_table_too_short(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n\n"
            "| Threat |\n"
            "|--------|\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-004" for e in errors)

    def test_stride_table_missing_columns(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n\n"
            "| Name | Value |\n"
            "|------|-------|\n"
            "| Spoofing | auth |\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-005" for e in errors)

    def test_stride_table_missing_control_column(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n\n"
            "| Threat | Category |\n"
            "|--------|----------|\n"
            "| Spoofing | S |\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-006" for e in errors)
        assert any(e.severity == Severity.WARNING for e in errors if e.rule_id == "SECURITY-006")

    def test_stride_table_empty_control(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n\n"
            "| Threat | Category | Control |\n"
            "|--------|----------|---------|\n"
            "| Spoofing | S | |\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-007" for e in errors)

    def test_missing_security_controls(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n- Spoofing\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-008" for e in errors)

    def test_missing_preventive_controls(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n- Spoofing\n"
            "### Security Controls\n\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-009" for e in errors)

    def test_empty_preventive_controls(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n- Spoofing\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-010" for e in errors)

    def test_missing_detective_controls(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n- Spoofing\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-011" for e in errors)

    def test_empty_detective_controls(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n- Spoofing\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-012" for e in errors)

    def test_missing_corrective_controls(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n- Spoofing\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-013" for e in errors)

    def test_empty_corrective_controls(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n- Spoofing\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "SECURITY-014" for e in errors)

    def test_complete_security_with_table(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n\n"
            "| Threat | Category | Control |\n"
            "|--------|----------|---------|\n"
            "| Spoofing | S | MFA |\n"
            "| Tampering | T | Signatures |\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 0

    def test_complete_security_with_list(self):
        check = SecuritySpecCheck()
        content = (
            "## Security Specifications\n\n"
            "### STRIDE Threat Modeling\n- Spoofing\n- Tampering\n"
            "### Security Controls\n\n"
            "#### Preventive Controls\n- Input validation\n"
            "#### Detective Controls\n- Logging\n"
            "#### Corrective Controls\n- Rollback\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 0

    def test_suggestions_provided(self):
        check = SecuritySpecCheck()
        errors = check.validate("# Spec\n", Path("test.md"))
        assert all(e.suggestion is not None for e in errors)
