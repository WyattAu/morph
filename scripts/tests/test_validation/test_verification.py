"""Tests for verification plan check."""

from pathlib import Path

from spec_tools.validation.checks.verification import VerificationPlanCheck
from spec_tools.models import Severity


class TestVerificationPlanCheck:
    def test_description(self):
        check = VerificationPlanCheck()
        assert "verification plan" in check.description.lower()

    def test_missing_verification_plan(self):
        check = VerificationPlanCheck()
        content = "# Spec\n\nNo verification plan.\n"
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 1
        assert "missing" in errors[0].message.lower()
        assert errors[0].severity == Severity.ERROR
        assert errors[0].rule_id == "VERIFICATION-001"

    def test_missing_verification_methods(self):
        check = VerificationPlanCheck()
        content = "## Verification Plan\n\n### Verification Criteria\n- Criterion 1\n"
        errors = check.validate(content, Path("test.md"))
        method_errors = [e for e in errors if "Methods" in e.message]
        assert len(method_errors) == 1
        assert method_errors[0].rule_id == "VERIFICATION-002"

    def test_empty_verification_methods(self):
        check = VerificationPlanCheck()
        content = (
            "## Verification Plan\n\n"
            "### Verification Methods\n\n"
            "### Verification Criteria\n- C1\n"
        )
        errors = check.validate(content, Path("test.md"))
        method_errors = [e for e in errors if "No verification methods" in e.message]
        assert len(method_errors) == 1
        assert method_errors[0].rule_id == "VERIFICATION-003"

    def test_missing_verification_criteria(self):
        check = VerificationPlanCheck()
        content = (
            "## Verification Plan\n\n"
            "### Verification Methods\n- Test\n"
        )
        errors = check.validate(content, Path("test.md"))
        criteria_errors = [e for e in errors if "Criteria" in e.message and "VERIFICATION-004" in e.rule_id]
        assert len(criteria_errors) == 1

    def test_empty_verification_criteria(self):
        check = VerificationPlanCheck()
        content = (
            "## Verification Plan\n\n"
            "### Verification Methods\n- Test\n"
            "### Verification Criteria\n\n"
        )
        errors = check.validate(content, Path("test.md"))
        criteria_errors = [e for e in errors if "No verification criteria" in e.message]
        assert len(criteria_errors) == 1
        assert criteria_errors[0].rule_id == "VERIFICATION-005"

    def test_missing_acceptance_criteria(self):
        check = VerificationPlanCheck()
        content = (
            "## Verification Plan\n\n"
            "### Verification Methods\n- Test\n"
            "### Verification Criteria\n- C1\n"
        )
        errors = check.validate(content, Path("test.md"))
        acceptance_errors = [e for e in errors if "Acceptance" in e.message]
        assert len(acceptance_errors) == 1
        assert acceptance_errors[0].rule_id == "VERIFICATION-006"

    def test_empty_acceptance_criteria(self):
        check = VerificationPlanCheck()
        content = (
            "## Verification Plan\n\n"
            "### Verification Methods\n- Test\n"
            "### Verification Criteria\n- C1\n"
            "### Acceptance Criteria\n\n"
        )
        errors = check.validate(content, Path("test.md"))
        acceptance_errors = [e for e in errors if "No acceptance criteria" in e.message]
        assert len(acceptance_errors) == 1
        assert acceptance_errors[0].rule_id == "VERIFICATION-007"

    def test_complete_verification_plan(self):
        check = VerificationPlanCheck()
        content = (
            "## Verification Plan\n\n"
            "### Verification Methods\n- Inspection\n- Test\n"
            "### Verification Criteria\n- All requirements verified\n"
            "### Acceptance Criteria\n- System passes all tests\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 0

    def test_suggestions_provided(self):
        check = VerificationPlanCheck()
        content = "# Spec\n"
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
