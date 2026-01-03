"""
Verification plan validation check for specification files.

This module implements validation for verification plans in specification
files, ensuring that verification methods, criteria, and acceptance
criteria are properly defined.
"""

from pathlib import Path
from typing import List

from spec_tools.models import LintError, Severity
from spec_tools.validation.checks import ValidationCheck
from spec_tools.validation.utils import (
    extract_section,
    extract_list_items,
    find_section_line,
)


class VerificationPlanCheck(ValidationCheck):
    """Validates verification plan in specification files.

    This check ensures that:
    1. A verification plan section exists
    2. Verification methods are specified
    3. Verification criteria are defined
    4. Acceptance criteria are specified

    Attributes:
        description: Human-readable description of this check
    """

    @property
    def description(self) -> str:
        """Get description of this check."""
        return "Validates verification plan section and ensures verification methods and criteria are defined"

    def validate(self, content: str, filepath: Path) -> List[LintError]:
        """Validate verification plan in the content.

        Args:
            content: The content of the specification file
            filepath: Path to the file being validated

        Returns:
            List of validation errors found
        """
        errors: List[LintError] = []

        # Check if verification plan section exists
        verification_section = extract_section(content, "Verification Plan")
        if verification_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.ERROR,
                    rule_id="VERIFICATION-001",
                    message="Verification Plan section is missing",
                    suggestion="Add a '## Verification Plan' section to the specification",
                )
            )
            return errors

        # Find the line number of the section
        section_line = find_section_line(content, "Verification Plan")
        if section_line is None:
            section_line = 1

        # Check for verification methods
        methods_section = extract_section(verification_section, "Verification Methods")
        if methods_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="VERIFICATION-002",
                    message="Verification Methods subsection is missing",
                    suggestion="Add a '### Verification Methods' subsection to the Verification Plan",
                )
            )
        else:
            # Check if methods are specified
            methods = extract_list_items(methods_section)
            if not methods:
                methods_line = find_section_line(content, "Verification Methods")
                if methods_line is None:
                    methods_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=methods_line,
                        severity=Severity.ERROR,
                        rule_id="VERIFICATION-003",
                        message="No verification methods specified",
                        suggestion="Add a list of verification methods (e.g., inspection, analysis, demonstration, test)",
                    )
                )

        # Check for verification criteria
        criteria_section = extract_section(verification_section, "Verification Criteria")
        if criteria_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="VERIFICATION-004",
                    message="Verification Criteria subsection is missing",
                    suggestion="Add a '### Verification Criteria' subsection to the Verification Plan",
                )
            )
        else:
            # Check if criteria are defined
            criteria = extract_list_items(criteria_section)
            if not criteria:
                criteria_line = find_section_line(content, "Verification Criteria")
                if criteria_line is None:
                    criteria_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=criteria_line,
                        severity=Severity.ERROR,
                        rule_id="VERIFICATION-005",
                        message="No verification criteria defined",
                        suggestion="Add a list of verification criteria for each requirement",
                    )
                )

        # Check for acceptance criteria
        acceptance_section = extract_section(verification_section, "Acceptance Criteria")
        if acceptance_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="VERIFICATION-006",
                    message="Acceptance Criteria subsection is missing",
                    suggestion="Add a '### Acceptance Criteria' subsection to the Verification Plan",
                )
            )
        else:
            # Check if acceptance criteria are specified
            acceptance_criteria = extract_list_items(acceptance_section)
            if not acceptance_criteria:
                acceptance_line = find_section_line(content, "Acceptance Criteria")
                if acceptance_line is None:
                    acceptance_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=acceptance_line,
                        severity=Severity.ERROR,
                        rule_id="VERIFICATION-007",
                        message="No acceptance criteria specified",
                        suggestion="Add a list of acceptance criteria that must be met for the specification",
                    )
                )

        return errors


__all__ = ["VerificationPlanCheck"]
