"""
Traceability validation check for specification files.

This module implements validation for traceability matrices in specification
files, ensuring that all requirements are properly traced to design elements
and test cases.
"""

from pathlib import Path
from typing import List

from spec_tools.models import LintError, Severity
from spec_tools.validation.checks import ValidationCheck
from spec_tools.validation.utils import (
    extract_requirement_ids,
    extract_section,
    extract_table,
    find_section_line,
)


class TraceabilityCheck(ValidationCheck):
    """Validates traceability matrix in specification files.

    This check ensures that:
    1. A traceability matrix section exists
    2. The matrix is properly formatted as a table
    3. All requirements are traced to design elements
    4. All requirements are traced to test cases

    Attributes:
        description: Human-readable description of this check
    """

    @property
    def description(self) -> str:
        """Get description of this check."""
        return "Validates traceability matrix section and ensures all requirements are traced"

    def validate(self, content: str, filepath: Path) -> List[LintError]:
        """Validate traceability matrix in the content.

        Args:
            content: The content of the specification file
            filepath: Path to the file being validated

        Returns:
            List of validation errors found
        """
        errors: List[LintError] = []

        # Check if traceability section exists
        traceability_section = extract_section(content, "Traceability Matrix")
        if traceability_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.ERROR,
                    rule_id="TRACEABILITY-001",
                    message="Traceability Matrix section is missing",
                    suggestion="Add a '## Traceability Matrix' section to the specification",
                )
            )
            return errors

        # Find the line number of the section
        section_line = find_section_line(content, "Traceability Matrix")
        if section_line is None:
            section_line = 1

        # Extract and validate the table
        table = extract_table(traceability_section)
        if not table:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="TRACEABILITY-002",
                    message="Traceability matrix table is missing or malformed",
                    suggestion="Add a properly formatted markdown table in the Traceability Matrix section",
                )
            )
            return errors

        # Validate table structure
        if len(table) < 2:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="TRACEABILITY-003",
                    message="Traceability matrix must have at least a header row and one data row",
                    suggestion="Add table rows with requirement traceability information",
                )
            )
            return errors

        # Check for required columns
        header = table[0]
        header_lower = [col.lower() for col in header]

        required_columns = ["requirement", "design", "test"]
        missing_columns = [col for col in required_columns if col not in header_lower]

        if missing_columns:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="TRACEABILITY-004",
                    message=f"Traceability matrix missing required columns: {', '.join(missing_columns)}",
                    suggestion=f"Add columns for: {', '.join(required_columns)}",
                )
            )

        # Extract all requirement IDs from the entire document
        all_requirements = extract_requirement_ids(content)

        # Extract traced requirements from the table
        traced_requirements = set()
        for row in table[1:]:  # Skip header
            if row:
                # First column should contain requirement ID
                req_id = row[0].strip()
                if req_id:
                    traced_requirements.add(req_id)

        # Check for untraced requirements
        untraced_requirements = set(all_requirements) - traced_requirements
        if untraced_requirements:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.WARNING,
                    rule_id="TRACEABILITY-005",
                    message=f"Requirements not traced in matrix: {', '.join(sorted(untraced_requirements))}",
                    suggestion="Add these requirements to the traceability matrix",
                )
            )

        # Check for design element traces
        design_col_index = None
        for i, col in enumerate(header_lower):
            if "design" in col:
                design_col_index = i
                break

        if design_col_index is not None:
            for i, row in enumerate(table[1:], start=section_line + 1):
                if row and len(row) > design_col_index:
                    design_trace = row[design_col_index].strip()
                    if not design_trace:
                        req_id = row[0].strip() if row else "Unknown"
                        errors.append(
                            LintError(
                                file_path=str(filepath),
                                line_number=i,
                                severity=Severity.WARNING,
                                rule_id="TRACEABILITY-006",
                                message=f"Requirement '{req_id}' missing design element trace",
                                suggestion="Specify the design element that implements this requirement",
                            )
                        )

        # Check for test case traces
        test_col_index = None
        for i, col in enumerate(header_lower):
            if "test" in col:
                test_col_index = i
                break

        if test_col_index is not None:
            for i, row in enumerate(table[1:], start=section_line + 1):
                if row and len(row) > test_col_index:
                    test_trace = row[test_col_index].strip()
                    if not test_trace:
                        req_id = row[0].strip() if row else "Unknown"
                        errors.append(
                            LintError(
                                file_path=str(filepath),
                                line_number=i,
                                severity=Severity.WARNING,
                                rule_id="TRACEABILITY-007",
                                message=f"Requirement '{req_id}' missing test case trace",
                                suggestion="Specify the test case that validates this requirement",
                            )
                        )

        return errors


__all__ = ["TraceabilityCheck"]
