"""
Maintainability specification validation check for specification files.

This module implements validation for maintainability specifications in specification
files, ensuring that code quality metrics, documentation standards, and
evolution strategies are properly defined.
"""

from pathlib import Path
from typing import List

from spec_tools.models import LintError, Severity
from spec_tools.validation.checks import ValidationCheck
from spec_tools.validation.utils import (
    extract_list_items,
    extract_section,
    extract_table,
    find_section_line,
)


class MaintainabilitySpecCheck(ValidationCheck):
    """Validates maintainability specifications in specification files.

    This check ensures that:
    1. A maintainability specifications section exists
    2. Code quality metrics are defined
    3. Documentation standards are specified
    4. Evolution strategy is included

    Attributes:
        description: Human-readable description of this check
    """

    @property
    def description(self) -> str:
        """Get description of this check."""
        return "Validates maintainability specifications and ensures code quality metrics, documentation standards, and evolution strategy are defined"

    def validate(self, content: str, filepath: Path) -> List[LintError]:
        """Validate maintainability specifications in the content.

        Args:
            content: The content of the specification file
            filepath: Path to the file being validated

        Returns:
            List of validation errors found
        """
        errors: List[LintError] = []

        # Check if maintainability specifications section exists
        maintainability_section = extract_section(content, "Maintainability Specifications")
        if maintainability_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.ERROR,
                    rule_id="MAINTAINABILITY-001",
                    message="Maintainability Specifications section is missing",
                    suggestion="Add a '## Maintainability Specifications' section to the specification",
                )
            )
            return errors

        # Find the line number of the section
        section_line = find_section_line(content, "Maintainability Specifications")
        if section_line is None:
            section_line = 1

        # Check for code quality metrics
        quality_section = extract_section(maintainability_section, "Code Quality Metrics")
        if quality_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="MAINTAINABILITY-002",
                    message="Code Quality Metrics subsection is missing",
                    suggestion="Add a '### Code Quality Metrics' subsection to the Maintainability Specifications",
                )
            )
        else:
            # Check if metrics are defined (either in a table or list)
            metrics_table = extract_table(quality_section)
            metrics_list = extract_list_items(quality_section)

            if not metrics_table and not metrics_list:
                quality_line = find_section_line(content, "Code Quality Metrics")
                if quality_line is None:
                    quality_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=quality_line,
                        severity=Severity.ERROR,
                        rule_id="MAINTAINABILITY-003",
                        message="No code quality metrics defined",
                        suggestion="Add a table or list of code quality metrics (e.g., cyclomatic complexity, code coverage, maintainability index)",
                    )
                )

            # If using a table, validate its structure
            if metrics_table:
                if len(metrics_table) < 2:
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=section_line,
                            severity=Severity.ERROR,
                            rule_id="MAINTAINABILITY-004",
                            message="Code quality metrics table must have at least a header row and one data row",
                            suggestion="Add table rows with code quality metric information",
                        )
                    )
                else:
                    # Check for required columns
                    header = metrics_table[0]
                    header_lower = [col.lower() for col in header]

                    required_columns = ["metric", "target"]
                    missing_columns = [col for col in required_columns if col not in header_lower]

                    if missing_columns:
                        errors.append(
                            LintError(
                                file_path=str(filepath),
                                line_number=section_line,
                                severity=Severity.ERROR,
                                rule_id="MAINTAINABILITY-005",
                                message=f"Code quality metrics table missing required columns: {', '.join(missing_columns)}",
                                suggestion=f"Add columns for: {', '.join(required_columns)}",
                            )
                        )

                    # Check if targets are specified for each metric
                    target_col_index = None

                    for i, col in enumerate(header_lower):
                        if "target" in col:
                            target_col_index = i
                            break

                    if target_col_index is not None:
                        for i, row in enumerate(metrics_table[1:], start=section_line + 1):
                            if row and len(row) > target_col_index:
                                target = row[target_col_index].strip()
                                if not target:
                                    metric_name = row[0].strip() if row else "Unknown"
                                    errors.append(
                                        LintError(
                                            file_path=str(filepath),
                                            line_number=i,
                                            severity=Severity.WARNING,
                                            rule_id="MAINTAINABILITY-006",
                                            message=f"Code quality metric '{metric_name}' missing target value",
                                            suggestion="Specify a target value for this metric (e.g., < 10, > 80%)",
                                        )
                                    )

        # Check for documentation standards
        docs_section = extract_section(maintainability_section, "Documentation Standards")
        if docs_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="MAINTAINABILITY-007",
                    message="Documentation Standards subsection is missing",
                    suggestion="Add a '### Documentation Standards' subsection to the Maintainability Specifications",
                )
            )
        else:
            # Check if documentation standards are specified
            standards = extract_list_items(docs_section)
            if not standards:
                docs_line = find_section_line(content, "Documentation Standards")
                if docs_line is None:
                    docs_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=docs_line,
                        severity=Severity.ERROR,
                        rule_id="MAINTAINABILITY-008",
                        message="No documentation standards specified",
                        suggestion="Add a list of documentation standards (e.g., docstring format, inline comment requirements, API documentation)",
                    )
                )

        # Check for evolution strategy
        evolution_section = extract_section(maintainability_section, "Evolution Strategy")
        if evolution_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="MAINTAINABILITY-009",
                    message="Evolution Strategy subsection is missing",
                    suggestion="Add a '### Evolution Strategy' subsection to the Maintainability Specifications",
                )
            )
        else:
            # Check if evolution strategy is defined
            strategy_items = extract_list_items(evolution_section)
            if not strategy_items:
                evolution_line = find_section_line(content, "Evolution Strategy")
                if evolution_line is None:
                    evolution_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=evolution_line,
                        severity=Severity.ERROR,
                        rule_id="MAINTAINABILITY-010",
                        message="No evolution strategy defined",
                        suggestion="Add a list of evolution strategy items (e.g., versioning approach, deprecation policy, backward compatibility requirements)",
                    )
                )

        return errors


__all__ = ["MaintainabilitySpecCheck"]
