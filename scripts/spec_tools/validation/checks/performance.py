"""
Performance specification validation check for specification files.

This module implements validation for performance specifications in specification
files, ensuring that performance metrics, targets, and measurement methods
are properly defined.
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


class PerformanceSpecCheck(ValidationCheck):
    """Validates performance specifications in specification files.

    This check ensures that:
    1. A performance specifications section exists
    2. Performance metrics are defined
    3. Performance targets are specified
    4. Measurement methods are defined

    Attributes:
        description: Human-readable description of this check
    """

    @property
    def description(self) -> str:
        """Get description of this check."""
        return "Validates performance specifications and ensures metrics, targets, and measurement methods are defined"

    def validate(self, content: str, filepath: Path) -> List[LintError]:
        """Validate performance specifications in the content.

        Args:
            content: The content of the specification file
            filepath: Path to the file being validated

        Returns:
            List of validation errors found
        """
        errors: List[LintError] = []

        # Check if performance specifications section exists
        performance_section = extract_section(content, "Performance Specifications")
        if performance_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.ERROR,
                    rule_id="PERFORMANCE-001",
                    message="Performance Specifications section is missing",
                    suggestion="Add a '## Performance Specifications' section to the specification",
                )
            )
            return errors

        # Find the line number of the section
        section_line = find_section_line(content, "Performance Specifications")
        if section_line is None:
            section_line = 1

        # Check for performance metrics
        metrics_section = extract_section(performance_section, "Performance Metrics")
        if metrics_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="PERFORMANCE-002",
                    message="Performance Metrics subsection is missing",
                    suggestion="Add a '### Performance Metrics' subsection to the Performance Specifications",
                )
            )
        else:
            # Check if metrics are defined (either in a table or list)
            metrics_table = extract_table(metrics_section)
            metrics_list = extract_list_items(metrics_section)

            if not metrics_table and not metrics_list:
                metrics_line = find_section_line(content, "Performance Metrics")
                if metrics_line is None:
                    metrics_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=metrics_line,
                        severity=Severity.ERROR,
                        rule_id="PERFORMANCE-003",
                        message="No performance metrics defined",
                        suggestion="Add a table or list of performance metrics (e.g., response time, throughput, latency)",
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
                            rule_id="PERFORMANCE-004",
                            message="Performance metrics table must have at least a header row and one data row",
                            suggestion="Add table rows with performance metric information",
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
                                rule_id="PERFORMANCE-005",
                                message=f"Performance metrics table missing required columns: {', '.join(missing_columns)}",
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
                                            rule_id="PERFORMANCE-006",
                                            message=f"Performance metric '{metric_name}' missing target value",
                                            suggestion="Specify a target value for this metric (e.g., < 100ms, > 1000 req/s)",
                                        )
                                    )

        # Check for performance targets section
        targets_section = extract_section(performance_section, "Performance Targets")
        if targets_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.WARNING,
                    rule_id="PERFORMANCE-007",
                    message="Performance Targets subsection is missing",
                    suggestion="Add a '### Performance Targets' subsection to specify overall performance targets",
                )
            )
        else:
            # Check if targets are specified
            targets = extract_list_items(targets_section)
            if not targets:
                targets_line = find_section_line(content, "Performance Targets")
                if targets_line is None:
                    targets_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=targets_line,
                        severity=Severity.WARNING,
                        rule_id="PERFORMANCE-008",
                        message="No performance targets specified",
                        suggestion="Add a list of performance targets",
                    )
                )

        # Check for measurement methods
        measurement_section = extract_section(performance_section, "Measurement Methods")
        if measurement_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="PERFORMANCE-009",
                    message="Measurement Methods subsection is missing",
                    suggestion="Add a '### Measurement Methods' subsection to the Performance Specifications",
                )
            )
        else:
            # Check if measurement methods are defined
            methods = extract_list_items(measurement_section)
            if not methods:
                measurement_line = find_section_line(content, "Measurement Methods")
                if measurement_line is None:
                    measurement_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=measurement_line,
                        severity=Severity.ERROR,
                        rule_id="PERFORMANCE-010",
                        message="No measurement methods defined",
                        suggestion="Add a list of measurement methods for each performance metric",
                    )
                )

        return errors


__all__ = ["PerformanceSpecCheck"]
