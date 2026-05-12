"""
Risk assessment validation check for specification files.

This module implements validation for risk assessment in specification
files, ensuring that risks are properly identified, analyzed, and
mitigated.
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


class RiskAssessmentCheck(ValidationCheck):
    """Validates risk assessment in specification files.

    This check ensures that:
    1. A risk assessment section exists
    2. Risks are identified
    3. Risk analysis includes probability and impact
    4. Mitigation strategies are specified

    Attributes:
        description: Human-readable description of this check
    """

    @property
    def description(self) -> str:
        """Get description of this check."""
        return "Validates risk assessment section and ensures risks are properly analyzed and mitigated"

    def validate(self, content: str, filepath: Path) -> List[LintError]:
        """Validate risk assessment in the content.

        Args:
            content: The content of the specification file
            filepath: Path to the file being validated

        Returns:
            List of validation errors found
        """
        errors: List[LintError] = []

        # Check if risk assessment section exists
        risk_section = extract_section(content, "Risk Assessment")
        if risk_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.ERROR,
                    rule_id="RISK-001",
                    message="Risk Assessment section is missing",
                    suggestion="Add a '## Risk Assessment' section to the specification",
                )
            )
            return errors

        # Find the line number of the section
        section_line = find_section_line(content, "Risk Assessment")
        if section_line is None:
            section_line = 1

        # Check for risk identification
        risks_section = extract_section(risk_section, "Identified Risks")
        if risks_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="RISK-002",
                    message="Identified Risks subsection is missing",
                    suggestion="Add a '### Identified Risks' subsection to the Risk Assessment",
                )
            )
        else:
            # Check if risks are identified (either in a table or list)
            risks_table = extract_table(risks_section)
            risks_list = extract_list_items(risks_section)

            if not risks_table and not risks_list:
                risks_line = find_section_line(content, "Identified Risks")
                if risks_line is None:
                    risks_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=risks_line,
                        severity=Severity.ERROR,
                        rule_id="RISK-003",
                        message="No risks identified",
                        suggestion="Add a table or list of identified risks",
                    )
                )

            # If using a table, validate its structure
            if risks_table:
                if len(risks_table) < 2:
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=section_line,
                            severity=Severity.ERROR,
                            rule_id="RISK-004",
                            message="Risk assessment table must have at least a header row and one data row",
                            suggestion="Add table rows with risk information",
                        )
                    )
                else:
                    # Check for required columns
                    header = risks_table[0]
                    header_lower = [col.lower() for col in header]

                    required_columns = ["risk", "probability", "impact"]
                    missing_columns = [col for col in required_columns if col not in header_lower]

                    if missing_columns:
                        errors.append(
                            LintError(
                                file_path=str(filepath),
                                line_number=section_line,
                                severity=Severity.ERROR,
                                rule_id="RISK-005",
                                message=f"Risk assessment table missing required columns: {', '.join(missing_columns)}",
                                suggestion=f"Add columns for: {', '.join(required_columns)}",
                            )
                        )

                    # Check if probability and impact are specified for each risk
                    prob_col_index = None
                    impact_col_index = None

                    for i, col in enumerate(header_lower):
                        if "probability" in col:
                            prob_col_index = i
                        if "impact" in col:
                            impact_col_index = i

                    for i, row in enumerate(risks_table[1:], start=section_line + 1):
                        if row:
                            # Check probability
                            if prob_col_index is not None and len(row) > prob_col_index:
                                probability = row[prob_col_index].strip()
                                if not probability:
                                    risk_name = row[0].strip() if row else "Unknown"
                                    errors.append(
                                        LintError(
                                            file_path=str(filepath),
                                            line_number=i,
                                            severity=Severity.WARNING,
                                            rule_id="RISK-006",
                                            message=f"Risk '{risk_name}' missing probability assessment",
                                            suggestion="Specify the probability (e.g., Low, Medium, High)",
                                        )
                                    )

                            # Check impact
                            if impact_col_index is not None and len(row) > impact_col_index:
                                impact = row[impact_col_index].strip()
                                if not impact:
                                    risk_name = row[0].strip() if row else "Unknown"
                                    errors.append(
                                        LintError(
                                            file_path=str(filepath),
                                            line_number=i,
                                            severity=Severity.WARNING,
                                            rule_id="RISK-007",
                                            message=f"Risk '{risk_name}' missing impact assessment",
                                            suggestion="Specify the impact (e.g., Low, Medium, High)",
                                        )
                                    )

        # Check for mitigation strategies
        mitigation_section = extract_section(risk_section, "Mitigation Strategies")
        if mitigation_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="RISK-008",
                    message="Mitigation Strategies subsection is missing",
                    suggestion="Add a '### Mitigation Strategies' subsection to the Risk Assessment",
                )
            )
        else:
            # Check if mitigation strategies are specified
            mitigations = extract_list_items(mitigation_section)
            if not mitigations:
                mitigation_line = find_section_line(content, "Mitigation Strategies")
                if mitigation_line is None:
                    mitigation_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=mitigation_line,
                        severity=Severity.ERROR,
                        rule_id="RISK-009",
                        message="No mitigation strategies specified",
                        suggestion="Add a list of mitigation strategies for each identified risk",
                    )
                )

        return errors


__all__ = ["RiskAssessmentCheck"]
