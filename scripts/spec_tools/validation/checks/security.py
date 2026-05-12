"""
Security specification validation check for specification files.

This module implements validation for security specifications in specification
files, ensuring that STRIDE threat modeling and security controls are properly
defined.
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


class SecuritySpecCheck(ValidationCheck):
    """Validates security specifications in specification files.

    This check ensures that:
    1. A security specifications section exists
    2. STRIDE threat modeling is included
    3. Security controls are specified for each threat
    4. Preventive, detective, and corrective controls are defined

    Attributes:
        description: Human-readable description of this check
    """

    @property
    def description(self) -> str:
        """Get description of this check."""
        return "Validates security specifications and ensures STRIDE threat modeling and controls are defined"

    def validate(self, content: str, filepath: Path) -> List[LintError]:
        """Validate security specifications in the content.

        Args:
            content: The content of the specification file
            filepath: Path to the file being validated

        Returns:
            List of validation errors found
        """
        errors: List[LintError] = []

        # Check if security specifications section exists
        security_section = extract_section(content, "Security Specifications")
        if security_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.ERROR,
                    rule_id="SECURITY-001",
                    message="Security Specifications section is missing",
                    suggestion="Add a '## Security Specifications' section to the specification",
                )
            )
            return errors

        # Find the line number of the section
        section_line = find_section_line(content, "Security Specifications")
        if section_line is None:
            section_line = 1

        # Check for STRIDE threat modeling
        stride_section = extract_section(security_section, "STRIDE Threat Modeling")
        if stride_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="SECURITY-002",
                    message="STRIDE Threat Modeling subsection is missing",
                    suggestion="Add a '### STRIDE Threat Modeling' subsection to the Security Specifications",
                )
            )
        else:
            # Check if threats are identified
            threats_table = extract_table(stride_section)
            threats_list = extract_list_items(stride_section)

            if not threats_table and not threats_list:
                stride_line = find_section_line(content, "STRIDE Threat Modeling")
                if stride_line is None:
                    stride_line = section_line
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=stride_line,
                        severity=Severity.ERROR,
                        rule_id="SECURITY-003",
                        message="No threats identified in STRIDE model",
                        suggestion="Add a table or list of threats using STRIDE categories (Spoofing, Tampering, Repudiation, Information Disclosure, Denial of Service, Elevation of Privilege)",
                    )
                )

            # If using a table, validate its structure
            if threats_table:
                if len(threats_table) < 2:
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=section_line,
                            severity=Severity.ERROR,
                            rule_id="SECURITY-004",
                            message="STRIDE threat table must have at least a header row and one data row",
                            suggestion="Add table rows with threat information",
                        )
                    )
                else:
                    # Check for required columns
                    header = threats_table[0]
                    header_lower = [col.lower() for col in header]

                    required_columns = ["threat", "category"]
                    missing_columns = [col for col in required_columns if col not in header_lower]

                    if missing_columns:
                        errors.append(
                            LintError(
                                file_path=str(filepath),
                                line_number=section_line,
                                severity=Severity.ERROR,
                                rule_id="SECURITY-005",
                                message=f"STRIDE threat table missing required columns: {', '.join(missing_columns)}",
                                suggestion=f"Add columns for: {', '.join(required_columns)}",
                            )
                        )

                    # Check if security controls are specified for each threat
                    control_col_index = None

                    for i, col in enumerate(header_lower):
                        if "control" in col:
                            control_col_index = i
                            break

                    if control_col_index is None:
                        errors.append(
                            LintError(
                                file_path=str(filepath),
                                line_number=section_line,
                                severity=Severity.WARNING,
                                rule_id="SECURITY-006",
                                message="STRIDE threat table missing security controls column",
                                suggestion="Add a column for security controls",
                            )
                        )
                    else:
                        for i, row in enumerate(threats_table[1:], start=section_line + 1):
                            if row and len(row) > control_col_index:
                                controls = row[control_col_index].strip()
                                if not controls:
                                    threat_name = row[0].strip() if row else "Unknown"
                                    errors.append(
                                        LintError(
                                            file_path=str(filepath),
                                            line_number=i,
                                            severity=Severity.WARNING,
                                            rule_id="SECURITY-007",
                                            message=f"Threat '{threat_name}' missing security controls",
                                            suggestion="Specify security controls to mitigate this threat",
                                        )
                                    )

        # Check for security controls section
        controls_section = extract_section(security_section, "Security Controls")
        if controls_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="SECURITY-008",
                    message="Security Controls subsection is missing",
                    suggestion="Add a '### Security Controls' subsection to the Security Specifications",
                )
            )
        else:
            # Check for preventive controls
            preventive_section = extract_section(controls_section, "Preventive Controls")
            if preventive_section is None:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=section_line,
                        severity=Severity.WARNING,
                        rule_id="SECURITY-009",
                        message="Preventive Controls subsection is missing",
                        suggestion="Add a '#### Preventive Controls' subsection to specify preventive security controls",
                    )
                )
            else:
                preventive_controls = extract_list_items(preventive_section)
                if not preventive_controls:
                    preventive_line = find_section_line(content, "Preventive Controls")
                    if preventive_line is None:
                        preventive_line = section_line
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=preventive_line,
                            severity=Severity.WARNING,
                            rule_id="SECURITY-010",
                            message="No preventive controls specified",
                            suggestion="Add a list of preventive security controls",
                        )
                    )

            # Check for detective controls
            detective_section = extract_section(controls_section, "Detective Controls")
            if detective_section is None:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=section_line,
                        severity=Severity.WARNING,
                        rule_id="SECURITY-011",
                        message="Detective Controls subsection is missing",
                        suggestion="Add a '#### Detective Controls' subsection to specify detective security controls",
                    )
                )
            else:
                detective_controls = extract_list_items(detective_section)
                if not detective_controls:
                    detective_line = find_section_line(content, "Detective Controls")
                    if detective_line is None:
                        detective_line = section_line
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=detective_line,
                            severity=Severity.WARNING,
                            rule_id="SECURITY-012",
                            message="No detective controls specified",
                            suggestion="Add a list of detective security controls",
                        )
                    )

            # Check for corrective controls
            corrective_section = extract_section(controls_section, "Corrective Controls")
            if corrective_section is None:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=section_line,
                        severity=Severity.WARNING,
                        rule_id="SECURITY-013",
                        message="Corrective Controls subsection is missing",
                        suggestion="Add a '#### Corrective Controls' subsection to specify corrective security controls",
                    )
                )
            else:
                corrective_controls = extract_list_items(corrective_section)
                if not corrective_controls:
                    corrective_line = find_section_line(content, "Corrective Controls")
                    if corrective_line is None:
                        corrective_line = section_line
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=corrective_line,
                            severity=Severity.WARNING,
                            rule_id="SECURITY-014",
                            message="No corrective controls specified",
                            suggestion="Add a list of corrective security controls",
                        )
                    )

        return errors


__all__ = ["SecuritySpecCheck"]
