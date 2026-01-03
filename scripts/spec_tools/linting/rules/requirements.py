"""
EARS pattern validation rule.

This module implements the EARSValidationRule which validates
requirements against the EARS (Easy Approach to Requirements Syntax) pattern.
"""

import re
from pathlib import Path
from typing import List, Set

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class EARSValidationRule(LintingRule):
    """Validates requirements using EARS pattern.

    This rule checks that:
    - Requirement IDs follow the format REQ-XXX
    - No duplicate requirement IDs exist
    - Requirements use EARS pattern keywords
    - Required attributes (Priority, Verification Method) are present

    EARS pattern keywords:
    - The system shall...
    - The system shall, when..., ...
    - Where..., the system shall...
    - If..., then the system shall...
    - When..., the system shall...
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Validates requirements against EARS pattern"

    def __init__(self):
        """Initialize EARS validation rule."""
        self._req_id_pattern = re.compile(r"REQ-\d+")
        self._ears_keywords = [
            "shall",
            "shall, when",
            "shall, if",
            "shall, where",
        ]
        self._ears_pattern = re.compile(
            r"(The system\s+shall(?:,\s+(?:when|if|where)\s+[^.]+)?)",
            re.IGNORECASE,
        )
        self._req_pattern = re.compile(r"^\s*REQ-\d+:\s*(.+)$")

    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content complies with EARS pattern.

        Args:
            content: Full content of file
            lines: List of lines in file
            filepath: File path for error reporting

        Returns:
            List of EARS validation errors
        """
        errors = []
        requirements = self._extract_requirements(lines)

        # Check for duplicate requirement IDs
        req_ids = [req["id"] for req in requirements]
        duplicates = self._find_duplicates(req_ids)
        for req_id in duplicates:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.ERROR,
                    rule_id="ears-validation",
                    message=f"Duplicate requirement ID: {req_id}",
                    suggestion="Use unique requirement IDs",
                )
            )

        # Validate each requirement
        for req in requirements:
            self._validate_requirement(req, filepath, errors)

        return errors

    def _extract_requirements(self, lines: List[str]) -> List[dict]:
        """Extract all requirements from file lines.

        Args:
            lines: List of lines in file

        Returns:
            List of requirement dictionaries
        """
        requirements = []

        for line_num, line in enumerate(lines, start=1):
            match = self._req_pattern.match(line)
            if match:
                req_id = line.split(":")[0].strip()
                req_text = match.group(1).strip()
                requirements.append(
                    {
                        "id": req_id,
                        "text": req_text,
                        "line_number": line_num,
                    }
                )

        return requirements

    def _find_duplicates(self, items: List[str]) -> Set[str]:
        """Find duplicate items in a list.

        Args:
            items: List of items to check

        Returns:
            Set of duplicate items
        """
        seen = set()
        duplicates = set()

        for item in items:
            if item in seen:
                duplicates.add(item)
            else:
                seen.add(item)

        return duplicates

    def _validate_requirement(
        self, req: dict, filepath: Path, errors: List[LintError]
    ) -> None:
        """Validate a single requirement.

        Args:
            req: Requirement dictionary
            filepath: File path for error reporting
            errors: List to append errors to
        """
        # Validate requirement ID format
        if not self._req_id_pattern.match(req["id"]):
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=req["line_number"],
                    severity=Severity.ERROR,
                    rule_id="ears-validation",
                    message=f"Invalid requirement ID format: {req['id']} (must be REQ-XXX)",
                    suggestion="Use format REQ-XXX where XXX is a number",
                    context=req["id"],
                )
            )

        # Validate EARS pattern compliance
        if not self._ears_pattern.search(req["text"]):
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=req["line_number"],
                    severity=Severity.WARNING,
                    rule_id="ears-validation",
                    message=f"Requirement does not follow EARS pattern",
                    suggestion="Use EARS pattern: 'The system shall...' or 'The system shall, when/where/if...'",
                    context=req["text"][:80] + "..." if len(req["text"]) > 80 else req["text"],
                )
            )

        # Check for required attributes (Priority, Verification Method)
        # These are typically in the same or following lines
        # For simplicity, we check if they appear in the requirement text
        has_priority = "Priority:" in req["text"] or "Priority " in req["text"]
        has_verification = (
            "Verification Method:" in req["text"]
            or "Verification Method " in req["text"]
        )

        if not has_priority:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=req["line_number"],
                    severity=Severity.WARNING,
                    rule_id="ears-validation",
                    message=f"Requirement missing Priority attribute",
                    suggestion="Add 'Priority: <value>' to requirement",
                    context=req["id"],
                )
            )

        if not has_verification:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=req["line_number"],
                    severity=Severity.WARNING,
                    rule_id="ears-validation",
                    message=f"Requirement missing Verification Method attribute",
                    suggestion="Add 'Verification Method: <value>' to requirement",
                    context=req["id"],
                )
            )
