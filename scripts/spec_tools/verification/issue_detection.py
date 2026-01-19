"""
Automated Issue Detection Tool

This module provides tools for automatically detecting issues in Lean 4
specification files, following ADR-013 guidelines.

The tool supports:
- Detection of unclear specification points (USP)
- Detection of Lean 4 compilation failures (LCF)
- Detection of insufficient rigor (ISR)
- Detection of missing examples or lemmas (MEL)
- Detection of inconsistencies between files (IBF)
"""

import re
from pathlib import Path
from typing import List, Optional, Set, Tuple
from dataclasses import dataclass, field

from spec_tools.verification.models import (
    Issue,
    IssueCategory,
    IssueSeverity,
    IssueId,
)


@dataclass
class DetectionConfig:
    """Configuration for automated issue detection.

    Attributes:
        detect_usp: Whether to detect unclear specification points
        detect_lcf: Whether to detect Lean 4 compilation failures
        detect_isr: Whether to detect insufficient rigor
        detect_mel: Whether to detect missing examples or lemmas
        detect_ibf: Whether to detect inconsistencies between files
        strict_mode: Whether to treat warnings as errors
    """

    detect_usp: bool = True
    detect_lcf: bool = True
    detect_isr: bool = True
    detect_mel: bool = True
    detect_ibf: bool = True
    strict_mode: bool = False


class AutomatedIssueDetector:
    """Automatically detects issues in Lean 4 specification files.

    This class implements ADR-013's decision to use automated
    detection for identifying issues across the five categories defined
    in ADR-003.
    """

    # USP Detection Patterns
    _USP_PATTERNS = [
        (r'\b(appropriate|reasonable|sufficient|adequate)\b', "Ambiguous quantifier"),
        (r'\b(some|many|several|few)\b', "Ambiguous quantifier"),
        (r'\bshould\b', "Normative language"),
        (r'\bmust\b', "Strong requirement without formal definition"),
        (r'\bmay\b', "Permissive language without criteria"),
    ]

    # ISR Detection Patterns
    _ISR_PATTERNS = [
        (r'/\*\s*[^\n]*?\*/', "Informal comment block"),
        (r'^--\s*[^\n]*$', "Informal comment line"),
        (r'\b(described|defined|specified)\b.*?\b(informally|roughly|approximately)\b', "Informal description'),
        (r'\b(example|instance|case)\b.*?\b(like|similar to)\b', "Informal comparison'),
    ]

    # MEL Detection Patterns
    _MEL_FILE_PATTERNS = [
        (r'^\s*$', "Empty file"),
        (r'^/\*\s*\*/\s*$', "Only comment block"),
    ]

    def __init__(self, config: Optional[DetectionConfig] = None):
        """Initialize detector with optional configuration.

        Args:
            config: Detection configuration. If None, uses defaults.
        """
        self.config = config or DetectionConfig()
        self._category_counters = {
            IssueCategory.USP: 0,
            IssueCategory.LCF: 0,
            IssueCategory.ISR: 0,
            IssueCategory.MEL: 0,
            IssueCategory.IBF: 0,
        }

    def detect_issues(self, file_path: Path) -> List[Issue]:
        """Detect issues in a single Lean 4 file.

        Args:
            file_path: Path to Lean 4 file to analyze.

        Returns:
            List of Issue objects found in the file.
        """
        issues = []

        try:
            content = file_path.read_text(encoding='utf-8')
            lines = content.split('\n')

            # Detect USP issues
            if self.config.detect_usp:
                usp_issues = self._detect_usp_issues(file_path, lines)
                issues.extend(usp_issues)

            # Detect ISR issues
            if self.config.detect_isr:
                isr_issues = self._detect_isr_issues(file_path, lines)
                issues.extend(isr_issues)

            # Detect MEL issues
            if self.config.detect_mel:
                mel_issues = self._detect_mel_issues(file_path, lines, content)
                issues.extend(mel_issues)

            # Detect IBF issues
            if self.config.detect_ibf:
                ibf_issues = self._detect_ibf_issues(file_path, lines, content)
                issues.extend(ibf_issues)

        except Exception as e:
            issues.append(Issue(
                issue_id=IssueId(IssueCategory.USP, self._category_counters[IssueCategory.USP] + 1),
                category=IssueCategory.USP,
                severity=IssueSeverity.MEDIUM,
                spec_name=file_path.parent.name,
                file_path=file_path,
                line_numbers=[1],
                description=f"Error reading file: {str(e)}",
                detection_method="Automated Detection",
                suggested_fix="Ensure file is readable and properly formatted",
            ))

        return issues

    def detect_directory(self, directory: Path) -> List[Issue]:
        """Detect issues in all Lean 4 files in a directory.

        Args:
            directory: Path to directory containing Lean 4 files.

        Returns:
            List of Issue objects found in all files.
        """
        issues = []
        lean_files = list(directory.glob("**/*.lean"))

        for file_path in lean_files:
            file_issues = self.detect_issues(file_path)
            issues.extend(file_issues)

        return issues

    def detect_cross_file_inconsistencies(
        self,
        spec_dir: Path
    ) -> List[Issue]:
        """Detect inconsistencies between related files.

        Args:
            spec_dir: Path to specification directory containing
                      Spec.lean, Examples.lean, and Lemmas.lean.

        Returns:
            List of Issue objects representing cross-file inconsistencies.
        """
        issues = []

        # Get file paths
        spec_path = spec_dir / "Spec.lean"
        examples_path = spec_dir / "Examples.lean"
        lemmas_path = spec_dir / "Lemmas.lean"

        # Check which files exist
        files_to_check = []
        if spec_path.exists():
            files_to_check.append(spec_path)
        if examples_path.exists():
            files_to_check.append(examples_path)
        if lemmas_path.exists():
            files_to_check.append(lemmas_path)

        # Collect all definitions and examples
        all_definitions: Set[str] = set()
        all_examples: Set[str] = set()

        for file_path in files_to_check:
            try:
                content = file_path.read_text(encoding='utf-8')
                definitions = self._extract_definitions(content)
                examples = self._extract_examples(content)
                all_definitions.update(definitions)
                all_examples.update(examples)
            except Exception:
                continue

        # Check for inconsistencies
        if self.config.detect_ibf:
            ibf_issues = self._detect_ibf_cross_file(
                spec_dir, spec_path, examples_path, lemmas_path,
                all_definitions, all_examples
            )
            issues.extend(ibf_issues)

        return issues

    def _detect_usp_issues(
        self,
        file_path: Path,
        lines: List[str]
    ) -> List[Issue]:
        """Detect unclear specification points (USP).

        Args:
            file_path: Path to file being analyzed.
            lines: List of lines in the file.

        Returns:
            List of Issue objects for USP category.
        """
        issues = []
        content = '\n'.join(lines)

        for line_num, line in enumerate(lines, start=1):
            line = line.strip()

            # Skip comments and empty lines
            if not line or line.startswith('--') or line.startswith('/-'):
                continue

            # Check for USP patterns
            for pattern, description in self._USP_PATTERNS:
                if re.search(pattern, line, re.IGNORECASE):
                    self._category_counters[IssueCategory.USP] += 1
                    issues.append(Issue(
                        issue_id=IssueId(IssueCategory.USP, self._category_counters[IssueCategory.USP]),
                        category=IssueCategory.USP,
                        severity=IssueSeverity.MEDIUM,
                        spec_name=file_path.parent.name,
                        file_path=file_path,
                        line_numbers=[line_num],
                        description=f"Unclear specification: {description}",
                        detection_method="Automated USP Detection",
                        suggested_fix="Replace with formal definition or precise language",
                    ))

        return issues

    def _detect_isr_issues(
        self,
        file_path: Path,
        lines: List[str]
    ) -> List[Issue]:
        """Detect insufficient rigor (ISR).

        Args:
            file_path: Path to file being analyzed.
            lines: List of lines in the file.

        Returns:
            List of Issue objects for ISR category.
        """
        issues = []

        for line_num, line in enumerate(lines, start=1):
            line = line.strip()

            # Skip comments
            if line.startswith('--') or line.startswith('/-'):
                continue

            # Check for ISR patterns
            for pattern, description in self._ISR_PATTERNS:
                if re.search(pattern, line, re.IGNORECASE):
                    self._category_counters[IssueCategory.ISR] += 1
                    severity = IssueSeverity.HIGH if "informal" in description.lower() else IssueSeverity.MEDIUM
                    issues.append(Issue(
                        issue_id=IssueId(IssueCategory.ISR, self._category_counters[IssueCategory.ISR]),
                        category=IssueCategory.ISR,
                        severity=severity,
                        spec_name=file_path.parent.name,
                        file_path=file_path,
                        line_numbers=[line_num],
                        description=f"Insufficient rigor: {description}",
                        detection_method="Automated ISR Detection",
                        suggested_fix="Replace with formal definition using Lean 4 syntax",
                    ))

        return issues

    def _detect_mel_issues(
        self,
        file_path: Path,
        lines: List[str],
        content: str
    ) -> List[Issue]:
        """Detect missing examples or lemmas (MEL).

        Args:
            file_path: Path to file being analyzed.
            lines: List of lines in the file.
            content: Full content of the file.

        Returns:
            List of Issue objects for MEL category.
        """
        issues = []

        # Check if file is empty or only comments
        is_empty = True
        for line in lines:
            stripped = line.strip()
            if stripped and not stripped.startswith('--') and not stripped.startswith('/-'):
                is_empty = False
                break

        if is_empty:
            self._category_counters[IssueCategory.MEL] += 1
            issues.append(Issue(
                issue_id=IssueId(IssueCategory.MEL, self._category_counters[IssueCategory.MEL]),
                category=IssueCategory.MEL,
                severity=IssueSeverity.HIGH,
                spec_name=file_path.parent.name,
                file_path=file_path,
                line_numbers=[1],
                description="File is empty or contains only comments",
                detection_method="Automated MEL Detection",
                suggested_fix="Add examples or lemmas to this file",
            ))

        # Check for missing examples in Examples.lean
        if file_path.name == "Examples.lean":
            example_count = self._extract_examples(content)
            if len(example_count) < 3:
                self._category_counters[IssueCategory.MEL] += 1
                issues.append(Issue(
                    issue_id=IssueId(IssueCategory.MEL, self._category_counters[IssueCategory.MEL]),
                    category=IssueCategory.MEL,
                    severity=IssueSeverity.MEDIUM,
                    spec_name=file_path.parent.name,
                    file_path=file_path,
                    line_numbers=[],
                    description=f"Insufficient examples: only {len(example_count)} examples found",
                    detection_method="Automated MEL Detection",
                    suggested_fix="Add more examples covering edge cases",
                ))

        # Check for missing lemmas in Lemmas.lean
        if file_path.name == "Lemmas.lean":
            lemma_count = self._extract_lemmas(content)
            if len(lemma_count) < 3:
                self._category_counters[IssueCategory.MEL] += 1
                issues.append(Issue(
                    issue_id=IssueId(IssueCategory.MEL, self._category_counters[IssueCategory.MEL]),
                    category=IssueCategory.MEL,
                    severity=IssueSeverity.HIGH,
                    spec_name=file_path.parent.name,
                    file_path=file_path,
                    line_numbers=[],
                    description=f"Insufficient lemmas: only {len(lemma_count)} lemmas found",
                    detection_method="Automated MEL Detection",
                    suggested_fix="Add lemmas for key specification properties",
                ))

        return issues

    def _detect_ibf_issues(
        self,
        file_path: Path,
        lines: List[str],
        content: str
    ) -> List[Issue]:
        """Detect inconsistencies within a single file (IBF).

        Args:
            file_path: Path to file being analyzed.
            lines: List of lines in the file.
            content: Full content of the file.

        Returns:
            List of Issue objects for IBF category.
        """
        issues = []

        # Extract all definitions
        definitions = self._extract_definitions(content)

        # Check for duplicate definitions
        definition_counts: Dict[str, List[int]] = {}
        for line_num, line in enumerate(lines, start=1):
            match = re.match(r'def\s+(\w+)', line)
            if match:
                def_name = match.group(1)
                if def_name not in definition_counts:
                    definition_counts[def_name] = []
                definition_counts[def_name].append(line_num)

        for def_name, line_nums in definition_counts.items():
            if len(line_nums) > 1:
                self._category_counters[IssueCategory.IBF] += 1
                issues.append(Issue(
                    issue_id=IssueId(IssueCategory.IBF, self._category_counters[IssueCategory.IBF]),
                    category=IssueCategory.IBF,
                    severity=IssueSeverity.MEDIUM,
                    spec_name=file_path.parent.name,
                    file_path=file_path,
                    line_numbers=line_nums,
                    description=f"Duplicate definition: '{def_name}' defined at lines {line_nums}",
                    detection_method="Automated IBF Detection",
                    suggested_fix="Remove duplicate definition or rename one",
                ))

        return issues

    def _detect_ibf_cross_file(
        self,
        spec_dir: Path,
        spec_path: Path,
        examples_path: Path,
        lemmas_path: Path,
        all_definitions: Set[str],
        all_examples: Set[str]
    ) -> List[Issue]:
        """Detect inconsistencies between related files (IBF).

        Args:
            spec_dir: Path to specification directory.
            spec_path: Path to Spec.lean file.
            examples_path: Path to Examples.lean file.
            lemmas_path: Path to Lemmas.lean file.
            all_definitions: Set of all definitions found.
            all_examples: Set of all examples found.

        Returns:
            List of Issue objects for IBF category.
        """
        issues = []

        # Check if Examples.lean references non-existent definitions
        if examples_path.exists():
            try:
                content = examples_path.read_text(encoding='utf-8')
                referenced = self._extract_references(content)
                undefined = referenced - all_definitions

                if undefined:
                    self._category_counters[IssueCategory.IBF] += 1
                    issues.append(Issue(
                        issue_id=IssueId(IssueCategory.IBF, self._category_counters[IssueCategory.IBF]),
                        category=IssueCategory.IBF,
                        severity=IssueSeverity.HIGH,
                        spec_name=spec_dir.name,
                        file_path=examples_path,
                        line_numbers=[],
                        description=f"Examples reference undefined definitions: {', '.join(undefined)}",
                        detection_method="Automated IBF Cross-File Detection",
                        suggested_fix="Add missing definitions to Spec.lean or remove references",
                    ))
            except Exception:
                pass

        # Check if Lemmas.lean references non-existent definitions
        if lemmas_path.exists():
            try:
                content = lemmas_path.read_text(encoding='utf-8')
                referenced = self._extract_references(content)
                undefined = referenced - all_definitions

                if undefined:
                    self._category_counters[IssueCategory.IBF] += 1
                    issues.append(Issue(
                        issue_id=IssueId(IssueCategory.IBF, self._category_counters[IssueCategory.IBF]),
                        category=IssueCategory.IBF,
                        severity=IssueSeverity.HIGH,
                        spec_name=spec_dir.name,
                        file_path=lemmas_path,
                        line_numbers=[],
                        description=f"Lemmas reference undefined definitions: {', '.join(undefined)}",
                        detection_method="Automated IBF Cross-File Detection",
                        suggested_fix="Add missing definitions to Spec.lean or remove references",
                    ))
            except Exception:
                pass

        return issues

    def _extract_definitions(self, content: str) -> Set[str]:
        """Extract all definition names from Lean 4 code.

        Args:
            content: Lean 4 file content.

        Returns:
            Set of definition names found.
        """
        definitions = set()

        # Match def, structure, inductive, class definitions
        patterns = [
            r'def\s+(\w+)',
            r'structure\s+(\w+)',
            r'inductive\s+(\w+)',
            r'class\s+(\w+)',
        ]

        for pattern in patterns:
            for match in re.finditer(pattern, content):
                definitions.add(match.group(1))

        return definitions

    def _extract_examples(self, content: str) -> Set[str]:
        """Extract all example names from Lean 4 code.

        Args:
            content: Lean 4 file content.

        Returns:
            Set of example names found.
        """
        examples = set()

        # Match example, theorem, lemma declarations
        patterns = [
            r'example\s+:\s*(\w+)',
            r'theorem\s+(\w+)',
            r'lemma\s+(\w+)',
        ]

        for pattern in patterns:
            for match in re.finditer(pattern, content):
                examples.add(match.group(1))

        return examples

    def _extract_lemmas(self, content: str) -> Set[str]:
        """Extract all lemma names from Lean 4 code.

        Args:
            content: Lean 4 file content.

        Returns:
            Set of lemma names found.
        """
        lemmas = set()

        # Match lemma declarations
        pattern = r'lemma\s+(\w+)'

        for match in re.finditer(pattern, content):
            lemmas.add(match.group(1))

        return lemmas

    def _extract_references(self, content: str) -> Set[str]:
        """Extract all referenced names from Lean 4 code.

        Args:
            content: Lean 4 file content.

        Returns:
            Set of referenced names found.
        """
        references = set()

        # Match variable/function references (simplified)
        pattern = r'\b([A-Z][a-zA-Z0-9_]*)\b'

        for match in re.finditer(pattern, content):
            references.add(match.group(1))

        return references

    def get_statistics(self, issues: List[Issue]) -> Dict[str, int]:
        """Get issue statistics from detected issues.

        Args:
            issues: List of Issue objects.

        Returns:
            Dictionary with issue statistics.
        """
        stats = {
            "total_issues": len(issues),
        }

        for category in IssueCategory:
            count = sum(1 for i in issues if i.category == category)
            stats[f"{category.value}_count"] = count

        for severity in IssueSeverity:
            count = sum(1 for i in issues if i.severity == severity)
            stats[f"{severity.value}_count"] = count

        return stats
