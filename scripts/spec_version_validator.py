#!/usr/bin/env python3
"""
Specification Version Validator

Validates version numbers and compatibility across all Morph specifications
according to spec/conventions/version_compatibility_spec.md

Author: Kilo Code
Date: 2026-01-02
Version: 1.0.0
"""

import argparse
import re
import sys
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
import json


class VersionErrorType(Enum):
    """Types of version validation errors"""
    INVALID_FORMAT = "INVALID_FORMAT"
    INCOMPATIBLE_VERSIONS = "INCOMPATIBLE_VERSIONS"
    SYNC_GROUP_MISMATCH = "SYNC_GROUP_MISMATCH"
    VERSION_CONFLICT = "VERSION_CONFLICT"
    DEPENDENCY_MISMATCH = "DEPENDENCY_MISMATCH"
    EOL_VERSION = "EOL_VERSION"
    DEPRECATED_VERSION = "DEPRECATED_VERSION"


@dataclass
class Version:
    """Represents a semantic version"""
    major: int
    minor: int
    patch: int
    prerelease: Optional[str] = None
    build: Optional[str] = None

    def __str__(self) -> str:
        version = f"{self.major}.{self.minor}.{self.patch}"
        if self.prerelease:
            version += f"-{self.prerelease}"
        if self.build:
            version += f"+{self.build}"
        return version

    def __eq__(self, other) -> bool:
        if not isinstance(other, Version):
            return False
        return (self.major == other.major and
                self.minor == other.minor and
                self.patch == other.patch and
                self.prerelease == other.prerelease)

    def __lt__(self, other) -> bool:
        """Compare versions lexicographically"""
        # MASTER versions have highest precedence
        if self.is_master() and not other.is_master():
            return False
        if not self.is_master() and other.is_master():
            return True
        
        if self.major != other.major:
            return self.major < other.major
        if self.minor != other.minor:
            return self.minor < other.minor
        if self.patch != other.patch:
            return self.patch < other.patch
        
        # Handle prerelease versions
        if self.prerelease is None and other.prerelease is None:
            return False
        if self.prerelease is None:
            return False  # Release version > prerelease
        if other.prerelease is None:
            return True  # Prerelease < release version
        
        # Compare prerelease identifiers
        return self._compare_prerelease(self.prerelease, other.prerelease) < 0

    def __le__(self, other) -> bool:
        return self < other or self == other

    def __gt__(self, other) -> bool:
        return not self <= other

    def __ge__(self, other) -> bool:
        return not self < other

    def __hash__(self) -> int:
        return hash((self.major, self.minor, self.patch, self.prerelease))

    def _compare_prerelease(self, p1: str, p2: str) -> int:
        """Compare prerelease identifiers"""
        parts1 = p1.split('.')
        parts2 = p2.split('.')
        
        for i in range(max(len(parts1), len(parts2))):
            if i >= len(parts1):
                return -1
            if i >= len(parts2):
                return 1
            
            part1 = parts1[i]
            part2 = parts2[i]
            
            # Try numeric comparison
            try:
                num1 = int(part1)
                num2 = int(part2)
                if num1 != num2:
                    return num1 - num2
            except ValueError:
                # String comparison
                if part1 != part2:
                    return -1 if part1 < part2 else 1
        
        return 0

    def is_master(self) -> bool:
        """Check if this is a MASTER version"""
        return self.prerelease == "MASTER"

    def is_prerelease(self) -> bool:
        """Check if this is a prerelease version"""
        return self.prerelease is not None and not self.is_master()


@dataclass
class SpecInfo:
    """Information about a specification file"""
    path: Path
    name: str
    version: Version
    line_number: int
    status: str = "Active"
    layer: str = ""
    domain: str = ""


@dataclass
class VersionError:
    """Represents a version validation error"""
    error_type: VersionErrorType
    spec1: SpecInfo
    spec2: Optional[SpecInfo]
    message: str
    severity: str = "ERROR"  # ERROR, WARNING

    def __str__(self) -> str:
        if self.spec2:
            return f"{self.severity}: {self.message}\n  {self.spec1.path}:{self.spec1.line_number}\n  {self.spec2.path}:{self.spec2.line_number}"
        return f"{self.severity}: {self.message}\n  {self.spec1.path}:{self.spec1.line_number}"


class VersionValidator:
    """Validates version numbers and compatibility across specifications"""

    # Synchronization groups from version_compatibility_spec.md
    SYNC_GROUPS = {
        "core": [
            "morph_language_spec.md",
            "type_system_spec.md",
            "memory_model_spec.md",
            "execution_model_spec.md",
            "security_flow_spec.md",
        ],
        "type_system": [
            "type_system_spec.md",
            "type_category_spec.md",
            "type_unification_spec.md",
            "pure_type_spec.md",
            "effect_system_spec.md",
        ],
        "concurrency": [
            "execution_model_spec.md",
            "concurrency_process_algebra_spec.md",
            "monadic_effect_spec.md",
            "scheduling_modes_spec.md",
            "scheduler_randomized_stealing_spec.md",
            "layered_concurrency_spec.md",
        ],
    }

    # Dependency requirements from version_compatibility_spec.md
    DEPENDENCY_REQUIREMENTS = {
        "type_system_spec.md": {
            "morph_language_spec.md": "2.0.0",
        },
        "memory_model_spec.md": {
            "type_system_spec.md": "2.0.0",
        },
        "execution_model_spec.md": {
            "type_system_spec.md": "2.0.0",
            "memory_model_spec.md": "2.0.0",
        },
        "security_flow_spec.md": {
            "type_system_spec.md": "2.0.0",
        },
    }

    # EOL versions
    EOL_VERSIONS = {
        "1.0.0": "2026-07-02",
    }

    def __init__(self, spec_dir: Path):
        self.spec_dir = spec_dir
        self.specs: Dict[str, SpecInfo] = {}
        self.errors: List[VersionError] = []
        self.warnings: List[VersionError] = []

    def parse_version(self, version_str: str) -> Optional[Version]:
        """Parse a version string into a Version object"""
        # Remove build metadata for parsing
        version_str = version_str.split('+')[0]
        
        # Handle MASTER suffix
        is_master = False
        if version_str.endswith("-MASTER"):
            is_master = True
            version_str = version_str[:-7]
        
        # Parse MAJOR.MINOR.PATCH
        match = re.match(r'^(\d+)\.(\d+)\.(\d+)(?:-([a-zA-Z0-9.-]+))?$', version_str)
        if not match:
            return None
        
        major = int(match.group(1))
        minor = int(match.group(2))
        patch = int(match.group(3))
        prerelease = match.group(4)
        
        if is_master:
            prerelease = "MASTER"
        
        return Version(major, minor, patch, prerelease)

    def extract_version_from_file(self, file_path: Path) -> Optional[Tuple[Version, int]]:
        """Extract version from specification file header"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            for i, line in enumerate(lines, 1):
                # Look for version line in header
                if line.strip().startswith('**Version:**'):
                    # Extract version string
                    match = re.search(r'\*\*Version:\*\*\s*([^\s]+)', line)
                    if match:
                        version_str = match.group(1)
                        version = self.parse_version(version_str)
                        if version:
                            return version, i
        except Exception as e:
            print(f"Error reading {file_path}: {e}", file=sys.stderr)
        
        return None

    def load_specifications(self) -> None:
        """Load all specification files and extract version information"""
        spec_files = list(self.spec_dir.rglob("*.md"))
        
        for spec_file in spec_files:
            if spec_file.name == "README.md":
                continue
            
            result = self.extract_version_from_file(spec_file)
            if result:
                version, line_number = result
                spec_info = SpecInfo(
                    path=spec_file,
                    name=spec_file.name,
                    version=version,
                    line_number=line_number,
                )
                self.specs[spec_file.name] = spec_info
            else:
                # Warning: no version found
                self.warnings.append(VersionError(
                    error_type=VersionErrorType.INVALID_FORMAT,
                    spec1=SpecInfo(path=spec_file, name=spec_file.name, version=Version(0, 0, 0), line_number=1),
                    spec2=None,
                    message=f"No version found in specification header",
                    severity="WARNING"
                ))

    def validate_version_format(self) -> None:
        """Validate version format for all specifications"""
        for spec_name, spec_info in self.specs.items():
            version_str = str(spec_info.version)
            parsed = self.parse_version(version_str)
            
            if not parsed:
                self.errors.append(VersionError(
                    error_type=VersionErrorType.INVALID_FORMAT,
                    spec1=spec_info,
                    spec2=None,
                    message=f"Invalid version format: {version_str}. Expected MAJOR.MINOR.PATCH format"
                ))

    def check_compatibility(self, v1: Version, v2: Version) -> bool:
        """Check if two versions are compatible"""
        # Different MAJOR versions are incompatible
        if v1.major != v2.major:
            return False
        
        # Same MAJOR version is compatible
        return True

    def validate_compatibility(self) -> None:
        """Validate version compatibility between all specification pairs"""
        spec_names = list(self.specs.keys())
        
        for i in range(len(spec_names)):
            for j in range(i + 1, len(spec_names)):
                spec1 = self.specs[spec_names[i]]
                spec2 = self.specs[spec_names[j]]
                
                if not self.check_compatibility(spec1.version, spec2.version):
                    self.errors.append(VersionError(
                        error_type=VersionErrorType.INCOMPATIBLE_VERSIONS,
                        spec1=spec1,
                        spec2=spec2,
                        message=f"Incompatible versions: {spec1.version} vs {spec2.version}. Different MAJOR versions are incompatible."
                    ))

    def validate_synchronization_groups(self) -> None:
        """Validate version synchronization within synchronization groups"""
        for group_name, group_specs in self.SYNC_GROUPS.items():
            # Find specs in this group
            group_versions = []
            for spec_name in group_specs:
                if spec_name in self.specs:
                    group_versions.append((spec_name, self.specs[spec_name].version))
            
            if len(group_versions) < 2:
                continue
            
            # Check if all have the same MAJOR version
            major_versions = set(v.major for _, v in group_versions)
            if len(major_versions) > 1:
                # Create error message
                spec_list = "\n    ".join([f"{name}: {v}" for name, v in group_versions])
                for spec_name, version in group_versions:
                    spec_info = self.specs[spec_name]
                    self.errors.append(VersionError(
                        error_type=VersionErrorType.SYNC_GROUP_MISMATCH,
                        spec1=spec_info,
                        spec2=None,
                        message=f"Synchronization group '{group_name}' has inconsistent MAJOR versions:\n    {spec_list}"
                    ))

    def validate_dependencies(self) -> None:
        """Validate dependency version requirements"""
        for spec_name, dependencies in self.DEPENDENCY_REQUIREMENTS.items():
            if spec_name not in self.specs:
                continue
            
            spec_info = self.specs[spec_name]
            
            for dep_name, min_version_str in dependencies.items():
                if dep_name not in self.specs:
                    continue
                
                dep_info = self.specs[dep_name]
                min_version = self.parse_version(min_version_str)
                
                if not min_version:
                    continue
                
                if dep_info.version < min_version:
                    self.errors.append(VersionError(
                        error_type=VersionErrorType.DEPENDENCY_MISMATCH,
                        spec1=spec_info,
                        spec2=dep_info,
                        message=f"Dependency version mismatch: {spec_name} requires {dep_name} >= {min_version}, but found {dep_info.version}"
                    ))

    def check_eol_versions(self) -> None:
        """Check for End of Life versions"""
        for spec_name, spec_info in self.specs.items():
            version_str = f"{spec_info.version.major}.{spec_info.version.minor}.{spec_info.version.patch}"
            
            if version_str in self.EOL_VERSIONS:
                eol_date = self.EOL_VERSIONS[version_str]
                self.errors.append(VersionError(
                    error_type=VersionErrorType.EOL_VERSION,
                    spec1=spec_info,
                    spec2=None,
                    message=f"Version {version_str} is End of Life (EOL) since {eol_date}. Must upgrade to a supported version."
                ))

    def validate(self) -> Tuple[List[VersionError], List[VersionError]]:
        """Run all validation checks"""
        self.load_specifications()
        self.validate_version_format()
        self.validate_compatibility()
        self.validate_synchronization_groups()
        self.validate_dependencies()
        self.check_eol_versions()
        
        return self.errors, self.warnings

    def generate_report(self, output_format: str = "text") -> str:
        """Generate a compatibility report"""
        if output_format == "json":
            return self._generate_json_report()
        else:
            return self._generate_text_report()

    def _generate_text_report(self) -> str:
        """Generate a text format report"""
        lines = []
        lines.append("=" * 80)
        lines.append("SPECIFICATION VERSION VALIDATION REPORT")
        lines.append("=" * 80)
        lines.append("")
        
        # Summary
        lines.append("SUMMARY")
        lines.append("-" * 80)
        lines.append(f"Total specifications: {len(self.specs)}")
        lines.append(f"Errors: {len(self.errors)}")
        lines.append(f"Warnings: {len(self.warnings)}")
        lines.append("")
        
        # Version inventory
        lines.append("VERSION INVENTORY")
        lines.append("-" * 80)
        for spec_name in sorted(self.specs.keys()):
            spec_info = self.specs[spec_name]
            lines.append(f"  {spec_name}: {spec_info.version}")
        lines.append("")
        
        # Errors
        if self.errors:
            lines.append("ERRORS")
            lines.append("-" * 80)
            for error in self.errors:
                lines.append(str(error))
                lines.append("")
        
        # Warnings
        if self.warnings:
            lines.append("WARNINGS")
            lines.append("-" * 80)
            for warning in self.warnings:
                lines.append(str(warning))
                lines.append("")
        
        # Compatibility matrix
        lines.append("COMPATIBILITY MATRIX")
        lines.append("-" * 80)
        spec_names = sorted(self.specs.keys())
        for i in range(len(spec_names)):
            for j in range(i + 1, len(spec_names)):
                spec1 = self.specs[spec_names[i]]
                spec2 = self.specs[spec_names[j]]
                compatible = self.check_compatibility(spec1.version, spec2.version)
                status = "✅" if compatible else "❌"
                lines.append(f"  {status} {spec1.version} ({spec_names[i]}) <-> {spec2.version} ({spec_names[j]})")
        lines.append("")
        
        lines.append("=" * 80)
        return "\n".join(lines)

    def _generate_json_report(self) -> str:
        """Generate a JSON format report"""
        report = {
            "summary": {
                "total_specs": len(self.specs),
                "errors": len(self.errors),
                "warnings": len(self.warnings),
            },
            "specifications": [
                {
                    "name": spec_name,
                    "version": str(spec_info.version),
                    "path": str(spec_info.path),
                    "line_number": spec_info.line_number,
                }
                for spec_name, spec_info in sorted(self.specs.items())
            ],
            "errors": [
                {
                    "type": error.error_type.value,
                    "message": error.message,
                    "spec1": {
                        "name": error.spec1.name,
                        "version": str(error.spec1.version),
                        "path": str(error.spec1.path),
                        "line_number": error.spec1.line_number,
                    },
                    "spec2": {
                        "name": error.spec2.name,
                        "version": str(error.spec2.version),
                        "path": str(error.spec2.path),
                        "line_number": error.spec2.line_number,
                    } if error.spec2 else None,
                    "severity": error.severity,
                }
                for error in self.errors
            ],
            "warnings": [
                {
                    "type": warning.error_type.value,
                    "message": warning.message,
                    "spec1": {
                        "name": warning.spec1.name,
                        "version": str(warning.spec1.version),
                        "path": str(warning.spec1.path),
                        "line_number": warning.spec1.line_number,
                    },
                    "spec2": {
                        "name": warning.spec2.name,
                        "version": str(warning.spec2.version),
                        "path": str(warning.spec2.path),
                        "line_number": warning.spec2.line_number,
                    } if warning.spec2 else None,
                    "severity": warning.severity,
                }
                for warning in self.warnings
            ],
        }
        return json.dumps(report, indent=2)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Validate version numbers and compatibility across Morph specifications",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Validate all specifications
  python scripts/spec_version_validator.py

  # Validate specific directory
  python scripts/spec_version_validator.py --spec-dir ./spec

  # Generate JSON report
  python scripts/spec_version_validator.py --format json

  # Save report to file
  python scripts/spec_version_validator.py --output report.txt

  # Show only errors
  python scripts/spec_version_validator.py --errors-only
        """
    )
    
    parser.add_argument(
        "--spec-dir",
        type=Path,
        default=Path("spec"),
        help="Directory containing specification files (default: spec)"
    )
    
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)"
    )
    
    parser.add_argument(
        "--output",
        type=Path,
        help="Output file path (default: stdout)"
    )
    
    parser.add_argument(
        "--errors-only",
        action="store_true",
        help="Show only errors, not warnings"
    )
    
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress all output except errors"
    )
    
    args = parser.parse_args()
    
    # Create validator
    validator = VersionValidator(args.spec_dir)
    
    # Run validation
    errors, warnings = validator.validate()
    
    # Generate report
    report = validator.generate_report(args.format)
    
    # Output report
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(report)
        if not args.quiet:
            print(f"Report saved to {args.output}", file=sys.stderr)
    else:
        if not args.quiet:
            print(report)
    
    # Exit with error code if there are errors
    if errors:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()
