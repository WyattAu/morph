"""
Validate Command Handler

This module implements the validate command for the spec-tools CLI.
"""

import sys
from pathlib import Path
from typing import Any, List

from spec_tools.models import Config, ValidationResult
from spec_tools.exceptions import SpecToolsError
from spec_tools.validation import SpecValidator


def run_validate_command(args: Any, config: Config) -> int:
    """
    Run the validate command.
    
    Args:
        args: Parsed command-line arguments
        config: Configuration instance
        
    Returns:
        Exit code (0 for success, 1 for errors)
    """
    path = Path(args.path)
    
    # Validate path exists
    if not path.exists():
        print(f"Error: Path not found: {path}", file=sys.stderr)
        return 1
    
    # Update config with command-line arguments
    if args.check_traceability:
        config.validation.check_traceability = True
    if args.check_security:
        config.validation.check_security_specs = True
    if args.check_performance:
        config.validation.check_performance_specs = True
    if args.check_maintainability:
        config.validation.check_maintainability_specs = True
    if args.check_risk:
        config.validation.check_risk_assessment = True
    if args.check_verification:
        config.validation.check_verification_plan = True
    
    # If no specific checks are enabled, enable all
    if not any([
        args.check_traceability,
        args.check_security,
        args.check_performance,
        args.check_maintainability,
        args.check_risk,
        args.check_verification,
    ]):
        config.validation.check_traceability = True
        config.validation.check_security_specs = True
        config.validation.check_performance_specs = True
        config.validation.check_maintainability_specs = True
        config.validation.check_risk_assessment = True
        config.validation.check_verification_plan = True
    
    # Create validator with config
    validator = SpecValidator(config.validation)
    
    # Process file or directory
    if path.is_file():
        return _validate_file(validator, path)
    elif path.is_dir():
        return _validate_directory(validator, path)
    else:
        print(f"Error: Not a file or directory: {path}", file=sys.stderr)
        return 1


def _validate_file(validator: SpecValidator, filepath: Path) -> int:
    """
    Validate a single file.
    
    Args:
        validator: SpecValidator instance
        filepath: Path to the file
        
    Returns:
        Exit code (0 for success, 1 for errors)
    """
    try:
        result = validator.validate_file(filepath)
        return _display_validation_result(result)
            
    except SpecToolsError as e:
        print(f"Error validating {filepath}: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Unexpected error validating {filepath}: {e}", file=sys.stderr)
        return 1


def _validate_directory(validator: SpecValidator, directory: Path) -> int:
    """
    Validate all files in a directory.
    
    Args:
        validator: SpecValidator instance
        directory: Path to the directory
        
    Returns:
        Exit code (0 for success, 1 if any file has errors)
    """
    try:
        # Find all markdown files
        md_files = list(directory.rglob("*.md"))
        
        if not md_files:
            print(f"No markdown files found in {directory}")
            return 0
        
        print(f"Validating {len(md_files)} file(s) in {directory}...")
        
        # Validate all files
        results: List[ValidationResult] = validator.validate_directory(directory, recursive=True)
        
        # Display results
        total_errors = 0
        total_warnings = 0
        failed_files = 0
        
        for result in results:
            if not result.passed:
                failed_files += 1
                total_errors += result.error_count
                total_warnings += result.warning_count
        
        # Display individual file results
        for result in results:
            _display_validation_result(result, show_summary=False)
        
        # Display summary
        print(f"\n{'='*60}")
        print(f"Validation Summary:")
        print(f"  Files processed: {len(results)}")
        print(f"  Files with issues: {failed_files}")
        print(f"  Errors: {total_errors}")
        print(f"  Warnings: {total_warnings}")
        
        if total_errors > 0:
            print(f"\n✗ Validation failed with {total_errors} error(s)")
            return 1
        elif total_warnings > 0:
            print(f"\n✓ Validation passed with {total_warnings} warning(s)")
            return 0
        else:
            print(f"\n✓ All files passed validation")
            return 0
            
    except SpecToolsError as e:
        print(f"Error validating directory: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Unexpected error validating directory: {e}", file=sys.stderr)
        return 1


def _display_validation_result(
    result: ValidationResult,
    show_summary: bool = True
) -> int:
    """
    Display validation result for a file.
    
    Args:
        result: ValidationResult instance
        show_summary: If True, show summary line
        
    Returns:
        Exit code (0 for success, 1 for errors)
    """
    if result.passed:
        if show_summary:
            print(f"✓ {result.file_path}: Validation passed")
        return 0
    
    # Display errors and warnings
    print(f"✗ {result.file_path}:")
    
    for error in result.errors:
        severity_str = error.severity.value
        location = f"Line {error.line_number}"
        if error.column_number > 0:
            location += f":{error.column_number}"
        
        print(f"  {location} [{severity_str}] {error.rule_id}: {error.message}")
        
        if error.suggestion:
            print(f"    Suggestion: {error.suggestion}")
    
    # Determine exit code
    if result.error_count > 0:
        return 1
    
    return 0
