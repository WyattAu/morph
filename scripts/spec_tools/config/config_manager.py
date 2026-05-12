"""
Configuration manager for the spec_tools package.

This module provides functionality for loading, saving, and managing
configuration for the spec-tools package using YAML format.
"""

from pathlib import Path

import yaml

from spec_tools.exceptions import ValidationError
from spec_tools.models import (
    Config,
    FormattingConfig,
    LinkCheckingConfig,
    LintingConfig,
    OutputConfig,
    ValidationConfig,
)


class ConfigManager:
    """Manager for loading and saving configuration files.

    This class provides methods to load configuration from YAML files,
    save configuration to YAML files, and get default configuration
    values. It also validates configuration values to ensure they are
    within acceptable ranges.
    """

    @staticmethod
    def load_config(filepath: Path) -> Config:
        """Load configuration from a YAML file.

        Args:
            filepath: Path to the YAML configuration file

        Returns:
            Config object with loaded values

        Raises:
            ValidationError: If the file cannot be read or contains invalid data
        """
        try:
            with open(filepath, encoding="utf-8") as f:
                data = yaml.safe_load(f)
        except FileNotFoundError as e:
            raise ValidationError(
                f"Configuration file not found: {filepath}",
                file_path=str(filepath),
            ) from e
        except yaml.YAMLError as e:
            raise ValidationError(
                f"Invalid YAML in configuration file: {filepath}",
                file_path=str(filepath),
                details={"error": str(e)},
            ) from e
        except Exception as e:
            raise ValidationError(
                f"Error reading configuration file: {filepath}",
                file_path=str(filepath),
                details={"error": str(e)},
            ) from e

        if data is None:
            return Config()

        return ConfigManager._parse_config(data, filepath)

    @staticmethod
    def save_config(config: Config, filepath: Path) -> None:
        """Save configuration to a YAML file.

        Args:
            config: Config object to save
            filepath: Path where the configuration file should be saved

        Raises:
            ValidationError: If the file cannot be written
        """
        try:
            # Ensure parent directory exists
            filepath.parent.mkdir(parents=True, exist_ok=True)

            # Convert config to dictionary
            data = ConfigManager._config_to_dict(config)

            with open(filepath, "w", encoding="utf-8") as f:
                yaml.dump(data, f, default_flow_style=False, sort_keys=False)
        except Exception as e:
            raise ValidationError(
                f"Error writing configuration file: {filepath}",
                file_path=str(filepath),
                details={"error": str(e)},
            ) from e

    @staticmethod
    def get_default_config() -> Config:
        """Get default configuration.

        Returns:
            Config object with default values
        """
        return Config()

    @staticmethod
    def _parse_config(data: dict, filepath: Path) -> Config:
        """Parse configuration dictionary into Config object.

        Args:
            data: Dictionary containing configuration data
            filepath: Path to the configuration file (for error reporting)

        Returns:
            Config object with parsed values

        Raises:
            ValidationError: If configuration values are invalid
        """
        # Parse formatting config
        formatting_data = data.get("formatting", {})
        formatting = FormattingConfig(
            max_line_length=formatting_data.get("max_line_length", 120),
            enforce_trailing_whitespace=formatting_data.get("enforce_trailing_whitespace", True),
            normalize_lists=formatting_data.get("normalize_lists", True),
            fix_heading_spacing=formatting_data.get("fix_heading_spacing", True),
            normalize_emphasis=formatting_data.get("normalize_emphasis", True),
        )
        ConfigManager._validate_formatting_config(formatting, filepath)

        # Parse linting config
        linting_data = data.get("linting", {})
        linting = LintingConfig(
            strict=linting_data.get("strict", False),
            check_ears_pattern=linting_data.get("check_ears_pattern", True),
            check_math_notation=linting_data.get("check_math_notation", True),
            check_mermaid_syntax=linting_data.get("check_mermaid_syntax", True),
            check_cross_references=linting_data.get("check_cross_references", True),
        )

        # Parse validation config
        validation_data = data.get("validation", {})
        validation = ValidationConfig(
            check_traceability=validation_data.get("check_traceability", True),
            check_verification_plan=validation_data.get("check_verification_plan", True),
            check_risk_assessment=validation_data.get("check_risk_assessment", True),
            check_security_specs=validation_data.get("check_security_specs", True),
            check_performance_specs=validation_data.get("check_performance_specs", True),
            check_maintainability_specs=validation_data.get("check_maintainability_specs", True),
        )

        # Parse link checking config
        link_checking_data = data.get("link_checking", {})
        link_checking = LinkCheckingConfig(
            check_broken_links=link_checking_data.get("check_broken_links", True),
            check_orphaned_sections=link_checking_data.get("check_orphaned_sections", True),
            check_duplicate_links=link_checking_data.get("check_duplicate_links", True),
            check_self_references=link_checking_data.get("check_self_references", False),
        )

        # Parse output config
        output_data = data.get("output", {})
        output = OutputConfig(
            format=output_data.get("format", "text"),
            verbose=output_data.get("verbose", False),
            quiet=output_data.get("quiet", False),
            color_output=output_data.get("color_output", True),
        )
        ConfigManager._validate_output_config(output, filepath)

        return Config(
            formatting=formatting,
            linting=linting,
            validation=validation,
            link_checking=link_checking,
            output=output,
        )

    @staticmethod
    def _config_to_dict(config: Config) -> dict:
        """Convert Config object to dictionary.

        Args:
            config: Config object to convert

        Returns:
            Dictionary representation of the configuration
        """
        return {
            "formatting": {
                "max_line_length": config.formatting.max_line_length,
                "enforce_trailing_whitespace": config.formatting.enforce_trailing_whitespace,
                "normalize_lists": config.formatting.normalize_lists,
                "fix_heading_spacing": config.formatting.fix_heading_spacing,
                "normalize_emphasis": config.formatting.normalize_emphasis,
            },
            "linting": {
                "strict": config.linting.strict,
                "check_ears_pattern": config.linting.check_ears_pattern,
                "check_math_notation": config.linting.check_math_notation,
                "check_mermaid_syntax": config.linting.check_mermaid_syntax,
                "check_cross_references": config.linting.check_cross_references,
            },
            "validation": {
                "check_traceability": config.validation.check_traceability,
                "check_verification_plan": config.validation.check_verification_plan,
                "check_risk_assessment": config.validation.check_risk_assessment,
                "check_security_specs": config.validation.check_security_specs,
                "check_performance_specs": config.validation.check_performance_specs,
                "check_maintainability_specs": config.validation.check_maintainability_specs,
            },
            "link_checking": {
                "check_broken_links": config.link_checking.check_broken_links,
                "check_orphaned_sections": config.link_checking.check_orphaned_sections,
                "check_duplicate_links": config.link_checking.check_duplicate_links,
                "check_self_references": config.link_checking.check_self_references,
            },
            "output": {
                "format": config.output.format,
                "verbose": config.output.verbose,
                "quiet": config.output.quiet,
                "color_output": config.output.color_output,
            },
        }

    @staticmethod
    def _validate_formatting_config(config: FormattingConfig, filepath: Path) -> None:
        """Validate formatting configuration values.

        Args:
            config: FormattingConfig to validate
            filepath: Path to the configuration file (for error reporting)

        Raises:
            ValidationError: If configuration values are invalid
        """
        if config.max_line_length < 40:
            raise ValidationError(
                f"max_line_length must be at least 40, got {config.max_line_length}",
                file_path=str(filepath),
                section="formatting",
                details={"max_line_length": config.max_line_length},
            )

        if config.max_line_length > 200:
            raise ValidationError(
                f"max_line_length must be at most 200, got {config.max_line_length}",
                file_path=str(filepath),
                section="formatting",
                details={"max_line_length": config.max_line_length},
            )

    @staticmethod
    def _validate_output_config(config: OutputConfig, filepath: Path) -> None:
        """Validate output configuration values.

        Args:
            config: OutputConfig to validate
            filepath: Path to the configuration file (for error reporting)

        Raises:
            ValidationError: If configuration values are invalid
        """
        if config.format not in ("text", "json"):
            raise ValidationError(
                f"output format must be 'text' or 'json', got '{config.format}'",
                file_path=str(filepath),
                section="output",
                details={"format": config.format},
            )

        if config.verbose and config.quiet:
            raise ValidationError(
                "output verbose and quiet cannot both be True",
                file_path=str(filepath),
                section="output",
                details={"verbose": config.verbose, "quiet": config.quiet},
            )
