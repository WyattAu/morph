"""
Unit tests for ConfigManager.
"""

from pathlib import Path

import pytest

from spec_tools.config import ConfigManager
from spec_tools.exceptions import ValidationError
from spec_tools.models import Config, FormattingConfig, LintingConfig, ValidationConfig, LinkCheckingConfig, OutputConfig


class TestConfigManager:
    """Test cases for ConfigManager."""

    def test_get_default_config(self):
        """Test get_default_config() returns default config."""
        config = ConfigManager.get_default_config()
        assert isinstance(config, Config)
        assert isinstance(config.formatting, FormattingConfig)
        assert isinstance(config.linting, LintingConfig)
        assert isinstance(config.validation, ValidationConfig)
        assert isinstance(config.link_checking, LinkCheckingConfig)
        assert isinstance(config.output, OutputConfig)

    def test_load_config_valid_file(self, temp_dir):
        """Test load_config() with valid YAML file."""
        config_file = temp_dir / "config.yaml"
        config_file.write_text(
            """formatting:
  max_line_length: 100
linting:
  strict: true
validation:
  check_traceability: false
link_checking:
  check_broken_links: false
output:
  format: json
""",
            encoding="utf-8",
        )

        config = ConfigManager.load_config(config_file)
        assert config.formatting.max_line_length == 100
        assert config.linting.strict is True
        assert config.validation.check_traceability is False
        assert config.link_checking.check_broken_links is False
        assert config.output.format == "json"

    def test_load_config_empty_file(self, temp_dir):
        """Test load_config() with empty YAML file."""
        config_file = temp_dir / "config.yaml"
        config_file.write_text("", encoding="utf-8")

        config = ConfigManager.load_config(config_file)
        assert isinstance(config, Config)

    def test_load_config_file_not_found(self, temp_dir):
        """Test load_config() with non-existent file."""
        config_file = temp_dir / "nonexistent.yaml"

        with pytest.raises(ValidationError) as exc_info:
            ConfigManager.load_config(config_file)
        assert "Configuration file not found" in str(exc_info.value)

    def test_load_config_invalid_yaml(self, temp_dir):
        """Test load_config() with invalid YAML."""
        config_file = temp_dir / "config.yaml"
        config_file.write_text("invalid: yaml: content:", encoding="utf-8")

        with pytest.raises(ValidationError) as exc_info:
            ConfigManager.load_config(config_file)
        assert "Invalid YAML" in str(exc_info.value)

    def test_save_config(self, temp_dir):
        """Test save_config() writes valid YAML."""
        config = ConfigManager.get_default_config()
        config_file = temp_dir / "config.yaml"

        ConfigManager.save_config(config, config_file)

        assert config_file.exists()
        loaded_config = ConfigManager.load_config(config_file)
        assert loaded_config.formatting.max_line_length == config.formatting.max_line_length

    def test_save_config_creates_directory(self, temp_dir):
        """Test save_config() creates parent directory if needed."""
        config = ConfigManager.get_default_config()
        config_file = temp_dir / "subdir" / "config.yaml"

        ConfigManager.save_config(config, config_file)

        assert config_file.exists()
        assert config_file.parent.exists()

    def test_save_config_error(self, temp_dir):
        """Test save_config() raises error on write failure."""
        config = ConfigManager.get_default_config()
        # Use a path that will fail (e.g., invalid characters)
        config_file = temp_dir / "config.yaml"

        # This should work normally
        ConfigManager.save_config(config, config_file)
        assert config_file.exists()

    def test_validate_formatting_config_valid(self):
        """Test _validate_formatting_config() with valid values."""
        config = FormattingConfig(max_line_length=100)
        # Should not raise
        ConfigManager._validate_formatting_config(config, Path("config.yaml"))

    def test_validate_formatting_config_too_short(self):
        """Test _validate_formatting_config() rejects too short max_line_length."""
        config = FormattingConfig(max_line_length=30)

        with pytest.raises(ValidationError) as exc_info:
            ConfigManager._validate_formatting_config(config, Path("config.yaml"))
        assert "max_line_length must be at least 40" in str(exc_info.value)

    def test_validate_formatting_config_too_long(self):
        """Test _validate_formatting_config() rejects too long max_line_length."""
        config = FormattingConfig(max_line_length=250)

        with pytest.raises(ValidationError) as exc_info:
            ConfigManager._validate_formatting_config(config, Path("config.yaml"))
        assert "max_line_length must be at most 200" in str(exc_info.value)

    def test_validate_output_config_valid(self):
        """Test _validate_output_config() with valid values."""
        config = OutputConfig(format="text", verbose=True, quiet=False)
        # Should not raise
        ConfigManager._validate_output_config(config, Path("config.yaml"))

    def test_validate_output_config_invalid_format(self):
        """Test _validate_output_config() rejects invalid format."""
        config = OutputConfig(format="invalid")

        with pytest.raises(ValidationError) as exc_info:
            ConfigManager._validate_output_config(config, Path("config.yaml"))
        assert "output format must be 'text' or 'json'" in str(exc_info.value)

    def test_validate_output_config_verbose_and_quiet(self):
        """Test _validate_output_config() rejects verbose and quiet both True."""
        config = OutputConfig(verbose=True, quiet=True)

        with pytest.raises(ValidationError) as exc_info:
            ConfigManager._validate_output_config(config, Path("config.yaml"))
        assert "verbose and quiet cannot both be True" in str(exc_info.value)

    def test_config_to_dict(self):
        """Test _config_to_dict() converts config to dictionary."""
        config = ConfigManager.get_default_config()
        config_dict = ConfigManager._config_to_dict(config)

        assert isinstance(config_dict, dict)
        assert "formatting" in config_dict
        assert "linting" in config_dict
        assert "validation" in config_dict
        assert "link_checking" in config_dict
        assert "output" in config_dict

    def test_parse_config_partial(self, temp_dir):
        """Test _parse_config() with partial config."""
        config_file = temp_dir / "config.yaml"
        config_file.write_text(
            """formatting:
  max_line_length: 100
""",
            encoding="utf-8",
        )

        config = ConfigManager.load_config(config_file)
        assert config.formatting.max_line_length == 100
        # Other values should be defaults
        assert config.linting.strict is False
        assert config.validation.check_traceability is True
