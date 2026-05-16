"""Tests for CLI init-config command."""

from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from spec_tools.cli.commands.init_config import (
    run_init_config_command,
    ConfigManager,
)
from spec_tools.models import Config


def _make_args(output="config.yaml", template="default"):
    return SimpleNamespace(output=output, template=template)


class TestRunInitConfigCommand:
    def test_creates_config_file(self, temp_dir):
        output_path = str(temp_dir / "config.yaml")
        args = _make_args(output=output_path)
        result = run_init_config_command(args)
        assert result == 0
        assert (temp_dir / "config.yaml").exists()

    def test_file_already_exists(self, temp_dir):
        config_file = temp_dir / "config.yaml"
        config_file.write_text("existing content")
        args = _make_args(output=str(config_file))
        result = run_init_config_command(args)
        assert result == 1

    def test_with_template(self, temp_dir):
        output_path = str(temp_dir / "custom.yaml")
        args = _make_args(output=output_path, template="strict")
        result = run_init_config_command(args)
        assert result == 0


class TestConfigManager:
    def test_save_config(self, temp_dir):
        manager = ConfigManager()
        config = Config()
        output_path = temp_dir / "config.yaml"
        manager.save_config(config, output_path)
        assert output_path.exists()
        content = output_path.read_text()
        assert "formatting:" in content
        assert "linting:" in content

    def test_load_config(self, temp_dir):
        import yaml
        config_file = temp_dir / "config.yaml"
        config_file.write_text("formatting:\n  max_line_length: 80\n")

        manager = ConfigManager()
        config = manager.load_config(config_file)
        assert config.formatting.max_line_length == 80

    def test_load_empty_config(self, temp_dir):
        config_file = temp_dir / "config.yaml"
        config_file.write_text("")

        manager = ConfigManager()
        config = manager.load_config(config_file)
        assert isinstance(config, Config)

    def test_load_yaml_error(self, temp_dir):
        config_file = temp_dir / "config.yaml"
        config_file.write_text("bad: [unclosed")

        manager = ConfigManager()
        with pytest.raises(Exception):
            manager.load_config(config_file)

    def test_save_config_structure(self, temp_dir):
        manager = ConfigManager()
        config = Config()
        config.formatting.max_line_length = 100
        config.linting.strict = True
        output_path = temp_dir / "config.yaml"
        manager.save_config(config, output_path)

        content = output_path.read_text()
        assert "Spec Tools Configuration" in content
        assert "max_line_length: 100" in content
        assert "strict: true" in content

    def test_load_config_all_sections(self, temp_dir):
        config_file = temp_dir / "full.yaml"
        config_file.write_text(
            "formatting:\n"
            "  max_line_length: 80\n"
            "  enforce_trailing_whitespace: false\n"
            "  normalize_lists: false\n"
            "  fix_heading_spacing: false\n"
            "  normalize_emphasis: false\n"
            "linting:\n"
            "  strict: true\n"
            "  check_ears_pattern: false\n"
            "  check_math_notation: false\n"
            "  check_mermaid_syntax: false\n"
            "  check_cross_references: false\n"
            "validation:\n"
            "  check_traceability: false\n"
            "  check_verification_plan: false\n"
            "  check_risk_assessment: false\n"
            "  check_security_specs: false\n"
            "  check_performance_specs: false\n"
            "  check_maintainability_specs: false\n"
            "link_checking:\n"
            "  check_broken_links: false\n"
            "  check_orphaned_sections: false\n"
            "  check_duplicate_links: false\n"
            "  check_self_references: true\n"
            "output:\n"
            "  format: json\n"
            "  verbose: true\n"
            "  quiet: true\n"
            "  color_output: false\n"
        )

        manager = ConfigManager()
        config = manager.load_config(config_file)
        assert config.formatting.max_line_length == 80
        assert config.formatting.enforce_trailing_whitespace is False
        assert config.formatting.normalize_lists is False
        assert config.linting.strict is True
        assert config.linting.check_ears_pattern is False
        assert config.validation.check_traceability is False
        assert config.link_checking.check_self_references is True
        assert config.output.format == "json"
        assert config.output.verbose is True
        assert config.output.quiet is True
        assert config.output.color_output is False

    def test_load_config_partial_sections(self, temp_dir):
        config_file = temp_dir / "partial.yaml"
        config_file.write_text(
            "formatting:\n"
            "  max_line_length: 90\n"
            "output:\n"
            "  format: json\n"
        )

        manager = ConfigManager()
        config = manager.load_config(config_file)
        assert config.formatting.max_line_length == 90
        assert config.linting.strict is False
        assert config.output.format == "json"

    def test_load_config_general_exception(self, temp_dir):
        import os

        config_file = temp_dir / "config.yaml"
        config_file.write_text("key: value")
        os.chmod(str(config_file), 0o000)
        try:
            manager = ConfigManager()
            with pytest.raises(Exception):
                manager.load_config(config_file)
        finally:
            os.chmod(str(config_file), 0o644)

    def test_run_init_config_exception(self, temp_dir):
        args = _make_args(output=str(temp_dir / "fail.yaml"))
        with patch.object(
            ConfigManager, "save_config", side_effect=RuntimeError("disk full")
        ):
            result = run_init_config_command(args)
            assert result == 1
