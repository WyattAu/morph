"""
Unit tests for CLI main module.
"""

from pathlib import Path
from unittest.mock import patch

import pytest

from spec_tools.cli.main import main
from spec_tools.models import Config


class TestCLIMain:
    """Test cases for CLI main module."""

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_format_command(self, mock_config_manager):
        """Test main() with format command."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "format", "test.md"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_lint_command(self, mock_config_manager):
        """Test main() with lint command."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "lint", "test.md"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_validate_command(self, mock_config_manager):
        """Test main() with validate command."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "validate", "test.md"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_check_links_command(self, mock_config_manager):
        """Test main() with check-links command."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "check-links", "test.md"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_check_all_command(self, mock_config_manager):
        """Test main() with check-all command."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "check-all", "test.md"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_init_config_command(self, mock_config_manager):
        """Test main() with init-config command."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "init-config"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_no_command(self, mock_config_manager):
        """Test main() with no command."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code != 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_invalid_command(self, mock_config_manager):
        """Test main() with invalid command."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "invalid-command"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code != 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_with_config_file(self, mock_config_manager):
        """Test main() with custom config file."""
        mock_config_manager.return_value.load_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "--config", "custom.yaml", "format", "test.md"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_with_verbose_flag(self, mock_config_manager):
        """Test main() with verbose flag."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "--verbose", "format", "test.md"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_with_quiet_flag(self, mock_config_manager):
        """Test main() with quiet flag."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "--quiet", "format", "test.md"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_with_help_flag(self, mock_config_manager):
        """Test main() with help flag."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "--help"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    @patch("spec_tools.cli.main.ConfigManager")
    def test_main_with_version_flag(self, mock_config_manager):
        """Test main() with version flag."""
        mock_config_manager.return_value.get_default_config.return_value = Config()
        
        with patch("sys.argv", ["spec-tools", "--version"]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0
