# Specification Test Suite

Comprehensive test suite for validating Morph specifications according to SPEC_FIX_PROPOSAL.md and specification_convention.md.

## Overview

This test suite provides comprehensive validation for all Morph specifications, including:

- **Unit Tests**: Individual specification validation
- **Integration Tests**: Cross-specification validation
- **Property-Based Tests**: Mathematical property verification
- **Coverage Reporting**: Test coverage metrics

## Test Categories

### 1. Unit Tests

Tests that validate individual specifications:

- `TestSpecificationStructure`: Validates specification structure and formatting
- `TestRequirements`: Validates requirement extraction and EARS pattern compliance
- `TestMathematicalNotation`: Validates LaTeX formatting and syntax

### 2. Integration Tests

Tests that validate cross-specification consistency:

- `TestCrossReferences`: Validates cross-reference validity and detects circular references
- `TestTerminologyConsistency`: Validates terminology consistency across specifications
- `TestVersionCompatibility`: Validates version compatibility matrix

### 3. Property-Based Tests

Tests that verify mathematical properties:

- `TestTypeSafetyProperties`: Tests type safety properties (transitivity, uniqueness)
- `TestEffectSubtypingProperties`: Tests effect subtyping properties (reflexivity, transitivity, associativity)
- `TestIsomorphismProperties`: Tests isomorphism properties (round-trip, type isomorphism)

### 4. Coverage Tests

Tests that measure and report test coverage:

- `TestCoverageReporting`: Validates coverage calculation and thresholds

## Installation

### Prerequisites

- Python 3.8+
- pip

### Install Dependencies

```bash
pip install -r requirements.txt
```

## Running Tests

### Run All Tests

```bash
# Using pytest
pytest tests/specification_test_suite.py -v

# Using unittest
python tests/specification_test_suite.py

# With coverage
python tests/specification_test_suite.py --coverage
```

### Run Specific Test Categories

```bash
# Run only unit tests
pytest tests/specification_test_suite.py::TestSpecificationStructure -v

# Run only integration tests
pytest tests/specification_test_suite.py::TestCrossReferences -v

# Run only property-based tests
pytest tests/specification_test_suite.py::TestTypeSafetyProperties -v
```

### Run Specific Test

```bash
# Run a specific test
pytest tests/specification_test_suite.py::TestSpecificationStructure::test_spec_file_exists -v
```

### Verbose Output

```bash
# Verbose output
pytest tests/specification_test_suite.py -vv

# Very verbose output
python tests/specification_test_suite.py --verbose
```

## Test Coverage

### Generate Coverage Report

```bash
# Generate HTML coverage report
pytest tests/specification_test_suite.py --cov=tests --cov-report=html

# Generate terminal coverage report
pytest tests/specification_test_suite.py --cov=tests --cov-report=term

# Generate XML coverage report (for CI/CD)
pytest tests/specification_test_suite.py --cov=tests --cov-report=xml
```

### Coverage Threshold

The test suite enforces a minimum coverage threshold of **80%**.

## Test Fixtures

The test suite includes pytest fixtures for common test scenarios:

- `spec_dir`: Provides the specification directory path
- `spec_utils`: Provides specification utility functions
- `sample_spec`: Provides a sample specification for testing

## Test Utilities

The `SpecTestUtils` class provides utility functions for:

- `extract_spec_header()`: Extract specification metadata from header
- `extract_requirements()`: Extract all requirements from specification
- `extract_cross_references()`: Extract all cross-references
- `extract_mathematical_expressions()`: Extract LaTeX expressions
- `validate_version_format()`: Validate semantic versioning format
- `validate_ears_pattern()`: Validate EARS pattern for requirements
- `calculate_test_coverage()`: Calculate test coverage metrics

## CI/CD Integration

### GitHub Actions

See `.github/workflows/specification_tests.yml` for GitHub Actions integration.

### GitLab CI

See `.gitlab-ci.yml` for GitLab CI integration.

### Jenkins

See `Jenkinsfile` for Jenkins integration.

## Test Results

### Exit Codes

- `0`: All tests passed
- `1`: One or more tests failed

### Test Reports

Test results are printed to the console. For detailed reports:

```bash
# Generate JUnit XML report
pytest tests/specification_test_suite.py --junitxml=test-results.xml

# Generate HTML report
pytest tests/specification_test_suite.py --html=test-report.html
```

## Troubleshooting

### Common Issues

#### Import Errors

If you encounter import errors:

```bash
# Install dependencies
pip install -r requirements.txt

# Ensure you're in the project root
cd /path/to/morph
```

#### Test Failures

If tests fail:

1. Check the error message for details
2. Verify that specification files exist in `spec/` directory
3. Ensure specifications follow the specification convention
4. Check for broken cross-references

#### Coverage Issues

If coverage is below threshold:

1. Run tests with verbose output to see which tests are failing
2. Add tests for uncovered specifications
3. Ensure all specifications have proper headers and requirements

## Contributing

### Adding New Tests

1. Create a new test class inheriting from `unittest.TestCase`
2. Add test methods starting with `test_`
3. Use `SpecTestUtils` for common operations
4. Run tests to verify they pass
5. Update this README with new test documentation

### Test Naming Conventions

- Test classes: `Test<FeatureName>`
- Test methods: `test_<specific_behavior>`
- Fixtures: `<feature_name>`

## Maintenance

### Updating Test Suite

When specifications are updated:

1. Update test expectations to match new specification structure
2. Add tests for new specification features
3. Remove tests for deprecated features
4. Update coverage thresholds if needed

### Version Compatibility

The test suite is compatible with:

- Python 3.8+
- pytest 7.0+
- unittest (standard library)

## References

- [SPEC_FIX_PROPOSAL.md](../SPEC_FIX_PROPOSAL.md): Specification fix proposal
- [specification_convention.md](../docs/conventions/specification_convention.md): Specification convention standard
- [pytest documentation](https://docs.pytest.org/): pytest documentation
- [unittest documentation](https://docs.python.org/3/library/unittest.html): unittest documentation

## License

This test suite is part of the Morph project and follows the same license.

## Support

For issues or questions:

1. Check the troubleshooting section above
2. Review test error messages carefully
3. Consult the specification convention document
4. Open an issue on GitHub

## Changelog

### Version 1.0.0 (2026-01-02)

- Initial release
- Unit tests for specification structure
- Integration tests for cross-references
- Property-based tests for mathematical properties
- Coverage reporting
- CI/CD integration examples
