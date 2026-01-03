# Specification Test Suite Documentation

## Overview

The Morph specification test suite provides comprehensive validation for all specifications according to SPEC_FIX_PROPOSAL.md and specification_convention.md requirements.

## Architecture

### Test Categories

1. **Unit Tests** - Validate individual specifications
2. **Integration Tests** - Validate cross-specification consistency
3. **Property-Based Tests** - Verify mathematical properties
4. **Coverage Tests** - Measure and report test coverage

### Test Structure

```
tests/
├── specification_test_suite.py    # Main test suite
├── test_spec_version_validator.py # Version validator tests
├── test_spec_linter.py          # Linter tests
├── test_spec_link_checker.py      # Link checker tests
├── generate_coverage_report.py    # Coverage report generator
├── requirements.txt              # Python dependencies
├── pytest.ini                   # Pytest configuration
└── README.md                    # Test suite documentation
```

## Test Coverage

### Specifications Covered

#### New Specifications (Created During Refinement)
- `spec/type/pure_type_spec.md` - Pure type formal definition
- `spec/type/effect_system_spec.md` - Effect system specification
- `spec/language/operator_null_coalescing_spec.md` - ?? operator semantics
- `spec/language/dialect_projection_spec.md` - Projectional editing
- `spec/concurrency/scheduling_modes_spec.md` - Scheduling modes
- `spec/architecture/layered_concurrency_spec.md` - Layered architecture
- `spec/conventions/terminology_standardization_spec.md` - Terminology standardization
- `spec/conventions/version_compatibility_spec.md` - Version compatibility
- `spec/language/dual_optimization_spec.md` - Dual optimization
- `spec/language/syntax_translation_spec.md` - Syntax translation
- `spec/optimization/selective_monomorphization_spec.md` - Selective monomorphization
- `spec/memory/arc_affine_integration_spec.md` - ARC with affine types
- `spec/validation/unproven_assumptions_spec.md` - Unproven assumptions

#### Updated Specifications
- `spec/type/type_system_spec.md` - Type system updates
- `spec/language/morph_language_spec.md` - Language specification updates
- `spec/concurrency/execution_model_spec.md` - Execution model updates
- `spec/language/strict_state_unidirectionality_spec.md` - Unidirectionality updates
- `spec/language/unidirectional_data_flow_spec.md` - Data flow updates
- `spec/security/security_flow_spec.md` - Security flow updates

### Validation Categories

#### 1. Structure Validation
- Document header format
- Mandatory sections presence
- Section numbering
- Version format (semantic versioning)
- Status values (Draft, Active, Deprecated)

#### 2. Content Validation
- Requirement extraction
- EARS pattern compliance
- Requirement attributes (priority, verification method, rationale, dependencies, traceability)
- Mathematical notation (LaTeX syntax)
- Cross-reference validity

#### 3. Cross-Specification Validation
- Cross-reference existence
- Circular reference detection
- Terminology consistency (Signal vs Stream, Reducer vs Transducer)
- Version compatibility matrix

#### 4. Mathematical Property Validation
- Type safety properties (transitivity, uniqueness)
- Effect subtyping properties (reflexivity, transitivity, associativity)
- Isomorphism properties (round-trip, type isomorphism)

## Test Utilities

### SpecTestUtils Class

The `SpecTestUtils` class provides utility functions for specification testing:

#### Methods

- `extract_spec_header(content, file_path)` - Extract specification metadata
- `extract_requirements(content, spec_name)` - Extract all requirements
- `extract_cross_references(content, spec_dir)` - Extract cross-references
- `extract_mathematical_expressions(content)` - Extract LaTeX expressions
- `validate_version_format(version)` - Validate semantic versioning
- `validate_ears_pattern(requirement_text)` - Validate EARS pattern
- `calculate_test_coverage(spec_dir, test_results)` - Calculate coverage metrics

### Data Classes

#### SpecMetadata
```python
@dataclass
class SpecMetadata:
    path: Path
    name: str
    version: str
    status: str
    context: str
    formalism: str
    last_modified: str
    author: str
    reviewers: List[str]
    line_number: int
```

#### Requirement
```python
@dataclass
class Requirement:
    id: str
    text: str
    priority: str
    verification_method: str
    rationale: str
    dependencies: List[str]
    traceability: List[str]
    line_number: int
    spec_file: str
```

#### TestCoverage
```python
@dataclass
class TestCoverage:
    total_specs: int
    tested_specs: int
    total_requirements: int
    tested_requirements: int
    coverage_percentage: float
```

## Running Tests

### Quick Start

```bash
# Install dependencies
pip install -r tests/requirements.txt

# Run all tests
pytest tests/specification_test_suite.py -v

# Run with coverage
pytest tests/specification_test_suite.py --cov=tests --cov-report=html
```

### Test Categories

```bash
# Run only unit tests
pytest tests/specification_test_suite.py::TestSpecificationStructure -v

# Run only integration tests
pytest tests/specification_test_suite.py::TestCrossReferences -v

# Run only property-based tests
pytest tests/specification_test_suite.py::TestTypeSafetyProperties -v
```

### Specific Tests

```bash
# Run a specific test
pytest tests/specification_test_suite.py::TestSpecificationStructure::test_spec_file_exists -v

# Run tests matching a pattern
pytest tests/specification_test_suite.py -k "test_spec_header" -v
```

### Verbose Output

```bash
# Verbose output
pytest tests/specification_test_suite.py -vv

# Very verbose output
python tests/specification_test_suite.py --verbose
```

## Coverage Reporting

### Generate Coverage Reports

```bash
# Generate HTML coverage report
pytest tests/specification_test_suite.py --cov=tests --cov-report=html

# Generate terminal coverage report
pytest tests/specification_test_suite.py --cov=tests --cov-report=term

# Generate XML coverage report (for CI/CD)
pytest tests/specification_test_suite.py --cov=tests --cov-report=xml

# Generate all coverage reports
python tests/generate_coverage_report.py --spec-dir spec --output-dir test-reports
```

### Coverage Threshold

The test suite enforces a minimum coverage threshold of **80%**.

### Coverage Report Formats

1. **Text Report** - Plain text summary
2. **JSON Report** - Machine-readable JSON
3. **HTML Report** - Interactive HTML with visualizations

## CI/CD Integration

### GitHub Actions

Configuration: `.github/workflows/specification_tests.yml`

Features:
- Multi-version Python testing (3.8, 3.9, 3.10, 3.11)
- Coverage reporting with Codecov
- Artifact upload for reports
- Security scanning (Bandit, Safety)
- Scheduled daily runs

### GitLab CI

Configuration: `.gitlab-ci.yml`

Features:
- Multi-version Python testing
- Coverage reporting
- Artifact upload
- Security scanning
- Scheduled tests

### Jenkins

Configuration: `Jenkinsfile`

Features:
- Multi-version Python testing
- Parallel test execution
- Coverage reporting
- HTML report publishing
- Security scanning
- Email notifications

## Test Fixtures

### Pytest Fixtures

- `spec_dir` - Provides specification directory path
- `spec_utils` - Provides specification utility functions
- `sample_spec` - Provides a sample specification for testing

### Usage Example

```python
def test_spec_header_extraction(spec_utils, sample_spec):
    """Test specification header extraction"""
    metadata = spec_utils.extract_spec_header(sample_spec, Path("test.md"))
    assert metadata is not None
    assert metadata.version == "1.0.0"
```

## Test Markers

Pytest markers for categorizing tests:

- `@pytest.mark.unit` - Unit tests
- `@pytest.mark.integration` - Integration tests
- `@pytest.mark.property` - Property-based tests
- `@pytest.mark.coverage` - Coverage tests
- `@pytest.mark.slow` - Slow-running tests
- `@pytest.mark.fast` - Fast-running tests

### Running Marked Tests

```bash
# Run only unit tests
pytest tests/specification_test_suite.py -m unit -v

# Run only fast tests
pytest tests/specification_test_suite.py -m fast -v

# Run tests excluding slow tests
pytest tests/specification_test_suite.py -m "not slow" -v
```

## Test Results

### Exit Codes

- `0` - All tests passed
- `1` - One or more tests failed

### Test Reports

#### JUnit XML

```bash
pytest tests/specification_test_suite.py --junitxml=test-results.xml
```

#### HTML Report

```bash
pytest tests/specification_test_suite.py --html=test-report.html
```

#### Coverage Reports

```bash
pytest tests/specification_test_suite.py --cov=tests --cov-report=html:htmlcov
```

## Troubleshooting

### Common Issues

#### Import Errors

**Problem:** `ModuleNotFoundError: No module named 'pytest'`

**Solution:**
```bash
pip install -r tests/requirements.txt
```

#### Test Failures

**Problem:** Tests fail with assertion errors

**Solution:**
1. Check error message for details
2. Verify specification files exist in `spec/` directory
3. Ensure specifications follow specification convention
4. Check for broken cross-references

#### Coverage Issues

**Problem:** Coverage below threshold

**Solution:**
1. Run tests with verbose output to see which tests are failing
2. Add tests for uncovered specifications
3. Ensure all specifications have proper headers and requirements

### Debug Mode

```bash
# Run tests with debug output
pytest tests/specification_test_suite.py -vv --tb=long

# Run tests with debugger
pytest tests/specification_test_suite.py --pdb
```

## Contributing

### Adding New Tests

1. Create a new test class inheriting from `unittest.TestCase`
2. Add test methods starting with `test_`
3. Use `SpecTestUtils` for common operations
4. Run tests to verify they pass
5. Update documentation

### Test Naming Conventions

- Test classes: `Test<FeatureName>`
- Test methods: `test_<specific_behavior>`
- Fixtures: `<feature_name>`

### Code Style

Follow PEP 8 style guidelines:
```bash
# Format code
black tests/specification_test_suite.py

# Sort imports
isort tests/specification_test_suite.py

# Lint code
pylint tests/specification_test_suite.py
```

## Maintenance

### Updating Test Suite

When specifications are updated:

1. Update test expectations to match new specification structure
2. Add tests for new specification features
3. Remove tests for deprecated features
4. Update coverage thresholds if needed
5. Update documentation

### Version Compatibility

The test suite is compatible with:
- Python 3.8+
- pytest 7.0+
- unittest (standard library)

## Performance

### Test Execution Time

- Unit tests: ~1-2 minutes
- Integration tests: ~2-3 minutes
- Property-based tests: ~1-2 minutes
- Total: ~4-7 minutes

### Optimization Tips

```bash
# Run tests in parallel
pytest tests/specification_test_suite.py -n auto

# Run only changed tests
pytest tests/specification_test_suite.py --only-failed

# Cache test results
pytest tests/specification_test_suite.py --cache-show
```

## Security

### Security Scanning

The test suite includes security scanning:

- **Bandit** - Python security linter
- **Safety** - Dependency vulnerability scanner

### Running Security Scans

```bash
# Run Bandit
bandit -r tests/ -f json -o bandit-report.json

# Run Safety
safety check --file tests/requirements.txt
```

## Best Practices

### Test Design

1. **Atomic Tests** - Each test should verify one thing
2. **Independent Tests** - Tests should not depend on each other
3. **Repeatable Tests** - Tests should produce same results on multiple runs
4. **Fast Tests** - Tests should run quickly
5. **Clear Names** - Test names should describe what they test

### Test Organization

1. Group related tests in test classes
2. Use descriptive test names
3. Add docstrings to explain test purpose
4. Use fixtures for common setup
5. Keep tests focused and simple

### Error Handling

1. Use specific assertions (assertEqual, assertTrue, etc.)
2. Provide helpful error messages
3. Test both success and failure cases
4. Handle edge cases
5. Test error conditions

## References

- [SPEC_FIX_PROPOSAL.md](../SPEC_FIX_PROPOSAL.md) - Specification fix proposal
- [specification_convention.md](../docs/conventions/specification_convention.md) - Specification convention standard
- [pytest documentation](https://docs.pytest.org/) - pytest documentation
- [unittest documentation](https://docs.python.org/3/library/unittest.html) - unittest documentation
- [coverage.py documentation](https://coverage.readthedocs.io/) - coverage.py documentation

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
- CI/CD integration (GitHub Actions, GitLab CI, Jenkins)
- Comprehensive documentation
