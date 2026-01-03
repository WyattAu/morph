"""
Pytest configuration and fixtures for spec-tools package tests.

This module provides shared fixtures and configuration for all test modules.
"""

import tempfile
from pathlib import Path
from typing import Generator

import pytest

from spec_tools.config import ConfigManager
from spec_tools.models import Config


@pytest.fixture
def temp_dir() -> Generator[Path, None, None]:
    """Create a temporary directory for test files.

    Yields:
        Path to temporary directory
    """
    with tempfile.TemporaryDirectory() as tmpdir:
        yield Path(tmpdir)


@pytest.fixture
def sample_config() -> Config:
    """Get a sample configuration for testing.

    Returns:
        Config object with default values
    """
    return ConfigManager.get_default_config()


@pytest.fixture
def sample_spec_content() -> str:
    """Get sample specification content for testing.

    Returns:
        String containing sample specification markdown
    """
    return """# Sample Specification

## Overview

This is a sample specification for testing purposes.

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

### REQ-002: Advanced Requirement

The system SHALL provide advanced functionality when configured.

## Design

### Architecture

The system uses a layered architecture.

### Components

- Component A: Handles input processing
- Component B: Handles business logic
- Component C: Handles output generation

## Verification

### Test Plan

1. Test basic functionality
2. Test advanced functionality
3. Test integration

## Change Log

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0.0 | 2024-01-01 | John Doe | Initial version |
"""


@pytest.fixture
def sample_spec_with_issues() -> str:
    """Get sample specification with formatting and linting issues.

    Returns:
        String containing specification with intentional issues
    """
    return """#Sample Specification with Issues

##Overview

This is a sample specification with issues.

##Requirements

###REQ-001:Basic Requirement

The system SHALL provide basic functionality.

###REQ-002:Advanced Requirement

The system SHALL provide advanced functionality when configured.

##Design

###Architecture

The system uses a layered architecture.

###Components

-Component A:Handles input processing
-Component B:Handles business logic
-Component C:Handles output generation

##Verification

###Test Plan

1.Test basic functionality
2.Test advanced functionality
3.Test integration

##Change Log

|Version|Date|Author|Description|
|---------|------|--------|-------------|
|1.0.0|2024-01-01|John Doe|Initial version|
"""


@pytest.fixture
def sample_spec_file(temp_dir: Path, sample_spec_content: str) -> Path:
    """Create a sample specification file for testing.

    Args:
        temp_dir: Temporary directory fixture
        sample_spec_content: Sample specification content fixture

    Returns:
        Path to the created specification file
    """
    spec_file = temp_dir / "sample_spec.md"
    spec_file.write_text(sample_spec_content, encoding="utf-8")
    return spec_file


@pytest.fixture
def sample_config_file(temp_dir: Path, sample_config: Config) -> Path:
    """Create a sample configuration file for testing.

    Args:
        temp_dir: Temporary directory fixture
        sample_config: Sample configuration fixture

    Returns:
        Path to the created configuration file
    """
    config_file = temp_dir / ".spec-tools.yaml"
    ConfigManager.save_config(sample_config, config_file)
    return config_file


@pytest.fixture
def sample_spec_with_links() -> str:
    """Get sample specification with various link types.

    Returns:
        String containing specification with links
    """
    return """# Specification with Links

## Overview

This specification contains various types of links.

## Internal Links

See [Section 3](#design) for design details.

## File Links

See [Another Spec](another_spec.md) for more information.

## External Links

Visit [GitHub](https://github.com) for the repository.

## Cross-References

This requirement is related to [REQ-001](#req-001-basic-requirement).

## Design

### Architecture

The system architecture is described here.

### Components

- Component A
- Component B
- Component C

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

### REQ-002: Advanced Requirement

The system SHALL provide advanced functionality.
"""


@pytest.fixture
def sample_spec_with_math() -> str:
    """Get sample specification with mathematical notation.

    Returns:
        String containing specification with math notation
    """
    return """# Specification with Math

## Mathematical Model

The system uses the following mathematical model:

### Equations

The performance is calculated as:

$$P = \\frac{1}{n} \\sum_{i=1}^{n} x_i$$

Where:
- $P$ is the performance metric
- $n$ is the number of samples
- $x_i$ is the i-th sample value

### Inline Math

The value of $x$ is calculated as $x = \\sqrt{y^2 + z^2}$.

## Verification

The mathematical model is verified through:
1. Unit tests
2. Integration tests
3. Performance benchmarks
"""


@pytest.fixture
def sample_spec_with_mermaid() -> str:
    """Get sample specification with Mermaid diagrams.

    Returns:
        String containing specification with Mermaid diagrams
    """
    return """# Specification with Mermaid

## Architecture

### System Flow

```mermaid
graph TD
    A[Start] --> B[Process]
    B --> C{Decision}
    C -->|Yes| D[Action 1]
    C -->|No| E[Action 2]
    D --> F[End]
    E --> F
```

### Sequence Diagram

```mermaid
sequenceDiagram
    participant User
    participant System
    participant Database

    User->>System: Request
    System->>Database: Query
    Database-->>System: Result
    System-->>User: Response
```

## Components

### Component A

Handles input processing.

### Component B

Handles business logic.
"""


@pytest.fixture
def sample_spec_with_ears() -> str:
    """Get sample specification with EARS pattern requirements.

    Returns:
        String containing specification with EARS patterns
    """
    return """# Specification with EARS Patterns

## Requirements

### Universal Requirements

The system SHALL provide user authentication.

### State-Driven Requirements

When the user is authenticated, the system SHALL display the dashboard.

### Event-Driven Requirements

When the user clicks the submit button, the system SHALL process the form.

### Optional Features

The system MAY provide dark mode support.

### Unwanted Behavior

The system SHALL NOT allow unauthorized access.

### Complex Requirements

If the user is an administrator, then the system SHALL provide admin controls,
otherwise the system SHALL provide standard user controls.

## Verification

All requirements are verified through automated testing.
"""


@pytest.fixture
def sample_spec_with_traceability() -> str:
    """Get sample specification with traceability information.

    Returns:
        String containing specification with traceability matrix
    """
    return """# Specification with Traceability

## Requirements

### REQ-001: User Authentication

The system SHALL provide user authentication.

**Traceability:**
- Design: [DESIGN-001](#design-001-authentication-module)
- Implementation: [IMPL-001](#impl-001-auth-service)
- Test: [TEST-001](#test-001-auth-tests)

### REQ-002: Data Persistence

The system SHALL persist user data.

**Traceability:**
- Design: [DESIGN-002](#design-002-database-layer)
- Implementation: [IMPL-002](#impl-002-data-service)
- Test: [TEST-002](#test-002-data-tests)

## Design

### DESIGN-001: Authentication Module

The authentication module handles user login and logout.

### DESIGN-002: Database Layer

The database layer provides data persistence.

## Implementation

### IMPL-001: Auth Service

The auth service implements authentication logic.

### IMPL-002: Data Service

The data service implements data persistence logic.

## Tests

### TEST-001: Auth Tests

Tests for authentication functionality.

### TEST-002: Data Tests

Tests for data persistence functionality.

## Traceability Matrix

| Requirement | Design | Implementation | Test |
|-------------|--------|----------------|------|
| REQ-001 | DESIGN-001 | IMPL-001 | TEST-001 |
| REQ-002 | DESIGN-002 | IMPL-002 | TEST-002 |
"""


@pytest.fixture
def sample_spec_with_risk_assessment() -> str:
    """Get sample specification with risk assessment.

    Returns:
        String containing specification with risk assessment
    """
    return """# Specification with Risk Assessment

## Requirements

### REQ-001: Data Security

The system SHALL encrypt sensitive data at rest.

### REQ-002: Performance

The system SHALL respond to requests within 200ms.

## Risk Assessment

### Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Database failure | Medium | High | Implement replication |
| Network latency | High | Medium | Use CDN |
| Memory leaks | Low | High | Regular profiling |

### Security Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| SQL injection | Low | Critical | Use parameterized queries |
| XSS attacks | Medium | High | Input sanitization |
| CSRF attacks | Low | High | CSRF tokens |

## Mitigation Strategies

1. Implement comprehensive logging
2. Regular security audits
3. Performance monitoring
4. Automated testing
"""


@pytest.fixture
def sample_spec_with_security_specs() -> str:
    """Get sample specification with security specifications.

    Returns:
        String containing specification with security specs
    """
    return """# Specification with Security Specs

## Security Requirements

### AUTH-001: Authentication

The system SHALL implement multi-factor authentication.

### AUTH-002: Authorization

The system SHALL implement role-based access control.

### DATA-001: Data Encryption

The system SHALL encrypt data using AES-256.

### DATA-002: Data Integrity

The system SHALL verify data integrity using checksums.

## Security Architecture

### Threat Model

The system protects against:
- SQL injection
- XSS attacks
- CSRF attacks
- Session hijacking

### Security Controls

1. Input validation
2. Output encoding
3. Secure session management
4. Regular security updates

## Compliance

The system complies with:
- GDPR
- SOC 2
- ISO 27001
"""


@pytest.fixture
def sample_spec_with_performance_specs() -> str:
    """Get sample specification with performance specifications.

    Returns:
        String containing specification with performance specs
    """
    return """# Specification with Performance Specs

## Performance Requirements

### PERF-001: Response Time

The system SHALL respond to API requests within 200ms (p95).

### PERF-002: Throughput

The system SHALL handle 10,000 requests per second.

### PERF-003: Scalability

The system SHALL scale horizontally to handle increased load.

### PERF-004: Resource Usage

The system SHALL use less than 2GB memory under normal load.

## Performance Targets

| Metric | Target | Measurement |
|--------|--------|-------------|
| API Response Time | < 200ms (p95) | Request duration |
| Throughput | > 10,000 RPS | Requests per second |
| Memory Usage | < 2GB | Resident set size |
| CPU Usage | < 70% | CPU utilization |

## Performance Testing

1. Load testing
2. Stress testing
3. Endurance testing
4. Spike testing
"""


@pytest.fixture
def sample_spec_with_maintainability_specs() -> str:
    """Get sample specification with maintainability specifications.

    Returns:
        String containing specification with maintainability specs
    """
    return """# Specification with Maintainability Specs

## Maintainability Requirements

### MAINT-001: Code Quality

The system SHALL maintain code coverage above 80%.

### MAINT-002: Documentation

The system SHALL have comprehensive API documentation.

### MAINT-003: Modularity

The system SHALL be organized into loosely coupled modules.

### MAINT-004: Testability

The system SHALL be designed for easy testing.

## Code Standards

### Style Guidelines

- Follow PEP 8
- Use type hints
- Write docstrings
- Keep functions small

### Code Review

All code changes SHALL undergo peer review.

## Documentation Standards

### API Documentation

All public APIs SHALL have:
- Description
- Parameters
- Return values
- Examples

### Architecture Documentation

The system SHALL have:
- Architecture diagrams
- Component descriptions
- Data flow diagrams
- Deployment guides

## Maintenance Procedures

1. Regular dependency updates
2. Security patching
3. Performance monitoring
4. Code refactoring
"""


@pytest.fixture
def sample_spec_with_change_log() -> str:
    """Get sample specification with change log.

    Returns:
        String containing specification with change log
    """
    return """# Specification with Change Log

## Overview

This specification describes the system requirements.

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

### REQ-002: Advanced Requirement

The system SHALL provide advanced functionality.

## Change Log

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0.0 | 2024-01-01 | John Doe | Initial version |
| 1.1.0 | 2024-02-01 | Jane Smith | Added advanced features |
| 1.2.0 | 2024-03-01 | Bob Johnson | Fixed bugs and improved performance |
| 2.0.0 | 2024-04-01 | Alice Brown | Major redesign |
"""


@pytest.fixture
def sample_spec_with_sections() -> str:
    """Get sample specification with proper section structure.

    Returns:
        String containing specification with proper sections
    """
    return """# Sample Specification

## Overview

This is a sample specification.

## Requirements

### Functional Requirements

#### REQ-001: User Authentication

The system SHALL provide user authentication.

#### REQ-002: Data Persistence

The system SHALL persist user data.

### Non-Functional Requirements

#### NFR-001: Performance

The system SHALL respond within 200ms.

#### NFR-002: Security

The system SHALL implement encryption.

## Design

### Architecture

The system uses a layered architecture.

### Components

- Authentication Service
- Data Service
- API Gateway

## Implementation

### Technology Stack

- Python 3.8+
- PostgreSQL
- Redis

### Code Structure

```
src/
  auth/
  data/
  api/
```

## Verification

### Test Plan

1. Unit tests
2. Integration tests
3. End-to-end tests

### Acceptance Criteria

All requirements SHALL be verified and approved.

## Change Log

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0.0 | 2024-01-01 | John Doe | Initial version |
"""


@pytest.fixture
def sample_spec_with_cross_references() -> str:
    """Get sample specification with cross-references.

    Returns:
        String containing specification with cross-references
    """
    return """# Specification with Cross-References

## Overview

This specification contains cross-references to other specifications.

## Requirements

### REQ-001: Authentication

The system SHALL provide authentication as described in [Security Spec](security_spec.md).

### REQ-002: Data Storage

The system SHALL store data as described in [Storage Spec](storage_spec.md).

## Related Specifications

- [Security Spec](security_spec.md)
- [Storage Spec](storage_spec.md)
- [API Spec](api_spec.md)

## Cross-Reference Matrix

| Requirement | Related Spec | Section |
|-------------|--------------|---------|
| REQ-001 | security_spec.md | Authentication |
| REQ-002 | storage_spec.md | Data Storage |
"""
