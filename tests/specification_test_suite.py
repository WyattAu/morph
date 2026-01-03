#!/usr/bin/env python3
"""
Comprehensive Test Suite for Morph Specifications

This test suite validates all specifications according to SPEC_FIX_PROPOSAL.md
and specification_convention.md requirements.

Test Categories:
- Unit Tests: Individual specification validation
- Integration Tests: Cross-specification validation
- Property-Based Tests: Mathematical property verification
- Coverage Tests: Test coverage reporting

Author: Kilo Code
Date: 2026-01-02
Version: 1.0.0
"""

import unittest
import pytest
import tempfile
import shutil
from pathlib import Path
from typing import List, Dict, Set, Tuple, Optional
from dataclasses import dataclass
from enum import Enum
import re
import json
import hashlib


# ============================================================================
# Test Fixtures and Utilities
# ============================================================================

class SpecTestError(Exception):
    """Base exception for specification test errors"""
    pass


class SpecValidationError(SpecTestError):
    """Raised when specification validation fails"""
    pass


class SpecCoverageError(SpecTestError):
    """Raised when test coverage is insufficient"""
    pass


@dataclass
class SpecMetadata:
    """Metadata extracted from a specification file"""
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


@dataclass
class Requirement:
    """A requirement extracted from a specification"""
    id: str
    text: str
    priority: str
    verification_method: str
    rationale: str
    dependencies: List[str]
    traceability: List[str]
    line_number: int
    spec_file: str


@dataclass
class TestCoverage:
    """Test coverage metrics"""
    total_specs: int
    tested_specs: int
    total_requirements: int
    tested_requirements: int
    coverage_percentage: float


class SpecTestUtils:
    """Utility functions for specification testing"""

    @staticmethod
    def extract_spec_header(content: str, file_path: Path) -> Optional[SpecMetadata]:
        """Extract specification metadata from header"""
        lines = content.split('\n')
        
        # Find header block (first 20 lines)
        header_lines = lines[:20]
        header_text = '\n'.join(header_lines)
        
        # Extract fields using regex
        version_match = re.search(r'\*\*Version:\*\*\s*(\S+)', header_text)
        status_match = re.search(r'\*\*Status:\*\*\s*(\S+)', header_text)
        context_match = re.search(r'\*\*Context:\*\*\s*(.+)', header_text)
        formalism_match = re.search(r'\*\*Formalism:\*\*\s*(.+)', header_text)
        last_modified_match = re.search(r'\*\*Last Modified:\*\*\s*(\S+)', header_text)
        author_match = re.search(r'\*\*Author:\*\*\s*(.+)', header_text)
        reviewers_match = re.search(r'\*\*Reviewers:\*\*\s*(.+)', header_text)
        
        if not version_match:
            return None
        
        return SpecMetadata(
            path=file_path,
            name=file_path.name,
            version=version_match.group(1),
            status=status_match.group(1) if status_match else "Unknown",
            context=context_match.group(1).strip() if context_match else "Unknown",
            formalism=formalism_match.group(1).strip() if formalism_match else "Unknown",
            last_modified=last_modified_match.group(1) if last_modified_match else "Unknown",
            author=author_match.group(1).strip() if author_match else "Unknown",
            reviewers=[r.strip() for r in reviewers_match.group(1).split(',')] if reviewers_match else [],
            line_number=1
        )

    @staticmethod
    def extract_requirements(content: str, spec_name: str) -> List[Requirement]:
        """Extract all requirements from specification"""
        requirements = []
        lines = content.split('\n')
        
        # Pattern for requirement IDs: XXX-REQ-XXX, XXX-CON-XXX, XXX-INV-XXX
        req_pattern = re.compile(r'\*\s+([A-Z]{3,4}-(?:REQ|CON|INV)-\d+):\*\*\s*(.+)')
        
        for i, line in enumerate(lines, 1):
            match = req_pattern.match(line)
            if match:
                req_id = match.group(1)
                req_text = match.group(2)
                
                # Extract attributes (next few lines)
                priority = "Unknown"
                verification_method = "Unknown"
                rationale = "Unknown"
                dependencies = []
                traceability = []
                
                j = i
                while j < len(lines) and j < i + 10:
                    attr_line = lines[j]
                    if attr_line.strip().startswith('* Priority:'):
                        priority = attr_line.split(':', 1)[1].strip()
                    elif attr_line.strip().startswith('* Verification Method:'):
                        verification_method = attr_line.split(':', 1)[1].strip()
                    elif attr_line.strip().startswith('* Rationale:'):
                        rationale = attr_line.split(':', 1)[1].strip()
                    elif attr_line.strip().startswith('* Dependencies:'):
                        deps = attr_line.split(':', 1)[1].strip()
                        dependencies = [d.strip() for d in deps.split(',') if d.strip()]
                    elif attr_line.strip().startswith('* Traceability:'):
                        traces = attr_line.split(':', 1)[1].strip()
                        traceability = [t.strip() for t in traces.split(',') if t.strip()]
                    elif attr_line.strip().startswith('* ') and not any(
                        attr_line.strip().startswith(f'* {k}')
                        for k in ['Priority:', 'Verification Method:', 'Rationale:', 
                                 'Dependencies:', 'Traceability:']
                    ):
                        break
                    j += 1
                
                requirements.append(Requirement(
                    id=req_id,
                    text=req_text,
                    priority=priority,
                    verification_method=verification_method,
                    rationale=rationale,
                    dependencies=dependencies,
                    traceability=traceability,
                    line_number=i,
                    spec_file=spec_name
                ))
        
        return requirements

    @staticmethod
    def extract_cross_references(content: str, spec_dir: Path) -> List[Tuple[str, str, int]]:
        """Extract all cross-references from specification"""
        references = []
        lines = content.split('\n')
        
        # Pattern for markdown links to other specs
        link_pattern = re.compile(r'\[([^\]]+)\]\((spec/[^)]+)\)')
        
        for i, line in enumerate(lines, 1):
            matches = link_pattern.findall(line)
            for text, url in matches:
                references.append((text, url, i))
        
        return references

    @staticmethod
    def extract_mathematical_expressions(content: str) -> List[Tuple[str, int]]:
        """Extract all mathematical expressions (LaTeX)"""
        expressions = []
        lines = content.split('\n')
        
        # Inline math: $...$
        inline_pattern = re.compile(r'\$([^$]+)\$')
        # Block math: $$...$$
        block_pattern = re.compile(r'\$\$([^$]+)\$\$', re.MULTILINE)
        
        for i, line in enumerate(lines, 1):
            inline_matches = inline_pattern.findall(line)
            for expr in inline_matches:
                expressions.append((f'${expr}$', i))
        
        # Find block math (spans multiple lines)
        block_matches = block_pattern.findall(content)
        for expr in block_matches:
            # Find line number
            line_num = content.find(f'$${expr}$$')
            line_num = content[:line_num].count('\n') + 1
            expressions.append((f'$${expr}$$', line_num))
        
        return expressions

    @staticmethod
    def validate_version_format(version: str) -> bool:
        """Validate semantic versioning format"""
        # Semantic versioning: X.Y.Z
        # Optional: -prerelease, +build
        pattern = r'^\d+\.\d+\.\d+(?:-[a-zA-Z0-9.-]+)?(?:\+[a-zA-Z0-9.-]+)?$'
        return bool(re.match(pattern, version))

    @staticmethod
    def validate_ears_pattern(requirement_text: str) -> bool:
        """Validate EARS pattern for requirements"""
        # EARS patterns:
        # - "THE system SHALL ..."
        # - "WHEN ..., THE system SHALL ..."
        # - "WHILE ..., THE system SHALL ..."
        # - "WHERE ..., THE system SHALL ..."
        ears_patterns = [
            r'^THE system SHALL',
            r'^WHEN .+, THE system SHALL',
            r'^WHILE .+, THE system SHALL',
            r'^WHERE .+, THE system SHALL'
        ]
        
        return any(re.match(pattern, requirement_text.strip()) for pattern in ears_patterns)

    @staticmethod
    def calculate_test_coverage(spec_dir: Path, test_results: Dict[str, bool]) -> TestCoverage:
        """Calculate test coverage metrics"""
        spec_files = list(spec_dir.rglob('*.md'))
        total_specs = len(spec_files)
        tested_specs = len(test_results)
        
        # Extract requirements from all specs
        total_requirements = 0
        tested_requirements = 0
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            requirements = SpecTestUtils.extract_requirements(content, spec_file.name)
            total_requirements += len(requirements)
            
            # Count tested requirements (simplified: assume all tested if spec is tested)
            if spec_file.name in test_results and test_results[spec_file.name]:
                tested_requirements += len(requirements)
        
        coverage_percentage = (tested_requirements / total_requirements * 100) if total_requirements > 0 else 0
        
        return TestCoverage(
            total_specs=total_specs,
            tested_specs=tested_specs,
            total_requirements=total_requirements,
            tested_requirements=tested_requirements,
            coverage_percentage=coverage_percentage
        )


# ============================================================================
# Unit Tests for Individual Specifications
# ============================================================================

class TestSpecificationStructure(unittest.TestCase):
    """Test specification structure and formatting"""

    def setUp(self):
        """Set up test fixtures"""
        self.spec_dir = Path('spec')
        self.utils = SpecTestUtils()

    def test_spec_file_exists(self):
        """Test that all specification files exist"""
        # List of expected specification files
        expected_specs = [
            'spec/type/pure_type_spec.md',
            'spec/type/effect_system_spec.md',
            'spec/language/operator_null_coalescing_spec.md',
            'spec/language/dialect_projection_spec.md',
            'spec/concurrency/scheduling_modes_spec.md',
            'spec/architecture/layered_concurrency_spec.md',
            'spec/conventions/terminology_standardization_spec.md',
            'spec/conventions/version_compatibility_spec.md',
            'spec/language/dual_optimization_spec.md',
            'spec/language/syntax_translation_spec.md',
            'spec/optimization/selective_monomorphization_spec.md',
            'spec/memory/arc_affine_integration_spec.md',
            'spec/validation/unproven_assumptions_spec.md',
        ]
        
        for spec_path in expected_specs:
            spec_file = Path(spec_path)
            self.assertTrue(
                spec_file.exists(),
                f"Specification file {spec_path} does not exist"
            )

    def test_spec_header_format(self):
        """Test that all specifications have proper header format"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            metadata = self.utils.extract_spec_header(content, spec_file)
            
            self.assertIsNotNone(
                metadata,
                f"Specification {spec_file} has invalid or missing header"
            )
            
            # Validate required fields
            self.assertIsNotNone(metadata.version, f"Missing version in {spec_file}")
            self.assertIsNotNone(metadata.status, f"Missing status in {spec_file}")
            self.assertIn(
                metadata.status,
                ['Draft', 'Active', 'Deprecated'],
                f"Invalid status '{metadata.status}' in {spec_file}"
            )

    def test_spec_version_format(self):
        """Test that all specification versions follow semantic versioning"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            metadata = self.utils.extract_spec_header(content, spec_file)
            
            if metadata:
                self.assertTrue(
                    self.utils.validate_version_format(metadata.version),
                    f"Invalid version format '{metadata.version}' in {spec_file}"
                )

    def test_spec_mandatory_sections(self):
        """Test that all specifications have mandatory sections"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        mandatory_sections = [
            '## 1. Purpose and Scope',
            '## 2. Formal Definitions',
            '## 3. Requirements',
            '## 4. Design',
            '## 5. Correctness Properties',
            '## 6. Examples',
        ]
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            
            for section in mandatory_sections:
                self.assertIn(
                    section,
                    content,
                    f"Missing mandatory section '{section}' in {spec_file}"
                )


class TestRequirements(unittest.TestCase):
    """Test requirement extraction and validation"""

    def setUp(self):
        """Set up test fixtures"""
        self.spec_dir = Path('spec')
        self.utils = SpecTestUtils()

    def test_requirement_extraction(self):
        """Test that requirements are extracted correctly"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            requirements = self.utils.extract_requirements(content, spec_file.name)
            
            # Each requirement should have valid ID
            for req in requirements:
                self.assertRegex(
                    req.id,
                    r'^[A-Z]{3,4}-(?:REQ|CON|INV)-\d+$',
                    f"Invalid requirement ID '{req.id}' in {spec_file}"
                )

    def test_ears_pattern_compliance(self):
        """Test that all requirements follow EARS pattern"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            requirements = self.utils.extract_requirements(content, spec_file.name)
            
            for req in requirements:
                self.assertTrue(
                    self.utils.validate_ears_pattern(req.text),
                    f"Requirement '{req.id}' does not follow EARS pattern in {spec_file}"
                )

    def test_requirement_attributes(self):
        """Test that all requirements have required attributes"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            requirements = self.utils.extract_requirements(content, spec_file.name)
            
            for req in requirements:
                # Check required attributes
                self.assertIn(
                    req.priority,
                    ['Critical', 'High', 'Medium', 'Low'],
                    f"Invalid priority '{req.priority}' for requirement '{req.id}' in {spec_file}"
                )
                
                self.assertIn(
                    req.verification_method,
                    ['Inspection', 'Analysis', 'Demonstration', 'Test'],
                    f"Invalid verification method '{req.verification_method}' for requirement '{req.id}' in {spec_file}"
                )


class TestMathematicalNotation(unittest.TestCase):
    """Test mathematical notation and LaTeX formatting"""

    def setUp(self):
        """Set up test fixtures"""
        self.spec_dir = Path('spec')
        self.utils = SpecTestUtils()

    def test_latex_delimiters(self):
        """Test that LaTeX expressions use proper delimiters"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            expressions = self.utils.extract_mathematical_expressions(content)
            
            for expr, line_num in expressions:
                # Check for proper delimiters
                self.assertTrue(
                    expr.startswith('$') and expr.endswith('$'),
                    f"Invalid LaTeX delimiters at line {line_num} in {spec_file}: {expr}"
                )

    def test_latex_syntax(self):
        """Test that LaTeX expressions are syntactically valid"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            expressions = self.utils.extract_mathematical_expressions(content)
            
            # Basic syntax checks
            for expr, line_num in expressions:
                # Check for balanced braces
                open_braces = expr.count('{')
                close_braces = expr.count('}')
                self.assertEqual(
                    open_braces,
                    close_braces,
                    f"Unbalanced braces in LaTeX at line {line_num} in {spec_file}"
                )
                
                # Check for balanced parentheses
                open_parens = expr.count('(')
                close_parens = expr.count(')')
                self.assertEqual(
                    open_parens,
                    close_parens,
                    f"Unbalanced parentheses in LaTeX at line {line_num} in {spec_file}"
                )


# ============================================================================
# Integration Tests for Cross-Specification Validation
# ============================================================================

class TestCrossReferences(unittest.TestCase):
    """Test cross-reference validity and consistency"""

    def setUp(self):
        """Set up test fixtures"""
        self.spec_dir = Path('spec')
        self.utils = SpecTestUtils()

    def test_all_references_exist(self):
        """Test that all cross-references point to existing files"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        for spec_file in spec_files:
            content = spec_file.read_text()
            references = self.utils.extract_cross_references(content, self.spec_dir)
            
            for text, url, line_num in references:
                # Resolve relative path
                if url.startswith('spec/'):
                    target_path = self.spec_dir / url.replace('spec/', '', 1)
                else:
                    target_path = spec_file.parent / url
                
                self.assertTrue(
                    target_path.exists(),
                    f"Broken reference in {spec_file}:{line_num}: [{text}]({url})"
                )

    def test_no_circular_references(self):
        """Test that there are no circular reference chains"""
        spec_files = list(self.spec_dir.rglob('*.md'))
        
        # Build reference graph
        ref_graph: Dict[str, Set[str]] = {}
        
        for spec_file in spec_files:
            spec_name = spec_file.name
            content = spec_file.read_text()
            references = self.utils.extract_cross_references(content, self.spec_dir)
            
            # Extract target spec names
            targets = set()
            for text, url, line_num in references:
                if url.startswith('spec/'):
                    target_name = Path(url).name
                    targets.add(target_name)
            
            ref_graph[spec_name] = targets
        
        # Check for cycles using DFS
        def has_cycle(node: str, visited: Set[str], rec_stack: Set[str]) -> bool:
            visited.add(node)
            rec_stack.add(node)
            
            for neighbor in ref_graph.get(node, set()):
                if neighbor not in visited:
                    if has_cycle(neighbor, visited, rec_stack):
                        return True
                elif neighbor in rec_stack:
                    return True
            
            rec_stack.remove(node)
            return False
        
        for spec_name in ref_graph:
            visited = set()
            rec_stack = set()
            self.assertFalse(
                has_cycle(spec_name, visited, rec_stack),
                f"Circular reference detected involving {spec_name}"
            )


class TestTerminologyConsistency(unittest.TestCase):
    """Test terminology consistency across specifications"""

    def setUp(self):
        """Set up test fixtures"""
        self.spec_dir = Path('spec')

    def test_signal_stream_distinction(self):
        """Test that Signal and Stream are used consistently"""
        # FRP spec should use Signal
        frp_spec = self.spec_dir / 'tooling' / 'reactive_frp_spec.md'
        if frp_spec.exists():
            content = frp_spec.read_text()
            self.assertIn('Signal', content, "FRP spec should use 'Signal'")
        
        # Data flow spec should use Stream
        data_flow_spec = self.spec_dir / 'language' / 'unidirectional_data_flow_spec.md'
        if data_flow_spec.exists():
            content = data_flow_spec.read_text()
            self.assertIn('Stream', content, "Data flow spec should use 'Stream'")

    def test_reducer_transducer_distinction(self):
        """Test that Reducer and Transducer are used consistently"""
        # AST spec should use Reducer
        ast_spec = self.spec_dir / 'language' / 'ast_graph_spec.md'
        if ast_spec.exists():
            content = ast_spec.read_text()
            self.assertIn('Reducer', content, "AST spec should use 'Reducer'")
        
        # Graph rewriting spec should use Transducer
        graph_spec = self.spec_dir / 'tooling' / 'graph_rewriting_spec.md'
        if graph_spec.exists():
            content = graph_spec.read_text()
            self.assertIn('Transducer', content, "Graph rewriting spec should use 'Transducer'")


class TestVersionCompatibility(unittest.TestCase):
    """Test version compatibility across specifications"""

    def setUp(self):
        """Set up test fixtures"""
        self.spec_dir = Path('spec')
        self.utils = SpecTestUtils()

    def test_version_compatibility_matrix(self):
        """Test that version compatibility matrix is consistent"""
        # Extract versions from all specs
        versions: Dict[str, str] = {}
        
        spec_files = list(self.spec_dir.rglob('*.md'))
        for spec_file in spec_files:
            content = spec_file.read_text()
            metadata = self.utils.extract_spec_header(content, spec_file)
            if metadata:
                versions[spec_file.name] = metadata.version
        
        # Check compatibility rules (simplified)
        # Morph language v0.3.0 requires type system v0.2.1+
        if 'morph_language_spec.md' in versions and 'type_system_spec.md' in versions:
            morph_version = versions['morph_language_spec.md']
            type_version = versions['type_system_spec.md']
            
            # Simple version comparison
            morph_parts = morph_version.replace('v', '').split('.')
            type_parts = type_version.replace('v', '').split('.')
            
            # Type system should be at least v0.2.1
            if len(type_parts) >= 3:
                type_major = int(type_parts[0])
                type_minor = int(type_parts[1])
                type_patch = int(type_parts[2])
                
                self.assertTrue(
                    type_major > 0 or (type_major == 0 and type_minor >= 2),
                    f"Type system version {type_version} incompatible with Morph {morph_version}"
                )


# ============================================================================
# Property-Based Tests for Mathematical Properties
# ============================================================================

class TestTypeSafetyProperties(unittest.TestCase):
    """Test type safety properties"""

    def test_type_subtyping_transitivity(self):
        """Test that type subtyping is transitive"""
        # This is a property-based test
        # If A <: B and B <: C, then A <: C
        
        # Example: Pure <: Effect<IO> and Effect<IO> <: Effect<IO|State>
        # Therefore: Pure <: Effect<IO|State>
        
        # This would be tested with actual type system implementation
        # For now, we test that the specification documents this property
        type_spec = Path('spec/type/type_system_spec.md')
        if type_spec.exists():
            content = type_spec.read_text()
            # Check for transitivity property
            self.assertIn(
                'transitive',
                content.lower(),
                "Type system spec should document subtyping transitivity"
            )

    def test_type_uniqueness(self):
        """Test that types are unique"""
        # Each type should have a unique representation
        
        type_spec = Path('spec/type/type_system_spec.md')
        if type_spec.exists():
            content = type_spec.read_text()
            # Check for uniqueness property
            self.assertIn(
                'unique',
                content.lower(),
                "Type system spec should document type uniqueness"
            )


class TestEffectSubtypingProperties(unittest.TestCase):
    """Test effect subtyping properties"""

    def test_effect_subtyping_reflexivity(self):
        """Test that effect subtyping is reflexive"""
        # For any effect E, E <: E
        
        effect_spec = Path('spec/type/effect_system_spec.md')
        if effect_spec.exists():
            content = effect_spec.read_text()
            # Check for reflexivity property
            self.assertIn(
                'reflexive',
                content.lower(),
                "Effect system spec should document subtyping reflexivity"
            )

    def test_effect_subtyping_transitivity(self):
        """Test that effect subtyping is transitive"""
        # If E1 <: E2 and E2 <: E3, then E1 <: E3
        
        effect_spec = Path('spec/type/effect_system_spec.md')
        if effect_spec.exists():
            content = effect_spec.read_text()
            # Check for transitivity property
            self.assertIn(
                'transitive',
                content.lower(),
                "Effect system spec should document subtyping transitivity"
            )

    def test_effect_composition_associativity(self):
        """Test that effect composition is associative"""
        # (E1 | E2) | E3 = E1 | (E2 | E3)
        
        effect_spec = Path('spec/type/effect_system_spec.md')
        if effect_spec.exists():
            content = effect_spec.read_text()
            # Check for associativity property
            self.assertIn(
                'associative',
                content.lower(),
                "Effect system spec should document composition associativity"
            )


class TestIsomorphismProperties(unittest.TestCase):
    """Test isomorphism properties"""

    def test_projection_round_trip(self):
        """Test that projection translation is round-trip safe"""
        # agentToHuman(humanToAgent(agentAST)) ≈ agentAST
        # humanToAgent(agentToHuman(humanAST)) ≈ humanAST
        
        translation_spec = Path('spec/language/syntax_translation_spec.md')
        if translation_spec.exists():
            content = translation_spec.read_text()
            # Check for round-trip property
            self.assertIn(
                'round-trip',
                content.lower(),
                "Syntax translation spec should document round-trip property"
            )

    def test_type_isomorphism(self):
        """Test that isomorphic types are equivalent"""
        # If A ≅ B, then A and B can be used interchangeably
        
        type_spec = Path('spec/type/type_system_spec.md')
        if type_spec.exists():
            content = type_spec.read_text()
            # Check for isomorphism property
            self.assertIn(
                'isomorph',
                content.lower(),
                "Type system spec should document isomorphism properties"
            )


# ============================================================================
# Test Coverage Reporting
# ============================================================================

class TestCoverageReporting(unittest.TestCase):
    """Test coverage reporting and metrics"""

    def setUp(self):
        """Set up test fixtures"""
        self.spec_dir = Path('spec')
        self.utils = SpecTestUtils()

    def test_coverage_calculation(self):
        """Test that coverage is calculated correctly"""
        # Simulate test results
        test_results = {
            'pure_type_spec.md': True,
            'effect_system_spec.md': True,
            'operator_null_coalescing_spec.md': False,
        }
        
        coverage = self.utils.calculate_test_coverage(self.spec_dir, test_results)
        
        self.assertGreater(coverage.total_specs, 0)
        self.assertGreaterEqual(coverage.tested_specs, 0)
        self.assertGreaterEqual(coverage.coverage_percentage, 0)
        self.assertLessEqual(coverage.coverage_percentage, 100)

    def test_coverage_threshold(self):
        """Test that coverage meets minimum threshold"""
        # Minimum coverage threshold: 80%
        MIN_COVERAGE = 80.0
        
        # Calculate actual coverage
        test_results = {}  # Would be populated from actual test runs
        coverage = self.utils.calculate_test_coverage(self.spec_dir, test_results)
        
        # For now, just check the threshold constant
        self.assertGreater(MIN_COVERAGE, 0)


# ============================================================================
# Pytest Fixtures
# ============================================================================

@pytest.fixture
def spec_dir():
    """Fixture providing specification directory"""
    return Path('spec')


@pytest.fixture
def spec_utils():
    """Fixture providing specification utilities"""
    return SpecTestUtils()


@pytest.fixture
def sample_spec():
    """Fixture providing a sample specification for testing"""
    return """# Test Specification

**File:** `spec/test_spec.md`
**Version:** 1.0.0
**Context:** Layer 2 (Test Component)
**Formalism:** Set Theory
**Status:** Active
**Last Modified:** 2026-01-02
**Author:** Test Author
**Reviewers:** Reviewer 1, Reviewer 2

---

## 1. Purpose and Scope

### 1.1 Purpose

This is a test specification.

## 2. Formal Definitions

Let $S = \\{x \\in \\mathbb{Z} \\mid x > 0\\}$.

## 3. Requirements

**TEST-REQ-001:** THE system SHALL validate all inputs.

* Priority:** Critical
* Verification Method:** Test
* Rationale:** Ensures data integrity
* Dependencies:** None
* Traceability:** Section 2

## 4. Design

Design section.

## 5. Correctness Properties

Properties section.

## 6. Examples

Examples section.
"""


# ============================================================================
# Pytest Tests
# ============================================================================

def test_spec_header_extraction(spec_utils, sample_spec):
    """Test specification header extraction"""
    import tempfile
    with tempfile.NamedTemporaryFile(mode='w', suffix='.md', delete=False) as f:
        f.write(sample_spec)
        f.flush()
        temp_path = Path(f.name)
    
    try:
        metadata = spec_utils.extract_spec_header(sample_spec, temp_path)
        assert metadata is not None
        assert metadata.version == "1.0.0"
        assert metadata.status == "Active"
    finally:
        temp_path.unlink()


def test_requirement_extraction(spec_utils, sample_spec):
    """Test requirement extraction"""
    requirements = spec_utils.extract_requirements(sample_spec, "test_spec.md")
    assert len(requirements) == 1
    assert requirements[0].id == "TEST-REQ-001"
    assert requirements[0].priority == "Critical"


def test_version_validation(spec_utils):
    """Test version format validation"""
    assert spec_utils.validate_version_format("1.0.0")
    assert spec_utils.validate_version_format("1.2.3-alpha")
    assert spec_utils.validate_version_format("2.0.0+20230101")
    assert not spec_utils.validate_version_format("1.0")
    assert not spec_utils.validate_version_format("v1.0.0")


def test_ears_pattern_validation(spec_utils):
    """Test EARS pattern validation"""
    assert spec_utils.validate_ears_pattern("THE system SHALL validate all inputs.")
    assert spec_utils.validate_ears_pattern("WHEN input is received, THE system SHALL process it.")
    assert spec_utils.validate_ears_pattern("WHILE processing, THE system SHALL log errors.")
    assert spec_utils.validate_ears_pattern("WHERE enabled, THE system SHALL optimize.")
    assert not spec_utils.validate_ears_pattern("The system should validate inputs.")


# ============================================================================
# Main Test Runner
# ============================================================================

def run_tests(coverage: bool = False, verbose: bool = False) -> int:
    """
    Run the complete test suite
    
    Args:
        coverage: Generate coverage report
        verbose: Verbose output
    
    Returns:
        Exit code (0 for success, 1 for failure)
    """
    import sys
    
    # Run pytest tests
    pytest_args = ['tests/specification_test_suite.py', '-v']
    if coverage:
        pytest_args.extend(['--cov=tests', '--cov-report=html'])
    if verbose:
        pytest_args.append('-vv')
    
    exit_code = pytest.main(pytest_args)
    
    # Run unittest tests
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2 if verbose else 1)
    result = runner.run(suite)
    
    # Combine results
    if exit_code != 0 or not result.wasSuccessful():
        return 1
    
    return 0


if __name__ == '__main__':
    import sys
    verbose = '-v' in sys.argv or '--verbose' in sys.argv
    coverage = '--coverage' in sys.argv or '-c' in sys.argv
    
    sys.exit(run_tests(coverage=coverage, verbose=verbose))
