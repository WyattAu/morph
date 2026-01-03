"""
Utility functions for validation module.

This module provides helper functions for validation operations,
such as section extraction and content parsing.
"""

import re
from typing import List, Optional, Tuple


def extract_section(content: str, section_name: str) -> Optional[str]:
    """Extract a section from markdown content.

    Args:
        content: The markdown content to search
        section_name: The name of the section to extract (without #)

    Returns:
        The section content if found, None otherwise
    """
    # Pattern to match section headers (## Section Name)
    pattern = rf"^##\s+{re.escape(section_name)}\s*$"
    lines = content.split('\n')

    section_start = None
    section_end = None

    for i, line in enumerate(lines):
        if re.match(pattern, line, re.IGNORECASE):
            section_start = i
            # Find the next section at the same or higher level
            for j in range(i + 1, len(lines)):
                if lines[j].startswith('##'):
                    section_end = j
                    break
            break

    if section_start is None:
        return None

    if section_end is None:
        section_end = len(lines)

    # Extract content between header and next section
    section_lines = lines[section_start + 1:section_end]
    return '\n'.join(section_lines).strip()


def find_section_line(content: str, section_name: str) -> Optional[int]:
    """Find the line number of a section header.

    Args:
        content: The markdown content to search
        section_name: The name of the section to find (without #)

    Returns:
        The line number (1-indexed) if found, None otherwise
    """
    pattern = rf"^##\s+{re.escape(section_name)}\s*$"
    lines = content.split('\n')

    for i, line in enumerate(lines):
        if re.match(pattern, line, re.IGNORECASE):
            return i + 1  # Convert to 1-indexed

    return None


def extract_table(content: str) -> List[List[str]]:
    """Extract a markdown table from content.

    Args:
        content: The content to extract table from

    Returns:
        List of rows, where each row is a list of cell values
    """
    lines = content.split('\n')
    table = []
    in_table = False

    for line in lines:
        stripped = line.strip()
        if not stripped:
            if in_table:
                break
            continue

        if '|' in stripped:
            if not in_table:
                in_table = True

            # Check if it's a separator line (e.g., |---|---|)
            if re.match(r'^\|[\s\-:]+\|$', stripped):
                continue

            # Parse table row
            cells = [cell.strip() for cell in stripped.split('|')]
            # Remove empty cells at start and end
            if cells and cells[0] == '':
                cells = cells[1:]
            if cells and cells[-1] == '':
                cells = cells[:-1]

            if cells:
                table.append(cells)

    return table


def extract_list_items(content: str) -> List[str]:
    """Extract list items from markdown content.

    Args:
        content: The content to extract list items from

    Returns:
        List of list item texts (without the bullet/number)
    """
    lines = content.split('\n')
    items = []

    for line in lines:
        stripped = line.strip()
        # Match bullet points (-, *, +) or numbered lists (1., 2., etc.)
        match = re.match(r'^[\-\*\+]\s+(.+)$|^\d+\.\s+(.+)$', stripped)
        if match:
            item_text = match.group(1) or match.group(2)
            items.append(item_text.strip())

    return items


def parse_requirement_ref(text: str) -> Optional[str]:
    """Parse a requirement reference from text.

    Args:
        text: Text that may contain a requirement reference

    Returns:
        The requirement ID if found, None otherwise
    """
    # Pattern for requirement references like [REQ-001], REQ-001, etc.
    patterns = [
        r'\[([A-Z]+-\d+)\]',  # [REQ-001]
        r'\b([A-Z]+-\d+)\b',   # REQ-001
    ]

    for pattern in patterns:
        match = re.search(pattern, text)
        if match:
            return match.group(1)

    return None


def extract_requirement_ids(content: str) -> List[str]:
    """Extract all requirement IDs from content.

    Args:
        content: The content to search for requirement IDs

    Returns:
        List of unique requirement IDs found
    """
    pattern = r'\b([A-Z]+-\d+)\b'
    matches = re.findall(pattern, content)
    return list(set(matches))


__all__ = [
    "extract_section",
    "find_section_line",
    "extract_table",
    "extract_list_items",
    "parse_requirement_ref",
    "extract_requirement_ids",
]
