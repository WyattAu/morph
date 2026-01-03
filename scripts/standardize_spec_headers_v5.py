#!/usr/bin/env python3
"""
Standardize Spec Headers Script

This script standardizes header format across all spec files to use:
- `- Field:* Value` format (dash prefix, single asterisk, colon separator)
- Consistent field names: File, Version, Context, Formalism, Status, Last Modified, Author, Reviewers
- Consistent separator line: `- -`

Key change: Convert `**` (double asterisk) to `*` (single asterisk) in field names
"""

import os
import re
from pathlib import Path

def standardize_header(content):
    """
    Standardize header of a spec file.
    
    Args:
        content: The file content as a string
        
    Returns:
        Standardized content
    """
    lines = content.split('\n')
    
    # Find header section (between title and first ##)
    header_start = -1
    header_end = -1
    
    for i, line in enumerate(lines):
        if line.startswith('#'):
            header_start = i + 1
        elif line.startswith('##') and header_start != -1:
            header_end = i
            break
    
    if header_start == -1 or header_end == -1:
        # No header found, return as-is
        return content
    
    # Extract header lines
    header_lines = lines[header_start:header_end]
    
    # Build new standardized header
    new_header = []
    metadata = {}
    
    # Parse existing metadata - handle various formats
    for line in header_lines:
        # Skip separator lines
        if line.strip() in ['---', '- -', '* -']:
            continue
        
        # Skip System field (not in standard list)
        if 'System:' in line and 'Morph' in line:
            continue
        
        # Match various header formats
        # Format 1: `- Field:** Value` or `- Field:* Value` (dash prefix)
        match1 = re.match(r'^-\s*(\w+)\s*[:\*]+\s*(.+)$', line.strip())
        if match1:
            field = match1.group(1)
            value = match1.group(2).strip()
            # Remove backticks from value if present
            value = value.replace('`', '').replace("'", '')
            metadata[field] = value
            continue
        
        # Format 2: `* Field:* Value` (asterisk prefix)
        match2 = re.match(r'^\*\s*(\w+)\s*[:\*]+\s*(.+)$', line.strip())
        if match2:
            field = match2.group(1)
            value = match2.group(2).strip()
            # Remove backticks from value if present
            value = value.replace('`', '').replace("'", '')
            metadata[field] = value
            continue
    
    # Build standardized header
    new_header.append('- -')
    for field in ['File', 'Version', 'Context', 'Formalism', 'Status', 'Last Modified', 'Author', 'Reviewers']:
        if field in metadata:
            value = metadata[field]
            new_header.append(f'- {field}:* `{value}`')
        else:
            # Use default value for missing fields
            if field == 'Reviewers':
                new_header.append(f'- {field}:* Pending')
            elif field == 'Status':
                new_header.append(f'- {field}:* Active')
    new_header.append('- -')
    
    # Replace old header with new header
    new_content = '\n'.join(lines[:header_start] + new_header + lines[header_end:])
    
    return new_content

def process_spec_file(file_path):
    """
    Process a single spec file.
    
    Args:
        file_path: Path to spec file
        
    Returns:
        True if file was modified, False otherwise
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        new_content = standardize_header(content)
        
        if new_content != content:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
            print(f"✓ Standardized: {file_path}")
            return True
        else:
            print(f"  Already standardized: {file_path}")
            return False
    except Exception as e:
        print(f"✗ Error processing {file_path}: {e}")
        return False

def main():
    """Main function to process all spec files."""
    spec_dir = Path('spec')
    
    if not spec_dir.exists():
        print(f"Error: spec directory not found at {spec_dir}")
        return
    
    # Find all .md files in spec directory and subdirectories
    spec_files = list(spec_dir.rglob('*.md'))
    
    if not spec_files:
        print("No spec files found")
        return
    
    print(f"Found {len(spec_files)} spec files")
    print("Standardizing headers...")
    print()
    
    modified_count = 0
    for spec_file in sorted(spec_files):
        if process_spec_file(spec_file):
            modified_count += 1
    
    print()
    print(f"Summary:")
    print(f"  Total files processed: {len(spec_files)}")
    print(f"  Files modified: {modified_count}")
    print(f"  Files already standardized: {len(spec_files) - modified_count}")

if __name__ == '__main__':
    main()
