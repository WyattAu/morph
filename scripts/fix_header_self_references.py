#!/usr/bin/env python3
"""
Fix self-references in spec file headers.

This script removes the "spec/" prefix from header fields that reference the file itself.

Usage:
    python scripts/fix_header_self_references.py
"""

import re
from pathlib import Path


def fix_header_self_references(file_path: Path, spec_dir: Path) -> int:
    """Fix self-references in a single file's header.
    
    Returns:
        Number of fixes made
    """
    content = file_path.read_text(encoding='utf-8')
    lines = content.split('\n')
    
    # Get relative path from spec_dir
    try:
        rel_path = file_path.relative_to(spec_dir)
    except ValueError:
        # File is not in spec_dir, skip
        return 0
    
    fixes = 0
    new_lines = []
    
    for line in lines:
        new_line = line
        
        # Check if this line contains a self-reference in the header
        # Pattern: - `Field:* `spec/path/to/file.md`
        if 'spec/' in line and rel_path.name in line:
            # Check if it's a self-reference
            if f'spec/{rel_path}' in line or f'spec/{rel_path.parent}/{rel_path.name}' in line:
                # Remove the "spec/" prefix
                new_line = line.replace(f'spec/{rel_path}', str(rel_path))
                new_line = new_line.replace(f'spec/{rel_path.parent}/{rel_path.name}', str(rel_path))
                fixes += 1
        
        new_lines.append(new_line)
    
    # Write back if changes were made
    if fixes > 0:
        new_content = '\n'.join(new_lines)
        file_path.write_text(new_content, encoding='utf-8')
        print(f"  Fixed {fixes} self-reference(s)")
    
    return fixes


def main():
    """Main entry point."""
    spec_dir = Path('spec')
    
    if not spec_dir.exists():
        print(f"Error: Spec directory '{spec_dir}' does not exist")
        return
    
    # Find all markdown files in spec directory
    spec_files = list(spec_dir.rglob('*.md'))
    
    print(f"Found {len(spec_files)} specification files")
    print()
    
    total_fixes = 0
    files_modified = 0
    
    for spec_file in spec_files:
        print(f"Processing: {spec_file.relative_to(spec_dir.parent)}")
        fixes = fix_header_self_references(spec_file, spec_dir)
        
        if fixes > 0:
            files_modified += 1
            total_fixes += fixes
    
    print()
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"Files processed:  {len(spec_files)}")
    print(f"Files modified:   {files_modified}")
    print(f"Total fixes:      {total_fixes}")
    print("=" * 80)


if __name__ == '__main__':
    main()
