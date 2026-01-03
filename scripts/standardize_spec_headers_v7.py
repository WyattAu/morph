#!/usr/bin/env python3
"""
Standardize Spec Headers Script - Simple String Replacement

This script standardizes header format across all spec files by:
1. Converting `**` (double asterisk) to `*` (single asterisk) in field names
2. Ensuring consistent field names: File, Version, Context, Formalism, Status, Last Modified, Author, Reviewers
3. Using consistent separator line: `- -`
"""

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
    
    # Process header lines
    new_lines = lines[:header_start]
    
    for i in range(header_start, header_end):
        line = lines[i]
        
        # Skip separator lines
        if line.strip() in ['---', '- -', '* -']:
            new_lines.append('- -')
            continue
        
        # Skip System field (not in standard list)
        if 'System:' in line and 'Morph' in line:
            continue
        
        # Simple string replacement: convert ** to * in field names
        # Pattern: `- Field:** Value` -> `- Field:* Value`
        if ':**' in line:
            line = line.replace(':**', ':*')
            new_lines.append(line)
        elif ':*' in line:
            # Already has single asterisk, keep as-is
            new_lines.append(line)
        else:
            # Keep line as-is if it doesn't match pattern
            new_lines.append(line)
    
    # Add closing separator if not present
    if not new_lines[-1].strip() == '- -':
        new_lines.append('- -')
    
    # Add rest of file
    new_lines.extend(lines[header_end:])
    
    return '\n'.join(new_lines)

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
