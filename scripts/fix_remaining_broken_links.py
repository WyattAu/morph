#!/usr/bin/env python3
"""
Fix remaining broken cross-references in Morph specification files.

This script fixes:
1. Self-references in headers with "spec/" prefix
2. Incorrect file paths
3. Typos in filenames

Usage:
    python scripts/fix_remaining_broken_links.py
"""

import re
from pathlib import Path


def fix_links_in_file(file_path: Path, spec_dir: Path) -> int:
    """Fix links in a single file.
    
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
    
    # Known filename corrections
    filename_corrections = {
        'lexical_strcutre_syntax_spec.md': 'lexical_structure_syntax_spec.md',
        'effect_monad_spec.md': 'monadic_effect_spec.md',
        'category_theory_type_system_spec.md': 'type_category_spec.md',
        'AgentPlanningMDP_Spec.md': 'agent_planning_mdp_spec.md',
        'TypeSystemSpec.md': 'type_system_spec.md',
    }
    
    # Pattern for markdown links
    markdown_link_pattern = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
    
    for line in lines:
        new_line = line
        
        # Fix self-references in headers
        # Pattern: - `Field:* `spec/path/to/file.md`
        if 'spec/' in line and rel_path.name in line:
            # Check if it's a self-reference
            if f'spec/{rel_path}' in line or f'spec/{rel_path.parent}/{rel_path.name}' in line:
                # Remove "spec/" prefix
                new_line = line.replace(f'spec/{rel_path}', str(rel_path))
                new_line = new_line.replace(f'spec/{rel_path.parent}/{rel_path.name}', str(rel_path))
                fixes += 1
            elif f'spec/{rel_path.name}' in line:
                # Replace with relative path
                new_line = line.replace(f'spec/{rel_path.name}', str(rel_path))
                fixes += 1
        
        # Fix markdown links with incorrect paths
        matches = markdown_link_pattern.finditer(line)
        for match in matches:
            text = match.group(1)
            url = match.group(2)
            
            # Skip external links
            if url.startswith('http://') or url.startswith('https://'):
                continue
            
            # Skip section references within same file
            if url.startswith('#'):
                continue
            
            # Fix absolute paths (spec/ -> relative)
            if url.startswith('spec/'):
                # Check if it's a self-reference
                if url == f'spec/{rel_path}' or url.startswith(f'spec/{rel_path}#'):
                    # Remove self-reference entirely
                    new_line = new_line.replace(f'[{text}]({url})', text)
                    fixes += 1
                    continue
                
                # Convert to relative path
                new_url = url[5:]  # Remove 'spec/' prefix
                
                # Check for filename typos
                filename = new_url.split('/')[-1]
                if filename in filename_corrections:
                    new_url = new_url.replace(filename, filename_corrections[filename])
                    new_line = new_line.replace(f'[{text}]({url})', f'[{text}]({new_url})')
                    fixes += 1
                    continue
                
                # Check if the file exists
                target_path = spec_dir / new_url
                if not target_path.exists():
                    # Remove invalid link
                    new_line = new_line.replace(f'[{text}]({url})', text)
                    fixes += 1
                else:
                    new_line = new_line.replace(f'[{text}]({url})', f'[{text}]({new_url})')
                    fixes += 1
        
        new_lines.append(new_line)
    
    # Write back if changes were made
    if fixes > 0:
        new_content = '\n'.join(new_lines)
        file_path.write_text(new_content, encoding='utf-8')
        print(f"  Fixed {fixes} link(s)")
    
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
        fixes = fix_links_in_file(spec_file, spec_dir)
        
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
