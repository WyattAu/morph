#!/usr/bin/env python3
"""
Fix broken cross-references in Morph specification files.

This script fixes:
1. Absolute paths (spec/) to relative paths
2. Self-references (links to the same file)
3. Incorrect file paths
4. Typos in filenames

Usage:
    python scripts/fix_spec_links.py
"""

import re
from pathlib import Path
from typing import Dict, List, Tuple


def fix_links_in_file(file_path: Path, spec_dir: Path) -> Tuple[int, int, int]:
    """Fix links in a single file.
    
    Returns:
        Tuple of (links_fixed, self_references_removed, invalid_links_removed)
    """
    content = file_path.read_text(encoding='utf-8')
    lines = content.split('\n')
    
    links_fixed = 0
    self_references_removed = 0
    invalid_links_removed = 0
    
    # Get relative path from spec_dir
    try:
        rel_path = file_path.relative_to(spec_dir)
    except ValueError:
        # File is not in spec_dir, skip
        return 0, 0, 0
    
    # Pattern for markdown links
    markdown_link_pattern = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
    
    # Known filename corrections
    filename_corrections = {
        'lexical_strcutre_syntax_spec.md': 'lexical_structure_syntax_spec.md',
        'effect_monad_spec.md': 'monadic_effect_spec.md',
        'category_theory_type_system_spec.md': 'type_category_spec.md',
        'AgentPlanningMDP_Spec.md': 'agent_planning_mdp_spec.md',
        'TypeSystemSpec.md': 'type_system_spec.md',
    }
    
    new_lines = []
    for line_num, line in enumerate(lines, 1):
        new_line = line
        
        # Find all markdown links in this line
        matches = markdown_link_pattern.finditer(line)
        for match in matches:
            text = match.group(1)
            url = match.group(2)
            original_url = url
            
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
                    self_references_removed += 1
                    continue
                
                # Convert to relative path
                new_url = url[5:]  # Remove 'spec/' prefix
                
                # Check for filename typos
                filename = new_url.split('/')[-1]
                if filename in filename_corrections:
                    new_url = new_url.replace(filename, filename_corrections[filename])
                    links_fixed += 1
                
                # Check if the file exists
                target_path = spec_dir / new_url
                if not target_path.exists():
                    # Remove invalid link
                    new_line = new_line.replace(f'[{text}]({url})', text)
                    invalid_links_removed += 1
                else:
                    new_line = new_line.replace(f'[{text}]({url})', f'[{text}]({new_url})')
                    links_fixed += 1
        
        new_lines.append(new_line)
    
    # Write back if changes were made
    if links_fixed > 0 or self_references_removed > 0 or invalid_links_removed > 0:
        new_content = '\n'.join(new_lines)
        file_path.write_text(new_content, encoding='utf-8')
        print(f"  Fixed {links_fixed} links, removed {self_references_removed} self-refs, removed {invalid_links_removed} invalid links")
    
    return links_fixed, self_references_removed, invalid_links_removed


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
    
    total_links_fixed = 0
    total_self_references_removed = 0
    total_invalid_links_removed = 0
    files_modified = 0
    
    for spec_file in spec_files:
        print(f"Processing: {spec_file.relative_to(spec_dir.parent)}")
        links_fixed, self_references_removed, invalid_links_removed = fix_links_in_file(spec_file, spec_dir)
        
        if links_fixed > 0 or self_references_removed > 0 or invalid_links_removed > 0:
            files_modified += 1
            total_links_fixed += links_fixed
            total_self_references_removed += self_references_removed
            total_invalid_links_removed += invalid_links_removed
    
    print()
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"Files processed:         {len(spec_files)}")
    print(f"Files modified:          {files_modified}")
    print(f"Links fixed:             {total_links_fixed}")
    print(f"Self-refs removed:       {total_self_references_removed}")
    print(f"Invalid links removed:   {total_invalid_links_removed}")
    print("=" * 80)


if __name__ == '__main__':
    main()
