#!/usr/bin/env python3
"""
Restore Lean 4 Files from Backups
Restores all .lean files from their .backup counterparts.
"""

import os
from pathlib import Path

SPECS_DIR = Path("Morph/Specs")

def restore_from_backups():
    """Restore all .lean files from .backup files."""
    restored_count = 0
    
    for root, dirs, files in os.walk(SPECS_DIR):
        for file in files:
            if file.endswith('.lean.backup'):
                backup_path = Path(root) / file
                original_path = backup_path.with_suffix('')
                
                if original_path.exists():
                    # Restore from backup
                    import shutil
                    shutil.copy2(backup_path, original_path)
                    restored_count += 1
                    try:
                        print(f"Restored: {original_path.relative_to(Path.cwd())}")
                    except ValueError:
                        print(f"Restored: {original_path}")
    
    print(f"\nTotal files restored: {restored_count}")

if __name__ == "__main__":
    print("Restoring files from backups...")
    restore_from_backups()
    print("Restore complete!")
