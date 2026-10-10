#!/usr/bin/env python3
"""Copy a validated current dist/ into the GitHub Pages docs/ directory."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
subprocess.run([sys.executable, str(root / "tools/check_sync.py")], cwd=root, check=True)
manifest = json.loads((root / "dist/MANIFEST.json").read_text())
files = [entry if isinstance(entry, str) else entry["path"] for entry in manifest["files"]]
files.append("MANIFEST.json")
for name in files:
    path = Path(name)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError(f"Invalid manifest path: {name}")
    if not (root / "dist" / path).is_file():
        raise FileNotFoundError(name)
for name in files:
    target = root / "docs" / name
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(root / "dist" / name, target)
# Remove obsolete generated files so old claim pages do not remain published.
expected = set(files)
for path in (root / "docs").rglob("*"):
    if path.is_file() and path.relative_to(root / "docs").as_posix() not in expected:
        path.unlink()
print(f"Published {len(files)} files to docs/")
