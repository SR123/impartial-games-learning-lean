#!/usr/bin/env python3
"""Write SOURCE_MANIFEST.json: every file of the edition's source folder with its size, SHA-256 and role.

    python3 tools/make_manifest.py

The published site has its own manifest (dist/MANIFEST.json, written by tools/build_site.py); here dist/ is
summarised by that file's hash.  Scratch space (work/), installed packages (tools/node_modules/) and Python
caches are not part of the edition and are excluded.
"""
import hashlib
import json
import os
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXCLUDE_DIRS = {"work", "node_modules", "__pycache__", ".git", "dist", "delivery_archive"}
EXCLUDE_FILES = {"SOURCE_MANIFEST.json", ".DS_Store"}

ROLES = [  # (path prefix, role, note) - first match wins
    ("input/", "input", "versioned manuscript and PDF snapshots; see EDITORIAL_HISTORY.md"),
    ("CLAUDE_INTERACTIVE_BRIEF.txt", "input", "supplied with the brief; not modified"),
    ("PERSONAL_HISTORY_DRAFT.txt", "input", "supplied with the brief; not modified"),
    ("DISPATCH.json", "input", "supplied with the brief; not modified"),
    ("lean/", "lean-source-copy", "copy of the audited Lean sources and build metadata (hashes checked against the audit index)"),
    ("evidence_inputs/phase8_audit_2026-10-10/", "audit-evidence-copy", "unchanged copy of the phase-8 audit files"),
    ("evidence_inputs/fresh-build-20261010/", "build-evidence", "record of the fresh Lean rebuild of 2026-10-10"),
    ("evidence_inputs/reference_compile/", "build-evidence", "label numbers from a pdflatex compile of input/jmlr_source"),
    ("data/declaration_index.json", "audit-evidence-copy", "audited declaration index (copy)"),
    ("data/paper_proof_correspondence.json", "reviewed-correspondence", "original audited rows retained, with current manuscript hashes and revision-review metadata"),
    ("data/lean_export.json", "generated", "tools/lean/ExportDecls.lean run on the fresh rebuild"),
    ("data/fresh_build.json", "generated", "tools/lean/parse_build.py summary of the fresh rebuild"),
    ("data/claims.json", "generated", "claim map written by tools/build_site.py"),
    ("data/claim_map.tsv", "generated", "claim map table written by tools/build_site.py"),
    ("data/claims.source.yaml", "content", "claim metadata (handwritten)"),
    ("data/claims.lock.json", "content", "reviewed statement-source hashes"),
    ("data/visual_reference_lean.", "lean-evaluation", "Lean's evaluation of the illustrated definitions on small inputs (tools/lean/VisualRef.lean) and its provenance"),
    ("data/reviews/", "review-record", "archived review lists of pinned claim and illustration changes"),
    ("content/visuals/", "content", "illustrations: specification, prose and reviewed-input lock"),
    ("content/", "content", "handwritten explanations, author's note, edition and coverage text, figure alternatives"),
    ("generated/", "generated", "converter output written by tools/build_site.py"),
    ("tools/visuals/", "code", "illustration engine, renderer, browser controls and their tests"),
    ("tools/", "code", "build, validation and preview tools"),
    ("validation/", "validation-evidence", "last run of tools/validate_site.py"),
    ("site.config.yaml", "config", "pinned input hashes and site settings"),
]


def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def role(rel):
    for prefix, r, note in ROLES:
        if rel == prefix or rel.startswith(prefix):
            return r, note
    return "documentation", "report or documentation of this delivery"


def main():
    files = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDE_DIRS)
        for f in sorted(filenames):
            if f in EXCLUDE_FILES:
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, ROOT).replace(os.sep, "/")
            r, note = role(rel)
            files.append({"path": rel, "bytes": os.path.getsize(p), "sha256": sha256(p), "role": r, "note": note})
    dist_man = os.path.join(ROOT, "dist", "MANIFEST.json")
    dist = None
    if os.path.exists(dist_man):
        m = json.load(open(dist_man))
        dist = {"manifest": "dist/MANIFEST.json", "manifest_sha256": sha256(dist_man), "files": len(m["files"]),
                "bytes": sum(x["bytes"] for x in m["files"])}
    counts = {}
    for x in files:
        counts[x["role"]] = counts.get(x["role"], 0) + 1
    out = {"edition": "interactive edition of the NIM paper (local review build)",
           "written_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
           "excluded": sorted(EXCLUDE_DIRS - {"dist"}) + ["dist/ (listed in dist/MANIFEST.json)"],
           "dist": dist, "counts_by_role": counts, "files": files}
    with open(os.path.join(ROOT, "SOURCE_MANIFEST.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1, ensure_ascii=False)
    print(f"SOURCE_MANIFEST.json: {len(files)} files {counts}; dist: {dist and dist['files']} files")


if __name__ == "__main__":
    main()
