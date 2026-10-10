#!/usr/bin/env python3
"""Is the interactive edition in step with the manuscript, the PDF and the proofs?

    python3 tools/check_sync.py [--canonical PATH] [--jmlr-pdf PATH] [--jmlr-source PATH] [--require-upstream]

Run this before and after every manuscript edit (see README.md, "Keeping the paper and the edition in step").
It changes nothing.  Each check prints PASS, WARN or FAIL; the exit status is 1 if any check fails, and a
JSON report is written to work/review/sync_report.json.

  1  input snapshots       input/ files against the hashes pinned in site.config.yaml and input/source_manifest.json
  2  upstream manuscript   the canonical source, JMLR source and JMLR PDF outside this folder, when reachable
                           (default paths ../../02_working_copy/candidate/paper_revised_final.tex,
                           ../../07_jmlr_review/source/paper_jmlr.tex and ../../07_jmlr_review/paper_jmlr.pdf);
                           when they are not reachable this is reported as a snapshot boundary, not as a pass
  3  reference compile     evidence_inputs/reference_compile/paper_jmlr.aux and .log against the JMLR source and the
                           PDF: the label set, the page count and the byte count of the PDF the log reports
  4  proof correspondence  data/paper_proof_correspondence.json names the current manuscript hashes
  5  claims, illustrations a check-only build (tools/build_site.py --check): every claim statement source against
     and Lean reference    data/claims.lock.json, every illustration against content/visuals/visuals.lock.json, the
                           Lean reference values against the bundled Lean sources, and the illustration engine against
                           those values; a stale claim or illustration also writes a review list in work/review/
  6  built site            dist/MANIFEST.json against the current inputs, content and tools (is dist/ out of date?)
                           and against the files actually in dist/
"""
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = []

# Files whose content determines the built site.  dist/MANIFEST.json records their hashes.
BUILD_INPUT_DIRS = ["input", "content", "lean", "tools/visuals", "tools/site_assets", "tools/lean"]
BUILD_INPUT_FILES = ["site.config.yaml", "data/claims.source.yaml", "data/claims.lock.json", "data/lean_export.json",
                     "data/fresh_build.json", "data/declaration_index.json", "data/paper_proof_correspondence.json",
                     "data/visual_reference_lean.jsonl", "data/visual_reference_lean.meta.json",
                     "tools/build_site.py", "tools/latex2html.py", "tools/build_figures.py", "tools/katex_render.mjs",
                     "tools/visuals_build.py", "tools/review_gate.py", "tools/package-lock.json"]


def sha_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def build_inputs(root=ROOT):
    """{relative path: sha256} of every file that determines the built site."""
    out = {}
    for d in BUILD_INPUT_DIRS:
        base = os.path.join(root, d)
        for dp, dns, fs in os.walk(base):
            dns[:] = sorted(x for x in dns if x not in ("node_modules", "__pycache__"))
            for f in sorted(fs):
                if f.endswith((".pyc", ".DS_Store")):
                    continue
                p = os.path.join(dp, f)
                out[os.path.relpath(p, root).replace(os.sep, "/")] = sha_file(p)
    for f in BUILD_INPUT_FILES:
        p = os.path.join(root, f)
        if os.path.exists(p):
            out[f] = sha_file(p)
    return dict(sorted(out.items()))


def report(check, status, detail, data=None):
    RESULTS.append({"check": check, "status": status, "detail": detail, "data": data})
    print(f"[{status}] {check}: {detail}")


def arg(name, default):
    if name in sys.argv:
        return sys.argv[sys.argv.index(name) + 1]
    return default


def main():
    import yaml
    cfg = yaml.safe_load(open(os.path.join(ROOT, "site.config.yaml"), encoding="utf-8"))
    ins = cfg["inputs"]
    cur = {k: sha_file(os.path.join(ROOT, ins[k]["path"])) for k in ("jmlr_tex", "canonical_tex", "pdf")}

    # 1. snapshots
    bad = [f"{ins[k]['path']}: pinned {ins[k]['sha256'][:12]}, actual {cur[k][:12]}" for k in cur if cur[k] != ins[k]["sha256"]]
    report("input snapshots match site.config.yaml", "FAIL" if bad else "PASS",
           "; ".join(bad) if bad else "canonical source, JMLR source and PDF as pinned", bad)
    man_p = os.path.join(ROOT, "input", "source_manifest.json")
    if os.path.exists(man_p):
        man = json.load(open(man_p, encoding="utf-8"))
        fields = {"canonical_tex": "canonical_sha256", "jmlr_tex": "jmlr_sha256", "pdf": "pdf_sha256"}
        probs, absent = [], []
        for k, f in fields.items():
            if f not in man:
                absent.append(f)
            elif man[f] != cur[k]:
                probs.append(f"{f} in the manifest is not the hash of {ins[k]['path']}")
        status = "FAIL" if probs else ("WARN" if absent else "PASS")
        report("input/source_manifest.json names the current snapshots", status,
               "; ".join(probs) if probs else ("matches; the manifest does not record " + ", ".join(absent) if absent
                                               else "canonical, JMLR and PDF hashes match"), probs or absent)
    else:
        report("input/source_manifest.json names the current snapshots", "WARN", "no source manifest in input/")

    # 2. upstream
    ups = {"canonical_tex": arg("--canonical", os.path.join(ROOT, "..", "..", "02_working_copy", "candidate", "paper_revised_final.tex")),
           "jmlr_tex": arg("--jmlr-source", os.path.join(ROOT, "..", "..", "07_jmlr_review", "source", "paper_jmlr.tex")),
           "pdf": arg("--jmlr-pdf", os.path.join(ROOT, "..", "..", "07_jmlr_review", "paper_jmlr.pdf"))}
    unreachable, stale = [], []
    for k, p in ups.items():
        p = os.path.normpath(p)
        if not os.path.exists(p):
            unreachable.append(f"{k}: {p}")
        elif sha_file(p) != cur[k]:
            stale.append(f"{ins[k]['path']} differs from upstream {p}")
    if stale:
        report("snapshots equal the upstream manuscript", "FAIL", "; ".join(stale) + ". Sync the snapshots (and their "
               "hashes) before building; never present the older edition as matching the newer PDF.", stale)
    elif unreachable:
        status = "FAIL" if "--require-upstream" in sys.argv else "WARN"
        report("snapshots equal the upstream manuscript", status, "upstream not reachable from this folder, so the "
               "snapshots in input/ are the boundary of what this check can confirm: " + "; ".join(unreachable), unreachable)
    else:
        report("snapshots equal the upstream manuscript", "PASS", "canonical source, JMLR source and JMLR PDF equal upstream")

    # 3. reference compile
    tex = open(os.path.join(ROOT, ins["jmlr_tex"]["path"]), encoding="utf-8").read()
    labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
    rc = os.path.join(ROOT, "evidence_inputs", "reference_compile")
    aux_p, log_p = os.path.join(rc, "paper_jmlr.aux"), os.path.join(rc, "paper_jmlr.log")
    if not (os.path.exists(aux_p) and os.path.exists(log_p)):
        report("reference compile matches source and PDF", "FAIL", "evidence_inputs/reference_compile/paper_jmlr.aux or .log missing")
    else:
        aux = set(re.findall(r"\\newlabel\{([^}]+)\}\{\{", open(aux_p, encoding="utf-8", errors="replace").read()))
        aux = {a for a in aux if not a.endswith("@cref")}
        log = open(log_p, encoding="utf-8", errors="replace").read()
        log = re.sub(r"(?m)^(.{79})\n", r"\1", log)          # TeX wraps its log at 79 characters
        m = re.search(r"Output written on (\S+) \((\d+) pages?, (\d+) bytes\)", log)
        pdf_p = os.path.join(ROOT, ins["pdf"]["path"])
        pages = None
        try:
            out = subprocess.run(["pdfinfo", pdf_p], capture_output=True, text=True).stdout
            pages = int(re.search(r"Pages:\s+(\d+)", out).group(1))
        except (OSError, AttributeError):
            pass
        probs = []
        if aux != labels:
            probs.append(f"label sets differ (only in source: {sorted(labels - aux)[:8]}; only in .aux: {sorted(aux - labels)[:8]})")
        if not m:
            probs.append("the .log does not report an output file")
        else:
            if int(m.group(3)) != os.path.getsize(pdf_p):
                probs.append(f"the .log reports {m.group(3)} bytes, the PDF has {os.path.getsize(pdf_p)}")
            if pages is not None and int(m.group(2)) != pages:
                probs.append(f"the .log reports {m.group(2)} pages, the PDF has {pages}")
        report("reference compile matches source and PDF", "FAIL" if probs else "PASS",
               "; ".join(probs) if probs else f"{len(labels)} labels; the log reports this PDF's {m.group(2)} pages and "
               f"{m.group(3)} bytes", probs)

    # 4. correspondence
    corr = json.load(open(os.path.join(ROOT, "data", "paper_proof_correspondence.json"), encoding="utf-8"))
    probs = []
    if corr.get("manuscript_sha256") != cur["canonical_tex"]:
        probs.append("manuscript_sha256 is not the canonical snapshot's hash")
    if corr.get("jmlr_source_sha256") and corr["jmlr_source_sha256"] != cur["jmlr_tex"]:
        probs.append("jmlr_source_sha256 is not the JMLR snapshot's hash")
    report("proof correspondence names the current manuscript", "FAIL" if probs else "PASS",
           "; ".join(probs) if probs else "manuscript and JMLR hashes current", probs)

    # 5. check-only build
    p = subprocess.run([sys.executable, os.path.join(ROOT, "tools", "build_site.py"), "--check"],
                       capture_output=True, text=True, cwd=ROOT)
    msg = (p.stdout + p.stderr).strip()
    report("claims, illustrations and Lean reference match their reviewed locks", "PASS" if p.returncode == 0 else "FAIL",
           msg.splitlines()[-1] if p.returncode == 0 else msg[-3000:])

    # 6. built site
    dm = os.path.join(ROOT, "dist", "MANIFEST.json")
    if not os.path.exists(dm):
        report("dist/ is up to date", "FAIL", "no dist/MANIFEST.json: build the site")
    else:
        m = json.load(open(dm, encoding="utf-8"))
        probs = []
        if m.get("inputs") != cur:
            probs.append("built from other manuscript snapshots")
        recorded = m.get("build_inputs")
        if recorded is None:
            probs.append("the manifest does not record its build inputs (built by an older builder)")
        else:
            now = build_inputs()
            changed = sorted(k for k in set(now) | set(recorded) if now.get(k) != recorded.get(k))
            if changed:
                probs.append(f"{len(changed)} input file(s) changed since the build, e.g. {', '.join(changed[:6])}")
        wrong = [f["path"] for f in m["files"] if not os.path.exists(os.path.join(ROOT, "dist", f["path"]))
                 or sha_file(os.path.join(ROOT, "dist", f["path"])) != f["sha256"]]
        if wrong:
            probs.append(f"{len(wrong)} file(s) in dist/ differ from the manifest, e.g. {', '.join(wrong[:4])}")
        report("dist/ is up to date", "FAIL" if probs else "PASS",
               "; ".join(probs) + ". Rebuild with python3 tools/build_site.py." if probs else
               f"{len(m['files'])} files, built from the current inputs, content and tools", probs)

    os.makedirs(os.path.join(ROOT, "work", "review"), exist_ok=True)
    json.dump({"results": RESULTS}, open(os.path.join(ROOT, "work", "review", "sync_report.json"), "w"), indent=1)
    fails = [r for r in RESULTS if r["status"] == "FAIL"]
    warns = [r for r in RESULTS if r["status"] == "WARN"]
    print(f"\n{len(RESULTS) - len(fails) - len(warns)} passed, {len(warns)} warning(s), {len(fails)} failed")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
