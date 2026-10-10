#!/usr/bin/env python3
"""Summarise a fresh isolated Lean build made by build_bundle.sh.

Usage: python3 tools/lean/parse_build.py <build-dir> <out.json>

Reads <build-dir>/results.txt, started/finished stamps, lean_version.txt and every module
log.  Collects the `#print axioms` reports (which the project sources issue for their
headline theorems), every error/warning/sorry line, and per-module exit status.  Fails
(exit 1) if any module failed, any error or `sorry` appears, or any reported axiom lies
outside Lean's standard three (propext, Classical.choice, Quot.sound).
"""
import json, os, re, sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def main(bdir, out):
    res = {}
    for line in open(os.path.join(bdir, "results.txt")):
        m, s = line.split()
        res[m] = int(s)
    logs = {}
    axioms = {}
    problems = []
    warnings = {}
    for m in res:
        text = open(os.path.join(bdir, "logs", m + ".log"), encoding="utf-8").read()
        logs[m] = len(text.splitlines())
        # messages start with "<path>:<line>:<col>: <severity>:"; join continuation lines
        # A message starts at "<path>:<line>:<col>: <severity>:" or, for `#print axioms`
        # output (printed without a location), at a line beginning with a quoted name.
        msgs = re.split(r"\n(?=\S+\.lean:\d+:\d+: |'\S+' (?:depends|does not))", text.strip()) if text.strip() else []
        wcount = 0
        for msg in msgs:
            flat = " ".join(msg.split())
            mm = re.match(r"(\S+\.lean):(\d+):(\d+): (\w+): (.*)", flat)
            if not mm and flat.startswith("'"):
                body, sev = flat, "info"
                a = re.match(r"'(\S+)' depends on axioms: \[([^\]]*)\]$", body)
                if a:
                    axs = [x.strip() for x in a.group(2).split(",") if x.strip()]
                    axioms[a.group(1)] = {"module": m, "axioms": axs}
                    if not set(axs) <= STANDARD:
                        problems.append({"module": m, "nonstandard_axioms": a.group(1), "axioms": axs})
                    continue
                a = re.match(r"'(\S+)' does not depend on any axioms$", body)
                if a:
                    axioms[a.group(1)] = {"module": m, "axioms": []}
                    continue
                problems.append({"module": m, "unparsed": flat[:300]})
                continue
            if not mm:
                problems.append({"module": m, "unparsed": flat[:300]})
                continue
            sev, body = mm.group(4), mm.group(5)
            if sev == "error":
                problems.append({"module": m, "error": body[:300]})
            if "sorry" in body and sev == "warning":
                problems.append({"module": m, "sorry": body[:300]})
            if sev == "warning":
                wcount += 1
            a = re.match(r"'([^']+)' depends on axioms: \[(.*)\]", body)
            if a:
                axs = [x.strip() for x in a.group(2).split(",") if x.strip()]
                axioms[a.group(1)] = {"module": m, "axioms": axs, "line": int(mm.group(2))}
                if not set(axs) <= STANDARD:
                    problems.append({"module": m, "nonstandard_axioms": a.group(1), "axioms": axs})
            a = re.match(r"'([^']+)' does not depend on any axioms", body)
            if a:
                axioms[a.group(1)] = {"module": m, "axioms": [], "line": int(mm.group(2))}
        warnings[m] = wcount
    failed = [m for m, s in res.items() if s != 0]
    summary = {
        "build_dir_name": os.path.basename(os.path.normpath(bdir)),
        "started_utc": open(os.path.join(bdir, "started_utc.txt")).read().strip(),
        "finished_utc": open(os.path.join(bdir, "finished_utc.txt")).read().strip()
            if os.path.exists(os.path.join(bdir, "finished_utc.txt")) else None,
        "lean_version": open(os.path.join(bdir, "lean_version.txt")).read().strip(),
        "modules": len(res),
        "modules_ok": sum(1 for s in res.values() if s == 0),
        "failed": failed,
        "warnings_per_module": warnings,
        "warning_total": sum(warnings.values()),
        "axiom_reports": len(axioms),
        "axiom_sets": sorted({", ".join(v["axioms"]) or "(none)" for v in axioms.values()}),
        "problems": problems,
        "axioms": axioms,
    }
    json.dump(summary, open(out, "w"), indent=1, sort_keys=True)
    print(f"{summary['modules_ok']}/{summary['modules']} modules ok; "
          f"{summary['axiom_reports']} axiom reports; {summary['warning_total']} warnings; "
          f"{len(problems)} problems; axiom sets: {summary['axiom_sets']}")
    if failed or problems:
        sys.exit(1)

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
