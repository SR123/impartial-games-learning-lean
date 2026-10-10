"""Illustrations of the interactive edition (used by tools/build_site.py).

  * content/visuals/visuals.yaml lists the illustrations, the claims they attach to and the Lean
    declarations they depict; content/visuals/<name>.md holds their prose.
  * content/visuals/visuals.lock.json records, per illustration, the statement sources of its claims, the
    statements of its Lean declarations and the source of the paper figures it explains.  A change stops the
    build until the illustration is reviewed (--pin-visuals, through tools/review_gate.py).
  * data/visual_reference_lean.jsonl holds Lean's own evaluation of the depicted definitions on small inputs
    (tools/lean/VisualRef.lean); data/visual_reference_lean.meta.json records the Lean sources and script it
    came from.  The build refuses a reference computed from other Lean sources, and refuses to build if the
    browser engine (tools/visuals/nimvis-core.js) disagrees with it on any case.

Run directly to (re)write the reference metadata after regenerating the reference values:
    python3 tools/visuals_build.py --write-reference-meta "<lean --version output>"
"""
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys

import yaml

import review_gate

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPEC = os.path.join(ROOT, "content", "visuals", "visuals.yaml")
LOCK_REL = os.path.join("content", "visuals", "visuals.lock.json")
REF = os.path.join(ROOT, "data", "visual_reference_lean.jsonl")
REF_META = os.path.join(ROOT, "data", "visual_reference_lean.meta.json")
SCRIPT = os.path.join(ROOT, "tools", "lean", "VisualRef.lean")
ASSETS = ["nimvis-core.js", "nimvis-render.js", "nimvis-ui.js"]

KINDS = {
    "exact": ("Exact construction trace",
              "Every value is computed from the construction’s definitions for the example shown."),
    "schematic": ("Schematic", "Boxes summarise resources or group operations; they are not gates, layers or measurements."),
    "mixed": ("Exact trace and teaching example",
              "The checked compiler’s exact output is shown beside a hand-made teaching circuit; each part is labelled."),
}
TYPES = {"restore": ["rest"], "compile": ["net"], "rollout": ["shoot"],
         "recurrence": ["ctrl", "store", "summ"], "overview": []}


class VisualError(Exception):
    pass


def sha_text(t):
    return hashlib.sha256(t.encode("utf-8")).hexdigest()


def sha_file(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def prose(v):
    path = os.path.join(ROOT, v["prose"])
    if not os.path.exists(path):
        raise VisualError(f"illustration prose {v['prose']} missing")
    txt = open(path, encoding="utf-8").read()
    parts = dict(re.findall(r"<!--\s*(intro|notes)\s*-->\s*(.*?)(?=<!--\s*(?:intro|notes)\s*-->|\Z)", txt, flags=re.S))
    if set(parts) != {"intro", "notes"}:
        raise VisualError(f"{v['prose']}: needs <!-- intro --> and <!-- notes --> sections")
    return parts["intro"].strip(), parts["notes"].strip()


def link_target(ref, claims):
    cid, _, frag = ref.partition("#")
    if cid not in claims:
        raise VisualError(f"link to unknown claim {cid}")
    return f"claims/{cid.replace(':', '__')}.html" + (f"#{frag}" if frag else "")


def load(claims, export, labels):
    """Validate the specification against the claim map, the Lean export and the article labels."""
    spec = yaml.safe_load(open(SPEC, encoding="utf-8"))["visuals"]
    problems = []
    for vid, v in spec.items():
        for f in ("title", "kind", "type", "prose", "attach"):
            if f not in v:
                problems.append(f"{vid}: missing field {f}")
        if v.get("kind") not in KINDS:
            problems.append(f"{vid}: unknown kind {v.get('kind')}")
        if v.get("type") not in TYPES:
            problems.append(f"{vid}: unknown type {v.get('type')}")
        for n in v.get("lean", []):
            if n not in export:
                problems.append(f"{vid}: Lean declaration {n} not in the export")
        for lab in v.get("figures", []):
            if lab not in labels:
                problems.append(f"{vid}: unknown paper figure {lab}")
        for a in v.get("attach", []):
            if a["claim"] not in claims:
                problems.append(f"{vid}: attached to unknown claim {a['claim']}")
        for k, ref in (v.get("config", {}).get("links") or {}).items():
            try:
                link_target(ref, claims)
            except VisualError as e:
                problems.append(f"{vid}: {e}")
        try:
            prose(v)
        except VisualError as e:
            problems.append(str(e))
    if problems:
        raise VisualError("illustration specification problems:\n  " + "\n  ".join(problems))
    return spec


def fingerprint(spec, claims, export, blocks_by_label):
    fp = {}
    for vid, v in spec.items():
        fp[vid] = {
            "claims": {a["claim"]: claims[a["claim"]]["source_sha256"] for a in v["attach"]},
            "lean": {n: sha_text(export[n]["type"]) for n in v.get("lean", [])},
            "figures": {lab: sha_text(blocks_by_label[lab]["src"]) for lab in v.get("figures", [])},
        }
    return fp


def check_lock(fp, pin):
    gate = review_gate.Gate(ROOT, "visuals", "illustrations", LOCK_REL, "--pin-visuals")
    lock = gate.load_lock()
    items = []
    if lock is None:
        items = [{"id": vid, "change": "no lock yet", "old": None, "new": sha_text(json.dumps(fp[vid], sort_keys=True)),
                  "detail": "illustration not yet reviewed"} for vid in fp]
    else:
        old = lock.get("visuals", {})
        for vid, cur in fp.items():
            prev = old.get(vid)
            if prev is None:
                items.append({"id": vid, "change": "new illustration", "old": None,
                              "new": sha_text(json.dumps(cur, sort_keys=True))})
                continue
            changed = []
            for part in ("claims", "lean", "figures"):
                a, b = prev.get(part, {}), cur[part]
                for k in sorted(set(a) | set(b)):
                    if a.get(k) != b.get(k):
                        changed.append(f"{ {'claims': 'claim', 'lean': 'Lean declaration', 'figures': 'figure'}[part]} {k}: " +
                                       ("added" if k not in a else "removed" if k not in b else "changed"))
            if changed:
                items.append({"id": vid, "change": "inputs changed", "old": sha_text(json.dumps(prev, sort_keys=True)),
                              "new": sha_text(json.dumps(cur, sort_keys=True)), "detail": "; ".join(changed)})
        for vid in old:
            if vid not in fp:
                items.append({"id": vid, "change": "illustration removed", "old": None, "new": None})
    if not items:
        if pin:
            gate.clear()
        return
    if pin:
        try:
            doc = gate.require_reviewed(items)
        except review_gate.ReviewError as e:
            raise VisualError(str(e))
        json.dump({"visuals": fp}, open(os.path.join(ROOT, LOCK_REL), "w", encoding="utf-8"), indent=1, sort_keys=True)
        where = gate.archive(doc, "lock")
        gate.clear()
        print(f"pinned {len(items)} reviewed illustration change(s); review archived in {where}")
        return
    gate.write_review(items, {})
    raise VisualError("STALE ILLUSTRATIONS - " + str(len(items)) + " illustration(s) depend on changed claims, Lean "
                      "statements or paper figures. A review list is in work/review/VISUALS_REVIEW.md. Check each "
                      "illustration, mark the items reviewed in work/review/visuals_review.json, then run with "
                      "--pin-visuals:\n  " + "\n  ".join(f"{i['id']}: {i['change']} {i.get('detail', '')}" for i in items))


def lean_sources():
    out = {}
    d = os.path.join(ROOT, "lean")
    for dp, _, fs in os.walk(d):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                out[os.path.relpath(p, d)] = sha_file(p)
    return dict(sorted(out.items()))


def expected_meta(lean_version):
    return {"script": "tools/lean/VisualRef.lean", "script_sha256": sha_file(SCRIPT),
            "reference": "data/visual_reference_lean.jsonl", "reference_sha256": sha_file(REF),
            "lean_sources_sha256": lean_sources(), "lean_version": lean_version,
            "command": "LEAN_PATH=<build>/olean lean tools/lean/VisualRef.lean > data/visual_reference_lean.jsonl",
            "written_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}


def check_reference():
    """The reference must come from the current script and the current Lean sources."""
    if not os.path.exists(REF_META):
        raise VisualError("data/visual_reference_lean.meta.json missing: regenerate the Lean reference values")
    meta = json.load(open(REF_META, encoding="utf-8"))
    problems = []
    if meta["script_sha256"] != sha_file(SCRIPT):
        problems.append("tools/lean/VisualRef.lean changed since the reference was computed")
    if meta["reference_sha256"] != sha_file(REF):
        problems.append("data/visual_reference_lean.jsonl differs from the recorded file")
    if meta["lean_sources_sha256"] != lean_sources():
        problems.append("the bundled Lean sources changed since the reference was computed")
    if problems:
        raise VisualError("STALE LEAN REFERENCE FOR THE ILLUSTRATIONS:\n  " + "\n  ".join(problems) +
                          "\n  Recompute it with tools/lean/VisualRef.lean (see the file header).")
    return meta


def check_engine():
    p = subprocess.run(["node", os.path.join(ROOT, "tools", "visuals", "check_engine.js"), REF],
                       capture_output=True, text=True)
    try:
        res = json.loads(p.stdout)
    except ValueError:
        raise VisualError("engine check failed to run:\n" + p.stderr[-1500:])
    if p.returncode != 0 or res["total_mismatches"]:
        raise VisualError("the illustration engine disagrees with Lean's evaluation:\n  " +
                          json.dumps(res["first"], ensure_ascii=False)[:2000])
    return res


def reference_data():
    nets, restsize = {}, []
    for line in open(REF, encoding="utf-8"):
        if not line.startswith("{"):
            continue
        r = json.loads(line)
        if r["kind"] == "net":
            nets[r["name"]] = {k: r[k] for k in ("n", "depths", "sizes", "prog", "outs", "levels", "layers", "table")}
        elif r["kind"] == "restsize":
            restsize.append({k: r[k] for k in ("B", "N", "D", "S", "K", "layers", "gates")})
    return {"nets": nets, "restsize": restsize}


def instances(spec, claims):
    out = []
    for vid, v in spec.items():
        for a in v["attach"]:
            cfg = dict(v.get("config", {}))
            cfg.update(a.get("config", {}) or {})
            if "links" in cfg:
                cfg["links"] = {k: link_target(ref, claims) for k, ref in cfg["links"].items()}
            out.append({"key": f"{vid}|{a['claim']}", "vid": vid, "claim": a["claim"], "type": v["type"], "config": cfg})
    return out


def render(insts, data):
    req = {"instances": [{"key": i["key"], "type": i["type"], "config": i["config"]} for i in insts], "data": data}
    p = subprocess.run(["node", os.path.join(ROOT, "tools", "visuals", "render_static.js")], input=json.dumps(req),
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise VisualError("illustration rendering failed:\n" + p.stderr[-2000:])
    return json.loads(p.stdout)


if __name__ == "__main__":
    if len(sys.argv) >= 3 and sys.argv[1] == "--write-reference-meta":
        json.dump(expected_meta(sys.argv[2]), open(REF_META, "w", encoding="utf-8"), indent=1)
        print("wrote", os.path.relpath(REF_META, ROOT))
    else:
        print(__doc__)
