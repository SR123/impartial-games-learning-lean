#!/usr/bin/env python3
"""Build the static interactive edition into dist/.

    python3 tools/build_site.py            # build; fail on any stale or unresolved link
    python3 tools/build_site.py --pin      # after human review: re-pin claim source hashes

Pipeline (each step fails loudly):
  1. verify the pinned input hashes (site.config.yaml);
  2. convert the manuscript (tools/latex2html.py) and build figure SVGs;
  3. verify the bundled Lean sources against the audited declaration index, and every
     declaration named by a claim against the fresh Lean export;
  4. load claim metadata (data/claims.source.yaml) and handwritten explanations
     (content/explanations/*.md); resolve every claim anchor; compare each claim's
     statement-source hash with data/claims.lock.json (stale -> failure);
  5. render pages: index, paper, one page per claim (all four levels, no JavaScript
     needed), coverage, source browser, build provenance, edition notes, author's note;
  6. write data/claims.json (machine-readable claim records) and dist/MANIFEST.json.
"""
import hashlib
import html
import json
import os
import re
import shutil
import subprocess
import sys

import markdown
import yaml

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import latex2html  # noqa
import review_gate  # noqa
import visuals_build  # noqa: E402
import check_sync  # noqa: E402

DIST = os.path.join(ROOT, "dist")
GEN = os.path.join(ROOT, "generated")

CATEGORIES = {
    "checked-theorem": ("Checked theorem", "Lean checks a formal statement corresponding to this claim."),
    "checked-definition": ("Checked definition or construction",
                           "Lean contains the definition or construction, with checked properties."),
    "checked-conditional": ("Checked conditional theorem using named classical input",
                            "Lean checks the implication from a named, unproved classical hypothesis."),
    "classical-external": ("External cited result",
                           "A published result used as background or input; not proved in Lean here."),
    "empirical": ("Empirical result", "Supported by saved experimental runs, not by a proof."),
    "informal": ("Informal interpretation", "Motivation, interpretation or scope; not a formal claim."),
    "open": ("Open or deferred item", "Explicitly left open, deferred or not yet connected."),
}
LEVELS = [("explain", "Explain this"), ("formal", "How this is formalised"),
          ("lean", "Lean statement and source")]


class BuildError(Exception):
    pass


def sha256_file(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def sha256_text(t):
    return hashlib.sha256(t.encode("utf-8")).hexdigest()


def esc(t):
    return html.escape(str(t), quote=True)


def fileid(cid):
    return cid.replace(":", "__")


# ---------------------------------------------------------------------------------------
# Inputs
# ---------------------------------------------------------------------------------------

def load_config():
    cfg = yaml.safe_load(open(os.path.join(ROOT, "site.config.yaml"), encoding="utf-8"))
    problems = []
    for key in ("jmlr_tex", "canonical_tex", "pdf"):
        ent = cfg["inputs"][key]
        actual = sha256_file(os.path.join(ROOT, ent["path"]))
        if actual != ent["sha256"]:
            problems.append(f"{ent['path']}: expected {ent['sha256']}, found {actual}")
    if problems:
        raise BuildError("input hash mismatch (refusing to build against another version):\n  "
                         + "\n  ".join(problems))
    return cfg


def lean_sources(decl_index):
    """Map module -> info for the 38 bundled files; verify hashes against the audit index."""
    mods = {}
    for d in decl_index:
        rel = d["source"].split("05_revision_cycle/lean/", 1)[1]
        mods.setdefault(d["module"], {"rel": rel, "sha256": d["sha256"]})
    lean_dir = os.path.join(ROOT, "lean")
    # modules without theorems would be missing from the index: none in this development
    found = {}
    for dirpath, _, files in os.walk(lean_dir):
        for f in files:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, f), lean_dir)
                found[os.path.splitext(f)[0]] = rel
    problems = []
    for m, info in mods.items():
        p = os.path.join(lean_dir, info["rel"])
        if not os.path.exists(p):
            problems.append(f"missing {info['rel']}")
            continue
        actual = sha256_file(p)
        if actual != info["sha256"]:
            problems.append(f"{info['rel']}: audited {info['sha256'][:12]}, bundled {actual[:12]}")
        text = open(p, encoding="utf-8").read()
        info["text"] = text
        info["lines"] = text.split("\n")
        if info["lines"] and info["lines"][-1] == "":
            info["lines"] = info["lines"][:-1]
        info["imports"] = [l.split()[1] for l in info["lines"] if l.startswith("import ")]
        m0 = re.match(r"\s*/-(.*?)-/", re.sub(r"^(import .*\n|\s*\n)*", "", text), re.S)
        info["header"] = m0.group(1).strip() if m0 else ""
        info["phase"] = info["rel"].split("/")[0] if "/" in info["rel"] else "phase1"
    extra = set(found) - set(mods)
    if extra:
        problems.append(f"Lean files not in the audited index: {sorted(extra)}")
    if problems:
        raise BuildError("Lean sources differ from the audited declaration index:\n  " + "\n  ".join(problems))
    return mods


# ---------------------------------------------------------------------------------------
# Markdown with math and cross-references
# ---------------------------------------------------------------------------------------

class Markup:
    def __init__(self, article, export, mods, claims_by_id, macros):
        self.article = article
        self.labels = article["labels"]
        self.blocks = {b["id"]: b for b in article["blocks"] if b.get("id")}
        for b in article["blocks"]:
            for x in b.get("runin_ids", []):
                self.blocks.setdefault(x, dict(b, display_name=f"“{b.get('runin_title_text', '').rstrip('.')}”"))
            for x in b.get("extra_ids", []):
                self.blocks.setdefault(x, b)
        self.export = export
        self.mods = mods
        self.claims = claims_by_id
        self.macros = macros
        self.math = []          # (token, tex, display)
        self.errors = []

    def label_name(self, lab):
        info = self.labels.get(lab)
        if info:
            k, n = info["kind"], info["number"]
            if k == "section":
                return (f"Appendix {n}" if n[:1].isalpha() and "." not in n else f"Section {n}")
            if k == "equation":
                return f"({n})"
            if k in ("figure",):
                return f"Figure {n}"
            if k == "table":
                return f"Table {n}"
            if k == "paragraph":
                return f"Section {n}"
            return f"{k.capitalize()} {n}"
        b = self.blocks.get(lab)
        if b and b.get("display_name"):
            return b["display_name"]
        if lab in self.claims:
            return self.claims[lab]["display"]
        return None

    def lean_link(self, name):
        e = self.export.get(name)
        if not e:
            self.errors.append(f"unknown Lean declaration {name}")
            return f"<code>{esc(name)}</code>"
        short = name.replace("NimAudit.", "")
        return (f'<a class="lean-ref" href="source/{e["module"]}.html#L{e["line"]}">'
                f"<code>{esc(short)}</code></a>")

    def render(self, text, where):
        toks = {}

        def keep(h):
            t = f"XQX{len(toks)}XQX"
            toks[t] = h
            return t

        def mathsub(m, display):
            tok = f"XMX{len(self.math)}XMX"
            self.math.append((tok, m.group(1).strip(), display))
            return tok

        s = text
        s = re.sub(r"\$\$(.+?)\$\$", lambda m: mathsub(m, True), s, flags=re.S)
        s = re.sub(r"(?<![\\$])\$(?!\$)(.+?)(?<!\\)\$", lambda m: mathsub(m, False), s)

        def xref(m):
            lab, _, txt = m.group(1).partition("|")
            lab = lab.strip()
            name = self.label_name(lab)
            if name is None:
                self.errors.append(f"{where}: unknown paper reference [[{lab}]]")
                return keep(esc(txt or lab))
            return keep(f'<a class="paper-ref" href="paper.html#{esc(lab)}">{esc(txt.strip() or name)}</a>')
        s = re.sub(r"\[\[([^\]]+)\]\]", xref, s)
        s = re.sub(r"\{\{lean:([^}]+)\}\}", lambda m: keep(self.lean_link(m.group(1).strip())), s)

        def cref(m):
            cid = m.group(1).strip()
            if cid not in self.claims:
                self.errors.append(f"{where}: unknown claim {cid}")
                return keep(esc(cid))
            return keep(f'<a class="claim-ref" href="claims/{fileid(cid)}.html">'
                        f'{esc(self.claims[cid]["display"])}</a>')
        s = re.sub(r"\{\{claim:([^}]+)\}\}", cref, s)
        s = re.sub(r"\[AUTHOR TO (ADD|REVIEW):([^\]]*)\]",
                   lambda m: keep(f'<span class="editorial">[Author to {m.group(1).lower()}:'
                                  f'{esc(m.group(2))}]</span>'), s)
        h = markdown.markdown(s, extensions=["tables", "sane_lists", "fenced_code"])
        for t, v in toks.items():
            h = h.replace(t, v)
        return h

    def finish(self, html_parts):
        """Render collected math with KaTeX and substitute into the given strings."""
        if not self.math:
            return html_parts
        items = [{"id": tok, "tex": tex, "display": disp} for tok, tex, disp in self.math]
        req = {"macros": self.macros, "items": items}
        p = subprocess.run(["node", os.path.join(ROOT, "tools", "katex_render.mjs")],
                           input=json.dumps(req), capture_output=True, text=True,
                           cwd=os.path.join(ROOT, "tools"))
        if p.returncode != 0:
            raise BuildError("KaTeX failed: " + p.stderr[-1500:])
        res = json.loads(p.stdout)
        if res["errors"]:
            raise BuildError("KaTeX rejected explanation math:\n  " + "\n  ".join(
                f"{e['tex'][:80]}: {e['message']}" for e in res["errors"]))
        out = []
        for part in html_parts:
            def sub(m):
                return res["html"][m.group(0)]
            part = re.sub(r"XMX\d+XMX", sub, part)
            out.append(part)
        return out


def load_explanations():
    """content/explanations/*.md: entries introduced by <!-- explain: ID --> or <!-- formal: ID -->."""
    entries = {}
    d = os.path.join(ROOT, "content", "explanations")
    for f in sorted(os.listdir(d)):
        if not f.endswith(".md"):
            continue
        text = open(os.path.join(d, f), encoding="utf-8").read()
        parts = re.split(r"<!--\s*(explain|formal):\s*([^\s]+)\s*-->", text)
        for i in range(1, len(parts), 3):
            key = f"{parts[i]}/{parts[i + 1]}"
            if key in entries:
                raise BuildError(f"duplicate explanation {key}")
            entries[key] = {"text": parts[i + 2].strip(), "file": f"content/explanations/{f}"}
    return entries


# ---------------------------------------------------------------------------------------
# Claims
# ---------------------------------------------------------------------------------------

def norm_src(s):
    return re.sub(r"\s+", " ", s).strip()


def resolve_claims(article, raw_claims, export, decl_index_names, expl):
    blocks = article["blocks"]
    by_id = {b["id"]: b for b in blocks if b.get("id")}
    extra_ids = {}
    for b in blocks:
        for x in b.get("extra_ids", []) + b.get("runin_ids", []):
            extra_ids[x] = b
        for x in re.findall(r'\sid="([^"]+)"', b["html"]):
            if x not in by_id:
                extra_ids.setdefault(x, b)
    claims, problems, seen = [], [], set()
    for c in raw_claims:
        cid = c["id"]
        if cid in seen:
            problems.append(f"duplicate claim id {cid}")
        seen.add(cid)
        if c["category"] not in CATEGORIES:
            problems.append(f"{cid}: unknown category {c['category']}")
        blk = None
        if c.get("snippet"):
            scope = c.get("in")
            cands = [b for b in blocks if (scope is None or b["heading"] == scope or b.get("id") == scope)
                     and norm_src(c["snippet"]) in b["src"]]
            if len(cands) != 1:
                problems.append(f"{cid}: snippet matches {len(cands)} blocks in {scope}: {c['snippet'][:50]!r}")
                continue
            blk = cands[0]
            c["anchor"] = cid
            c["anchor_mode"] = "website"
        else:
            target = c.get("target", cid)
            blk = by_id.get(target) or extra_ids.get(target)
            if blk is None:
                problems.append(f"{cid}: target {target} not found in the generated article")
                continue
            c["anchor"] = target
            c["anchor_mode"] = "label" if target in article["labels"] else "website"
        c["block"] = blk
        c["block_id"] = blk["id"]
        c["source_sha256"] = sha256_text(blk["src"])
        c["source_lines"] = blk["lines"]
        for n in c.get("lean", []) + c.get("lean_defs", []):
            if n not in export:
                problems.append(f"{cid}: Lean declaration {n} not in the fresh export")
            elif export[n]["kind"] == "theorem" and n not in decl_index_names and not export[n]["private"]:
                problems.append(f"{cid}: theorem {n} not in the audited declaration index")
        for lvl in ("explain", "formal"):
            key = c.get(lvl, f"{lvl}/{cid}")
            c[lvl + "_id"] = key
            if key not in expl:
                problems.append(f"{cid}: missing explanation {key}")
        if c["category"] in ("checked-theorem", "checked-conditional", "checked-definition") and not c.get("lean"):
            problems.append(f"{cid}: category {c['category']} requires Lean declarations")
        if c["category"] == "checked-conditional" and not c.get("named_inputs"):
            problems.append(f"{cid}: conditional claim must name its classical input(s)")
        claims.append(c)
    if problems:
        raise BuildError("claim map problems:\n  " + "\n  ".join(problems))
    return claims


def check_lock(claims, lock_path, pin, manuscript_sha, illustrations=None):
    """Compare every claim's statement source with the reviewed lock.

    On a difference the build stops and writes a review list (work/review/CLAIMS_REVIEW.md and
    claims_review.json).  `--pin` writes a new lock only when every listed change has been marked
    reviewed with a note (tools/review_gate.py); it never blesses changes silently."""
    illustrations = illustrations or {}
    gate = review_gate.Gate(ROOT, "claims", "claim statement sources", os.path.relpath(lock_path, ROOT), "--pin")
    current = {c["id"]: {"source_sha256": c["source_sha256"], "block": c["block_id"],
                         "lines": c["source_lines"]} for c in claims}
    by_id = {c["id"]: c for c in claims}
    lock = gate.load_lock()
    items = []

    def item(cid, change, old, new):
        c = by_id.get(cid)
        it = {"id": cid, "change": change, "old": old, "new": new}
        if c:
            it.update({"block": c["block_id"], "lines": c["source_lines"],
                       "content": [c["explain_id"], c["formal_id"]], "lean": c.get("lean", []),
                       "illustrations": illustrations.get(cid, []), "excerpt": norm_src(c["block"]["src"])})
        return it
    if lock is None:
        items.append({"id": "(lock)", "change": "no lock yet", "old": None, "new": manuscript_sha,
                      "detail": "data/claims.lock.json is missing: review the whole claim map"})
    else:
        if lock["manuscript_sha256"] != manuscript_sha:
            items.append({"id": "(manuscript)", "change": "manuscript changed", "old": lock["manuscript_sha256"],
                          "new": manuscript_sha, "detail": "the converted JMLR source differs from the pinned one; "
                          "the claims listed below (if any) changed statement text"})
        for cid, cur in current.items():
            old = lock["claims"].get(cid)
            if old is None:
                items.append(item(cid, "new claim", None, cur["source_sha256"]))
            elif old["source_sha256"] != cur["source_sha256"]:
                items.append(item(cid, "statement source changed", old["source_sha256"], cur["source_sha256"]))
        for cid in lock["claims"]:
            if cid not in current:
                items.append({"id": cid, "change": "claim removed", "old": lock["claims"][cid]["source_sha256"],
                              "new": None})

    def write_lock():
        full = {cid: dict(v, source_text=norm_src(by_id[cid]["block"]["src"])) for cid, v in current.items()}
        json.dump({"manuscript_sha256": manuscript_sha, "claims": full}, open(lock_path, "w"), indent=1,
                  sort_keys=True, ensure_ascii=False)
    if not items:
        if pin:
            write_lock()
            gate.clear()
        return []
    if pin:
        try:
            doc = gate.require_reviewed(items)
        except review_gate.ReviewError as e:
            raise BuildError(str(e))
        write_lock()
        where = gate.archive(doc, manuscript_sha[:12])
        gate.clear()
        print(f"pinned {len(items)} reviewed change(s) to claim statements; review archived in {where}")
        return []
    gate.write_review(items, {"manuscript_sha256": manuscript_sha,
                              "locked_manuscript_sha256": lock and lock["manuscript_sha256"]})
    raise BuildError("STALE CLAIM METADATA - " + str(len(items)) + " change(s) since the last review. A review list "
                     "is in work/review/CLAIMS_REVIEW.md. Update the explanations and claim records it names, mark "
                     "each item reviewed in work/review/claims_review.json, then run with --pin:\n  " +
                     "\n  ".join(f"{i['id']}: {i['change']}" for i in items))


# ---------------------------------------------------------------------------------------
# HTML helpers
# ---------------------------------------------------------------------------------------

VIS_SCRIPTS = "".join(f'<script defer src="assets/visuals/{f}"></script>' for f in
                      ("nimvis-core.js", "nimvis-render.js", "nimvis-ui.js"))

NAV = [("paper.html", "Paper"), ("paper/paper_jmlr.pdf", "PDF"), ("coverage.html", "Proof coverage"),
       ("source/index.html", "Lean sources"), ("build.html", "Build"), ("edition.html", "About this edition")]


SUP_RE = re.compile(r"(A?CC|AC|TC|NC)\u2070")


def supfix(h):
    """Typeset AC⁰-style superscripts as <sup> in text nodes (some serif fonts lack U+2070)."""
    out = []
    for part in re.split(r"(<[^>]+>)", h):
        if part.startswith("<"):
            out.append(part)
        else:
            out.append(SUP_RE.sub(r"\1<sup>0</sup>", part))
    return "".join(out)


def page(title, body, cfg, page_class, rel, current=None, head_extra=""):
    """A complete HTML page for output path `rel` (relative to dist/).  Pages in
    subdirectories get a relative <base> pointing at the site root, so every link is written
    root-relative and works under any deployment prefix."""
    body = supfix(body)
    depth = rel.count("/")
    base = f'<base href="{"../" * depth}">' if depth else ""
    skip = f"{rel}#main" if depth else "#main"
    cur_attr = ' aria-current="page"'
    nav = " ".join(
        f'<a href="{h}"{cur_attr if h == current else ""}>{esc(t)}</a>' for h, t in NAV)
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
{base}
<title>{esc(title)}</title>
<link rel="stylesheet" href="assets/katex/katex.min.css">
<link rel="stylesheet" href="assets/site.css">
<script defer src="assets/site.js"></script>
{head_extra}
</head>
<body class="{page_class}">
<a class="skip" href="{skip}">Skip to content</a>
<header class="site-bar">
<a class="site-home" href="index.html">NIM paper · interactive edition</a>
<nav class="site-nav" aria-label="Edition">{nav}</nav>
<span class="build-flag">{esc(cfg["status_line"])}</span>
</header>
{body}
<footer class="site-foot">
<p>Interactive edition of a manuscript by Søren Riis ({esc(cfg["build_label"])}). The paper text is generated
from <code>paper_jmlr.tex</code>; the PDF is the exact layout reference. Explanations, coverage records and
source pages are additions of this edition and are not part of the paper.</p>
</footer>
</body>
</html>
"""


def cat_chip(cat):
    label, desc = CATEGORIES[cat]
    return f'<span class="cat cat-{cat}" title="{esc(desc)}">{esc(label)}</span>'


def rewrite_fragment_links(h):
    """For content shown outside paper.html: fragment links point into the paper."""
    return re.sub(r'href="#', 'href="paper.html#', h)


def strip_ids(h, prefix):
    return re.sub(r'\sid="([^"]+)"', lambda m: f' id="{prefix}{m.group(1)}"', h)


def lean_code(lines, start, end, numbered=True, mod=None):
    out = []
    for k in range(start, end + 1):
        txt = esc(lines[k - 1]) if k - 1 < len(lines) else ""
        if numbered:
            ln = (f'<a class="ln" href="source/{mod}.html#L{k}" aria-label="line {k}">{k}</a>'
                  if mod else f'<span class="ln">{k}</span>')
            out.append(f'<span class="cl">{ln}<span class="lc">{txt}</span></span>')
        else:
            out.append(txt)
    return '<pre class="lean"><code>' + "".join(out) + "</code></pre>"


# ---------------------------------------------------------------------------------------
# Builder
# ---------------------------------------------------------------------------------------

class Site:
    def __init__(self, pin=False, allow_incomplete=False, pin_visuals=False):
        self.pin = pin
        self.pin_visuals = pin_visuals
        self.allow_incomplete = allow_incomplete
        self.cfg = load_config()
        self.files = {}   # dist relative path -> origin description

    def write(self, rel, content, origin="generated"):
        p = os.path.join(DIST, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        mode = "wb" if isinstance(content, bytes) else "w"
        with open(p, mode, **({} if mode == "wb" else {"encoding": "utf-8"})) as f:
            f.write(content)
        self.files[rel] = origin

    def copy(self, src, rel, origin):
        p = os.path.join(DIST, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        shutil.copyfile(src, p)
        self.files[rel] = origin

    # -- step 2 --
    def convert(self, gen=None):
        cfg = self.cfg
        self.article = latex2html.convert(os.path.join(ROOT, cfg["inputs"]["jmlr_tex"]["path"]),
                                          os.path.join(ROOT, "content", "figures.yaml"), gen or GEN)
        if self.article["source_sha256"] != cfg["inputs"]["jmlr_tex"]["sha256"]:
            raise BuildError("converted source hash differs from the pinned input")
        if gen:
            return
        figs = os.path.join(DIST, "assets", "figures")
        p = subprocess.run([sys.executable, os.path.join(ROOT, "tools", "build_figures.py"), GEN,
                            os.path.join(ROOT, "input", "jmlr_source"), figs], capture_output=True, text=True)
        if p.returncode != 0:
            raise BuildError("figure build failed:\n" + p.stdout[-2000:] + p.stderr[-2000:])
        self.fig_manifest = json.load(open(os.path.join(GEN, "figures_manifest.json")))
        for f in self.fig_manifest:
            self.files[f["output"]] = f"figure from {f['source']} ({f['method']})"

    # -- step 3 --
    def load_lean(self):
        cfg = self.cfg
        self.decl_index = json.load(open(os.path.join(ROOT, cfg["inputs"]["declaration_index"])))
        self.decl_index_names = {d["name"] for d in self.decl_index}
        exp = json.load(open(os.path.join(ROOT, cfg["inputs"]["lean_export"])))
        self.export = {e["name"]: e for e in exp}
        self.fresh = json.load(open(os.path.join(ROOT, cfg["inputs"]["fresh_build"])))
        self.corr = json.load(open(os.path.join(ROOT, cfg["inputs"]["correspondence"])))
        self.mods = lean_sources(self.decl_index)
        # cross-check: every indexed theorem is in the export at the same selection line
        bad = [d["name"] for d in self.decl_index
               if d["name"] not in self.export or self.export[d["name"]]["selLine"] != d["line"]
               or self.export[d["name"]]["module"] != d["module"]]
        if bad:
            raise BuildError(f"declaration index and fresh export disagree for {len(bad)} names: {bad[:5]}")
        n_mod = cfg["lean"]["audited_extent"]["modules"]
        if self.fresh["modules_ok"] != n_mod or self.fresh["problems"]:
            raise BuildError(f"fresh Lean build evidence does not show {n_mod} clean modules")
        if set(self.fresh["axioms"]) != self.decl_index_names:
            raise BuildError("fresh axiom reports do not match the declaration index")
        if self.corr["manuscript_sha256"] != cfg["inputs"]["canonical_tex"]["sha256"] or \
                self.corr["jmlr_source_sha256"] != cfg["inputs"]["jmlr_tex"]["sha256"]:
            raise BuildError("correspondence map was made for a different manuscript version")
        for row in self.corr["rows"]:
            for p in row["proofs"]:
                d = self.export.get(p["name"])
                if d is None or d["module"] != p["module"] or d["selLine"] != p["line"]:
                    raise BuildError(f"correspondence row {row['label']}: {p['name']} does not match the export")
                if self.mods[p["module"]]["sha256"] != p["sha256"]:
                    raise BuildError(f"correspondence row {row['label']}: source hash mismatch for {p['module']}")

    # -- step 4 --
    def load_claims(self):
        raw = yaml.safe_load(open(os.path.join(ROOT, "data", "claims.source.yaml"), encoding="utf-8"))
        self.expl = load_explanations()
        self.claims = resolve_claims(self.article, raw["claims"], self.export, self.decl_index_names, self.expl)
        self.claim_by_id = {c["id"]: c for c in self.claims}
        for c in self.claims:
            c["section"] = self.section_number(c["block"]["heading"] if c["block"]["kind"] != "heading"
                                               else c["block"]["id"])
            if not c.get("display"):
                c["display"] = self.display_name(c)
        # coverage requirements
        problems = []
        covered = {c["anchor"] for c in self.claims} | {c["block_id"] for c in self.claims}
        for b in self.article["blocks"]:
            if b["kind"] == "stmt" and b["id"] not in covered:
                problems.append(f"statement {b['id']} has no claim record")
        rows = {r["label"] for r in self.corr["rows"]}
        mapped = set()
        for c in self.claims:
            mapped |= set(c.get("audit_rows", []))
        missing_rows = rows - mapped
        if missing_rows:
            problems.append(f"audited correspondence rows without a claim: {sorted(missing_rows)}")
        unknown_rows = mapped - rows
        if unknown_rows:
            problems.append(f"claims cite unknown audit rows: {sorted(unknown_rows)}")
        for c in self.claims:
            for d in c.get("depends_on", []):
                if d not in self.claim_by_id:
                    problems.append(f"{c['id']}: depends on unknown claim {d}")
        if problems:
            if self.allow_incomplete:
                print("WARNING (development build, --allow-incomplete): coverage inventory incomplete:\n  "
                      + "\n  ".join(problems[:20]) + (f"\n  … {len(problems) - 20} more" if len(problems) > 20 else ""))
            else:
                raise BuildError("coverage inventory incomplete:\n  " + "\n  ".join(problems))
        check_lock(self.claims, os.path.join(ROOT, "data", "claims.lock.json"), self.pin,
                   self.article["source_sha256"], self.illustration_map())

    # -- illustrations (tools/visuals_build.py) --
    def illustration_map(self):
        spec = yaml.safe_load(open(visuals_build.SPEC, encoding="utf-8"))["visuals"]
        out = {}
        for vid, v in spec.items():
            for a in v.get("attach", []):
                out.setdefault(a["claim"], []).append(vid)
        return out

    def label_block(self, lab):
        bid = self.article["labels"][lab]["id"]
        for b in self.article["blocks"]:
            if b.get("id") == bid or bid in b.get("extra_ids", []) or f'id="{bid}"' in b["html"]:
                return b
        raise BuildError(f"no block for label {lab}")

    def load_visuals(self):
        try:
            self.vspec = visuals_build.load(self.claim_by_id, self.export, self.article["labels"])
            labs = {lab for v in self.vspec.values() for lab in v.get("figures", [])}
            fp = visuals_build.fingerprint(self.vspec, self.claim_by_id, self.export,
                                           {lab: self.label_block(lab) for lab in labs})
            visuals_build.check_lock(fp, self.pin_visuals)
            self.vref_meta = visuals_build.check_reference()
            self.vengine = visuals_build.check_engine()
        except visuals_build.VisualError as e:
            raise BuildError(str(e))
        self.vinst = visuals_build.instances(self.vspec, self.claim_by_id)
        self.vprose = {vid: visuals_build.prose(v) for vid, v in self.vspec.items()}

    def build_visuals(self):
        data = visuals_build.reference_data()
        try:
            rendered = visuals_build.render(self.vinst, data)
        except visuals_build.VisualError as e:
            raise BuildError(str(e))
        cases = self.vengine["cases"]
        self.vis_html = {}
        for inst in self.vinst:
            vid, v = inst["vid"], self.vspec[inst["vid"]]
            label, desc = visuals_build.KINDS[v["kind"]]
            intro, notes = self.vprose_html[vid]
            cfg = dict(inst["config"])
            if v["type"] == "compile":
                cfg["data"] = data
            out = rendered[inst["key"]]
            app = "" if v["type"] == "overview" else (
                f'<div class="nv-app" data-type="{esc(v["type"])}" data-config="{esc(json.dumps(cfg, ensure_ascii=False))}">'
                f'<div class="nv-controls" hidden></div><div class="nv-out">{out["app"]}</div></div>')
            lean = ", ".join(self.mk.lean_link(n) for n in v.get("lean", []))
            figs = ", ".join(f'<a class="paper-ref" href="paper.html#{esc(lab)}">{esc(self.mk.label_name(lab))}</a>'
                             for lab in v.get("figures", []))
            n_cases = sum(cases.get(k, 0) for k in visuals_build.TYPES[v["type"]])
            if v["type"] == "overview":
                engine = "Schematic: nothing on this panel is computed; the numbers are the bounds stated in the paper."
            elif v["type"] == "compile":
                engine = (f"The grid is the network Lean itself computes for each formula; your browser only evaluates its "
                          f"gates (agreement with Lean's evaluation was checked for all {n_cases} formulas and every input at build "
                          f"time). The hand-made circuit is a teaching example, not part of the checked construction.")
            else:
                engine = (f"Computed in your browser by a short re-implementation of the definitions above "
                          f"(<code>tools/visuals/nimvis-core.js</code>). It is not itself checked by Lean. At build time it "
                          f"agreed with Lean's own evaluation of those definitions on all {n_cases:,} reference cases.")
                if v["type"] == "restore":
                    engine += (" Lean's evaluation fixes the output wires, the difference δ and the decoded move; the "
                               "intermediate tables (flags, first-flag bits) are re-derived from the same definitions.")
                elif v["type"] == "recurrence":
                    engine += " The comparison compares every register and output after every token."
            self.vis_html.setdefault(inst["claim"], []).append(
                f'<section class="vis vis-{esc(vid)}" id="vis-{esc(vid)}" aria-labelledby="vis-{esc(vid)}-h">'
                f'<h3 class="vis-h" id="vis-{esc(vid)}-h">{esc(v["title"])}</h3>'
                f'<p class="vis-kind-line"><span class="vis-kind vis-kind-{esc(v["kind"])}">{esc(label)}</span> '
                f'<span class="vis-kind-desc">{esc(desc)}</span></p>'
                f'<div class="vis-intro">{intro}</div>{app}{out["extra"]}'
                f'<div class="vis-notes">{notes}<p class="vis-meta">Depicted in Lean: {lean}.'
                + (f" Explains the paper’s {figs}." if figs else "") + f'</p><p class="vis-meta">{engine}</p></div></section>')

    def display_name(self, c):
        labels = self.article["labels"]
        b = c["block"]
        part = f" {c['part']}" if c.get("part") else ""
        a = c["anchor"]
        if a in labels:
            info = labels[a]
            k, n = info["kind"], info["number"]
            if k == "equation":
                return f"Equation ({n})" + part
            if k == "figure":
                return f"Figure {n}" + part
            if k == "table":
                return f"Table {n}" + part
            if k == "section":
                return (f"Appendix {n}" if n[:1].isalpha() and "." not in n else f"Section {n}") + part
            if k == "paragraph":
                return f"Section {n}, “{b.get('runin_title_text', '').rstrip('.')}”" + part
            return f"{latex2html.THEOREM_ENVS.get(k, k.capitalize())} {n}" + part
        if b["kind"] == "stmt":
            return b["display_name"] + part
        if b["kind"] == "abstract":
            return "Abstract" + part
        sec = c["section"]
        if b.get("runin_title_text"):
            return f"{sec}, “{b['runin_title_text'].rstrip('.')}”" + part
        if b["kind"] == "list":
            return f"{sec}, list" + part
        if b["kind"] == "table":
            return f"{sec}, table" + part
        if b["kind"] == "p":
            m = re.search(r"-p(\d+)$", b["id"] or "")
            return f"{sec}, paragraph {m.group(1)}" + part if m else f"{sec}" + part
        return sec + part

    def section_number(self, heading_id):
        """Number of the nearest numbered heading at or above a heading/run-in id."""
        last = None
        for b in self.article["blocks"]:
            if b["kind"] == "heading":
                last = b
            if b.get("id") == heading_id or heading_id in b.get("runin_ids", []):
                break
            if b["kind"] in ("acks", "bibliography", "abstract"):
                if b.get("id") == heading_id:
                    return b["kind"].capitalize()
        if heading_id in ("abstract",):
            return "Abstract"
        if last is None:
            return "front matter"
        n = last["number"]
        return f"Appendix {n}" if last.get("appendix") and "." not in n else f"Section {n}"

    # -- markup --
    def render_explanations(self):
        self.mk = Markup(self.article, self.export, self.mods, self.claim_by_id, self.article["katex_macros"])
        keys = sorted({c["explain_id"] for c in self.claims} | {c["formal_id"] for c in self.claims})
        parts = [self.mk.render(self.expl[k]["text"], k) for k in keys]
        notes = []
        for c in self.claims:
            for fld in ("assumptions", "correspondence"):
                if c.get(fld):
                    notes.append((c["id"], fld))
        note_html = [self.mk.render(self.claim_by_id[cid][fld], f"{cid}.{fld}") for cid, fld in notes]
        author_md = open(os.path.join(ROOT, "content", "authors-perspective.md"), encoding="utf-8").read()
        edition_md = open(os.path.join(ROOT, "content", "edition.md"), encoding="utf-8").read()
        author_html = self.mk.render(author_md, "authors-perspective.md")
        edition_html = self.mk.render(edition_md, "edition.md")
        coverage_md = open(os.path.join(ROOT, "content", "coverage.md"), encoding="utf-8").read()
        coverage_html = self.mk.render(coverage_md, "coverage.md")
        vkeys = sorted(self.vprose)
        vparts = []
        for vid in vkeys:
            vparts += [self.mk.render(self.vprose[vid][0], f"visuals/{vid}.intro"),
                       self.mk.render(self.vprose[vid][1], f"visuals/{vid}.notes")]
        if self.mk.errors:
            raise BuildError("unresolved references in handwritten content:\n  " + "\n  ".join(self.mk.errors))
        done = self.mk.finish(parts + note_html + [author_html, edition_html, coverage_html] + vparts)
        vdone = done[len(done) - len(vparts):] if vparts else []
        done = done[:len(done) - len(vparts)] if vparts else done
        self.vprose_html = {vid: (vdone[2 * k], vdone[2 * k + 1]) for k, vid in enumerate(vkeys)}
        self.expl_html = dict(zip(keys, done[:len(keys)]))
        for (cid, fld), h in zip(notes, done[len(keys):len(keys) + len(notes)]):
            self.claim_by_id[cid][fld + "_html"] = h
        self.author_html, self.edition_html, self.coverage_html = done[-3], done[-2], done[-1]

    # -- claim bar and paper --
    def claim_bar(self, claims):
        rows = []
        for c in claims:
            f = fileid(c["id"])
            lv = []
            for key, label in LEVELS:
                if key == "lean" and not c.get("lean"):
                    continue
                lv.append(f'<a class="lvl" data-level="{key}" data-claim="{esc(c["id"])}" '
                          f'href="claims/{f}.html#{key}">{esc(label)}</a>')
            part = f'<span class="claim-part">{esc(c["part"])}</span>' if c.get("part") else ""
            label, description = CATEGORIES[c["category"]]
            note = (f'<details class="claim-note"><summary class="cat cat-{c["category"]}">'
                    f'{esc(label)}</summary><div class="claim-note-body">'
                    f'<p class="claim-short">{esc(c["short"])}</p>'
                    f'<p class="claim-category-description">{esc(description)}</p></div></details>')
            rows.append(f'<div class="claim-row" data-claim="{esc(c["id"])}">{part}{note}'
                        f'<span class="lvls">{" ".join(lv)}</span></div>')
        return '<div class="claim-bar" role="group" aria-label="Coverage and explanations">' + "".join(rows) + "</div>"

    def build_paper(self):
        a = self.article
        by_block = {}
        for c in self.claims:
            by_block.setdefault(c["block_id"], []).append(c)
        front = a["front"]
        out = [f'<header class="paper-front"><h1 id="paper-title">{front["title_html"]}</h1>'
               f'<div class="authors"><p class="author-name">{front["author_name_html"]}</p>'
               f'<p class="author-email">{esc(front["email"])}</p>'
               f'<p class="author-addr">{"<br>".join(front["address"])}</p></div></header>']
        toc = []
        self.article_ids = set()
        for b in a["blocks"]:
            self.article_ids |= set(re.findall(r'\sid="([^"]+)"', b["html"]))
        for b in a["blocks"]:
            if b["kind"] == "title":
                continue
            cl = by_block.get(b["id"], [])
            # every claim id is a direct anchor: website anchors for unlabelled claims and for the
            # parts of split statements (the manuscript label stays on the statement itself)
            pre = "".join(f'<span class="claim-anchor" id="{esc(c["id"])}"></span>'
                          for c in cl if c["id"] != b["id"] and c["id"] not in self.article_ids)
            out.append(pre + b["html"])
            if cl:
                out.append(self.claim_bar(cl))
            if b["kind"] == "heading" and b["level"] <= 2:
                toc.append((b["level"], b["id"], b["number"], b["title"]))
            elif b["kind"] in ("abstract", "acks", "bibliography"):
                toc.append((1, b["id"], "", {"abstract": "Abstract", "acks": "Acknowledgments",
                                             "bibliography": "References"}[b["kind"]]))
        toc_html = ['<nav class="toc" aria-label="Contents"><details open><summary>Contents</summary><ol>']
        for lvl, ident, num, title in toc:
            shown = (f"Appendix {num}" if (num[:1].isalpha() and "." not in num) else num)
            # A heading can contain a cross-reference. Keep its visible number, but
            # do not nest that reference's anchor inside the TOC entry's anchor.
            toc_title = re.sub(r'</?a\b[^>]*>', '', title)
            toc_html.append(f'<li class="t{lvl}"><a href="#{esc(ident)}"><span class="tn">{esc(shown)}</span> '
                            f"{toc_title}</a></li>")
        toc_html.append("</ol></details></nav>")
        guide = ('<p class="reading-guide">Beneath statements, small controls open three further levels: '
                 '<em>Explain this</em>, <em>How this is formalised</em> and <em>Lean statement and source</em>. '
                 'They never change the paper text. Every level has its own link.</p>')
        extras = ('<nav class="reading-extras" aria-label="About the author and paper">'
                  '<a class="history-button" href="author.html">Personal history behind this paper</a></nav>')
        body = (f'<div class="paper-layout">{"".join(toc_html)}<main id="main" class="paper-main">{guide}{extras}'
                f'<article class="paper" aria-labelledby="paper-title">{"".join(out)}</article></main></div>')
        self.write("paper.html", page(front["title_text"] + " (interactive edition)", body, self.cfg,
                                      "page-paper", "paper.html", current="paper.html", head_extra=VIS_SCRIPTS))

    # -- Lean level --
    def decl_card(self, name, principal=True):
        e = self.export[name]
        m = self.mods[e["module"]]
        short = name.replace("NimAudit.", "")
        ax = ""
        if e["kind"] == "theorem" and name in self.fresh["axioms"]:
            axs = self.fresh["axioms"][name]["axioms"]
            ax = (f'<span class="axioms">Axioms reported by the fresh build: '
                  f'{esc(", ".join(axs)) if axs else "none"}</span>')
        doc = f'<p class="decl-doc">{esc(e["doc"].strip())}</p>' if e.get("doc") else ""

        def deps(lst):
            items = []
            for d in lst:
                if d == name or d not in self.export:
                    continue
                dd = self.export[d]
                items.append(f'<a href="source/{dd["module"]}.html#L{dd["line"]}"><code>'
                             f'{esc(d.replace("NimAudit.", ""))}</code></a>')
            return ", ".join(items) if items else "none"
        code = lean_code(m["lines"], e["line"], e["endLine"], mod=e["module"])
        open_attr = " open" if (e["endLine"] - e["line"]) <= 40 else ""
        return f"""<article class="decl{'' if principal else ' decl-aux'}">
<h4 class="decl-h"><span class="decl-kind">{esc(e["kind"])}</span> <code>{esc(short)}</code></h4>
<p class="decl-meta">Module <a href="source/{e["module"]}.html#L{e["line"]}">{esc(e["module"])}</a>
(<code>lean/{esc(m["rel"])}</code>, lines {e["line"]}–{e["endLine"]}) · file SHA-256 <code class="hash">{m["sha256"][:16]}…</code> {ax}</p>
{doc}
<div class="decl-type"><p class="lbl">Statement as elaborated and printed by Lean {esc(self.cfg["lean"]["version"])}</p>
<pre class="lean-type"><code>{esc(e["type"])}</code></pre></div>
<details class="decl-src"{open_attr}><summary>Exact source text, lines {e["line"]}–{e["endLine"]}</summary>{code}</details>
<p class="decl-deps"><span class="lbl">Project declarations in the statement:</span> {deps(e["typeDeps"])}</p>
<details class="decl-pdeps"><summary>Project declarations used by the proof or definition body</summary><p>{deps(e["valueDeps"])}</p></details>
</article>"""

    def lean_level(self, c):
        if not c.get("lean"):
            reason = c.get("no_lean_reason") or {
                "classical-external": "This is a published classical result. It is cited, not proved in this Lean development.",
                "empirical": "This is an empirical statement about saved experimental runs. Lean proofs do not certify training runs, curves or checkpoints.",
                "informal": "This is interpretation or motivation, not a formal mathematical claim.",
                "open": "This item is explicitly open or deferred.",
            }.get(c["category"], "No Lean declaration corresponds to this claim.")
            return f'<p class="no-lean">No Lean statement corresponds to this claim. {esc(reason)}</p>' + self.build_evidence()
        cards = [self.decl_card(n) for n in c["lean"]]
        defs = []
        seen = set(c["lean"])
        wanted = list(c.get("lean_defs", []))
        for n in c["lean"]:
            for d in self.export[n]["typeDeps"]:
                if d in self.export and self.export[d]["kind"] in ("def", "inductive") and d not in wanted:
                    wanted.append(d)
        for d in wanted:
            if d in seen:
                continue
            seen.add(d)
            defs.append(self.decl_card(d, principal=False))
        mods = sorted({self.export[n]["module"] for n in list(c["lean"]) + wanted})
        mod_rows = []
        for mname in mods:
            m = self.mods[mname]
            imps = ", ".join(f'<a href="source/{i}.html">{esc(i)}</a>' if i in self.mods else f"<code>{esc(i)}</code>"
                             for i in m["imports"]) or "none"
            mod_rows.append(f'<tr><td><a href="source/{mname}.html">{esc(mname)}</a></td><td><code>lean/{esc(m["rel"])}</code></td>'
                            f'<td>{len(m["lines"])}</td><td>{imps}</td></tr>')
        remote = ""  # Full source is bundled; external mirrors are optional.
        return (f'<h3 class="lvl-sub">Principal declarations</h3>{"".join(cards)}'
                + (f'<h3 class="lvl-sub">Definitions these statements use</h3>{"".join(defs)}' if defs else "")
                + '<h3 class="lvl-sub">Full modules</h3><table class="mods"><thead><tr><th>Module</th><th>File</th>'
                  f'<th>Lines</th><th>Imports</th></tr></thead><tbody>{"".join(mod_rows)}</tbody></table>'
                + remote + self.build_evidence())

    def build_evidence(self):
        f = self.fresh
        return (f'<p class="evidence">Build evidence: fresh isolated rebuild of all 38 bundled modules with '
                f'{esc(f["lean_version"].split(",")[0])}, started {esc(f["started_utc"])}, finished '
                f'{esc(f["finished_utc"])}: {f["modules_ok"]}/{f["modules"]} modules compiled, '
                f'{f["axiom_reports"]} axiom reports, no errors. See <a href="build.html">Build</a> for the commands and '
                f'<a href="{esc(self.cfg["lean"]["audit"]["report"])}">the independent audit of '
                f'{esc(self.cfg["lean"]["audit"]["date"])}</a> (dated evidence).</p>')

    def record_table(self, c):
        rows = [("Paper anchor", f'<a href="paper.html#{esc(c["anchor"])}"><code>{esc(c["anchor"])}</code></a>'
                 + (" (manuscript label)" if c["anchor_mode"] == "label" else " (website anchor; the manuscript has no label here)")),
                ("Displayed as", esc(c["display"])),
                ("Claim", esc(c["short"])),
                ("Coverage category", cat_chip(c["category"])),
                ("Statement source", f'paper_jmlr.tex lines {c["source_lines"][0]}–{c["source_lines"][1]}; '
                 f'SHA-256 of the normalised block source <code class="hash">{c["source_sha256"][:16]}…</code>')]
        if c.get("lean"):
            ls = []
            for n in c["lean"]:
                e = self.export[n]
                m = self.mods[e["module"]]
                ls.append(f'<li><a href="source/{e["module"]}.html#L{e["line"]}"><code>{esc(n)}</code></a> '
                          f'({esc(e["module"])}, lines {e["line"]}–{e["endLine"]}, file <code class="hash">{m["sha256"][:12]}…</code>)</li>')
            rows.append(("Lean declarations", "<ul>" + "".join(ls) + "</ul>"))
        if c.get("named_inputs"):
            rows.append(("Named classical inputs", ", ".join(f"<code>{esc(x)}</code>" for x in c["named_inputs"])))
        if c.get("assumptions_html"):
            rows.append(("Assumptions and domain", c["assumptions_html"]))
        if c.get("correspondence_html"):
            rows.append(("Prose-to-formal notes", c["correspondence_html"]))
        if c.get("depends_on"):
            rows.append(("Depends on", ", ".join(
                f'<a href="claims/{fileid(d)}.html">{esc(self.claim_by_id[d]["display"])}</a>' for d in c["depends_on"] if d in self.claim_by_id)))
        if c.get("audit_rows"):
            rows.append(("Audited correspondence rows", ", ".join(f"<code>{esc(r)}</code>" for r in c["audit_rows"])))
        rows.append(("Explanations", f'<code>{esc(c["explain_id"])}</code>, <code>{esc(c["formal_id"])}</code>'))
        rows.append(("Build evidence", '<a href="build.html">fresh isolated rebuild</a>, '
                     f'<a href="{esc(self.cfg["lean"]["audit"]["report"])}">audit report</a>'))
        return ('<table class="record"><caption>Coverage record</caption><tbody>'
                + "".join(f'<tr><th scope="row">{k}</th><td>{v}</td></tr>' for k, v in rows) + "</tbody></table>")

    def build_claim_pages(self):
        for c in self.claims:
            b = c["block"]
            excerpt = rewrite_fragment_links(strip_ids(b["html"], "x-"))
            ex = self.expl_html[c["explain_id"]] + "".join(self.vis_html.get(c["id"], []))
            fo = self.expl_html[c["formal_id"]]
            levels = []
            levels.append(f'<section class="level" id="explain" aria-labelledby="h-explain"><h2 id="h-explain">'
                          f'<span class="lvl-n">2</span> Explain this</h2><div class="lvl-body">{ex}</div></section>')
            levels.append(f'<section class="level" id="formal" aria-labelledby="h-formal"><h2 id="h-formal">'
                          f'<span class="lvl-n">3</span> How this is formalised</h2><div class="lvl-body">{fo}'
                          f'{self.record_table(c)}</div></section>')
            levels.append(f'<section class="level" id="lean" aria-labelledby="h-lean"><h2 id="h-lean">'
                          f'<span class="lvl-n">4</span> Lean statement and source</h2><div class="lvl-body">'
                          f'{self.lean_level(c)}</div></section>')
            body = f"""<main id="main" class="claim-page">
<nav class="crumbs" aria-label="Breadcrumb"><a href="paper.html#{esc(c["anchor"])}">Back to {esc(c["display"])} in the paper</a>
· <a href="coverage.html#c-{fileid(c["id"])}">Coverage table</a></nav>
<h1 data-title="{esc(c["display"])}: {esc(c["short"])}">{esc(c["display"])}<span class="claim-h-short">{esc(c["short"])}</span></h1>
<p class="cat-line">{cat_chip(c["category"])} <span class="cat-desc">{esc(CATEGORIES[c["category"]][1])}</span></p>
<section class="level" id="paper" aria-labelledby="h-paper"><h2 id="h-paper"><span class="lvl-n">1</span> Paper text</h2>
<div class="paper-excerpt">{excerpt}</div>
<p class="src-note">Generated from <code>paper_jmlr.tex</code>, lines {c["source_lines"][0]}–{c["source_lines"][1]}.</p></section>
{"".join(levels)}
</main>"""
            rel = f"claims/{fileid(c['id'])}.html"
            self.write(rel, page(f"{c['display']}: {c['short']}", body, self.cfg, "page-claim", rel,
                                 head_extra=VIS_SCRIPTS if c["id"] in self.vis_html else ""))

    # -- coverage --
    def build_coverage(self):
        counts = {k: 0 for k in CATEGORIES}
        for c in self.claims:
            counts[c["category"]] += 1
        ext = self.cfg["lean"]["audited_extent"]
        ax_counts = {}
        for v in self.fresh["axioms"].values():
            key = ", ".join(v["axioms"]) or "none"
            ax_counts[key] = ax_counts.get(key, 0) + 1
        ax_rows = "".join(f"<tr><td>{esc(k)}</td><td>{n}</td></tr>"
                          for k, n in sorted(ax_counts.items(), key=lambda x: -x[1]))
        cat_rows = "".join(f'<tr><td>{cat_chip(k)}</td><td>{esc(CATEGORIES[k][1])}</td><td class="num">{counts[k]}</td></tr>'
                           for k in CATEGORIES)
        n_lean = sum(1 for c in self.claims if c.get("lean"))
        n_decl = len({n for c in self.claims for n in c.get("lean", [])})
        groups, cur = [], None
        for c in sorted(self.claims, key=lambda c: (self.block_index(c["block_id"]), c.get("order", 0))):
            if c["section"] != cur:
                cur = c["section"]
                groups.append((cur, []))
            groups[-1][1].append(c)
        trs = []
        for sec, cl in groups:
            trs.append(f'<tr class="grp"><th colspan="4" scope="colgroup">{esc(sec)}</th></tr>')
            for c in cl:
                nl = len(c.get("lean", []))
                trs.append(f'<tr id="c-{fileid(c["id"])}"><td><a href="paper.html#{esc(c["anchor"])}">{esc(c["display"])}</a></td>'
                           f'<td>{esc(c["short"])}</td><td>{cat_chip(c["category"])}</td>'
                           f'<td><a href="claims/{fileid(c["id"])}.html">record</a>'
                           f'{f" · {nl} Lean declaration" + ("s" if nl != 1 else "") if nl else ""}</td></tr>')
        cov_md = self.coverage_html
        body = f"""<main id="main" class="coverage-page">
<h1>Proof coverage</h1>
{cov_md}
<h2 id="categories">Coverage categories</h2>
<p>Every mathematical, empirical or interpretive claim inventoried in the paper has one record and exactly one
category. Statements that mix kinds are split into parts. Counts are of claim records, not of Lean declarations.</p>
<table class="cats"><thead><tr><th>Category</th><th>Meaning</th><th>Claims</th></tr></thead><tbody>{cat_rows}
<tr class="total"><td colspan="2">All claim records</td><td class="num">{len(self.claims)}</td></tr></tbody></table>
<p>{n_lean} records cite at least one Lean declaration; together they cite {n_decl} distinct declarations as
principal statements.</p>
<h2 id="axioms">Lean's axiom basis</h2>
<p>Every theorem in the development was checked by the Lean kernel in the fresh rebuild, and the build printed the
axioms each theorem depends on. Only Lean's three standard axioms occur (propositional extensionality, the axiom
of choice and quotient soundness). No <code>sorry</code>, custom axiom or unchecked code was found by the audit.
These axioms are the ordinary foundation of Lean and Mathlib; they are different from the named mathematical
hypotheses described above, which appear as explicit premises of the conditional theorems.</p>
<table class="axioms-t"><thead><tr><th>Axioms used</th><th>Theorems</th></tr></thead><tbody>{ax_rows}</tbody></table>
<h2 id="extent">Extent of the Lean development</h2>
<p>Scope first: the counts below measure the whole local development, including helper lemmas, adapters and
auxiliary definitions. They do not mean {ext["theorems"]:,} independent paper results, and they exclude Lean,
Std, Mathlib, logs and audit copies.</p>
<table class="extent"><tbody>
<tr><th scope="row">Local Lean modules</th><td>{ext["modules"]}</td></tr>
<tr><th scope="row">Theorem and lemma declarations (audit count, helper lemmas included)</th><td>{ext["theorems"]:,}</td></tr>
<tr><th scope="row">Definition declarations (audit count)</th><td>{ext["defs"]}</td></tr>
<tr><th scope="row">Source lines / nonblank lines</th><td>{ext["source_lines"]:,} / {ext["nonblank_lines"]:,}</td></tr>
<tr><th scope="row">Code lines (comments, strings and <code>#print axioms</code> removed)</th><td>{ext["code_lines"]:,}</td></tr>
<tr><th scope="row">Toolchain</th><td>Lean {esc(self.cfg["lean"]["version"])}; Mathlib {esc(self.cfg["lean"]["mathlib_version"])}
(<code>{esc(self.cfg["lean"]["mathlib_commit"])}</code>), used only by RealNoise and RealFourier</td></tr>
</tbody></table>
<p class="small">The site's own declaration export lists {sum(1 for e in self.export.values() if e["kind"] == "theorem")}
theorem constants: the {ext["theorems"]:,} written theorem and lemma declarations plus
{sum(1 for e in self.export.values() if e["kind"] == "theorem") - ext["theorems"]} proof fields that Lean generates for
structures with propositional fields. The audit convention counts only the written declarations.</p>
<h2 id="table">All claim records</h2>
<table class="claims-t"><thead><tr><th>Where</th><th>Claim</th><th>Category</th><th>Record</th></tr></thead>
<tbody>{"".join(trs)}</tbody></table>
</main>"""
        self.write("coverage.html", page("Proof coverage (interactive edition)", body, self.cfg, "page-coverage",
                                         "coverage.html", current="coverage.html"))

    def block_index(self, bid):
        if not hasattr(self, "_bidx"):
            self._bidx = {b["id"]: i for i, b in enumerate(self.article["blocks"]) if b.get("id")}
        return self._bidx.get(bid, 10 ** 6)

    # -- source browser --
    @staticmethod
    def highlight(lines):
        out, in_block = [], False
        kw = re.compile(r"\b(theorem|lemma|def|abbrev|structure|inductive|instance|class|namespace|end|section|"
                        r"open|import|variable|where|deriving|private|noncomputable|attribute|set_option)\b")
        for line in lines:
            s, res, i = line, [], 0
            while i < len(s):
                if in_block:
                    j = s.find("-/", i)
                    if j < 0:
                        res.append(f'<span class="cm">{esc(s[i:])}</span>')
                        i = len(s)
                    else:
                        res.append(f'<span class="cm">{esc(s[i:j + 2])}</span>')
                        i = j + 2
                        in_block = False
                    continue
                j1 = s.find("/-", i)
                j2 = s.find("--", i)
                cands = [j for j in (j1, j2) if j >= 0]
                if not cands:
                    res.append(kw.sub(r'<span class="kw">\1</span>', esc(s[i:])))
                    break
                j = min(cands)
                res.append(kw.sub(r'<span class="kw">\1</span>', esc(s[i:j])))
                if j == j2 and (j1 < 0 or j2 < j1):
                    res.append(f'<span class="cm">{esc(s[j:])}</span>')
                    break
                in_block = True
                i = j
            out.append("".join(res))
        return out

    def build_sources(self):
        claims_by_mod = {}
        for c in self.claims:
            for n in c.get("lean", []):
                claims_by_mod.setdefault(self.export[n]["module"], set()).add(c["id"])
        decls_by_mod = {}
        for e in self.export.values():
            if e["kind"] in ("theorem", "def", "inductive") and not e["name"].endswith((".rec", ".recOn", ".casesOn")):
                decls_by_mod.setdefault(e["module"], []).append(e)
        order = ["phase1", "phase2", "phase3", "phase4", "phase5", "phase6", "phase7", "phase8"]
        rows = {}
        for mname, m in self.mods.items():
            rows.setdefault(m["phase"], []).append(mname)
        idx = []
        for ph in order:
            if ph not in rows:
                continue
            idx.append(f'<h2>{esc("Phase 1 (lean/)" if ph == "phase1" else f"Phase {ph[5:]} (lean/{ph}/)")}</h2><table class="srcs"><thead><tr>'
                       '<th>Module</th><th>Lines</th><th>Theorems</th><th>Summary (from the file header)</th></tr></thead><tbody>')
            for mname in sorted(rows[ph], key=lambda x: self.mod_order(x)):
                m = self.mods[mname]
                nth = sum(1 for d in self.decl_index if d["module"] == mname)
                summ = esc(" ".join(m["header"].split())[:240]) + ("…" if len(m["header"]) > 240 else "")
                idx.append(f'<tr><td><a href="source/{mname}.html">{esc(mname)}</a></td><td class="num">{len(m["lines"])}</td>'
                           f'<td class="num">{nth}</td><td class="small">{summ}</td></tr>')
            idx.append("</tbody></table>")
        remote = ""  # The bundled raw files are sufficient for source access.
        body = (f'<main id="main" class="sources-page"><h1>Lean sources</h1><p>All {len(self.mods)} project-local '
                'modules, exactly as audited (each file’s SHA-256 is checked against the audit’s declaration index '
                'when the site is built). Raw files, with their phase directories, build scripts and pinned Lake '
                f'metadata, are in <a href="lean/">lean/</a>. {remote} See <a href="build.html">Build</a> for the '
                'reproducible build.</p>' + "".join(idx) + "</main>")
        self.write("source/index.html", page("Lean sources (interactive edition)", body, self.cfg, "page-sources",
                                             "source/index.html", current="source/index.html"))
        claim_pos = {c["id"]: i for i, c in enumerate(self.claims)}
        for mname, m in self.mods.items():
            hl = self.highlight(m["lines"])
            code = "".join(f'<span class="cl" id="L{k}"><a class="ln" href="source/{mname}.html#L{k}">{k}</a>'
                             f'<span class="lc">{t}</span></span>' for k, t in enumerate(hl, 1))
            ds = sorted(decls_by_mod.get(mname, []), key=lambda e: e["line"])
            dl = "".join(f'<li><a href="source/{mname}.html#L{e["line"]}"><span class="decl-kind">{esc(e["kind"])}</span> '
                         f'<code>{esc(e["name"].replace("NimAudit.", ""))}</code></a></li>' for e in ds)
            cl = "".join(f'<li><a href="claims/{fileid(cid)}.html">{esc(self.claim_by_id[cid]["display"])}</a>: '
                         f'{esc(self.claim_by_id[cid]["short"])}</li>' for cid in sorted(claims_by_mod.get(mname, []),
                                                                                       key=lambda x: (self.block_index(self.claim_by_id[x]["block_id"]),
                                                                                                      claim_pos[x])))
            imps = ", ".join(f'<a href="source/{i}.html">{esc(i)}</a>' if i in self.mods else f"<code>{esc(i)}</code>"
                             for i in m["imports"]) or "none"
            body = f"""<main id="main" class="module-page">
<nav class="crumbs" aria-label="Breadcrumb"><a href="source/index.html">Lean sources</a> · <a href="lean/{esc(m["rel"])}">raw file</a></nav>
<h1>{esc(mname)}</h1>
<table class="modmeta"><tbody>
<tr><th scope="row">File</th><td><code>lean/{esc(m["rel"])}</code></td></tr>
<tr><th scope="row">SHA-256 (matches the audit)</th><td><code class="hash">{m["sha256"]}</code></td></tr>
<tr><th scope="row">Lines</th><td>{len(m["lines"])}</td></tr>
<tr><th scope="row">Imports</th><td>{imps}</td></tr>
</tbody></table>
{f'<details class="mod-claims" open><summary>Paper claims citing this module</summary><ul>{cl}</ul></details>' if cl else ''}
<details class="mod-decls"><summary>Declarations ({len(ds)})</summary><ul class="decl-list">{dl}</ul></details>
<p class="small">Comment and keyword shading is a reading aid only. It is not a verification marker; the evidence is
the build record on the <a href="build.html">Build</a> page.</p>
<pre class="lean full"><code>{code}</code></pre>
</main>"""
            self.write(f"source/{mname}.html", page(f"{mname}.lean (Lean source)", body, self.cfg, "page-module",
                                                    f"source/{mname}.html"))

    @staticmethod
    def mod_order(m):
        seq = ["NimCore", "NimRollout", "NimGame", "NimProbability", "NimAttain", "Circuit", "NimRecurrent",
               "BitBridge", "NimCorrBridge", "AttainCircuit", "FiniteNet", "BinaryReadout", "ParityCircuit",
               "Controller", "ControllerBits", "SharedCircuit", "SelectCircuit", "LocalRestore", "Foundation",
               "Coverage", "PriorityEncoder", "ThresholdNet", "ThresholdInst", "WholeGame", "Family", "Barrier",
               "RolloutExec", "Bypass", "Classical", "BoardStore", "Windows", "Misc", "NoiseModel", "Shootout",
               "WeakMastery", "Fourier", "RealNoise", "RealFourier"]
        return seq.index(m) if m in seq else 99

    # -- build provenance --
    def build_build_page(self):
        f = self.fresh
        rows = "".join(f'<tr><td><a href="source/{m}.html">{esc(m)}</a></td><td>{"compiled" if m not in f["failed"] else "FAILED"}</td>'
                       f'<td class="num">{sum(1 for v in f["axioms"].values() if v["module"] == m)}</td>'
                       f'<td class="num">{f["warnings_per_module"].get(m, 0)}</td>'
                       f'<td><a href="evidence/fresh-build/logs/{m}.log">log</a></td></tr>'
                       for m in sorted(self.mods, key=self.mod_order))
        lc = self.cfg["lean"]
        body = f"""<main id="main" class="build-page">
<h1>Reproducible Lean build</h1>
<p>The Lean development is checked by compiling its 38 modules. A successful compilation means that the Lean kernel
accepted every proof of every formal statement. It does not by itself show that a formal statement matches the
English sentence it is linked to; that correspondence is reviewed in each claim record.</p>
<h2>Pinned toolchain</h2>
<ul><li>Lean {esc(lc["version"])} (<code>leanprover/lean4:v4.26.0</code>, commit <code>d8204c9fd894f91bbb2cdfec5912ec8196fd8562</code>)</li>
<li>Mathlib {esc(lc["mathlib_version"])}, commit <code>{esc(lc["mathlib_commit"])}</code>, pinned in
<a href="lean/phase8/lakefile.toml"><code>lean/phase8/lakefile.toml</code></a> and
<a href="lean/phase8/lake-manifest.json"><code>lake-manifest.json</code></a>. Only RealNoise and RealFourier import Mathlib;
the other 36 modules use Lean core and Std only.</li></ul>
<h2>Commands</h2>
<p>From the root of this edition's source folder (the folder that contains <code>lean/</code> and <code>tools/</code>):</p>
<pre class="cmd"><code># 1. Pinned Mathlib, needed only for RealNoise and RealFourier (downloads into lean/phase8/.lake)
cd lean/phase8
lake exe cache get        # optional: official build cache, where the network allows it
lake build Mathlib.Data.Real.Archimedean Mathlib.Data.Fintype.BigOperators Mathlib.Algebra.BigOperators.Fin \\
  Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity \\
  Mathlib.Tactic.FieldSimp Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.GCongr
cd ../..

# 2. Compile all 38 modules into a NEW directory (the script refuses to reuse one)
sh tools/lean/build_bundle.sh work/lean_build_$(date +%Y%m%d_%H%M%S) lean/phase8

# 3. Summarise the run: exit codes, warnings and every #print axioms report
python3 tools/lean/parse_build.py work/lean_build_&lt;stamp&gt; work/lean_build_&lt;stamp&gt;.json

# 4. (site maintainers) export declaration types and dependencies for the website
LEAN_PATH="$(cd lean/phase8 &amp;&amp; lake env printenv LEAN_PATH):$PWD/work/lean_build_&lt;stamp&gt;/olean" \\
  lean tools/lean/ExportDecls.lean      # writes data/lean_export.json</code></pre>
<p>The per-phase scripts <code>lean/phase*/build.sh</code> from the original deliveries are included unchanged;
they write build products inside the source tree, so the bundle script above is preferred.</p>
<h2>Fresh build recorded for this edition</h2>
<p>Run in a new, isolated output directory (<code>{esc(f["build_dir_name"])}</code>), {esc(f["lean_version"])}.
Started {esc(f["started_utc"])}, finished {esc(f["finished_utc"])}. Result: {f["modules_ok"]} of {f["modules"]}
modules compiled; {f["axiom_reports"]} axiom reports, one for each audited theorem, using only
{esc("; ".join(f["axiom_sets"]))}; {f["warning_total"]} linter warnings (unused simp arguments and variables), no errors,
no <code>sorry</code>. Machine-readable summary: <a href="evidence/fresh-build/summary.json">summary.json</a>.</p>
<table class="build-t"><thead><tr><th>Module</th><th>Status</th><th>Axiom reports</th><th>Warnings</th><th>Log</th></tr></thead>
<tbody>{rows}</tbody></table>
<h2>Independent audit (dated evidence)</h2>
<p>The development was independently audited on {esc(lc["audit"]["date"])}: "{esc(lc["audit"]["title"])}". The audit
report, its declaration index and its correspondence map are reproduced unchanged in
<a href="evidence/audit/">evidence/audit/</a>. They are dated evidence from that audit, not results of this site build.</p>
<h2>Rebuilding the website</h2>
<pre class="cmd"><code>cd tools &amp;&amp; npm ci &amp;&amp; cd ..     # KaTeX 0.16.11 (pinned in tools/package.json)
python3 tools/build_site.py         # regenerates dist/ from the manuscript, content and data
python3 tools/validate_site.py      # fidelity, link, anchor and browser checks
python3 tools/serve.py              # local preview</code></pre>
</main>"""
        self.write("build.html", page("Reproducible build (interactive edition)", body, self.cfg, "page-build",
                                      "build.html", current="build.html"))

    def build_edition_page(self):
        rows = []
        for vid, v in self.vspec.items():
            claims = [i["claim"] for i in self.vinst if i["vid"] == vid]
            links = ", ".join(f'<a href="claims/{fileid(cid)}.html#vis-{esc(vid)}">{esc(self.claim_by_id[cid]["display"])}</a>'
                              for cid in claims)
            rows.append(f'<li><strong>{esc(v["title"])}</strong> <span class="vis-kind vis-kind-{esc(v["kind"])}">'
                        f'{esc(visuals_build.KINDS[v["kind"]][0])}</span><br>Shown with: {links}</li>')
        illus = (f'<h2 id="illustrations">Illustrations</h2><p>These illustrations appear in the “Explain this” level of the '
                 f'claims listed, before the formalisation level. Each is marked as an exact construction trace, a schematic, '
                 f'or an exact trace beside a teaching example.</p><ul class="vis-index">{"".join(rows)}</ul>')
        body = f'<main id="main" class="edition-page"><h1>About this edition</h1>{self.edition_html}{illus}</main>'
        self.write("edition.html", page("About this edition", body, self.cfg, "page-edition", "edition.html",
                                        current="edition.html"))

    def build_author_page(self):
        front = self.article["front"]
        body = f"""<main id="main" class="author-page">
<aside class="author-note" aria-labelledby="author-h">
<h1 id="author-h">Author’s perspective</h1>
{self.author_html}
<p class="author-back"><a href="index.html">Back to the edition</a> · <a href="paper.html">Read the paper</a></p>
</aside>
</main>"""
        self.write("author.html", page("Author’s perspective (separate from the paper)", body, self.cfg,
                                       "page-author", "author.html"))

    def build_index(self):
        front = self.article["front"]
        body = f"""<main id="main" class="landing">
<h1 class="landing-title">{front["title_html"]}</h1>
<p class="landing-author">{front["author_name_html"]}</p>
<p class="landing-affil">{"<br>".join(front["address"][:2])}</p>
<nav class="landing-links" aria-label="Start">
<a class="primary" href="paper.html">Read the paper</a>
<a href="paper/paper_jmlr.pdf" download>Download the identical PDF</a>
<a href="coverage.html">Proof coverage</a>
</nav>
<p class="landing-note">The paper text with optional explanations, formalisation notes and the full Lean sources.
The PDF is byte-identical to the reading copy (SHA-256 <code class="hash">{self.cfg["inputs"]["pdf"]["sha256"][:16]}…</code>).</p>
<p class="landing-aside"><a class="discreet" href="author.html">Author’s perspective</a></p>
</main>"""
        self.write("index.html", page(front["title_text"], body, self.cfg, "page-landing", "index.html"))

    # -- copies --
    def copy_assets(self):
        self.copy(os.path.join(ROOT, self.cfg["inputs"]["pdf"]["path"]), "paper/paper_jmlr.pdf",
                  "input/paper_jmlr.pdf (identical bytes)")
        kd = os.path.join(ROOT, "tools", "node_modules", "katex", "dist")
        self.copy(os.path.join(kd, "katex.min.css"), "assets/katex/katex.min.css", "KaTeX 0.16.11 (MIT licence)")
        self.copy(os.path.join(ROOT, "tools", "node_modules", "katex", "LICENSE"), "assets/katex/LICENSE",
                  "KaTeX licence")
        for f in os.listdir(os.path.join(kd, "fonts")):
            if f.endswith(".woff2"):
                self.copy(os.path.join(kd, "fonts", f), f"assets/katex/fonts/{f}", "KaTeX font (MIT licence)")
        for f in ("site.css", "site.js"):
            self.copy(os.path.join(ROOT, "tools", "site_assets", f), f"assets/{f}", "edition presentation code")
        for f in visuals_build.ASSETS:
            self.copy(os.path.join(ROOT, "tools", "visuals", f), f"assets/visuals/{f}",
                      "illustration code (re-implementation checked against Lean evaluations)")
        self.copy(visuals_build.REF, "evidence/visual_reference_lean.jsonl",
                  "Lean's evaluation of the depicted definitions on small inputs (tools/lean/VisualRef.lean)")
        self.copy(visuals_build.REF_META, "evidence/visual_reference_lean.meta.json", "provenance of the reference values")
        lean_dir = os.path.join(ROOT, "lean")
        listing = []
        for dirpath, _, files in os.walk(lean_dir):
            for f in sorted(files):
                rel = os.path.relpath(os.path.join(dirpath, f), lean_dir)
                self.copy(os.path.join(dirpath, f), f"lean/{rel}", "bundled Lean source (audited copy)")
                listing.append(rel)
        rows = "".join(f'<li><a href="lean/{esc(r)}">{esc(r)}</a></li>' for r in sorted(listing))
        self.write("lean/index.html", page("Raw Lean files", f'<main id="main" class="sources-page"><h1>Raw Lean files</h1><ul>{rows}</ul></main>',
                                           self.cfg, "page-raw", "lean/index.html"))
        # The audit folder beside this one (../phase8_audit_2026-10-10) is the authority; the copy
        # in evidence_inputs/ lets the folder rebuild on its own.  When both exist they must agree.
        audit_files = ("AUDIT_REPORT.txt", "declaration_index.json", "paper_proof_correspondence.json",
                       "reproduction_results.json", "input_manifest.json", "audit_results.json")
        audit_sibling = os.path.normpath(os.path.join(ROOT, "..", "phase8_audit_2026-10-10"))
        audit_local = os.path.join(ROOT, "evidence_inputs", "phase8_audit_2026-10-10")
        if os.path.isdir(audit_sibling):
            for f in audit_files:
                if os.path.exists(os.path.join(audit_local, f)) and \
                        sha256_file(os.path.join(audit_sibling, f)) != sha256_file(os.path.join(audit_local, f)):
                    raise BuildError(f"evidence_inputs/phase8_audit_2026-10-10/{f} differs from "
                                     f"../phase8_audit_2026-10-10/{f}")
        src_audit = audit_sibling if os.path.isdir(audit_sibling) else audit_local
        for f in audit_files:
            self.copy(os.path.join(src_audit, f), f"evidence/audit/{f}", "phase-8 audit (dated evidence, unchanged)")
        rows = "".join(f'<li><a href="evidence/audit/{f}">{f}</a></li>' for f in
                       ("AUDIT_REPORT.txt", "declaration_index.json", "paper_proof_correspondence.json",
                        "reproduction_results.json", "input_manifest.json", "audit_results.json"))
        self.write("evidence/audit/index.html", page("Audit evidence", f'<main id="main"><h1>Independent audit, '
                   f'{esc(self.cfg["lean"]["audit"]["date"])} (dated evidence)</h1><p>Unchanged copies.</p><ul>{rows}</ul></main>',
                   self.cfg, "page-raw", "evidence/audit/index.html"))
        # Record of the fresh rebuild (logs and results; the .olean files are not kept).
        fb = os.path.join(ROOT, "evidence_inputs", "fresh-build-" + self.fresh["build_dir_name"].rsplit("_", 1)[-1])
        if not os.path.isdir(fb):
            fb = os.path.join(ROOT, "work", self.fresh["build_dir_name"])
        self.copy(os.path.join(ROOT, self.cfg["inputs"]["fresh_build"]), "evidence/fresh-build/summary.json",
                  "parse_build.py summary of the fresh rebuild")
        for f in ("results.txt", "started_utc.txt", "finished_utc.txt", "lean_version.txt"):
            self.copy(os.path.join(fb, f), f"evidence/fresh-build/{f}", "fresh rebuild record")
        for f in os.listdir(os.path.join(fb, "logs")):
            self.copy(os.path.join(fb, "logs", f), f"evidence/fresh-build/logs/{f}", "fresh rebuild log")

    # -- machine-readable records --
    def write_claims_json(self):
        recs = []
        for c in self.claims:
            lean = []
            for n in c.get("lean", []):
                e = self.export[n]
                m = self.mods[e["module"]]
                lean.append({"name": n, "kind": e["kind"], "module": e["module"], "file": f"lean/{m['rel']}",
                             "file_sha256": m["sha256"], "lines": [e["line"], e["endLine"]],
                             "statement": e["type"],
                             "axioms": self.fresh["axioms"].get(n, {}).get("axioms") if e["kind"] == "theorem" else None,
                             "statement_deps": e["typeDeps"], "proof_deps": e["valueDeps"]})
            recs.append({
                "id": c["id"], "anchor": c["anchor"], "anchor_kind": c["anchor_mode"],
                "label": c["anchor"] if c["anchor_mode"] == "label" else None,
                "displayed": c["display"], "part": c.get("part"), "section": c["section"],
                "short_claim": c["short"], "category": c["category"],
                "category_label": CATEGORIES[c["category"]][0],
                "source_file": "input/jmlr_source/paper_jmlr.tex", "source_lines": c["source_lines"],
                "source_sha256": c["source_sha256"], "manuscript_sha256": self.article["source_sha256"],
                "canonical_manuscript_sha256": self.cfg["inputs"]["canonical_tex"]["sha256"],
                "explanation_ids": [c["explain_id"], c["formal_id"]],
                "lean": lean, "lean_definitions": c.get("lean_defs", []),
                "named_classical_inputs": c.get("named_inputs", []),
                "assumptions_and_domain": c.get("assumptions"), "correspondence_notes": c.get("correspondence"),
                "depends_on": c.get("depends_on", []), "audit_rows": c.get("audit_rows", []),
                "illustrations": [i["vid"] for i in self.vinst if i["claim"] == c["id"]],
                "build_evidence": {"fresh_build": "evidence/fresh-build/summary.json",
                                   "fresh_build_started_utc": self.fresh["started_utc"],
                                   "audit_report": self.cfg["lean"]["audit"]["report"],
                                   "audit_date": self.cfg["lean"]["audit"]["date"]},
                "page": f"claims/{fileid(c['id'])}.html"})
        doc = {"generated_from": {"jmlr_tex_sha256": self.article["source_sha256"],
                                  "canonical_tex_sha256": self.cfg["inputs"]["canonical_tex"]["sha256"],
                                  "pdf_sha256": self.cfg["inputs"]["pdf"]["sha256"]},
               "categories": {k: v[0] for k, v in CATEGORIES.items()}, "claims": recs}
        js = json.dumps(doc, ensure_ascii=False, indent=1)
        open(os.path.join(ROOT, "data", "claims.json"), "w", encoding="utf-8").write(js)
        self.write("data/claims.json", js, "machine-readable claim map")
        self.write("data/article_labels.json", json.dumps(self.article["labels"], ensure_ascii=False, indent=1),
                   "label table from the converter")
        # Flat, human-readable claim map (one row per claim record) for review in a spreadsheet.
        cols = ["id", "displayed", "section", "category", "paper_anchor", "short_claim", "lean_declarations",
                "named_classical_inputs", "explanation_ids", "audit_rows", "source_lines", "source_sha256"]

        def cell(v):
            return str(v).replace("\t", " ").replace("\n", " ")
        rows = ["\t".join(cols)]
        for r in recs:
            rows.append("\t".join(cell(x) for x in (
                r["id"], r["displayed"] or "", r["section"] or "", r["category"], "paper.html#" + r["anchor"],
                r["short_claim"], " ".join(d["name"] for d in r["lean"]),
                " ".join(r["named_classical_inputs"] or []), " ".join(r["explanation_ids"]),
                " ".join(str(a) for a in r["audit_rows"]), "-".join(str(x) for x in r["source_lines"] or []),
                r["source_sha256"])))
        tsv = "\n".join(rows) + "\n"
        open(os.path.join(ROOT, "data", "claim_map.tsv"), "w", encoding="utf-8").write(tsv)
        self.write("data/claim_map.tsv", tsv, "claim map as a table (tab-separated)")

    def write_manifest(self):
        items = []
        for rel in sorted(self.files):
            p = os.path.join(DIST, rel)
            items.append({"path": rel, "bytes": os.path.getsize(p), "sha256": sha256_file(p), "origin": self.files[rel]})
        man = {"edition": self.cfg["build_label"], "inputs": {k: self.cfg["inputs"][k]["sha256"]
                                                             for k in ("jmlr_tex", "canonical_tex", "pdf")},
               "build_inputs": check_sync.build_inputs(ROOT), "files": items}
        with open(os.path.join(DIST, "MANIFEST.json"), "w") as f:
            json.dump(man, f, indent=1)

    def run_check(self):
        """Every staleness check of a build, without writing the site (used by tools/check_sync.py)."""
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            self.convert(gen=tmp)
        self.load_lean()
        self.load_claims()
        self.load_visuals()
        print(f"check passed: {len(self.claims)} claim records and {len(self.vspec)} illustrations match their reviewed "
              f"locks; the illustration engine agrees with all Lean reference cases")

    def run(self):
        if os.path.isdir(DIST):
            shutil.rmtree(DIST)
        os.makedirs(DIST)
        self.convert()
        self.load_lean()
        self.load_claims()
        self.load_visuals()
        self.render_explanations()
        self.build_visuals()
        self.copy_assets()
        self.build_paper()
        self.build_claim_pages()
        self.build_coverage()
        self.build_sources()
        self.build_build_page()
        self.build_edition_page()
        self.build_author_page()
        self.build_index()
        self.write_claims_json()
        self.write(".nojekyll", "", "GitHub Pages: serve files as they are")
        self.write_manifest()
        counts = {}
        for c in self.claims:
            counts[c["category"]] = counts.get(c["category"], 0) + 1
        print(f"built dist/: {len(self.files)} files, {len(self.claims)} claim records {counts}")


def main():
    pin = "--pin" in sys.argv
    try:
        site = Site(pin=pin, allow_incomplete="--allow-incomplete" in sys.argv,
                    pin_visuals="--pin-visuals" in sys.argv)
        if "--check" in sys.argv:
            site.run_check()
        else:
            site.run()
    except (BuildError, latex2html.ConvError) as e:
        print("BUILD FAILED:", e, file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
