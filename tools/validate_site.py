#!/usr/bin/env python3
"""Validation of the built edition (dist/).

    python3 tools/validate_site.py [--no-browser]

Checks (each recorded in validation/validation_report.json; the summary is printed):
  A. inputs and PDF identity;
  B. fidelity: all source labels and their numbers (.aux), headings, statement headers, equation,
     figure and table numbers against the PDF text; captions; bibliography order; formula
     inventory (every source formula rendered, annotation equal to the source TeX);
     normalised word-sequence comparison of the article with (i) an independent
     source-derived text and (ii) pdftotext of the supplied PDF, with every difference
     classified;
  C. links and assets in every HTML file (relative targets and fragment ids);
  D. claim records: anchors, pages, Lean declarations against sources, hashes and lines;
  E. nested deployment: the whole site crawled over HTTP under a non-root prefix;
  F. browser checks (Playwright/Chromium): console errors, keyboard disclosure and focus
     return, direct level links, back/forward and scroll preservation, each bypass and a
     conditional probability result end-to-end to its source module, print media, no-JS
     degradation, author's-note isolation, desktop and mobile screenshots.
Exit status 1 if any check fails.
"""
import difflib
import hashlib
import html as htmlmod
import json
import os
import re
import socket
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import validate_visuals  # noqa: E402

from bs4 import BeautifulSoup

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIST = os.path.join(ROOT, "dist")
OUT = os.path.join(ROOT, "validation")
sys.path.insert(0, os.path.join(ROOT, "tools"))

RESULTS = []


def check(name, ok, detail=None, data=None):
    RESULTS.append({"check": name, "ok": bool(ok), "detail": detail, "data": data})
    mark = "PASS" if ok else "FAIL"
    print(f"[{mark}] {name}" + (f": {detail}" if detail else ""))
    return ok


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def words(t):
    t = fold(t.replace("\u00a0", " "))
    return [w.lower() for w in re.findall(r"[A-Za-z0-9]+", t)]


# ---------------------------------------------------------------------------------------
# A. inputs
# ---------------------------------------------------------------------------------------

def check_inputs(cfg):
    for k in ("jmlr_tex", "canonical_tex", "pdf"):
        e = cfg["inputs"][k]
        check(f"input hash {e['path']}", sha(os.path.join(ROOT, e["path"])) == e["sha256"])
    check("dist PDF is byte-identical to the input PDF",
          sha(os.path.join(DIST, "paper", "paper_jmlr.pdf")) == cfg["inputs"]["pdf"]["sha256"])


# ---------------------------------------------------------------------------------------
# B. fidelity
# ---------------------------------------------------------------------------------------

def pdf_text():
    p = subprocess.run(["pdftotext", "-layout", os.path.join(ROOT, "input", "paper_jmlr.pdf"), "-"],
                       capture_output=True, text=True)
    return p.stdout


def pdf_text_raw():
    p = subprocess.run(["pdftotext", os.path.join(ROOT, "input", "paper_jmlr.pdf"), "-"],
                       capture_output=True, text=True)
    return p.stdout


def fold(t):
    import unicodedata
    # pdfTeX may extract an accented i as dotless-i plus a combining accent.
    t = unicodedata.normalize("NFKD", t.replace("\u2019", "'").replace("\u00f8", "o").replace("\u00d8", "O").replace("\u0131", "i"))
    return "".join(ch for ch in t if not unicodedata.combining(ch))


def squash(t):
    return re.sub(r"[^a-z0-9]", "", fold(t).lower())


def article_soup():
    return BeautifulSoup(open(os.path.join(DIST, "paper.html"), encoding="utf-8").read(), "html.parser")


def check_labels(art):
    aux = {}
    # Label numbers from a pdflatex compile of input/jmlr_source (tools/reference_compile.sh).
    aux_path = os.path.join(ROOT, "work", "texbuild", "paper_jmlr.aux")
    if not os.path.exists(aux_path):
        aux_path = os.path.join(ROOT, "evidence_inputs", "reference_compile", "paper_jmlr.aux")
    for line in open(aux_path, encoding="utf-8"):
        m = re.match(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}\{(\d+)\}", line)
        if m:
            aux[m.group(1)] = m.group(2)
    soup = article_soup()
    ids = {t["id"] for t in soup.find_all(attrs={"id": True})}
    bad_num = [(k, v, art["labels"].get(k, {}).get("number")) for k, v in aux.items()
               if art["labels"].get(k, {}).get("number") != v]
    missing_ids = [k for k in aux if art["labels"].get(k, {}).get("id") not in ids]
    tex = open(os.path.join(ROOT, "input", "jmlr_source", "paper_jmlr.tex"), encoding="utf-8").read()
    source_labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
    check("all source LaTeX labels present with the .aux numbers", set(aux) == source_labels and not bad_num,
          f"{len(aux)} labels in .aux; {len(source_labels)} in source; {len(bad_num)} number mismatches", bad_num)
    check("every label is a direct anchor in paper.html", not missing_ids, f"{len(missing_ids)} missing", missing_ids)
    toc_entries = soup.select("nav.toc li")
    expected_targets = ["#" + b["id"] for b in art["blocks"]
                        if (b["kind"] == "heading" and b["level"] <= 2)
                        or b["kind"] in ("abstract", "acks", "bibliography")]
    toc_targets = [li.find("a").get("href") if li.find("a") else None for li in toc_entries]
    bad_toc = [li.get_text(" ", strip=True) for li in toc_entries if len(li.find_all("a")) != 1]
    check("each contents entry has one link to its own section", not bad_toc and toc_targets == expected_targets,
          f"{len(toc_entries)} entries; {len(bad_toc)} split or missing links", bad_toc)
    return aux


def check_numbers_against_pdf(art, ptxt):
    sq = squash(ptxt)
    problems = []
    n = 0
    for b in art["blocks"]:
        if b["kind"] == "heading":
            n += 1
            num = b["number"]
            prefix = f"Appendix {num}." if b.get("appendix") and b["level"] == 1 else num
            if squash(prefix + b["title_text"])[:60] not in sq:
                problems.append(("heading", num, b["title_text"]))
        elif b["kind"] == "stmt":
            n += 1
            head = b["display_name"] + (f" ({b['title_text']})" if b.get("title_text") else "")
            if squash(head)[:60] not in sq:
                problems.append(("statement", head))
        elif b["kind"] in ("figure", "table") and b.get("display_name"):
            n += 1
            cap = f"{b['display_name']}: {b['caption_text']}"
            if squash(cap)[:50] not in sq:
                problems.append((b["kind"], cap[:80]))
    for lab, info in art["labels"].items():
        if info["kind"] == "equation":
            n += 1
            if f"({info['number']})" not in ptxt:
                problems.append(("equation", info["number"]))
    for u in art["unlabelled_numbered"]:
        n += 1
        word = {"remark": "Remark", "example": "Example"}[u["kind"]]
        if f"{word} {u['number']}" not in ptxt:
            problems.append(("unlabelled", u))
    check("headings, statement headers, captions and equation numbers match the PDF text", not problems,
          f"{n} numbered items compared; {len(problems)} mismatches", problems)


def check_bibliography(art, ptxt):
    entries = art["bibliography"]
    ref_part = ptxt[ptxt.rfind("References"):]
    sq = squash(ref_part)
    pos, order_ok, missing = -1, True, []
    for e in entries:
        key = squash(e["text"])[:40]
        p = sq.find(key)
        if p < 0:
            missing.append(e["key"])
        elif p < pos:
            order_ok = False
        pos = max(pos, p)
    tex = open(os.path.join(ROOT, "input", "jmlr_source", "paper_jmlr.tex"), encoding="utf-8").read()
    source_keys = re.findall(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}", tex)
    check("bibliography: all source entries found in the PDF reference list, same order",
          [e["key"] for e in entries] == source_keys and not missing and order_ok,
          f"{len(entries)} entries; missing {missing}")
    # citations as typeset
    soup = article_soup()
    cits = [re.sub(r"\s+", " ", c.get_text()) for c in soup.select(".citation")]
    flat = squash(ptxt)
    bad = [c for c in cits if squash(c) not in flat]
    check("every rendered citation string occurs in the PDF text", not bad, f"{len(cits)} citations", bad)


def check_math(art):
    soup = article_soup()
    anns = [a.get_text() for a in soup.select("article.paper annotation[encoding='application/x-tex']")]
    src = [m["tex"] for m in art["math"]]

    def norm(t):
        t = re.sub(r"\\begin\{aligned\}|\\end\{aligned\}", "", t)
        return re.sub(r"\s+", "", t)
    src_n = sorted(norm(t) for t in src)
    ann_n = sorted(norm(t) for t in anns)
    check("formula inventory: every source formula rendered once with its exact TeX",
          src_n == ann_n, f"{len(src)} source formulas, {len(anns)} rendered annotations")
    errs = soup.select(".katex-error")
    check("no KaTeX rendering errors in the article", not errs, f"{len(errs)} errors")


def source_text_words(texfile):
    """An independent, deliberately simple LaTeX-to-words pass (not the converter)."""
    import latex2html
    raw = open(texfile, encoding="utf-8").read()
    s, _ = latex2html.strip_comments(raw)
    s = s[s.index("\\begin{document}") + 16: s.index("\\end{document}")]
    s = re.sub(r"\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}", " ", s, flags=re.S)
    s = re.sub(r"\\begin\{(equation|align\*)\}.*?\\end\{\1\}", " ", s, flags=re.S)
    s = re.sub(r"\\\[.*?\\\]", " ", s, flags=re.S)
    s = re.sub(r"(?<!\\)\$.*?(?<!\\)\$", " ", s, flags=re.S)
    s = re.sub(r"\\href\{[^}]*\}\{([^}]*)\}", r" \1 ", s)
    s = re.sub(r"\\url\{([^}]*)\}", r" \1 ", s)
    s = re.sub(r"\\(ref|citep|label|includegraphics|bibitem)(\[[^\]]*\])?\{[^}]*\}", " ", s)
    s = re.sub(r"\\begin\{(tabular|tabularx)\}(\{[^}]*\})?\{([^{}]|\{[^{}]*\}|\{[^{}]*\{[^{}]*\}[^{}]*\})*\}", " ", s)
    s = re.sub(r"\\begin\{(itemize|enumerate|figure|table|thebibliography|minipage)\}(\[[^\]]*\])?(\{[^}]*\})?", " ", s)
    s = re.sub(r"\\begin\{proof\}\[[^\]]*\]", " ", s)  # optional proof titles become .proof-head (removed in HTML)
    s = re.sub(r"\\(begin|end)\{[^}]*\}", " ", s)
    s = re.sub(r"\\begin\{proof\}\[[^\]]*\]", " ", s)  # optional proof titles become .proof-head (removed in HTML)
    s = re.sub(r"\\item\[[^\]]*\]", " ", s)  # explicit item labels become .item-label (removed in HTML)
    s = re.sub(r"\\texorpdfstring\{([^{}]*)\}\{[^{}]*\}", r"\1", s)
    s = s.replace("{\\o}", "ø").replace("{\\aa}", "å").replace("{\\'o}", "ó").replace('{\\"o}', "ö").replace("{\\'e}", "é")
    s = s.replace(r"\v{s}", "š").replace(r"\v{C}", "Č").replace(r"\v{z}", "ž").replace(r"{\'i}", "í").replace(r"{\'a}", "á")
    s = re.sub(r"\\[A-Za-z]+\*?", " ", s)
    s = s.replace("\\%", "%").replace("\\_", "_").replace("\\&", "&")
    s = re.sub(r"\\.", " ", s)
    s = re.sub(r"\[(h!|t|leftmargin=[^\]]*)\]", " ", s)
    return words(s)


def html_article_words(soup, mode="source"):
    """Words of the article.  mode='source': remove everything LaTeX generates automatically
    (numbers, labels, fixed headings, references, citations); mode='pdf': keep all visible
    article text except formulas and the edition's own controls."""
    art = soup.select_one("article.paper")
    art = BeautifulSoup(str(art), "html.parser")
    common = [".katex", ".claim-bar", ".claim-anchor", ".qed", "img"]
    auto = [".secnum", ".stmt-label", ".eq-num", ".cap-label", ".item-label", ".proof-head", "h2.abstract-h",
            ".keywords > strong:first-child", ".acks h2", ".references h2", ".paper-front", "a.ref", "span.citation"]
    for sel in common + (auto if mode == "source" else []):
        for t in art.select(sel):
            t.decompose()
    return words(art.get_text(" "))


def classify_diff(a, b, math_tokens):
    """Compare word lists a (reference) and b (HTML).  Returns unexplained opcodes."""
    sm = difflib.SequenceMatcher(a=a, b=b, autojunk=False)
    unexplained, explained = [], {"hyphenation": 0, "math": 0, "headers": 0}
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal":
            continue
        A, Bw = a[i1:i2], b[j1:j2]
        if "".join(A) == "".join(Bw):
            explained["hyphenation"] += 1
            continue
        if op == "delete" and all(w in math_tokens or w.isdigit() for w in A):
            explained["math"] += 1
            continue
        unexplained.append({"op": op, "reference": " ".join(A)[:200], "html": " ".join(Bw)[:200],
                            "context": " ".join(a[max(0, i1 - 6):i1])})
    return unexplained, explained, sm.ratio()


def check_text(art, ptxt_raw):
    soup = article_soup()
    hw = html_article_words(soup)
    sw = source_text_words(os.path.join(ROOT, "input", "jmlr_source", "paper_jmlr.tex"))
    un, ex, ratio = classify_diff(sw, hw, set())
    check("article text equals the independent source-derived text (normalised words)", not un,
          f"{len(hw)} HTML words, {len(sw)} source words, similarity {ratio:.5f}, {len(un)} unexplained differences",
          un[:40])
    # PDF comparison
    t = ptxt_raw
    t = re.sub(r"-\n", "-", t)
    t = t.replace("\f", "\n")
    # drop running heads and page numbers
    lines = [l for l in t.split("\n") if l.strip() not in ("Learning Bottlenecks in Impartial Games", "Riis")
             and not re.fullmatch(r"\s*\d+\s*", l)]
    t = "\n".join(lines)
    # Split literal prose suffixes attached to one-letter inline mathematics only
    # when that adjacency is present in the source (e.g. $j$th -> j th). Do this
    # before global word cancellation, which otherwise pairs unrelated "th" tokens.
    src = open(os.path.join(ROOT, "input", "jmlr_source", "paper_jmlr.tex")).read()
    for symbol, suffix in set(re.findall(r"\$([A-Za-z])\$([a-z]+)", src)):
        t = re.sub(r"\b" + re.escape(symbol + suffix) + r"\b", symbol + " " + suffix, t)
    # Verified pdfTeX extraction artefact in Lemma B.1: a displaced summation
    # glyph is read as P and glued to "at". Preserve the surrounding prose.
    t = re.sub(r"\batP\s+(?=most one)", "at P ", t)
    pw = words(t)
    hw = html_article_words(soup, "pdf")
    math_tokens = set()
    for m in art["math"]:
        tex = m["tex"]
        for k, v in art["macros"].items():
            tex = tex.replace(k, " " + v + " ")
        tex = re.sub(r"\\(mathrm|mathsf|mathbf|mathcal|mathbb|text|operatorname|mathtt|textsc)\b", " ", tex)
        tex = re.sub(r"\\(log|bmod|Pr|max|min|exp|det)\b", lambda m: " " + m.group(1).replace("bmod", "mod") + " ", tex)
        tex = re.sub(r"\\[A-Za-z]+", " ", tex)
        math_tokens |= set(words(tex))
        math_tokens |= {w for w in words(tex) for _ in [0]}
    # tikz node text appears in the PDF but is an image (with alt text) on the web page
    tikz_words = set()
    for name in os.listdir(os.path.join(ROOT, "generated", "tikz")):
        tikz_words |= set(words(re.sub(r"\\[A-Za-z]+", " ", open(os.path.join(ROOT, "generated", "tikz", name)).read())))
    def atom(w):
        return w in math_tokens or w.isdigit() or len(w) == 1

    def mathlike(w):
        if atom(w):
            return True
        m = re.fullmatch(r"([a-z]+)(\d+)", w) or re.fullmatch(r"(\d+)([a-z]+)", w)
        return bool(m) and all(atom(g) for g in m.groups())
    import yaml
    from collections import Counter
    fig_words = set(tikz_words)
    for v in yaml.safe_load(open(os.path.join(ROOT, "content", "figures.yaml"))).values():
        fig_words |= set(words(v["alt"]))

    def mathsplit(w):
        if mathlike(w):
            return True
        return any(atom(w[:k]) and mathlike(w[k:]) for k in range(1, len(w)))
    sm = difflib.SequenceMatcher(a=pw, b=hw, autojunk=False)
    counts = {"hyphenation": 0, "math": 0, "math_adjacency": 0, "figure_text": 0, "reordered_words": 0}
    res_pdf, res_html = Counter(), Counter()
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal":
            continue
        A, Bw = list(pw[i1:i2]), list(hw[j1:j2])
        if A and Bw and "".join(A).replace("-", "") == "".join(Bw):
            counts["hyphenation"] += 1
            continue
        # first within this difference: a formula glued to a word in the PDF ("jth", "atp") versus the
        # bare word on the web page ("th", "at")
        for w in list(Bw):
            for p_ in A:
                if p_ != w and ((p_.endswith(w) and mathlike(p_[:-len(w)])) or (p_.startswith(w) and mathlike(p_[len(w):]))):
                    A.remove(p_)
                    Bw.remove(w)
                    counts["math_adjacency"] += 1
                    break
        res_pdf.update(A)
        res_html.update(Bw)
    common = res_pdf & res_html
    counts["reordered_words"] = sum(common.values())
    only_pdf = res_pdf - common
    only_html = res_html - common
    # a formula glued to a word in the PDF ("jth") versus the bare word on the web page ("th")
    for w in list(only_html.elements()):
        for p_ in list(only_pdf):
            if only_pdf[p_] > 0 and p_ != w and ((p_.endswith(w) and mathlike(p_[:-len(w)])) or
                                                (p_.startswith(w) and mathlike(p_[len(w):]))):
                only_pdf[p_] -= 1
                only_html[w] -= 1
                counts["math_adjacency"] += 1
                break
    only_pdf, only_html = +only_pdf, +only_html
    mathw = Counter({w: n for w, n in only_pdf.items() if mathsplit(w)})
    counts["math"] = sum(mathw.values())
    only_pdf = only_pdf - mathw
    figure_text = Counter({w: n for w, n in only_pdf.items() if w in fig_words})
    counts["figure_text"] = sum(figure_text.values())
    only_pdf = only_pdf - figure_text
    unexplained = {"pdf_only_words": sorted(only_pdf.elements()), "html_only_words": sorted(only_html.elements())}
    n_un = len(unexplained["pdf_only_words"]) + len(unexplained["html_only_words"])
    check("article text against pdftotext of the supplied PDF: every difference classified", n_un == 0,
          f"similarity {sm.ratio():.4f}; classified {counts} (reordered words: float and table placement); "
          f"{n_un} unexplained words", unexplained)
    return unexplained


def check_front(art, ptxt):
    f = art["front"]
    sq = squash(ptxt[:3000])
    ok = squash(f["title_text"]) in sq and squash(f["author_name_text"]) in sq and \
        all(squash(a) in sq for a in f["address"])
    check("title, author and affiliation match the PDF", ok)
    soup = BeautifulSoup(open(os.path.join(DIST, "index.html"), encoding="utf-8").read(), "html.parser")
    links = {a.get_text(strip=True): a.get("href") for a in soup.select("main a")}
    want = {"Read the paper": "paper.html", "Download the identical PDF": "paper/paper_jmlr.pdf",
            "Proof coverage": "coverage.html", "Author’s perspective": "author.html"}
    check("landing page: exact title and author, the three main links and the discreet Author’s perspective link",
          all(links.get(k) == v for k, v in want.items()) and squash(f["title_text"]) in squash(soup.get_text()),
          str(links))


def check_author_isolation():
    note = re.sub(r"\s+", " ", open(os.path.join(ROOT, "content", "authors-perspective.md"), encoding="utf-8").read())
    probes = ["The starting point for this paper goes back to my thesis work",
              "logic, on feasible reasoning in bounded arithmetic", "When AlphaZero appeared",
              "the reception was mixed", "My subsequent work with Bei Zhou",
              "I think of restricted reasoning of this kind"]
    leaks = []
    for dirpath, _, files in os.walk(DIST):
        for f in files:
            if not f.endswith(".html") or f == "author.html":
                continue
            txt = re.sub(r"\s+", " ", open(os.path.join(dirpath, f), encoding="utf-8").read())
            for p in probes:
                if p in txt:
                    leaks.append((os.path.relpath(os.path.join(dirpath, f), DIST), p))
    check("author's note text appears only on author.html", not leaks and all(p in note for p in probes),
          str({"leaks": leaks, "missing_probes": [p for p in probes if p not in note]}))
    paper = open(os.path.join(DIST, "paper.html"), encoding="utf-8").read()
    soup = BeautifulSoup(paper, "html.parser")
    history_link = soup.select_one('.reading-extras a[href="author.html"]')
    check("paper offers a separate history link outside the manuscript text",
          history_link is not None and history_link.find_parent("article") is None
          and not soup.select_one('article.paper a[href="author.html"]'))


# ---------------------------------------------------------------------------------------
# C. links and assets
# ---------------------------------------------------------------------------------------

def check_links():
    pages = {}
    for dirpath, _, files in os.walk(DIST):
        for f in files:
            if f.endswith(".html"):
                rel = os.path.relpath(os.path.join(dirpath, f), DIST)
                pages[rel] = BeautifulSoup(open(os.path.join(dirpath, f), encoding="utf-8").read(), "html.parser")
    ids = {rel: {t["id"] for t in s.find_all(attrs={"id": True})} for rel, s in pages.items()}
    broken, external, n = [], set(), 0
    for rel, s in pages.items():
        base_tag = s.find("base")
        base = os.path.dirname(rel)
        if base_tag is not None:
            base = os.path.normpath(os.path.join(base, base_tag["href"]))
            base = "" if base == "." else base
        root_relative = []
        for tag, attr in (("a", "href"), ("link", "href"), ("script", "src"), ("img", "src")):
            for t in s.find_all(tag):
                u = t.get(attr)
                if not u:
                    continue
                n += 1
                if re.match(r"^[a-z]+:", u):
                    if u.startswith(("http:", "https:")):
                        external.add(u)
                    elif not u.startswith("mailto:"):
                        broken.append((rel, u, "scheme"))
                    continue
                if u.startswith("/"):
                    root_relative.append(u)
                    continue
                path, _, frag = u.partition("#")
                frag = urllib.parse.unquote(frag)
                if path == "":
                    target = rel if base_tag is None else None
                    if target is None:
                        broken.append((rel, u, "fragment-only link under <base>"))
                        continue
                else:
                    target = os.path.normpath(os.path.join(base, urllib.parse.unquote(path)))
                full = os.path.join(DIST, target)
                if os.path.isdir(full):
                    full = os.path.join(full, "index.html")
                    target = os.path.join(target, "index.html")
                if not os.path.exists(full):
                    broken.append((rel, u, "missing file"))
                    continue
                if frag and target.endswith(".html"):
                    if frag not in ids.get(target, set()):
                        lvl = frag.rsplit("~", 1)
                        if not (len(lvl) == 2 and lvl[1] in ("explain", "formal", "lean") and lvl[0] in ids.get(target, set())):
                            broken.append((rel, u, "missing fragment"))
        if root_relative:
            broken.append((rel, root_relative[:3], "root-relative links break under a subpath"))
    check("every internal link and asset resolves (files and fragment ids)", not broken,
          f"{n} references in {len(pages)} pages; {len(broken)} broken; {len(external)} external links (not fetched)",
          {"broken": broken[:50], "external": sorted(external)})
    return pages


# ---------------------------------------------------------------------------------------
# D. claims
# ---------------------------------------------------------------------------------------

def check_claims():
    cl = json.load(open(os.path.join(DIST, "data", "claims.json"), encoding="utf-8"))
    di = json.load(open(os.path.join(ROOT, "data", "declaration_index.json")))
    di_sha = {d["module"]: d["sha256"] for d in di}
    soup = article_soup()
    ids = {t["id"] for t in soup.find_all(attrs={"id": True})}
    problems = []
    counts = {}
    required = ["id", "anchor", "displayed", "short_claim", "source_sha256", "category", "explanation_ids", "lean",
                "assumptions_and_domain", "correspondence_notes", "depends_on", "build_evidence"]
    for c in cl["claims"]:
        counts[c["category"]] = counts.get(c["category"], 0) + 1
        for k in required:
            if k not in c:
                problems.append((c["id"], f"missing field {k}"))
        if c["anchor"] not in ids:
            problems.append((c["id"], "anchor not in paper.html"))
        if not os.path.exists(os.path.join(DIST, c["page"])):
            problems.append((c["id"], "claim page missing"))
        for d in c["lean"]:
            f = os.path.join(ROOT, d["file"])
            if sha(f) != d["file_sha256"] or di_sha.get(d["module"]) != d["file_sha256"]:
                problems.append((c["id"], d["name"], "file hash differs from the audited index"))
            lines = open(f, encoding="utf-8").read().split("\n")
            short = d["name"].split(".")[-1]
            seg = "\n".join(lines[d["lines"][0] - 1:d["lines"][1]])
            if short not in seg:
                problems.append((c["id"], d["name"], "name not found in its source range"))
            if d["kind"] == "theorem" and d["axioms"] is not None and not set(d["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}:
                problems.append((c["id"], d["name"], "non-standard axioms"))
            if not os.path.exists(os.path.join(DIST, "source", d["module"] + ".html")):
                problems.append((c["id"], d["module"], "source page missing"))
    labelled_stmts = [b for b in json.load(open(os.path.join(ROOT, "generated", "article.json")))["blocks"]
                      if b["kind"] == "stmt"]
    covered = {c["anchor"] for c in cl["claims"]}
    uncovered = [b["id"] for b in labelled_stmts if b["id"] not in covered]
    corr = json.load(open(os.path.join(ROOT, "data", "paper_proof_correspondence.json")))
    rows = {r["label"] for r in corr["rows"]}
    mapped = {r for c in cl["claims"] for r in c["audit_rows"]}
    check("claim records: required fields, anchors, pages, Lean names in their source ranges, audited hashes",
          not problems, f"{len(cl['claims'])} records; by category {counts}", problems[:40])
    check("every theorem-like environment has a claim record", not uncovered, f"{len(labelled_stmts)} statements", uncovered)
    check("every audited correspondence row is mapped to a claim record", bool(rows) and rows <= mapped,
          f"{len(rows)} rows; unmapped {sorted(rows - mapped)}")
    return counts


# ---------------------------------------------------------------------------------------
# E. nested deployment
# ---------------------------------------------------------------------------------------

def free_port():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]
    s.close()
    return p


def start_server(prefix):
    port = free_port()
    env = dict(os.environ, SERVE_QUIET="1")
    proc = subprocess.Popen([sys.executable, os.path.join(ROOT, "tools", "serve.py"), "--port", str(port),
                             "--prefix", prefix], env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    for _ in range(50):
        try:
            urllib.request.urlopen(f"http://127.0.0.1:{port}{prefix}index.html", timeout=1)
            break
        except Exception:
            time.sleep(0.1)
    return proc, f"http://127.0.0.1:{port}{prefix}"


def check_nested(base):
    seen, todo, bad = set(), ["index.html"], []
    while todo:
        rel = todo.pop()
        if rel in seen:
            continue
        seen.add(rel)
        url = base + rel
        try:
            r = urllib.request.urlopen(url, timeout=5)
            body = r.read()
        except Exception as e:
            bad.append((rel, str(e)))
            continue
        if not rel.endswith(".html"):
            continue
        s = BeautifulSoup(body.decode("utf-8"), "html.parser")
        b = s.find("base")
        cur = os.path.dirname(rel)
        if b is not None:
            cur = os.path.normpath(os.path.join(cur, b["href"]))
            cur = "" if cur == "." else cur
        for tag, attr in (("a", "href"), ("link", "href"), ("script", "src"), ("img", "src")):
            for t in s.find_all(tag):
                u = t.get(attr)
                if not u or re.match(r"^[a-z]+:", u) or u.startswith("#"):
                    continue
                path = u.split("#")[0]
                if not path:
                    continue
                tgt = os.path.normpath(os.path.join(cur, urllib.parse.unquote(path)))
                if tgt.startswith(".."):
                    bad.append((rel, u, "escapes the prefix"))
                    continue
                if path.endswith("/"):
                    tgt = os.path.join(tgt, "index.html")
                todo.append(tgt)
    check("site crawled over HTTP under the non-root prefix /nim-interactive/: every resource returns 200",
          not bad, f"{len(seen)} resources fetched; {len(bad)} failures", bad[:30])


# ---------------------------------------------------------------------------------------
# F. browser
# ---------------------------------------------------------------------------------------

def browser_checks(base, root_base=None):
    import asyncio
    from playwright.async_api import async_playwright
    shots = os.path.join(OUT, "screenshots")
    os.makedirs(shots, exist_ok=True)

    async def run():
        async with async_playwright() as p:
            b = await p.chromium.launch()
            ctx = await b.new_context(viewport={"width": 1366, "height": 900})
            pg = await ctx.new_page()
            errors = []
            pg.on("pageerror", lambda e: errors.append(str(e)))
            pg.on("console", lambda m: errors.append(m.text) if m.type == "error" else None)

            # console errors on every page type
            for u in ["index.html", "paper.html", "coverage.html", "claims/thm__sim-ac0.html", "source/index.html",
                      "source/Shootout.html", "build.html", "edition.html", "author.html"]:
                await pg.goto(base + u, wait_until="networkidle")
            check("browser: no console or page errors on the main page types", not errors, str(errors[:5]))

            # keyboard: Tab to a claim button, Enter opens, Escape closes and returns focus
            await pg.goto(base + "paper.html", wait_until="networkidle")
            sel = 'button.lvl[data-claim="thm:sim-ac0"][data-level="explain"]'
            await pg.focus(sel)
            await pg.keyboard.press("Enter")
            await pg.wait_for_selector("#panel-thm__sim-ac0 .panel-body p")
            focus_in_panel = await pg.evaluate("document.activeElement.classList.contains('panel-body')")
            expanded = await pg.get_attribute(sel, "aria-expanded")
            h = await pg.evaluate("location.hash")
            await pg.keyboard.press("Escape")
            await pg.wait_for_timeout(200)
            gone = await pg.evaluate("!document.getElementById('panel-thm__sim-ac0')")
            back_focus = await pg.evaluate(
                "document.activeElement.matches('button.lvl[data-claim=\"thm:sim-ac0\"][data-level=\"explain\"]')")
            check("keyboard: Enter opens the panel (aria-expanded, focus moves in, URL ~explain); Escape closes and returns focus",
                  focus_in_panel and expanded == "true" and h == "#thm:sim-ac0~explain" and gone and back_focus,
                  f"focus_in_panel={focus_in_panel} expanded={expanded} hash={h} closed={gone} focus_returned={back_focus}")
            # tab order reaches the claim controls with the keyboard alone
            await pg.goto(base + "paper.html", wait_until="networkidle")
            reached = False
            for _ in range(80):
                await pg.keyboard.press("Tab")
                if await pg.evaluate("document.activeElement && document.activeElement.classList.contains('lvl')"):
                    reached = True
                    break
            check("keyboard: Tab navigation reaches the first claim control", reached)

            # direct links restore panel and anchor
            await pg.goto(base + "paper.html#thm:search-gap.i~lean", wait_until="networkidle")
            await pg.wait_for_selector("#panel-thm__search-gap\\.i .decl")
            txt = await pg.inner_text("#panel-thm__search-gap\\.i")
            top = await pg.evaluate("document.getElementById('thm:search-gap').getBoundingClientRect().top")
            hn = "HastadNegl" in txt and "success_bound" in txt
            check("direct link #thm:search-gap.i~lean restores the Lean panel with the named input and the anchor in view",
                  hn and -50 < top < 900, f"top={top:.0f}")
            await pg.screenshot(path=os.path.join(shots, "desktop_lean_panel.png"))

            # back / forward and scroll preservation
            await pg.goto(base + "paper.html", wait_until="networkidle")
            await pg.evaluate("document.getElementById('prop:restore').scrollIntoView()")
            y0 = await pg.evaluate("window.scrollY")
            await pg.click('button.lvl[data-claim="prop:restore"][data-level="explain"]')
            await pg.wait_for_selector("#panel-prop__restore .panel-body p")
            await pg.click('button.lvl[data-claim="prop:restore"][data-level="formal"]')
            await pg.wait_for_timeout(300)
            st1 = await pg.evaluate("location.hash")
            y1 = await pg.evaluate("window.scrollY")
            await pg.click("#panel-prop__restore .panel-close")
            await pg.wait_for_timeout(200)
            y2 = await pg.evaluate("window.scrollY")
            await pg.go_back()
            await pg.wait_for_timeout(400)
            st2 = await pg.evaluate("location.hash")
            lvl2 = await pg.evaluate("(document.querySelector('#panel-prop__restore .pt-level')||{}).textContent")
            await pg.go_back()
            await pg.wait_for_timeout(400)
            st3 = await pg.evaluate("location.hash")
            lvl3 = await pg.evaluate("(document.querySelector('#panel-prop__restore .pt-level')||{}).textContent")
            await pg.go_back()
            await pg.wait_for_timeout(400)
            st4 = await pg.evaluate("location.hash")
            gone4 = await pg.evaluate("!document.getElementById('panel-prop__restore')")
            await pg.go_forward()
            await pg.wait_for_timeout(400)
            st5 = await pg.evaluate("location.hash")
            ok = (st1 == "#prop:restore~formal" and abs(y2 - y1) < 2 and st2 == "#prop:restore~formal"
                  and "formalised" in (lvl2 or "") and st3 == "#prop:restore~explain" and "Explain" in (lvl3 or "")
                  and gone4 and st5 == "#prop:restore~explain")
            check("back/forward walk through open/level/close states; closing keeps the scroll position", ok,
                  f"hashes {st1},{st2},{st3},{st4},{st5}; scroll before/after close {y1:.0f}/{y2:.0f}")

            # end-to-end paths: statement -> panel -> Lean card -> full module at the declaration line
            paths = [("c-restore-selector", "NimAudit.LocalRestore.restore_equiv", "LocalRestore"),
                     ("prop:rollout-sufficiency", "NimAudit.RolloutExec.mhExec_wins", "RolloutExec"),
                     ("c-replay", "NimAudit.WholeGame.replay_wins", "WholeGame"),
                     ("c-board-storage", "NimAudit.BoardStore.bits_store_wins", "BoardStore"),
                     ("thm:search-gap.i", "NimAudit.Prob.success_bound", "NimProbability")]
            exp = {e["name"]: e for e in json.load(open(os.path.join(ROOT, "data", "lean_export.json")))}
            for cid, decl, mod in paths:
                fid = cid.replace(":", "__")
                await pg.goto(base + f"paper.html#{cid}~lean", wait_until="networkidle")
                await pg.wait_for_selector(f"#panel-{fid.replace('.', chr(92) + '.')} .decl")
                line = exp[decl]["line"]
                link = await pg.query_selector(f"#panel-{fid.replace('.', chr(92) + '.')} a[href='source/{mod}.html#L{line}']")
                ok1 = link is not None
                if ok1:
                    await link.click()
                    await pg.wait_for_load_state("networkidle")
                url = pg.url
                tgt = await pg.evaluate(f"(document.getElementById('L{line}')||{{}}).textContent || ''")
                short = decl.split(".")[-1]
                check(f"end-to-end: {cid} → Lean panel → {mod}.lean line {line}",
                      ok1 and url.endswith(f"source/{mod}.html#L{line}") and (short in tgt or "/--" in tgt),
                      f"landed on {url.split('/')[-1]}")

            # print media: article only
            await pg.goto(base + "paper.html#prop:restore~explain", wait_until="networkidle")
            await pg.wait_for_selector("#panel-prop__restore")
            await pg.emulate_media(media="print")
            hidden = await pg.evaluate("""() => ['.site-bar','.toc','.claim-bar','.claim-panel','.reading-guide','.site-foot']
                 .every(s => [...document.querySelectorAll(s)].every(e => getComputedStyle(e).display === 'none'))""")
            await pg.pdf(path=os.path.join(OUT, "print_preview_paper.pdf"))
            ptxt = subprocess.run(["pdftotext", os.path.join(OUT, "print_preview_paper.pdf"), "-"],
                                  capture_output=True, text=True).stdout
            no_chrome = ("Explain this" not in ptxt and "Review build" not in ptxt and "Author" not in ptxt.split("Acknowledgments")[0][:400])
            check("print output contains the article only (no controls, panels, navigation or author's note)",
                  hidden and no_chrome and "Overcoming a Learning Bottleneck" in ptxt)
            await pg.emulate_media(media="screen")

            # no-JS degradation
            nojs = await b.new_context(java_script_enabled=False, viewport={"width": 1366, "height": 900})
            q = await nojs.new_page()
            await q.goto(base + "paper.html", wait_until="networkidle")
            a = await q.query_selector('a.lvl[data-claim="thm:sim-ac0"][data-level="formal"]')
            ok = a is not None
            if ok:
                await a.click()
                await q.wait_for_load_state("networkidle")
                ok = q.url.endswith("claims/thm__sim-ac0.html#formal") and "How this is formalised" in await q.inner_text("main")
            check("without JavaScript the controls are links to complete claim pages", ok)
            await nojs.close()

            # screenshots
            await pg.goto(base + "index.html", wait_until="networkidle")
            await pg.screenshot(path=os.path.join(shots, "desktop_landing.png"))
            await pg.goto(base + "paper.html", wait_until="networkidle")
            await pg.screenshot(path=os.path.join(shots, "desktop_paper_top.png"))
            await pg.goto(base + "paper.html#thm:singleframe-impossible", wait_until="networkidle")
            await pg.screenshot(path=os.path.join(shots, "desktop_theorem_5_2.png"))
            await pg.goto(base + "coverage.html", wait_until="networkidle")
            await pg.screenshot(path=os.path.join(shots, "desktop_coverage.png"), full_page=False)
            await pg.goto(base + "author.html", wait_until="networkidle")
            await pg.screenshot(path=os.path.join(shots, "desktop_author.png"))
            mob = await b.new_context(viewport={"width": 390, "height": 844}, device_scale_factor=2, is_mobile=True,
                                      has_touch=True)
            m = await mob.new_page()
            await m.goto(base + "paper.html#prop:restore~explain", wait_until="networkidle")
            await m.wait_for_selector("#panel-prop__restore .panel-body p")
            await m.screenshot(path=os.path.join(shots, "mobile_restore_explain.png"))
            overflow = await m.evaluate("document.documentElement.scrollWidth > window.innerWidth + 1")
            check("mobile (390 px): panels open and the page has no horizontal overflow", not overflow)
            await m.goto(base + "index.html", wait_until="networkidle")
            await m.screenshot(path=os.path.join(shots, "mobile_landing.png"))
            bases = ([("root", root_base)] if root_base else []) + [("prefix", base)]
            await validate_visuals.browser_checks(check, b, bases, shots)
            await b.close()
    asyncio.run(run())


def main():
    import yaml
    os.makedirs(OUT, exist_ok=True)
    cfg = yaml.safe_load(open(os.path.join(ROOT, "site.config.yaml")))
    art = json.load(open(os.path.join(ROOT, "generated", "article.json"), encoding="utf-8"))
    ptxt = pdf_text()
    ptxt_raw = pdf_text_raw()
    check_inputs(cfg)
    check_front(art, ptxt)
    check_labels(art)
    check_numbers_against_pdf(art, ptxt_raw)
    check_bibliography(art, ptxt_raw)
    check_math(art)
    check_text(art, ptxt_raw)
    check_author_isolation()
    check_links()
    counts = check_claims()
    validate_visuals.check_computation(check)
    validate_visuals.check_edge_cases(check)
    validate_visuals.check_pages(check)
    if "--no-stale-tests" not in sys.argv:
        validate_visuals.check_staleness(check)
    proc, base = start_server("/nim-interactive/")
    proc2, root_base = start_server("/")
    try:
        check_nested(base)
        if "--no-browser" not in sys.argv:
            browser_checks(base, root_base)
    finally:
        proc.terminate()
        proc2.terminate()
    ok = all(r["ok"] for r in RESULTS)
    rep = {"date_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "all_passed": ok,
           "passed": sum(r["ok"] for r in RESULTS), "total": len(RESULTS), "claim_counts": counts,
           "checks": RESULTS}
    json.dump(rep, open(os.path.join(OUT, "validation_report.json"), "w"), indent=1, ensure_ascii=False)
    write_markdown_report(rep)
    print(f"\n{rep['passed']}/{rep['total']} checks passed")
    sys.exit(0 if ok else 1)


def write_markdown_report(rep):
    """Human-readable companion of validation_report.json (same results, no extra judgement)."""
    import platform
    cfg_inputs = {}
    try:
        import yaml
        cfg = yaml.safe_load(open(os.path.join(ROOT, "site.config.yaml"), encoding="utf-8"))
        cfg_inputs = {v["path"]: v["sha256"] for k, v in cfg["inputs"].items() if isinstance(v, dict)}
    except Exception:
        pass
    lines = ["# Validation report: interactive edition (local review build)", "",
             f"Run: {rep['date_utc']} (UTC) by `python3 tools/validate_site.py`"
             f"{' --no-browser' if '--no-browser' in sys.argv else ''}; Python {platform.python_version()} on "
             f"{platform.system()} {platform.machine()}.", "",
             f"**Result: {rep['passed']} of {rep['total']} checks passed"
             f"{'' if rep['all_passed'] else ' (FAILURES BELOW)'}.**", "",
             "Machine-readable results, including the data behind each check: `validation_report.json`. "
             "Screenshots: `screenshots/`. Print rendering of the article: `print_preview_paper.pdf`.", "",
             "## Inputs checked", ""]
    for path, h in cfg_inputs.items():
        lines.append(f"- `{path}`: sha256 `{h}`")
    lines += ["", "## Checks", "", "| # | Result | Check | Detail |", "|---|---|---|---|"]
    for i, r in enumerate(rep["checks"], 1):
        det = str(r.get("detail") or "").replace("|", "\\|").replace("\n", " ")
        if len(det) > 400:
            det = det[:400] + " …"
        lines.append(f"| {i} | {'PASS' if r['ok'] else '**FAIL**'} | {r['check'].replace('|', '/')} | {det} |")
    lines += ["", "## Claim records by category", ""]
    for k, v in sorted(rep["claim_counts"].items()):
        lines.append(f"- {k}: {v}")
    lines += ["", "## What these checks do not establish", "",
              "- Passing the claim-record checks means each cited Lean declaration exists in the delivered source "
              "at the recorded lines and hash; it does not by itself show that the Lean statement matches the "
              "English sentence. That correspondence is stated, with its limits, in each claim record.",
              "- The text comparisons are of normalised words. Mathematics was compared as a formula inventory "
              "(exact TeX of every formula), and figures and rendered math were inspected visually in the "
              "screenshots; neither is a pixel comparison with the PDF.",
              "- The site build does not re-run Lean. The Lean evidence shown on the site is the recorded fresh "
              "rebuild of 2026-10-10 and the dated independent audit.", ""]
    open(os.path.join(OUT, "VALIDATION_REPORT.md"), "w", encoding="utf-8").write("\n".join(lines))


if __name__ == "__main__":
    main()
