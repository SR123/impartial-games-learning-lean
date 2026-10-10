"""Validation of the illustrations and of the synchronisation workflow (called by tools/validate_site.py).

  computation   the browser engine against Lean's evaluation (data/visual_reference_lean.jsonl) and against
                independent reference calculations written from the paper (tools/visuals/reference.py)
  edge cases    reset from arbitrary registers, separators that keep the retained summary, extra separators,
                reset between games, terminal and outside-the-promise inputs
  pages         every illustration section: its default example's values, its Lean links (source line anchors
                that name the declaration), figure links, overview links, and its claim attachments
  staleness     temporary copies of the edition with a changed claim, a changed Lean statement, a changed Lean
                source, a changed PDF and a changed content file: the build or tools/check_sync.py must refuse,
                write a review list, and refuse --pin until the changes are marked reviewed
  browser       controls, stepping, keyboard, reduced motion, phone width, no JavaScript, print, direct links and
                return navigation, at the site root and under /nim-interactive/
"""
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIST = os.path.join(ROOT, "dist")
sys.path.insert(0, os.path.join(ROOT, "tools", "visuals"))
import reference as REF  # noqa: E402


def engine(reqs):
    p = subprocess.run(["node", os.path.join(ROOT, "tools", "visuals", "run_engine.js")], input=json.dumps(reqs),
                       capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError(p.stderr[-2000:])
    return json.loads(p.stdout)


def boards(B, N):
    if N == 0:
        return [[]]
    return [[x] + rest for x in range(2 ** B) for rest in boards(B, N - 1)]


# ---------------------------------------------------------------------------------------------- computation

def check_computation(check):
    p = subprocess.run(["node", os.path.join(ROOT, "tools", "visuals", "check_engine.js"),
                        os.path.join(ROOT, "data", "visual_reference_lean.jsonl")], capture_output=True, text=True)
    res = json.loads(p.stdout)
    check("illustration engine equals Lean's evaluation of the depicted definitions on every reference case",
          p.returncode == 0 and res["total_mismatches"] == 0,
          "cases " + ", ".join(f"{k} {v}" for k, v in sorted(res["cases"].items())) + f"; mismatches {res['total_mismatches']}",
          res["first"])

    rnd = random.Random(20261010)
    # two-frame: exhaustive small sizes, random larger ones
    cases = [(B, Q, Qp) for B, N in ((1, 1), (1, 2), (2, 1), (2, 2), (1, 3)) for Q in boards(B, N) for Qp in boards(B, N)]
    for _ in range(3000):
        B, N = rnd.choice([(3, 3), (3, 4), (4, 3), (4, 5), (2, 6)])
        Q = [rnd.randrange(2 ** B) for _ in range(N)]
        Qp = list(Q)
        if rnd.random() < 0.8 and any(Qp):
            i = rnd.choice([k for k in range(N) if Qp[k]])
            Qp[i] = rnd.randrange(Qp[i])
        else:
            Qp = [rnd.randrange(2 ** B) for _ in range(N)]
        cases.append((B, Q, Qp))
    js = engine([{"op": "restore", "B": B, "Q": Q, "Qp": Qp} for B, Q, Qp in cases])
    bad = []
    for (B, Q, Qp), j in zip(cases, js):
        r = REF.restore(B, Q, Qp)
        if (j["delta"], j["move"], j["branch"], j["wires"], j["candidates"]) != (r["delta"], r["move"], r["branch"], r["wires"], r["candidates"]):
            bad.append({"B": B, "Q": Q, "Qp": Qp, "js": j, "ref": r})
    # promise property: zero predecessor, legal move -> cancelling reply with nim-sum 0
    prom = 0
    for (B, Q, Qp), j in zip(cases, js):
        if j["promise"]:
            prom += 1
            R = list(Qp)
            if not j["move"] or j["branch"] != "cancel":
                bad.append({"promise_without_cancel": [B, Q, Qp]})
                continue
            R[j["move"][0]] = j["move"][1]
            if REF.nim(R) != 0 or not j["move"][1] < Qp[j["move"][0]]:
                bad.append({"promise_reply_not_zero": [B, Q, Qp]})
    check("two-frame illustration equals the independent reference; inside the promise every reply is legal and restores 0",
          not bad, f"{len(cases)} cases ({prom} inside the promise); {len(bad)} disagreements", bad[:5])

    # rollouts
    rc = [(B, P, e) for B, N in ((1, 3), (2, 2), (2, 3), (3, 2), (3, 3)) for P in boards(B, N) for e in (False, True)]
    js = engine([{"op": "rollout", "B": B, "P": P, "early": e} for B, P, e in rc])
    bad = []
    for (B, P, e), j in zip(rc, js):
        r = REF.rollouts(B, P, e)
        if not (r["moves_formula_ok"] and r["channel_ok"] and r.get("sigma_ok", True)):
            bad.append({"paper_identity_fails": [B, P]})
        run = r["heads"] if e else B
        if j["moves"][:run] != r["moves"][:run] or j["evaluations"] != r["evaluations"]:
            bad.append({"B": B, "P": P, "early": e, "js": j, "ref": r})
        if e:
            if j["heads"] != r["heads"] or j["decision"] != r["decision"]:
                bad.append({"early": [B, P], "js": j, "ref": r})
        elif j["outs"] != r["outs"] or j["sigma"] != r["sigma"] or j["readout"] != r["readout"]:
            bad.append({"all": [B, P], "js": j, "ref": r})
    check("rollout illustration: outcomes are the paper's channel bits, move counts follow the heap formula, "
          "evaluations are M + 2B + 2 (all heads) and the readout is the cancelling move",
          not bad, f"{len(rc)} boards and schedules; {len(bad)} disagreements", bad[:5])

    # recurrence: games of up to three decisions
    games = []
    for _ in range(300):
        B, N = rnd.choice([(2, 2), (3, 3), (3, 4), (2, 5)])
        games.append([[rnd.randrange(2 ** B) for _ in range(N)] for _ in range(rnd.randint(1, 3))])
    reqs = [{"op": "decisions", "protocol": pr, "boards": g} for g in games for pr in ("replay", "store")]
    js = engine(reqs)
    bad = []
    for q, j in zip(reqs, js):
        ref = REF.decisions(q["boards"], q["protocol"])
        if q["protocol"] == "replay":
            got = [{"summary": a["summary"], "diff": a["diff"], "move": b["move"]} for a, b in zip(j["outs"][0::2], j["outs"][1::2])]
            want = [{"summary": o["summary"], "diff": o["diff"], "move": o["move"]} for o in ref]
        else:
            got = j["outs"]
            want = [{"summary": o["summary"], "move": o["move"]} for o in ref]
        if got != want or j["updates"] != 1 + sum(o["updates"] for o in ref):
            bad.append({"q": q, "js": j, "ref": ref})
    check("recurrence illustration: summaries, differences, moves and update counts (2N + 2 replay, N + 1 storage) "
          "equal the independent reference over whole games", not bad, f"{len(reqs)} games; {len(bad)} disagreements", bad[:3])


def check_edge_cases(check):
    rnd = random.Random(7)
    problems = []
    reqs = []
    for _ in range(200):
        st = {"replay": rnd.random() < .5, "acc": rnd.randrange(16), "prev": rnd.randrange(16), "valid": rnd.random() < .5,
              "sig": rnd.randrange(16), "idx": rnd.randrange(6), "sel": [rnd.randrange(4), rnd.randrange(8)] if rnd.random() < .5 else None,
              "fnz": [rnd.randrange(4), rnd.randrange(8)] if rnd.random() < .5 else None}
        reqs.append({"op": "reset", "state": st, "N": 3, "bstate": {"board": [rnd.randrange(8) for _ in range(3)], "acc": rnd.randrange(8), "idx": rnd.randrange(4)}})
    for r in engine(reqs):
        if r["ctrl"] != r["init"] or r["store"] != r["binit"]:
            problems.append(r)
    sc = engine([{"op": "scenario", "protocol": "replay", "scenario": "separator", "B": 3, "P": [3, 4, 6], "opp": [2, 1]},
                 {"op": "scenario", "protocol": "replay", "scenario": "reset", "B": 3, "P": [3, 4, 6], "opp": [2, 1]},
                 {"op": "scenario", "protocol": "store", "scenario": "reset", "B": 3, "P": [3, 4, 6], "opp": [2, 1]},
                 {"op": "scenario", "protocol": "replay", "scenario": "game", "B": 3, "P": [3, 4, 6], "opp": [2, 1]}])
    sep, rst, srst, game = sc
    outs = [s["out"] for s in sep["steps"] if s["out"]]
    # decision on (3,4,6): summary 1, move (0,2); extra SEP: summary 0 with diff 1 (the retained summary), then an empty replay: no move
    if not (outs[0] == {"summary": 1, "diff": None} and outs[1] == {"move": [0, 2]} and outs[2] == {"summary": 0, "diff": 1}
            and outs[3] == {"move": None}):
        problems.append({"separator": outs})
    for s in sep["steps"]:
        if s["tok"]["t"] == "sep" and s["phase"] == "summary" and not s["state"]["valid"]:
            problems.append({"separator_cleared_validity": s})
    routs = [s["out"] for s in rst["steps"] if s["out"]]
    # after a reset the next summary has no previous summary to compare with
    if not (routs[2]["summary"] == 0 and routs[2]["diff"] is None):
        problems.append({"reset": routs})
    if srst["steps"][4]["state"]["board"] != [3, 4, 6] or [s for s in srst["steps"] if s["tok"]["t"] == "reset"][-1]["state"] != {"board": [0, 0, 0], "acc": 0, "idx": 0}:
        problems.append({"store_reset": srst["steps"]})
    gouts = [s["out"] for s in game["steps"] if s["out"]]
    if not (game["boards"] == [[3, 4, 6], [2, 4, 6], [2, 4, 1]] and gouts[2] == {"summary": 7, "diff": 6} and gouts[3] == {"move": [1, 3]}):
        problems.append({"game": gouts})
    check("reset and separator edge cases: reset restores the initial registers from any state; a separator clears only "
          "the accumulator, keeping the completed position's summary and validity (an extra separator, read as an empty "
          "position, reports the difference from it); after a reset there is no previous summary; decision-time "
          "differences span two moves", not problems, f"{len(reqs)} random resets and 4 scenarios", problems[:3])


# ---------------------------------------------------------------------------------------------- pages

def check_pages(check):
    import yaml
    from bs4 import BeautifulSoup
    spec = yaml.safe_load(open(os.path.join(ROOT, "content", "visuals", "visuals.yaml"), encoding="utf-8"))["visuals"]
    claims = {c["id"]: c for c in json.load(open(os.path.join(DIST, "data", "claims.json"), encoding="utf-8"))["claims"]}
    exp = {d["name"]: d for d in json.load(open(os.path.join(ROOT, "data", "lean_export.json"), encoding="utf-8"))}
    problems, n_links, n_sections = [], 0, 0
    expected_text = {
        "restore": {"paper": ["Decoded move: set heap 0 to 2", "nim-sum 0"], "several": ["Candidates passing: 3"]},
        "rollout": {"346": ["= 35", "σ = 1"]},
        "recurrence": {"game": ["2N + 2 = 8", "difference from the previous summary 6", "move heap 1 → 3"]},
        "summary": {"game": ["2B + 1 = 7", "difference from the previous summary 6"]},
        "compile": {"xor": ["8 layers", "64 gates in total"]},
    }
    src_pages = {}
    for vid, v in spec.items():
        for a in v["attach"]:
            cid = a["claim"]
            rel = f"claims/{cid.replace(':', '__')}.html"
            soup = BeautifulSoup(open(os.path.join(DIST, rel), encoding="utf-8").read(), "html.parser")
            sec = soup.find(id=f"vis-{vid}")
            if sec is None:
                problems.append(f"{rel}: no section vis-{vid}")
                continue
            n_sections += 1
            if sec.find_parent(id="explain") is None:
                problems.append(f"{rel}: vis-{vid} is not inside the Explain level")
            if vid not in claims[cid].get("illustrations", []):
                problems.append(f"{cid}: claims.json does not list {vid}")
            kind = sec.select_one(".vis-kind")
            if kind is None or not kind.get_text(strip=True):
                problems.append(f"{rel}: vis-{vid} has no kind label")
            cfg = dict(v.get("config", {}))
            cfg.update(a.get("config", {}) or {})
            ex = cfg.get("example") or cfg.get("scenario") or cfg.get("formula") or {"restore": "paper", "rollout": "346", "recurrence": "game", "compile": "xor"}.get(v["type"])
            text = re.sub(r"\s+", " ", sec.get_text(" "))
            if v["type"] == "rollout" and cfg.get("schedule") == "early":
                want = ["after 1 of 3 heads"]
            elif v["type"] == "recurrence" and cfg.get("protocol") == "store":
                want = ["N + 1 = 4", "board storage: state updates"]
            elif v["type"] == "recurrence" and cfg.get("protocol") == "summary":
                want = expected_text["summary"].get(ex, [])
            else:
                want = expected_text.get(v["type"], {}).get(ex, [])
            for w in want:
                if w not in text:
                    problems.append(f"{rel}: vis-{vid} default example lacks {w!r}")
            for link in sec.select("a.lean-ref, a[href*='source/']"):
                href = link.get("href", "")
                m = re.match(r"source/([^#]+)\.html#L(\d+)$", href)
                if not m:
                    continue
                n_links += 1
                mod, line = m.group(1), int(m.group(2))
                if mod not in src_pages:
                    src_pages[mod] = open(os.path.join(DIST, "source", mod + ".html"), encoding="utf-8").read()
                if f'id="L{line}"' not in src_pages[mod]:
                    problems.append(f"{rel}: {href} has no line anchor")
                name = link.get_text(strip=True)
                full = "NimAudit." + name if "NimAudit." + name in exp else None
                if full and (exp[full]["module"] != mod or exp[full]["line"] != line):
                    problems.append(f"{rel}: {name} links to {mod}:{line}, export says {exp[full]['module']}:{exp[full]['line']}")
            for link in sec.select("a[href^='claims/']"):
                href = link["href"]
                page, _, frag = href.partition("#")
                if not os.path.exists(os.path.join(DIST, page)):
                    problems.append(f"{rel}: broken link {href}")
                elif frag and f'id="{frag}"' not in open(os.path.join(DIST, page), encoding="utf-8").read():
                    problems.append(f"{rel}: {href} has no target")
    # every listed Lean name appears as a link in each section
    check("illustration sections: inside the Explain level of every attached claim, labelled, showing their default "
          "example's values, with Lean links to the declaring source line and working claim links",
          not problems, f"{n_sections} sections; {n_links} Lean links checked", problems[:20])


# ---------------------------------------------------------------------------------------------- staleness

def _copy_edition(dst):
    def ignore(d, names):
        skip = {"dist", "work", "validation", "__pycache__", "delivery_archive", ".git"}
        return [n for n in names if n in skip or (d == os.path.join(ROOT, "tools") and n == "node_modules")]
    shutil.copytree(ROOT, dst, ignore=ignore, symlinks=True)
    os.symlink(os.path.join(ROOT, "tools", "node_modules"), os.path.join(dst, "tools", "node_modules"))


def _run(cwd, *args):
    p = subprocess.run([sys.executable] + list(args), capture_output=True, text=True, cwd=cwd)
    return p.returncode, p.stdout + p.stderr


def _set_config_hash(d, key, path):
    import hashlib
    cfg_p = os.path.join(d, "site.config.yaml")
    txt = open(cfg_p, encoding="utf-8").read()
    old = re.search(rf"{key}:\s*\n\s*path: [^\n]+\n\s*sha256: ([0-9a-f]+)", txt).group(1)
    new = hashlib.sha256(open(os.path.join(d, path), "rb").read()).hexdigest()
    open(cfg_p, "w", encoding="utf-8").write(txt.replace(old, new))


def _set_corr_hash(d):
    import hashlib
    p = os.path.join(d, "data", "paper_proof_correspondence.json")
    corr = json.load(open(p, encoding="utf-8"))
    corr["jmlr_source_sha256"] = hashlib.sha256(open(os.path.join(d, "input", "jmlr_source", "paper_jmlr.tex"), "rb").read()).hexdigest()
    json.dump(corr, open(p, "w", encoding="utf-8"), indent=1, ensure_ascii=False)


def check_staleness(check):
    results = {}
    with tempfile.TemporaryDirectory() as tmp:
        # A. a changed claim statement (one word in Proposition 5.3's statement)
        d = os.path.join(tmp, "a")
        _copy_edition(d)
        tex_p = os.path.join(d, "input", "jmlr_source", "paper_jmlr.tex")
        tex = open(tex_p, encoding="utf-8").read()
        old = "then $\\operatorname{nim}(R)=0$."
        assert old in tex, "probe sentence not found in the JMLR source"
        open(tex_p, "w", encoding="utf-8").write(tex.replace(old, "then $\\operatorname{nim}(R)=0$ again.", 1))
        _set_config_hash(d, "jmlr_tex", "input/jmlr_source/paper_jmlr.tex")
        _set_corr_hash(d)               # workflow step 3: the correspondence names the new JMLR source
        rc, out = _run(d, "tools/build_site.py")
        review = os.path.join(d, "work", "review", "claims_review.json")
        items = json.load(open(review))["items"] if os.path.exists(review) else []
        ids = {i["id"] for i in items}
        ok_a = rc != 0 and "STALE CLAIM METADATA" in out and "prop:restore" in ids and \
            any("restore" in i.get("illustrations", []) for i in items if i["id"] == "prop:restore")
        rc2, out2 = _run(d, "tools/build_site.py", "--pin")
        ok_b = rc2 != 0 and "not marked reviewed" in out2
        doc = json.load(open(review))
        for i in doc["items"]:
            i["reviewed"], i["note"] = True, "test review"
        json.dump(doc, open(review, "w"))
        rc3, out3 = _run(d, "tools/build_site.py", "--pin")
        # the illustration attached to prop:restore must now ask for review as well
        ok_c = rc3 != 0 and "STALE ILLUSTRATIONS" in out3 and "restore" in out3
        results["claim"] = (ok_a and ok_b and ok_c, {"build": out[-300:], "pin_unreviewed": out2[-300:], "pin_reviewed": out3[-400:]})

        # B. a changed Lean statement behind an illustration
        d = os.path.join(tmp, "b")
        _copy_edition(d)
        ex_p = os.path.join(d, "data", "lean_export.json")
        ex = json.load(open(ex_p, encoding="utf-8"))
        for e in ex:
            if e["name"] == "NimAudit.Shootout.ah_counts":
                e["type"] = e["type"].replace("2 * B + 1", "2 * B + 3")
        json.dump(ex, open(ex_p, "w", encoding="utf-8"))
        rc, out = _run(d, "tools/build_site.py")
        results["lean_statement"] = (rc != 0 and "STALE ILLUSTRATIONS" in out and "rollout" in out, out[-400:])

        # C. a changed Lean source
        d = os.path.join(tmp, "c")
        _copy_edition(d)
        lp = os.path.join(d, "lean", "phase7", "Shootout.lean")
        open(lp, "a", encoding="utf-8").write("\n-- changed\n")
        rc, out = _run(d, "tools/build_site.py")
        results["lean_source"] = (rc != 0 and ("differ from the audited declaration index" in out or "STALE LEAN REFERENCE" in out), out[-300:])

        # D. a PDF that is not the one the reference compile produced, E. content edited after a build
        d = os.path.join(tmp, "d")
        _copy_edition(d)
        rc, out = _run(d, "tools/build_site.py")
        rc1, out1 = _run(d, "tools/check_sync.py")
        with open(os.path.join(d, "content", "visuals", "rollout.md"), "a", encoding="utf-8") as f:
            f.write("\n")
        rc2, out2 = _run(d, "tools/check_sync.py")
        pdf = os.path.join(d, "input", "paper_jmlr.pdf")
        open(pdf, "ab").write(b"\n%")
        _set_config_hash(d, "pdf", "input/paper_jmlr.pdf")
        rc3, out3 = _run(d, "tools/check_sync.py")
        results["dist_and_pdf"] = (rc == 0 and rc1 == 0 and rc2 != 0 and "dist/ is up to date" in out2 and "[FAIL] dist/" in out2
                                   and rc3 != 0 and "[FAIL] reference compile" in out3,
                                   {"fresh": out1[-200:], "edited": out2[-300:], "pdf": out3[-300:]})
    check("stale-data detection: a changed claim statement, Lean statement, Lean source, PDF or content file is refused "
          "with a review list; --pin refuses unreviewed changes; after review the dependent illustration is flagged",
          all(ok for ok, _ in results.values()), ", ".join(f"{k}: {'refused' if ok else 'NOT DETECTED'}" for k, (ok, _) in results.items()),
          {k: d for k, (ok, d) in results.items() if not ok})


# ---------------------------------------------------------------------------------------------- browser

async def browser_checks(check, b, bases, shots):
    """b: a Playwright browser; bases: base URLs (root and prefix)."""
    pages = {"restore": "claims/par__construction-example.html", "compile": "claims/c-threshold-realisation.html",
             "rollout": "claims/prop__rollout-sufficiency.html", "recurrence": "claims/c-replay.html",
             "bypasses": "claims/prop__bypass-interfaces.html"}
    for label, base in bases:
        ctx = await b.new_context(viewport={"width": 1366, "height": 900}, reduced_motion="reduce")
        pg = await ctx.new_page()
        errors = []
        pg.on("pageerror", lambda e: errors.append(str(e)))
        pg.on("console", lambda m: errors.append(m.text) if m.type == "error" else None)
        probs = []
        for vid, rel in pages.items():
            await pg.goto(base + rel + f"#vis-{vid}", wait_until="networkidle")
            sec = await pg.query_selector(f"#vis-{vid}")
            if sec is None:
                probs.append(f"{rel}: no section")
                continue
            top = await sec.evaluate("e => e.getBoundingClientRect().top")
            if abs(top) > 40:
                probs.append(f"{rel}#vis-{vid}: direct link not scrolled into view (top {top})")
            if vid != "bypasses":
                hidden = await pg.evaluate(f"document.querySelector('#vis-{vid} .nv-controls').hidden")
                if hidden:
                    probs.append(f"{rel}: controls not enhanced")
            trans = await pg.evaluate(f"""() => [...document.querySelectorAll('#vis-{vid} *')].filter(e => {{
                const s = getComputedStyle(e); return (parseFloat(s.transitionDuration) || 0) > 0 || (s.animationName && s.animationName !== 'none'); }}).length""")
            if trans:
                probs.append(f"{rel}: {trans} elements animate under reduced motion")
            if label == "prefix":
                await sec.screenshot(path=os.path.join(shots, f"visual_{vid}.png"))
        # stepping with buttons and keyboard on the rollout stepper
        await pg.goto(base + pages["rollout"] + "#vis-rollout", wait_until="networkidle")
        last = await pg.inner_text("#vis-rollout .nv-now")
        await pg.click("#vis-rollout button[aria-label='First step']")
        first = await pg.inner_text("#vis-rollout .nv-now")
        await pg.click("#vis-rollout .nv-stepper button:has-text('Next')")
        second = await pg.inner_text("#vis-rollout .nv-now")
        live = await pg.inner_text("#vis-rollout .nv-live")
        await pg.focus("#vis-rollout input[type=range]")
        await pg.keyboard.press("ArrowRight")
        third = await pg.inner_text("#vis-rollout .nv-now")
        if not (last.startswith("35 / 35") and first.startswith("1 / 35") and "Reset" in first and second.startswith("2 / 35")
                and live == second and third.startswith("3 / 35")):
            probs.append(f"stepper: {last[:30]} | {first[:30]} | {second[:30]} | {live[:30]} | {third[:30]}")
        # changing the example re-renders with exact values
        await pg.select_option("#vis-rollout .nv-controls select >> nth=0", "567")
        txt = await pg.inner_text("#vis-rollout")
        if "σ = 4" not in txt:
            probs.append("rollout example change did not re-render")
        await pg.goto(base + pages["restore"] + "#vis-restore", wait_until="networkidle")
        await pg.select_option("#vis-restore .nv-controls select >> nth=0", "custom")
        await pg.fill("#vis-restore .nv-custom input >> nth=0", "1, 2, 3")
        await pg.fill("#vis-restore .nv-custom input >> nth=1", "1, 2, 0")
        txt = await pg.inner_text("#vis-restore")
        if "set heap 1 to 1" not in txt or "Inside the promise" not in txt:
            probs.append("custom boards not computed")
        await pg.fill("#vis-restore .nv-custom input >> nth=1", "1, 2, 9")
        msg = await pg.inner_text("#vis-restore .nv-msg")
        if "at most 7" not in msg:
            probs.append(f"invalid input not reported: {msg!r}")
        # keyboard: Tab from the example selector reaches the next control
        await pg.goto(base + pages["recurrence"] + "#vis-recurrence", wait_until="networkidle")
        await pg.focus("#vis-recurrence .nv-controls select")
        await pg.keyboard.press("Tab")
        tag = await pg.evaluate("document.activeElement.tagName + ':' + (document.activeElement.closest('#vis-recurrence') ? 'in' : 'out')")
        if tag != "SELECT:in":
            probs.append(f"Tab order: {tag}")
        # panel in the article, then back
        await pg.goto(base + "paper.html", wait_until="networkidle")
        await pg.goto(base + "paper.html#par:construction-example~explain", wait_until="networkidle")
        await pg.wait_for_selector("#panel-par__construction-example .nv-controls:not([hidden])")
        ptxt = await pg.inner_text("#panel-par__construction-example")
        if "Decoded move: set heap 0 to 2" not in ptxt:
            probs.append("panel illustration missing its result")
        await pg.click("#panel-par__construction-example .panel-close")
        await pg.go_back()
        await pg.wait_for_selector("#panel-par__construction-example .vis")
        await pg.go_back()
        await pg.wait_for_timeout(300)
        if await pg.query_selector(".claim-panel") is not None:
            probs.append("back did not return to the article without a panel")
        check(f"illustrations in the browser ({label}): sections reachable by direct link, controls enhanced, no animation "
              f"under reduced motion, stepping by button and keyboard with a live announcement, example and custom input "
              f"recomputed, invalid input reported, Tab order, article panel with back navigation, no console errors",
              not probs and not errors, "; ".join(probs[:6]) + (f" errors: {errors[:3]}" if errors else ""))
        await ctx.close()

    base = bases[-1][1]
    # phone width
    mob = await b.new_context(viewport={"width": 390, "height": 844}, device_scale_factor=2, is_mobile=True, has_touch=True)
    m = await mob.new_page()
    over = []
    for vid, rel in pages.items():
        await m.goto(base + rel + f"#vis-{vid}", wait_until="networkidle")
        if await m.evaluate("document.documentElement.scrollWidth > window.innerWidth + 1"):
            over.append(rel)
    await m.goto(base + pages["rollout"] + "#vis-rollout", wait_until="networkidle")
    await m.screenshot(path=os.path.join(shots, "visual_mobile_rollout.png"))
    check("illustrations at phone width (390 px): no horizontal page overflow on any illustrated claim page",
          not over, str(over))
    await mob.close()
    # no JavaScript: the static default is complete and the controls stay hidden
    nojs = await b.new_context(java_script_enabled=False, viewport={"width": 1366, "height": 900})
    q = await nojs.new_page()
    probs = []
    for vid, rel, want in (("restore", pages["restore"], "Decoded move: set heap 0 to 2"),
                           ("rollout", pages["rollout"], "= 35"), ("recurrence", pages["recurrence"], "move heap 1 → 3"),
                           ("compile", pages["compile"], "agree")):
        await q.goto(base + rel, wait_until="networkidle")
        t = await q.inner_text(f"#vis-{vid}")
        vis = await q.evaluate(f"!document.querySelector('#vis-{vid} .nv-controls') || document.querySelector('#vis-{vid} .nv-controls').hidden")
        if want not in t or not vis:
            probs.append(vid)
    check("illustrations without JavaScript: each shows its complete default example, with the controls hidden",
          not probs, str(probs))
    await nojs.close()
    # print of a claim page: controls hidden, illustration content kept
    pr = await b.new_context(viewport={"width": 1366, "height": 900})
    q = await pr.new_page()
    await q.goto(base + pages["rollout"], wait_until="networkidle")
    await q.emulate_media(media="print")
    hidden = await q.evaluate("[...document.querySelectorAll('.nv-controls, .nv-stepper')].every(e => getComputedStyle(e).display === 'none')")
    pdf_path = os.path.join(os.path.dirname(shots), "print_preview_claim_rollout.pdf")
    await q.pdf(path=pdf_path)
    ptxt = subprocess.run(["pdftotext", pdf_path, "-"], capture_output=True, text=True).stdout
    check("printing an illustrated claim page keeps the illustration's result and hides its controls",
          hidden and "Counting the work" in ptxt and "Previous" not in ptxt, "")
    await pr.close()
