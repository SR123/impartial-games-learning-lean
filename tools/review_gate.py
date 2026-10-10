"""Review gates for the interactive edition (used by tools/build_site.py).

A lock file records what was last reviewed (claim statement sources; the claims, Lean statements and paper
figures behind each illustration).  When the current inputs differ from the lock, the build stops and
writes a review list:

    work/review/<name>_review.json   machine-readable, one item per change, each with "reviewed": false
    work/review/<NAME>_REVIEW.md     the same, for reading

After updating the affected explanations or illustrations, the reviewer marks each item
"reviewed": true and adds a short "note", then runs the build with the pin flag.  Pinning refuses unless
the review file covers exactly the current changes and every item is reviewed; it then writes the new lock
and archives the review file in data/reviews/.  Nothing is blessed silently.
"""
import datetime
import json
import os
import shutil


class ReviewError(Exception):
    pass


def _now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


class Gate:
    def __init__(self, root, name, title, lock_rel, pin_flag):
        self.root = root
        self.name = name                     # e.g. "claims"
        self.title = title                   # e.g. "claim statements"
        self.lock = os.path.join(root, lock_rel)
        self.lock_rel = lock_rel
        self.pin_flag = pin_flag             # e.g. "--pin"
        self.review_dir = os.path.join(root, "work", "review")
        self.review_json = os.path.join(self.review_dir, f"{name}_review.json")
        self.review_md = os.path.join(self.review_dir, f"{name.upper()}_REVIEW.md")

    def load_lock(self):
        if not os.path.exists(self.lock):
            return None
        return json.load(open(self.lock, encoding="utf-8"))

    def write_review(self, items, context):
        os.makedirs(self.review_dir, exist_ok=True)
        old = {}
        if os.path.exists(self.review_json):
            try:
                prev = json.load(open(self.review_json, encoding="utf-8"))
                old = {(i["id"], i.get("new")): i for i in prev.get("items", [])}
            except (ValueError, KeyError):
                old = {}
        for it in items:          # keep reviews already recorded for the same change
            p = old.get((it["id"], it.get("new")))
            if p:
                it["reviewed"] = p.get("reviewed", False)
                it["note"] = p.get("note", "")
            else:
                it.setdefault("reviewed", False)
                it.setdefault("note", "")
        doc = {"gate": self.name, "written_utc": _now(), "context": context, "items": items,
               "instructions": f"Update the affected content, then set reviewed: true and a note for every item, "
                               f"and run python3 tools/build_site.py {self.pin_flag}."}
        json.dump(doc, open(self.review_json, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
        lines = [f"# Review list: {self.title}", "", f"Written {doc['written_utc']} by tools/build_site.py.", "",
                 f"The inputs differ from `{self.lock_rel}`. Review each item below, update the content it names, then "
                 f"mark it `\"reviewed\": true` with a note in `work/review/{self.name}_review.json` and run "
                 f"`python3 tools/build_site.py {self.pin_flag}`.", ""]
        for it in items:
            lines.append(f"## {it['id']} ({it['change']})")
            for k in ("detail", "block", "lines", "content", "lean", "illustrations"):
                if it.get(k):
                    v = it[k]
                    lines.append(f"- {k}: {', '.join(map(str, v)) if isinstance(v, list) else v}")
            if it.get("excerpt"):
                lines += ["", "```", it["excerpt"][:1500], "```"]
            lines.append(f"- reviewed: {it['reviewed']}")
            lines.append("")
        open(self.review_md, "w", encoding="utf-8").write("\n".join(lines))

    def require_reviewed(self, items):
        """Raise unless the review file covers exactly `items` and every one is reviewed with a note."""
        if not os.path.exists(self.review_json):
            raise ReviewError(f"{self.pin_flag}: no review list at work/review/{self.name}_review.json. Run the build "
                              f"without {self.pin_flag} first to create it.")
        doc = json.load(open(self.review_json, encoding="utf-8"))
        rec = {(i["id"], i.get("new")): i for i in doc.get("items", [])}
        want = {(i["id"], i.get("new")) for i in items}
        missing = sorted(k[0] for k in want - set(rec))
        extra = sorted(k[0] for k in set(rec) - want)
        unreviewed = sorted(k[0] for k in want & set(rec) if not (rec[k].get("reviewed") is True and str(rec[k].get("note", "")).strip()))
        problems = []
        if missing:
            problems.append("changes not in the review list (rerun without the pin flag): " + ", ".join(missing))
        if extra:
            problems.append("review list contains items that are no longer changes (rerun without the pin flag): " + ", ".join(extra))
        if unreviewed:
            problems.append("items not marked reviewed with a note: " + ", ".join(unreviewed))
        if problems:
            raise ReviewError(f"{self.pin_flag} refused for {self.title}:\n  " + "\n  ".join(problems))
        return doc

    def archive(self, doc, tag):
        d = os.path.join(self.root, "data", "reviews")
        os.makedirs(d, exist_ok=True)
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        dest = os.path.join(d, f"{self.name}-{tag}-{stamp}.json")
        json.dump(doc, open(dest, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
        return os.path.relpath(dest, self.root)

    def clear(self):
        for p in (self.review_json, self.review_md):
            if os.path.exists(p):
                os.remove(p)
