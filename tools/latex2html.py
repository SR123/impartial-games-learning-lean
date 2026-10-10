#!/usr/bin/env python3
"""Project-specific LaTeX -> semantic HTML converter for paper_jmlr.tex.

This converter handles exactly the constructs used by the NIM paper and FAILS on anything
else (unknown command, unknown environment, unresolved reference, math that KaTeX rejects).
It never drops content silently.

    python3 tools/latex2html.py <paper_jmlr.tex> <figures.yaml> <out-dir>

Writes <out-dir>/article.json: front matter, an ordered list of article blocks (each with
HTML, kind, id, enclosing heading, exact comment-stripped LaTeX source and source lines),
the label table (label -> displayed number, kind, id), the figure list, the bibliography,
and the math adaptations applied.  TikZ pictures are written to <out-dir>/tikz/<name>.tex for
tools/build_figures.py.

Numbering follows the LaTeX counters of the JMLR class as used by this paper:
  section (arabic; letters after \\appendix), subsection, subsubsection;
  theorem-like environments share one counter, reset per section (\\numberwithin);
  example has its own global counter; equation is reset per section; figure and table are
  global.  A \\label takes the value of the innermost enclosing refstepped counter (inside an
  environment) or the last sectioning command (outside), exactly as in LaTeX.  The result
  is checked against the .aux file and against the PDF text by tools/validate_site.py.
"""
import hashlib
import html
import json
import os
import re
import subprocess
import sys
import unicodedata

HERE = os.path.dirname(os.path.abspath(__file__))
CONVERTER_VERSION = "1.0"


class ConvError(Exception):
    pass


# --------------------------------------------------------------------------------------
# Comment stripping with a position -> source-line map
# --------------------------------------------------------------------------------------

def strip_comments(src):
    """Remove % comments as TeX does: the comment, its newline and the next line's leading
    blanks disappear.  Returns (text, lines) where lines[i] is the 1-based source line of
    text[i]."""
    out, lines = [], []
    i, line, n = 0, 1, len(src)
    while i < n:
        c = src[i]
        if c == "\\" and i + 1 < n:
            out.append(c); lines.append(line)
            out.append(src[i + 1]); lines.append(line)
            if src[i + 1] == "\n":
                line += 1
            i += 2
            continue
        if c == "%":
            while i < n and src[i] != "\n":
                i += 1
            if i < n:  # eat newline and leading blanks of next line
                i += 1
                line += 1
                while i < n and src[i] in " \t":
                    i += 1
            continue
        out.append(c); lines.append(line)
        if c == "\n":
            line += 1
        i += 1
    return "".join(out), lines


# --------------------------------------------------------------------------------------
# AST
# --------------------------------------------------------------------------------------

class Node:
    __slots__ = ("kind", "name", "opt", "args", "body", "text", "start", "end", "extra")

    def __init__(self, kind, start, end=None, **kw):
        self.kind = kind          # text | cmd | env | math | par | group
        self.start = start
        self.end = end
        self.name = kw.get("name")
        self.opt = kw.get("opt")
        self.args = kw.get("args", [])
        self.body = kw.get("body", [])
        self.text = kw.get("text")
        self.extra = kw.get("extra", {})

    def __repr__(self):
        return f"<{self.kind} {self.name or ''} {self.text[:20] if self.text else ''}>"


# Command signatures: name -> (optional?, list of arg kinds) ; kinds: 'n' parsed nodes, 'r' raw
CMD = {
    # text formatting
    "emph": (False, ["n"]), "textbf": (False, ["n"]), "textit": (False, ["n"]),
    "texttt": (False, ["n"]), "textsc": (False, ["n"]), "textup": (False, ["n"]),
    "textnormal": (False, ["n"]), "texorpdfstring": (False, ["n", "r"]),
    "url": (False, ["r"]), "nolinkurl": (False, ["r"]), "href": (False, ["r", "n"]), "ref": (False, ["r"]), "citep": (True, ["r"]),
    "label": (False, ["r"]),
    # sectioning
    "section": (True, ["n"]), "subsection": (True, ["n"]), "subsubsection": (True, ["n"]),
    "paragraph": (True, ["n"]),
    # floats and lists
    "caption": (True, ["n"]), "includegraphics": (True, ["r"]), "item": (True, []),
    "acks": (False, ["n"]), "bibitem": (True, ["r"]),
    # zero-argument commands
    "appendix": (False, []), "maketitle": (False, []), "noindent": (False, []),
    "centering": (False, []), "allowbreak": (False, []), "newblock": (False, []),
    "hline": (False, []), "footnotesize": (False, []), "small": (False, []),
    "o": (False, []), "aa": (False, []), "ldots": (False, []), "dots": (False, []),
}
ACCENTS = {"'": "\u0301", '"': "\u0308", "`": "\u0300", "^": "\u0302", "~": "\u0303", "v": "\u030c"}
CHAR_CMDS = {"o": "\u00f8", "aa": "\u00e5", "ldots": "\u2026", "dots": "\u2026"}
SYMBOL_CMDS = {"%": "%", "_": "_", "&": "&amp;", "$": "$", "#": "#", " ": " ",
               ",": "\u2009", "{": "{", "}": "}"}
DECLARATIONS = {"footnotesize", "small", "centering", "noindent", "allowbreak", "newblock",
                "hline"}

THEOREM_ENVS = {"theorem": "Theorem", "lemma": "Lemma", "proposition": "Proposition",
                "remark": "Remark", "definition": "Definition", "corollary": "Corollary",
                "example": "Example"}
MATH_ENVS = {"equation", "align*"}
KNOWN_ENVS = set(THEOREM_ENVS) | MATH_ENVS | {
    "proof", "itemize", "enumerate", "figure", "table", "center", "tabular", "tabularx",
    "tikzpicture", "quote", "minipage", "abstract", "keywords", "thebibliography"}


class Parser:
    def __init__(self, text, base):
        self.s = text
        self.base = base   # offset of self.s within the stripped document
        self.i = 0

    def err(self, msg, pos=None):
        raise ConvError(f"{msg} (stripped offset {self.base + (self.i if pos is None else pos)})")

    def at(self, k=0):
        j = self.i + k
        return self.s[j] if j < len(self.s) else ""

    # -- raw readers --
    def read_group_raw(self):
        """At '{' (after optional whitespace): return raw contents of the balanced group."""
        while self.at() in " \t\n":
            self.i += 1
        if self.at() != "{":
            self.err("expected '{'")
        depth, j = 0, self.i
        while j < len(self.s):
            c = self.s[j]
            if c == "\\":
                j += 2
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    raw = self.s[self.i + 1:j]
                    start = self.i + 1
                    self.i = j + 1
                    return raw, start
            j += 1
        self.err("unbalanced braces")

    def read_opt_raw(self):
        """If an optional [..] argument follows (no intervening blank line), return raw."""
        j = self.i
        while j < len(self.s) and self.s[j] in " \t":
            j += 1
        if j >= len(self.s) or self.s[j] != "[":
            return None, None
        depth, k, inmath = 0, j + 1, False
        while k < len(self.s):
            c = self.s[k]
            if c == "\\":
                k += 2
                continue
            if c == "$":
                inmath = not inmath
            elif c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
            elif c == "]" and depth == 0 and not inmath:
                raw = self.s[j + 1:k]
                self.i = k + 1
                return raw, j + 1
            k += 1
        self.err("unterminated optional argument")

    def sub(self, raw, start):
        return Parser(raw, self.base + start).parse()

    # -- main --
    def parse(self, stop_env=None):
        nodes = []
        buf, bstart = [], None

        def flush():
            nonlocal buf, bstart
            if buf:
                nodes.append(Node("text", self.base + bstart, self.base + self.i, text="".join(buf)))
            buf, bstart = [], None

        while self.i < len(self.s):
            c = self.s[self.i]
            if c == "\n":
                j = self.i + 1
                while j < len(self.s) and self.s[j] in " \t":
                    j += 1
                if j < len(self.s) and self.s[j] == "\n":
                    flush()
                    k = j
                    while k < len(self.s) and self.s[k] in " \t\n":
                        k += 1
                    nodes.append(Node("par", self.base + self.i, self.base + k))
                    self.i = k
                    continue
                if bstart is None:
                    bstart = self.i
                buf.append(" ")
                self.i += 1
                continue
            if c == "$":
                flush()
                nodes.append(self.read_inline_math())
                continue
            if c == "{":
                flush()
                raw, st = self.read_group_raw()
                g = Node("group", self.base + st - 1, self.base + self.i, body=self.sub(raw, st))
                nodes.append(g)
                continue
            if c == "}":
                self.err("unexpected '}'")
            if c == "~":
                if bstart is None:
                    bstart = self.i
                buf.append("\u00a0")
                self.i += 1
                continue
            if c == "&":
                flush()
                nodes.append(Node("cmd", self.base + self.i, self.base + self.i + 1, name="&"))
                self.i += 1
                continue
            if c == "\\":
                flush()
                node = self.read_command(stop_env)
                if node is None:   # \end{stop_env}
                    return nodes
                nodes.append(node)
                continue
            if bstart is None:
                bstart = self.i
            buf.append(c)
            self.i += 1
        flush()
        if stop_env:
            self.err(f"missing \\end{{{stop_env}}}")
        return nodes

    def read_inline_math(self):
        start = self.i
        if self.at(1) == "$":
            self.err("display $$ not supported")
        j = self.i + 1
        while j < len(self.s):
            if self.s[j] == "\\":
                j += 2
                continue
            if self.s[j] == "$":
                break
            j += 1
        else:
            self.err("unterminated $")
        tex = self.s[self.i + 1:j]
        self.i = j + 1
        return Node("math", self.base + start, self.base + self.i, text=tex,
                    extra={"display": False, "env": None})

    def read_command(self, stop_env):
        start = self.i
        self.i += 1
        c = self.at()
        if not c:
            self.err("trailing backslash")
        if c.isalpha():
            j = self.i
            while j < len(self.s) and self.s[j].isalpha():
                j += 1
            name = self.s[self.i:j]
            self.i = j
            # skip spaces after a control word (and a single newline, not a blank line)
            k = self.i
            while k < len(self.s) and self.s[k] in " \t":
                k += 1
            if k < len(self.s) and self.s[k] == "\n":
                k2 = k + 1
                while k2 < len(self.s) and self.s[k2] in " \t":
                    k2 += 1
                if not (k2 < len(self.s) and self.s[k2] == "\n"):
                    k = k2
            if name not in ("begin", "end"):
                self.i = k
        else:
            name = c
            self.i += 1
            if name == "[":
                return self.read_display_bracket(start)
            if name in ACCENTS:
                # argument: next char or group
                if self.at() == "{":
                    raw, st = self.read_group_raw()
                    arg = raw
                else:
                    arg = self.at()
                    self.i += 1
                if len(arg) != 1 or not arg.isalpha():
                    self.err(f"unsupported accent argument {arg!r}")
                ch = unicodedata.normalize("NFC", arg + ACCENTS[name])
                return Node("text", self.base + start, self.base + self.i, text=ch)
            if name == "\\":
                return Node("cmd", self.base + start, self.base + self.i, name="\\\\")
            if name in SYMBOL_CMDS:
                return Node("text", self.base + start, self.base + self.i,
                            text=SYMBOL_CMDS[name], extra={"html": True})
            self.err(f"unknown control symbol \\{name}")
        if name == "v":
            raw, _ = self.read_group_raw()
            if len(raw) != 1 or not raw.isalpha():
                self.err(f"unsupported caron argument {raw!r}")
            ch = unicodedata.normalize("NFC", raw + ACCENTS[name])
            return Node("text", self.base + start, self.base + self.i, text=ch)
        if name == "begin":
            return self.read_env(start)
        if name == "end":
            raw, st = self.read_group_raw()
            if raw != stop_env:
                self.err(f"unexpected \\end{{{raw}}} (open: {stop_env})", start)
            return None
        if name not in CMD:
            self.err(f"unknown command \\{name}", start)
        has_opt, kinds = CMD[name]
        opt = None
        if has_opt:
            raw, st = self.read_opt_raw()
            if raw is not None:
                opt = (raw, st)
        args = []
        for k in kinds:
            raw, st = self.read_group_raw()
            args.append(raw if k == "r" else self.sub(raw, st))
        optnodes = None
        if opt is not None:
            optnodes = opt[0] if name in ("includegraphics", "bibitem", "citep") else self.sub(*opt)
        return Node("cmd", self.base + start, self.base + self.i, name=name, opt=optnodes, args=args)

    def read_display_bracket(self, start):
        j = self.s.find("\\]", self.i)
        if j < 0:
            self.err("unterminated \\[")
        tex = self.s[self.i:j]
        self.i = j + 2
        return Node("math", self.base + start, self.base + self.i, text=tex,
                    extra={"display": True, "env": None})

    def read_env(self, start):
        name, _ = self.read_group_raw()
        if name not in KNOWN_ENVS:
            self.err(f"unknown environment {name}", start)
        end_tag = "\\end{" + name + "}"
        if name in MATH_ENVS or name == "tikzpicture":
            j = self.s.find(end_tag, self.i)
            if j < 0:
                self.err(f"missing {end_tag}")
            raw = self.s[self.i:j]
            body_start = self.i
            self.i = j + len(end_tag)
            if name == "tikzpicture":
                return Node("env", self.base + start, self.base + self.i, name=name, text=raw,
                            extra={"raw_start": self.base + body_start})
            return Node("math", self.base + start, self.base + self.i, text=raw,
                        extra={"display": True, "env": name})
        opt, args = None, []
        if name in ("tabular", "tabularx"):
            if name == "tabularx":
                w, _ = self.read_group_raw()
                args.append(w)
            spec, _ = self.read_group_raw()
            args.append(spec)
            j = self.s.find(end_tag, self.i)
            if j < 0:
                self.err(f"missing {end_tag}")
            raw = self.s[self.i:j]
            body_start = self.i
            self.i = j + len(end_tag)
            return Node("env", self.base + start, self.base + self.i, name=name, args=args,
                        text=raw, extra={"raw_start": self.base + body_start})
        if name == "minipage":
            w, _ = self.read_group_raw()
            args.append(w)
        if name == "thebibliography":
            w, _ = self.read_group_raw()
            args.append(w)
        if name in THEOREM_ENVS or name == "proof":
            raw, st = self.read_opt_raw()
            if raw is not None:
                opt = self.sub(raw, st)
        elif name in ("itemize", "enumerate", "figure", "table"):
            raw, st = self.read_opt_raw()
            if raw is not None:
                opt = raw
        body = self.parse(stop_env=name)
        return Node("env", self.base + start, self.base + self.i, name=name, opt=opt,
                    args=args, body=body)


# --------------------------------------------------------------------------------------
# Typography for plain text
# --------------------------------------------------------------------------------------

def typo(text, already_html=False):
    t = text if already_html else html.escape(text, quote=False)
    t = t.replace("``", "\u201c").replace("''", "\u201d")
    t = t.replace("`", "\u2018").replace("'", "\u2019")
    t = t.replace("---", "\u2014").replace("--", "\u2013")
    return t


def slug(s):
    s = s.replace("\u2013", "-").replace("\u2014", "-")
    s = unicodedata.normalize("NFKD", s)
    s = re.sub(r"[^\w\s-]", "", s.lower())
    return re.sub(r"[\s_]+", "-", s).strip("-")[:60]


def roman(n):
    vals = [(10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]
    out = ""
    for v, r in vals:
        while n >= v:
            out += r
            n -= v
    return out


# --------------------------------------------------------------------------------------
# Renderer
# --------------------------------------------------------------------------------------

class Renderer:
    def __init__(self, stripped, lines, figures_meta, cites):
        self.s = stripped
        self.lines = lines
        self.fig_meta = figures_meta
        self.cites = cites               # key -> (short author, year)
        self.math = []                   # (id, tex, display)
        self.blocks = []
        self.labels = {}                 # label -> dict(number, kind, id)
        self.ids = set()
        self.counters = {"section": 0, "subsection": 0, "subsubsection": 0, "theorem": 0,
                         "example": 0, "equation": 0, "figure": 0, "table": 0}
        self.appendix = False
        self.scope = [{"label": ""}]     # current-label scopes
        self.heading_id = "front"
        self.heading_stack = {}          # level -> id
        self.par_counter = {}
        self.figures = []
        self.tikz = {}
        self.unlabelled = []             # numbered items without labels
        self.cited = []
        self.math_adaptations = []
        self.inventory = {"theorem_envs": [], "proofs": 0, "equations": 0, "displays": 0,
                          "tables": 0, "figures": 0, "lists": 0, "paragraphs": 0}

    # -- helpers --
    def line_of(self, pos):
        return self.lines[min(pos, len(self.lines) - 1)]

    def src(self, a, b):
        return self.s[a:b]

    def new_id(self, base):
        cand, k = base, 2
        while cand in self.ids:
            cand = f"{base}-{k}"
            k += 1
        self.ids.add(cand)
        return cand

    def claim_id(self, ident):
        if ident in self.ids:
            raise ConvError(f"duplicate id {ident}")
        self.ids.add(ident)
        return ident

    def secnum(self, level):
        sec = chr(64 + self.counters["section"]) if self.appendix else str(self.counters["section"])
        if level == 1:
            return sec
        if level == 2:
            return f"{sec}.{self.counters['subsection']}"
        return f"{sec}.{self.counters['subsection']}.{self.counters['subsubsection']}"

    def thmnum(self):
        sec = chr(64 + self.counters["section"]) if self.appendix else str(self.counters["section"])
        return f"{sec}.{self.counters['theorem']}"

    def eqnum(self):
        sec = chr(64 + self.counters["section"]) if self.appendix else str(self.counters["section"])
        return f"{sec}.{self.counters['equation']}"

    def set_label(self, name, kind, ident):
        if name in self.labels:
            raise ConvError(f"duplicate label {name}")
        self.labels[name] = {"number": self.scope[-1]["label"], "kind": kind, "id": ident,
                             "heading": self.heading_id}

    def plain_text(self, h):
        """Plain text of rendered inline HTML that still contains math placeholders."""
        tex = {m["id"]: m["tex"] for m in self.math}
        h = re.sub(r"\x00MATH:(m\d+)\x00", lambda m: math_plain(tex[m.group(1)], self.macros), h)
        h = re.sub(r"\x00[^\x00]*\x00", "", h)
        return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", "", h))).strip()

    def add_math(self, tex, display, pos):
        mid = f"m{len(self.math)}"
        self.math.append({"id": mid, "tex": tex, "display": display, "line": self.line_of(pos)})
        return f"\x00MATH:{mid}\x00"

    # -- inline rendering --
    def inline(self, nodes, ctx=None):
        """Render a list of inline nodes to HTML.  Labels encountered are returned."""
        out, labels = [], []
        for nd in nodes:
            h, labs = self.inline_node(nd, ctx)
            out.append(h)
            labels += labs
        return "".join(out), labels

    def inline_node(self, nd, ctx):
        k = nd.kind
        if k == "text":
            if nd.extra.get("html"):
                return nd.text, []
            return typo(nd.text), []
        if k == "par":
            raise ConvError(f"paragraph break not allowed here (line {self.line_of(nd.start)})")
        if k == "group":
            return self.inline(nd.body, ctx)
        if k == "math":
            if nd.extra["display"]:
                return self.display_math(nd), []
            tex = nd.text
            if "\\label" in tex or "\\ref" in tex:
                raise ConvError(f"label/ref inside inline math, line {self.line_of(nd.start)}")
            return '<span class="math-inline">' + self.add_math(tex, False, nd.start) + "</span>", []
        if k == "cmd":
            return self.inline_cmd(nd, ctx)
        if k == "env":
            raise ConvError(f"block environment {nd.name} in inline context, line {self.line_of(nd.start)}")
        raise ConvError(f"unexpected node {nd}")

    def display_math(self, nd):
        tex = nd.text
        labels = re.findall(r"\\label\{([^}]*)\}", tex)
        tex_clean = re.sub(r"\\label\{[^}]*\}", "", tex).strip()
        if "\\ref" in tex_clean:
            raise ConvError(f"\\ref in display math, line {self.line_of(nd.start)}")
        env = nd.extra["env"]
        if env == "align*":
            tex_k = "\\begin{aligned}" + tex_clean + "\\end{aligned}"
            self.math_adaptations.append({"line": self.line_of(nd.start),
                                          "change": "align* rendered as aligned inside display math"})
        else:
            tex_k = tex_clean
        rendered = self.add_math(tex_k, True, nd.start)
        if env == "equation":
            self.counters["equation"] += 1
            self.inventory["equations"] += 1
            num = self.eqnum()
            if len(labels) != 1:
                raise ConvError(f"numbered equation needs exactly one label, line {self.line_of(nd.start)}")
            ident = self.claim_id(labels[0])
            self.scope.append({"label": num})
            self.set_label(labels[0], "equation", ident)
            self.scope.pop()
            return (f'<span class="equation" id="{ident}"><span class="eq-body">{rendered}</span>'
                    f'<span class="eq-num">({num})</span></span>')
        if labels:
            raise ConvError(f"label in unnumbered display, line {self.line_of(nd.start)}")
        self.inventory["displays"] += 1
        return f'<span class="display">{rendered}</span>'

    def inline_cmd(self, nd, ctx):
        n = nd.name
        if n in ("emph", "textit"):
            h, l = self.inline(nd.args[0], ctx)
            return f"<em>{h}</em>", l
        if n == "textbf":
            h, l = self.inline(nd.args[0], ctx)
            return f"<strong>{h}</strong>", l
        if n == "texttt":
            h, l = self.inline(nd.args[0], ctx)
            return f"<code>{h}</code>", l
        if n == "textsc":
            h, l = self.inline(nd.args[0], ctx)
            return f'<span class="smallcaps">{h}</span>', l
        if n in ("textup", "textnormal"):
            h, l = self.inline(nd.args[0], ctx)
            return f'<span class="upright">{h}</span>', l
        if n == "texorpdfstring":
            return self.inline(nd.args[0], ctx)
        if n == "href":
            h, labels = self.inline(nd.args[1], ctx)
            return f'<a href="{html.escape(nd.args[0], quote=True)}">{h}</a>', labels
        if n == "nolinkurl":
            return f'<span class="printed-url">{html.escape(nd.args[0])}</span>', []
        if n == "url":
            u = nd.args[0]
            return f'<a class="url" href="{html.escape(u)}">{html.escape(u)}</a>', []
        if n == "ref":
            return f"\x00REF:{nd.args[0]}\x00", []
        if n == "citep":
            if nd.opt:
                raise ConvError("citep optional argument not supported")
            return self.citation(nd.args[0]), []
        if n == "label":
            return "", [nd.args[0]]
        if n in CHAR_CMDS:
            return CHAR_CMDS[n], []
        if n == "\\\\":
            return "<br>", []
        if n in DECLARATIONS:
            return "", []
        raise ConvError(f"command \\{n} not allowed inline (line {self.line_of(nd.start)})")

    def citation(self, keys):
        keys = [k.strip() for k in keys.split(",")]
        parts, prev = [], None
        for k in keys:
            if k not in self.cites:
                raise ConvError(f"unknown citation key {k}")
            self.cited.append(k)
            au, yr = self.cites[k]
            link = lambda txt, k=k: f'<a class="cite" href="#bib-{k}">{txt}</a>'
            if prev and prev[0] == au:
                base_prev = re.sub(r"[a-z]$", "", prev[1])
                base = re.sub(r"[a-z]$", "", yr)
                if base == base_prev and yr != base:
                    parts[-1] += "," + link(yr[len(base):])
                else:
                    parts[-1] += ", " + link(typo(yr))
            else:
                parts.append(f"{html.escape(au)}, " + link(typo(yr)))
            prev = (au, yr)
        return '<span class="citation">(' + "; ".join(parts) + ")</span>"

    # -- block rendering --
    def emit(self, kind, html_, a, b, ident=None, extra=None):
        blk = {"kind": kind, "id": ident, "html": html_, "heading": self.heading_id,
               "src": re.sub(r"\s+", " ", self.src(a, b)).strip(),
               "lines": [self.line_of(a), self.line_of(max(a, b - 1))]}
        if extra:
            blk.update(extra)
        self.blocks.append(blk)
        return blk

    def para_html(self, nodes, a, b, cls=None):
        h, labels = self.inline(nodes)
        if labels:
            raise ConvError(f"unexpected label(s) {labels} in paragraph at line {self.line_of(a)}")
        h = h.strip()
        if not h:
            return None
        attr = f' class="{cls}"' if cls else ""
        return f"<p{attr}>{h}</p>"

    def split_paragraphs(self, nodes):
        """Split a node list into paragraphs and block elements."""
        items, cur = [], []
        for nd in nodes:
            if nd.kind == "par":
                if cur:
                    items.append(("p", cur))
                cur = []
            elif (nd.kind == "env" and nd.name not in ("tikzpicture",)) or \
                    (nd.kind == "cmd" and nd.name in ("section", "subsection", "subsubsection",
                                                       "paragraph", "acks", "appendix",
                                                       "maketitle", "item", "caption",
                                                       "includegraphics")):
                if cur:
                    items.append(("p", cur))
                cur = []
                items.append(("b", nd))
            else:
                cur.append(nd)
        if cur:
            items.append(("p", cur))
        # drop whitespace-only paragraphs
        out = []
        for kind, x in items:
            if kind == "p" and all(n.kind == "text" and not n.text.strip() for n in x):
                continue
            out.append((kind, x))
        return out

    def render_container(self, nodes, top=False):
        """Render block content.  At top level, emits blocks; otherwise returns HTML."""
        parts = []
        pending_runin = None
        for kind, x in self.split_paragraphs(nodes):
            if kind == "p":
                a, b = x[0].start, x[-1].end
                labels_here = [n for n in x if n.kind == "cmd" and n.name == "label"]
                rest = [n for n in x if not (n.kind == "cmd" and n.name == "label")]
                if labels_here and top:
                    # a label after a sectioning command at top level, possibly with text
                    for lab in labels_here:
                        self.attach_label_to_last_heading(lab.args[0])
                if labels_here and not top:
                    raise ConvError(f"label inside non-top paragraph, line {self.line_of(a)}")
                if all(n.kind == "text" and not n.text.strip() for n in rest):
                    continue
                if pending_runin is not None:
                    head_html, head_id = pending_runin
                    h, _ = self.inline(rest)
                    body = f'<p class="runin-para">{head_html} {h.strip()}</p>'
                    pending_runin = None
                else:
                    body = self.para_html(rest, a, b)
                if body is None:
                    continue
                self.inventory["paragraphs"] += 1
                if top:
                    k = self.par_counter.get(self.heading_id, 0) + 1
                    self.par_counter[self.heading_id] = k
                    pid = self.new_id(f"{self.heading_id}-p{k}")
                    body = body.replace("<p", f'<p id="{pid}"', 1)
                    self.emit("p", body, a, b, pid)
                else:
                    parts.append(body)
                continue
            nd = x
            if nd.kind == "cmd" and nd.name == "paragraph":
                if pending_runin is not None:
                    raise ConvError("two run-in headings in a row")
                pending_runin = self.runin_heading(nd)
                if top:
                    self.last_runin = pending_runin
                continue
            if pending_runin is not None:
                raise ConvError(f"run-in heading not followed by text (line {self.line_of(nd.start)})")
            h = self.block_node(nd, top)
            if h is not None:
                parts.append(h)
        if pending_runin is not None:
            raise ConvError("dangling run-in heading")
        return "".join(parts)

    def attach_label_to_last_heading(self, name):
        blk = self.last_heading_block
        if blk is None:
            raise ConvError(f"label {name} with no heading")
        if blk.get("labels") is None:
            blk["labels"] = []
        blk["labels"].append(name)
        if blk["kind"] == "heading" and blk.get("auto_id"):
            # the first label replaces the automatic id
            old = blk["id"]
            self.ids.discard(old)
            ident = self.claim_id(name)
            blk["html"] = blk["html"].replace(f'id="{old}"', f'id="{ident}"', 1)
            blk["id"] = ident
            blk["auto_id"] = False
            self.retarget_heading(old, ident)
        elif blk["kind"] == "runin":
            old = blk["id"]
            self.ids.discard(old)
            ident = self.claim_id(name)
            blk["id"] = ident
            blk["auto_id"] = False
            self.retarget_heading(old, ident)
        else:
            ident = self.claim_id(name)
            extra_anchor = f'<span class="anchor" id="{ident}"></span>'
            blk["html"] = blk["html"].replace("</h", extra_anchor + "</h", 1) \
                if blk["kind"] == "heading" else blk["html"]
            blk.setdefault("extra_ids", []).append(ident)
        self.set_label(name, "section" if blk["kind"] == "heading" else "paragraph", ident)

    def retarget_heading(self, old, new):
        if self.heading_id == old:
            self.heading_id = new
        for lv, v in list(self.heading_stack.items()):
            if v == old:
                self.heading_stack[lv] = new

    def runin_heading(self, nd):
        title, labels = self.inline(nd.args[0])
        if labels:
            raise ConvError("label inside paragraph title")
        ident = self.new_id("par-" + slug(self.plain_text(title)))
        holder = {"kind": "runin", "id": ident, "auto_id": True}
        self.last_heading_block = holder
        self.heading_id = ident
        self.par_counter[ident] = 0
        # the id is resolved at the end (labels may follow the heading)
        placeholder = f"\x00RUNIN:{len(self.runins)}\x00"
        self.runins.append((holder, title))
        return (placeholder, ident)

    def heading(self, nd, level):
        name = nd.name
        title_html, labels = self.inline(nd.args[0])
        if labels:
            raise ConvError("label inside heading")
        if nd.opt is not None:
            raise ConvError("optional sectioning argument not supported")
        if name == "section":
            self.counters["section"] += 1
            self.counters["subsection"] = 0
            self.counters["subsubsection"] = 0
            self.counters["theorem"] = 0
            self.counters["equation"] = 0
        elif name == "subsection":
            self.counters["subsection"] += 1
            self.counters["subsubsection"] = 0
        else:
            self.counters["subsubsection"] += 1
        num = self.secnum(level)
        self.scope[0]["label"] = num
        ident = self.new_id("sec-" + slug(self.plain_text(title_html)))
        tag = {1: "h2", 2: "h3", 3: "h4"}[level]
        shown = f"Appendix {num}." if (self.appendix and level == 1) else num
        h = (f'<{tag} id="{ident}" class="sec-h l{level}"><span class="secnum">{shown}</span> '
             f'<span class="sectitle">{title_html}</span></{tag}>')
        self.heading_id = ident
        self.heading_stack[level] = ident
        for lv in list(self.heading_stack):
            if lv > level:
                del self.heading_stack[lv]
        self.par_counter[ident] = 0
        blk = self.emit("heading", h, nd.start, nd.end, ident,
                        {"level": level, "number": num, "title": title_html,
                         "auto_id": True, "appendix": self.appendix})
        self.last_heading_block = blk
        return None

    def block_node(self, nd, top):
        if nd.kind == "cmd":
            n = nd.name
            if n in ("section", "subsection", "subsubsection"):
                if not top:
                    raise ConvError("sectioning inside environment")
                return self.heading(nd, {"section": 1, "subsection": 2, "subsubsection": 3}[n])
            if n == "appendix":
                self.appendix = True
                self.counters["section"] = 0
                self.counters["subsection"] = 0
                return None
            if n == "maketitle":
                self.emit("title", "", nd.start, nd.end, None)
                return None
            if n == "acks":
                body, labels = self.inline(nd.args[0])
                h = ('<section class="acks" id="acks"><h2 class="sec-h unnumbered">Acknowledgments '
                     f'and Disclosure of Funding</h2><p>{body.strip()}</p></section>')
                self.ids.add("acks")
                self.heading_id = "acks"
                self.emit("acks", h, nd.start, nd.end, "acks")
                return None
            raise ConvError(f"unexpected block command \\{n} (line {self.line_of(nd.start)})")
        if nd.kind == "env":
            return self.block_env(nd, top)
        raise ConvError(f"unexpected block node {nd}")

    def block_env(self, nd, top):
        n = nd.name
        if n in THEOREM_ENVS:
            return self.theorem_env(nd, top)
        if n == "proof":
            return self.proof_env(nd, top)
        if n in ("itemize", "enumerate"):
            h = self.list_env(nd)
            self.inventory["lists"] += 1
            if top:
                k = sum(1 for b in self.blocks if b["kind"] == "list" and b["heading"] == self.heading_id) + 1
                ident = self.new_id(f"{self.heading_id}-list{k}")
                h = h.replace(">", f' id="{ident}">', 1)
                self.emit("list", h, nd.start, nd.end, ident)
                return None
            return h
        if n == "figure":
            return self.figure_env(nd, top, "figure")
        if n == "table":
            return self.figure_env(nd, top, "table")
        if n == "center":
            inner = [x for x in nd.body if not (x.kind == "text" and not x.text.strip())
                     and x.kind != "par"]
            if len(inner) != 1 or inner[0].kind != "env" or inner[0].name != "tabular":
                raise ConvError("center environment is only supported around one tabular")
            k = sum(1 for b in self.blocks if b["kind"] == "table" and b["heading"] == self.heading_id) + 1
            ident = self.new_id(f"{self.heading_id}-table{k}")
            h = f'<div class="table-wrap unnumbered-table" id="{ident}">{self.tabular(inner[0])}</div>'
            self.inventory["tables"] += 1
            if top:
                self.emit("table", h, nd.start, nd.end, ident)
                return None
            return h
        if n == "quote":
            h = f"<blockquote>{self.render_container(nd.body)}</blockquote>"
            if top:
                self.emit("quote", h, nd.start, nd.end, None)
                return None
            return h
        if n == "minipage":
            if not top:
                raise ConvError("nested minipage")
            self.render_container(nd.body, top=True)
            return None
        if n == "abstract":
            body = self.render_container(nd.body)
            self.ids.add("abstract")
            h = f'<section class="abstract" id="abstract"><h2 class="abstract-h">Abstract</h2>{body}</section>'
            self.heading_id = "abstract"
            self.emit("abstract", h, nd.start, nd.end, "abstract")
            return None
        if n == "keywords":
            body, _ = self.inline([x for x in nd.body if x.kind != "par"])
            h = f'<p class="keywords"><strong>Keywords:</strong> {body.strip()}</p>'
            self.emit("keywords", h, nd.start, nd.end, "keywords")
            self.ids.add("keywords")
            return None
        if n == "thebibliography":
            return self.bibliography(nd)
        if n in ("tabular", "tabularx"):
            raise ConvError("bare tabular outside center/figure/table")
        raise ConvError(f"environment {n} not supported here (line {self.line_of(nd.start)})")

    def theorem_env(self, nd, top):
        n = nd.name
        if n == "example":
            self.counters["example"] += 1
            num = str(self.counters["example"])
        else:
            self.counters["theorem"] += 1
            num = self.thmnum()
        self.scope.append({"label": num})
        title_html = None
        if nd.opt is not None:
            title_html, labs = self.inline(nd.opt)
            if labs:
                raise ConvError("label in theorem title")
        # labels at the start of the body
        labels = [x.args[0] for x in nd.body if x.kind == "cmd" and x.name == "label"]
        body_nodes = [x for x in nd.body if not (x.kind == "cmd" and x.name == "label")]
        if labels:
            ident = self.claim_id(labels[0])
        else:
            tslug = slug(self.plain_text(title_html or "")) or num.replace(".", "-")
            ident = self.new_id(f"x-{n}-{tslug}")
            self.unlabelled.append({"id": ident, "kind": n, "number": num,
                                    "line": self.line_of(nd.start)})
        for i, lab in enumerate(labels):
            self.set_label(lab, n, ident if i == 0 else self.claim_id(lab))
        head = f'<span class="stmt-label">{THEOREM_ENVS[n]} {num}</span>'
        if title_html:
            head += f' <span class="stmt-title">({title_html})</span>'
        body = self.render_container(body_nodes)
        body = self.merge_head(body, f'<span class="stmt-head">{head}</span>')
        extra_anchors = "".join(f'<span class="anchor" id="{lab}"></span>' for lab in labels[1:])
        h = (f'<div class="stmt stmt-{n}" id="{ident}" data-number="{num}">{extra_anchors}'
             f'{body}</div>')
        self.scope.pop()
        self.inventory["theorem_envs"].append(ident)
        if top:
            self.emit("stmt", h, nd.start, nd.end, ident,
                      {"env": n, "number": num, "labels": labels,
                       "title": title_html, "display_name": f"{THEOREM_ENVS[n]} {num}"})
            return None
        return h

    @staticmethod
    def merge_head(body, head):
        """Put a run-in head at the start of the first paragraph (or before a list)."""
        if body.startswith("<p>"):
            return "<p>" + head + " " + body[3:]
        return f"<p>{head}</p>" + body

    def proof_env(self, nd, top):
        if nd.opt is not None:
            t, labs = self.inline(nd.opt)
            if labs:
                raise ConvError("label in proof title")
            head = f'<span class="proof-head">{t}.</span>'
        else:
            head = '<span class="proof-head">Proof.</span>'
        self.scope.append({"label": self.scope[-1]["label"]})
        body = self.render_container(nd.body)
        self.scope.pop()
        body = self.merge_head(body, head)
        # QED box at the end of the last paragraph
        idx = body.rfind("</p>")
        if idx < 0:
            raise ConvError("proof without paragraph")
        body = body[:idx] + '<span class="qed" aria-hidden="true">\u25a1</span>' + body[idx:]
        self.inventory["proofs"] += 1
        if top:
            # stable website-side id: proof of a referenced statement, else of the
            # immediately preceding statement
            m = re.search(r"\x00REF:([^\x00]+)\x00", head)
            if m:
                ident = self.new_id("proof-of-" + m.group(1))
            elif self.blocks and self.blocks[-1]["kind"] == "stmt":
                ident = self.new_id("proof-" + self.blocks[-1]["id"])
            else:
                ident = self.new_id(f"{self.heading_id}-proof")
            h = f'<div class="proof" id="{ident}">{body}</div>'
            self.emit("proof", h, nd.start, nd.end, ident, {"title": head})
            return None
        return f'<div class="proof">{body}</div>'


    def list_env(self, nd):
        n = nd.name
        fmt = None
        if nd.opt:
            m = re.search(r"label=([^,\]]+)", nd.opt)
            if m:
                fmt = m.group(1).strip()
        items, cur, cur_label = [], None, None
        for x in nd.body:
            if x.kind == "cmd" and x.name == "item":
                if cur is not None:
                    items.append((cur_label, cur))
                cur, cur_label = [], x.opt
                continue
            if cur is None:
                if (x.kind == "text" and not x.text.strip()) or x.kind == "par":
                    continue
                raise ConvError(f"content before first \\item (line {self.line_of(x.start)})")
            cur.append(x)
        if cur is not None:
            items.append((cur_label, cur))
        lis = []
        for k, (lab, content) in enumerate(items, 1):
            inner = self.render_container(content)
            if n == "enumerate":
                if lab is not None:
                    label_html, _ = self.inline(lab)
                elif fmt == r"(\arabic*)":
                    label_html = f"({k})"
                elif fmt == r"(\roman*)":
                    label_html = f"({roman(k)})"
                elif fmt is None:
                    label_html = f"{k}."
                else:
                    raise ConvError(f"unsupported enumerate label {fmt}")
                inner = self.merge_head(inner, f'<span class="item-label">{label_html}</span>')
            lis.append(f"<li>{inner}</li>")
        tag = "ol" if n == "enumerate" else "ul"
        cls = "enumerate" if n == "enumerate" else "itemize"
        return f'<{tag} class="{cls}">' + "".join(lis) + f"</{tag}>"

    def tabular(self, nd):
        spec = nd.args[-1]
        cols = self.parse_colspec(spec)
        raw = nd.text
        base = nd.extra["raw_start"]
        rows = self.split_top(raw, "\\\\")
        body_rows, hlines_before = [], []
        pending_hline = 0
        out_rows = []
        for r in rows:
            rr = r.strip()
            n_h = 0
            while rr.startswith("\\hline"):
                n_h += 1
                rr = rr[len("\\hline"):].strip()
            if rr == "":
                pending_hline += n_h
                continue
            cells = self.split_top(rr, "&")
            if len(cells) != len(cols):
                raise ConvError(f"table row has {len(cells)} cells, spec has {len(cols)}: {rr[:60]}")
            out_rows.append((pending_hline + n_h, cells))
            pending_hline = 0
        trailing = pending_hline
        grid = "|" in spec
        html_rows = []
        # The first row is a header when a rule separates it from the second row
        # (all tables in the paper use \hline header \hline rows \hline).
        header_first = len(out_rows) > 1 and out_rows[1][0] > 0
        for idx, (hl, cells) in enumerate(out_rows):
            is_header = idx == 0 and header_first
            tds = []
            for c, align in zip(cells, cols):
                p = Parser(c.strip(), 0)
                nodes = p.parse()
                h, labs = self.inline(nodes)
                if labs:
                    raise ConvError("label in table cell")
                tag = "th" if is_header else "td"
                scope = ' scope="col"' if is_header else ""
                tds.append(f'<{tag}{scope} class="al-{align}">{h.strip()}</{tag}>')
            rowcls = []
            if hl:
                rowcls.append("rule-above")
            if idx == len(out_rows) - 1 and trailing:
                rowcls.append("rule-below")
            cls = f' class="{" ".join(rowcls)}"' if rowcls else ""
            html_rows.append((is_header, f"<tr{cls}>" + "".join(tds) + "</tr>"))
        thead = "".join(r for hd, r in html_rows if hd)
        tbody = "".join(r for hd, r in html_rows if not hd)
        gcls = " grid" if grid else ""
        return (f'<table class="paper-table{gcls}">' + (f"<thead>{thead}</thead>" if thead else "")
                + f"<tbody>{tbody}</tbody></table>")

    @staticmethod
    def parse_colspec(spec):
        s = spec.replace("@{}", "")
        cols, i = [], 0
        while i < len(s):
            c = s[i]
            if c in "|":
                i += 1
                continue
            if c == ">":
                j = s.index("{", i)
                depth, k = 0, j
                while True:
                    if s[k] == "{":
                        depth += 1
                    elif s[k] == "}":
                        depth -= 1
                        if depth == 0:
                            break
                    k += 1
                i = k + 1
                continue
            if c in "lcrYX":
                cols.append({"l": "left", "c": "center", "r": "right", "Y": "left", "X": "left"}[c])
                i += 1
                continue
            if c == "p":
                j = s.index("}", i)
                cols.append("left")
                i = j + 1
                continue
            if c in " \t\n":
                i += 1
                continue
            raise ConvError(f"unsupported column spec {spec}")
        return cols

    @staticmethod
    def split_top(raw, sep):
        parts, depth, cur, i, inmath = [], 0, [], 0, False
        while i < len(raw):
            if raw.startswith(sep, i) and depth == 0 and not inmath:
                parts.append("".join(cur))
                cur = []
                i += len(sep)
                continue
            c = raw[i]
            if c == "\\" and not raw.startswith(sep, i):
                cur.append(raw[i:i + 2])
                i += 2
                continue
            if c == "$":
                inmath = not inmath
            elif c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
            cur.append(c)
            i += 1
        parts.append("".join(cur))
        return parts

    def figure_env(self, nd, top, kind):
        self.scope.append({"label": self.scope[-1]["label"]})
        content_html, caption_html, labels = [], None, []
        number = None
        for x in self.flatten_groups(nd.body):
            if x.kind == "par" or (x.kind == "text" and not x.text.strip()):
                continue
            if x.kind == "cmd" and x.name in ("centering", "small", "footnotesize"):
                continue
            if x.kind == "cmd" and x.name == "caption":
                self.counters[kind] += 1
                number = str(self.counters[kind])
                self.scope[-1]["label"] = number
                caption_html, labs = self.inline(x.args[0])
                if labs:
                    raise ConvError("label inside caption")
                continue
            if x.kind == "cmd" and x.name == "label":
                labels.append(x.args[0])
                continue
            if x.kind == "env" and x.name == "tikzpicture":
                content_html.append(("tikz", x))
                continue
            if x.kind == "cmd" and x.name == "includegraphics":
                content_html.append(("img", x))
                continue
            if x.kind == "env" and x.name in ("tabular", "tabularx"):
                content_html.append(("tab", self.tabular(x)))
                continue
            raise ConvError(f"unsupported content in {kind}: {x} (line {self.line_of(x.start)})")
        if number is None or len(labels) != 1:
            raise ConvError(f"{kind} needs one caption and one label (line {self.line_of(nd.start)})")
        ident = self.claim_id(labels[0])
        self.set_label(labels[0], kind, ident)
        self.scope.pop()
        name = re.sub(r"^(fig|table|tab):", "", labels[0])
        inner = []
        for t, x in content_html:
            if t == "tab":
                inner.append(f'<div class="table-wrap">{x}</div>')
                continue
            meta = self.fig_meta.get(labels[0])
            if not meta or not meta.get("alt"):
                raise ConvError(f"missing alt text for {labels[0]} in figures.yaml")
            if t == "tikz":
                self.tikz[name] = {"label": labels[0], "tex": x.text,
                                   "lines": [self.line_of(x.start), self.line_of(x.end - 1)]}
                srcfile = f"tikz:{name}"
            else:
                srcfile = x.args[0]
            asset = f"assets/figures/{name}.svg"
            alt = html.escape(meta["alt"])
            inner.append(f'<img class="fig-img fig-{name}" src="{asset}" alt="{alt}" '
                         f'width="{meta.get("width", 760)}" loading="lazy">')
            self.figures.append({"label": labels[0], "number": number, "kind": t,
                                 "source": srcfile, "asset": asset,
                                 "lines": [self.line_of(nd.start), self.line_of(nd.end - 1)]})
        word = "Figure" if kind == "figure" else "Table"
        cap = (f'<figcaption><span class="cap-label">{word} {number}:</span> '
               f"{caption_html.strip()}</figcaption>")
        h = f'<figure class="paper-{kind}" id="{ident}">' + "".join(inner) + cap + "</figure>"
        self.inventory["figures" if kind == "figure" else "tables"] += 1
        if top:
            self.emit(kind, h, nd.start, nd.end, ident,
                      {"number": number, "display_name": f"{word} {number}", "caption": caption_html})
            return None
        return h

    def flatten_groups(self, nodes):
        out = []
        for x in nodes:
            if x.kind == "group":
                out += self.flatten_groups(x.body)
            else:
                out.append(x)
        return out

    def bibliography(self, nd):
        entries, cur = [], None
        for x in nd.body:
            if x.kind == "cmd" and x.name == "bibitem":
                if cur:
                    entries.append(cur)
                cur = {"opt": x.opt, "key": x.args[0], "nodes": [], "start": x.start}
                continue
            if cur is None:
                if x.kind == "par" or (x.kind == "text" and not x.text.strip()):
                    continue
                raise ConvError("text before first bibitem")
            cur["nodes"].append(x)
            cur["end"] = x.end
        if cur:
            entries.append(cur)
        lis = []
        self.bib = []
        for e in entries:
            nodes = [n for n in e["nodes"] if n.kind != "par"]
            parts, cur_part = [], []
            for n in nodes:
                if n.kind == "cmd" and n.name == "newblock":
                    parts.append(cur_part)
                    cur_part = []
                else:
                    cur_part.append(n)
            parts.append(cur_part)
            segs = []
            for p in parts:
                h, _ = self.inline(p)
                h = re.sub(r"\s+", " ", h).strip()
                if h:
                    segs.append(h)
            body = " ".join(segs)
            key = e["key"]
            ident = self.claim_id(f"bib-{key}")
            lis.append(f'<li id="{ident}">{body}</li>')
            self.bib.append({"key": key, "id": ident, "html": body,
                             "text": re.sub(r"<[^>]+>", "", body),
                             "short": self.cites[key][0], "year": self.cites[key][1]})
        self.ids.add("references")
        h = ('<section class="references" id="references"><h2 class="sec-h unnumbered">References</h2>'
             '<ol class="bib">' + "".join(lis) + "</ol></section>")
        self.heading_id = "references"
        self.emit("bibliography", h, nd.start, nd.end, "references")
        return None


# --------------------------------------------------------------------------------------
# Preamble
# --------------------------------------------------------------------------------------

def parse_preamble(pre, pre_stripped):
    macros = {}
    for m in re.finditer(r"\\newcommand\{\\(\w+)\}", pre_stripped):
        p = Parser(pre_stripped, 0)
        p.i = m.end()
        body, _ = p.read_group_raw()
        macros["\\" + m.group(1)] = body
    title = re.search(r"\\title\{(.*?)\}\s*\n\s*\\author", pre, re.S).group(1)
    author = re.search(r"\\author\{(.*?)\}\s*\n\s*\\ShortHeadings", pre, re.S).group(1)
    return macros, title, author


def parse_cites(body):
    cites = {}
    for m in re.finditer(r"\\bibitem\[([^\]]*)\]\{([^}]*)\}", body):
        opt, key = m.group(1), m.group(2)
        mm = re.match(r"(.*?)\((.*?)\)(.*)$", opt)
        if not mm:
            raise ConvError(f"bad bibitem option {opt}")
        au = mm.group(1)
        au = au.replace("~", " ")
        au = au.replace("{\\aa}", "\u00e5").replace("{\\\"o}", "\u00f6").replace("{\\o}", "\u00f8")
        au = au.replace(r"\v{C}{\'i}\v{z}ek", "Čížek")
        if "\\" in au or "{" in au:
            raise ConvError(f"unsupported markup in citation name {au}")
        yr = mm.group(2).replace("--", "\u2013")
        cites[key] = (au.strip(), yr)
    return cites


def render_title_author(title_raw, author_raw, R):
    t = Parser(title_raw, 0).parse()
    title_html, _ = R.inline(t)
    title_text = re.sub(r"<br>", " ", title_html)
    title_text = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", "", title_text)).strip()
    # author: \name X \email Y \\ \addr L1\\ L2 \\ ...
    m = re.match(r"\s*\\name\s+(.*?)\s*\\email\s+(\S+)\s*\\\\\s*\\addr\s+(.*)$", author_raw, re.S)
    if not m:
        raise ConvError("unexpected author block")
    name_html, _ = R.inline(Parser(m.group(1), 0).parse())
    email = m.group(2)
    addr_lines = [x.strip() for x in m.group(3).split("\\\\")]
    addr_html = []
    for a in addr_lines:
        h, _ = R.inline(Parser(a, 0).parse())
        addr_html.append(h.strip())
    return {"title_html": re.sub(r"\s*<br>\s*", "<br>", title_html.strip()),
            "title_text": title_text, "author_name_html": name_html.strip(),
            "author_name_text": re.sub(r"<[^>]+>", "", name_html).strip(),
            "email": email, "address": addr_html}


# --------------------------------------------------------------------------------------
# KaTeX
# --------------------------------------------------------------------------------------

SUPERSCRIPT = str.maketrans("0123456789", "\u2070\u00b9\u00b2\u00b3\u2074\u2075\u2076\u2077\u2078\u2079")


def math_plain(tex, macros):
    """A plain-text rendering of a short formula, for page titles and accessible labels
    only (the article itself uses KaTeX).  Falls back to the TeX source."""
    t = tex
    for k, v in macros.items():
        t = re.sub(re.escape(k) + r"(?![A-Za-z])", lambda m, v=v: v, t)
    t = re.sub(r"\\(mathrm|mathsf|mathbf|mathcal|text|operatorname)\{([^{}]*)\}", r"\2", t)
    t = re.sub(r"\^\{?(\d)\}?", lambda m: m.group(1).translate(SUPERSCRIPT), t)
    for k, v in {"\\in": "\u2208", "\\ge": "\u2265", "\\le": "\u2264", "\\oplus": "\u2295",
                 "\\Delta": "\u0394", "\\sigma": "\u03c3", "\\pi": "\u03c0"}.items():
        t = t.replace(k, v)
    return t.replace("{", "").replace("}", "").strip()


def katex_macros(macros):
    out = {}
    for k, v in macros.items():
        if "\\textsc" in v:
            continue   # \FSQI is used only inside TikZ text
        out[k] = v
    return out


def render_math(items, macros):
    req = {"macros": macros, "items": [{"id": m["id"], "tex": m["tex"], "display": m["display"]}
                                       for m in items]}
    p = subprocess.run(["node", os.path.join(HERE, "katex_render.mjs")], input=json.dumps(req),
                       capture_output=True, text=True, cwd=HERE)
    if p.returncode != 0:
        raise ConvError("KaTeX renderer failed: " + p.stderr[-2000:])
    res = json.loads(p.stdout)
    if res["errors"]:
        msgs = []
        for e in res["errors"]:
            line = next(m["line"] for m in items if m["id"] == e["id"])
            msgs.append(f"line {line}: {e['message']}  [{e['tex'][:80]}]")
        raise ConvError("KaTeX rejected math:\n  " + "\n  ".join(msgs))
    return res["html"], res["katexVersion"]


# --------------------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------------------

def convert(tex_path, figures_yaml, out_dir):
    import yaml
    raw = open(tex_path, encoding="utf-8").read()
    sha = hashlib.sha256(raw.encode("utf-8")).hexdigest()
    stripped, lines = strip_comments(raw)
    b0 = stripped.index("\\begin{document}") + len("\\begin{document}")
    b1 = stripped.index("\\end{document}")
    pre = raw[:raw.index("\\begin{document}")]
    macros, title_raw, author_raw = parse_preamble(pre, stripped[:stripped.index("\\begin{document}")])
    cites = parse_cites(stripped[b0:b1])
    fig_meta = yaml.safe_load(open(figures_yaml, encoding="utf-8"))
    R = Renderer(stripped, lines, fig_meta, cites)
    R.macros = macros
    R.runins = []
    R.last_heading_block = None
    R.last_runin = None
    front = render_title_author(title_raw, author_raw, R)
    body_nodes = Parser(stripped[b0:b1], b0).parse()
    R.render_container(body_nodes, top=True)

    # resolve run-in headings (ids may have been replaced by labels)
    for k, (holder, title) in enumerate(R.runins):
        ph = f"\x00RUNIN:{k}\x00"
        head = (f'<span class="runin-head" role="heading" aria-level="5" id="{holder["id"]}">'
                f"{title}</span>")
        for blk in R.blocks:
            if ph in blk["html"]:
                blk["html"] = blk["html"].replace(ph, head)
                blk.setdefault("runin_ids", []).append(holder["id"])
                blk["runin_title"] = re.sub(r"<[^>]+>", "", title)
                break
        else:
            raise ConvError("run-in heading lost")
    # resolve references
    unresolved = []

    def refsub(m):
        lab = m.group(1)
        if lab not in R.labels:
            unresolved.append(lab)
            return "??"
        info = R.labels[lab]
        return f'<a class="ref" href="#{info["id"]}">{info["number"]}</a>'
    mtex = {m["id"]: m["tex"] for m in R.math}

    def plain(h):
        h = re.sub(r"\x00MATH:(m\d+)\x00", lambda m: math_plain(mtex[m.group(1)], macros), h)
        h = re.sub(r"\x00REF:([^\x00]+)\x00",
                   lambda m: R.labels.get(m.group(1), {}).get("number", "??"), h)
        h = re.sub(r"\x00RUNIN:\d+\x00", "", h)
        return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", "", h))).strip()
    for blk in R.blocks:
        for key in ("title", "caption", "runin_title"):
            if blk.get(key):
                blk[key + "_text"] = plain(blk[key])
        if blk["kind"] == "proof":
            blk["title_text"] = plain(blk["title"]).rstrip(".")
    for blk in R.blocks:
        for key in ("html", "title", "caption"):
            if blk.get(key):
                blk[key] = re.sub(r"\x00REF:([^\x00]+)\x00", refsub, blk[key])
    if unresolved:
        raise ConvError(f"unresolved references: {sorted(set(unresolved))}")
    # math
    kmacros = katex_macros(macros)
    rendered, kver = render_math(R.math, kmacros)
    front_html = {}
    for blk in R.blocks:
        for key in ("html", "title", "caption"):
            if blk.get(key):
                blk[key] = re.sub(r"\x00MATH:(m\d+)\x00", lambda m: rendered[m.group(1)], blk[key])
                if "\x00" in blk[key]:
                    raise ConvError("unresolved placeholder")
    for k in ("title_html", "author_name_html"):
        front[k] = re.sub(r"\x00MATH:(m\d+)\x00", lambda m: rendered[m.group(1)], front[k])
    # labelled numbers for run-in paragraph labels: number = enclosing section (already set)
    # sanity: every heading-level structure
    os.makedirs(out_dir, exist_ok=True)
    tikz_dir = os.path.join(out_dir, "tikz")
    os.makedirs(tikz_dir, exist_ok=True)
    for name, t in R.tikz.items():
        with open(os.path.join(tikz_dir, name + ".tex"), "w", encoding="utf-8") as f:
            f.write(t["tex"])
    tikz_libs = re.search(r"\\usetikzlibrary\{([^}]*)\}", pre).group(1)
    article = {
        "converter_version": CONVERTER_VERSION,
        "source_file": os.path.basename(tex_path),
        "source_sha256": sha,
        "katex_version": kver,
        "front": front,
        "macros": macros,
        "katex_macros": kmacros,
        "tikz_libraries": tikz_libs,
        "tikz": {k: {"label": v["label"], "lines": v["lines"]} for k, v in R.tikz.items()},
        "blocks": R.blocks,
        "labels": R.labels,
        "figures": R.figures,
        "bibliography": R.bib,
        "cited_keys": sorted(set(R.cited)),
        "uncited_keys": sorted(set(cites) - set(R.cited)),
        "unlabelled_numbered": R.unlabelled,
        "math_count": len(R.math),
        "math": [{"id": m["id"], "line": m["line"], "display": m["display"], "tex": m["tex"]}
                 for m in R.math],
        "math_adaptations": R.math_adaptations,
        "inventory": {**R.inventory, "theorem_envs": len(R.inventory["theorem_envs"])},
    }
    with open(os.path.join(out_dir, "article.json"), "w", encoding="utf-8") as f:
        json.dump(article, f, ensure_ascii=False, indent=1)
    return article


def main():
    if len(sys.argv) != 4:
        print(__doc__)
        sys.exit(2)
    try:
        a = convert(sys.argv[1], sys.argv[2], sys.argv[3])
    except ConvError as e:
        print("CONVERSION FAILED:", e, file=sys.stderr)
        sys.exit(1)
    inv = a["inventory"]
    print(f"converted {a['source_file']} ({a['source_sha256'][:12]}…): {len(a['blocks'])} blocks, "
          f"{len(a['labels'])} labels, {a['math_count']} formulas, {len(a['figures'])} figure images, "
          f"{len(a['bibliography'])} references; inventory {inv}")


if __name__ == "__main__":
    main()
