#!/usr/bin/env python3
"""Build the article's figure images as SVG.

    python3 tools/build_figures.py <generated-dir> <jmlr-source-dir> <assets-out-dir>

* TikZ figures: each tikzpicture extracted by latex2html.py (generated/tikz/<name>.tex, the
  exact source text) is compiled with pdflatex in a tightly cropped document that uses the
  paper's own packages, TikZ libraries and macros, then converted to SVG with pdftocairo.
* Plot figures: the vector PDFs included by the manuscript (figures/*.pdf, the replotted
  saved-data figures listed in input/figure_provenance.json) are converted to SVG with
  pdftocairo.  No data are re-plotted.
Writes <assets-out-dir>/<name>.svg and <generated-dir>/figures_manifest.json (input and
output SHA-256 for each figure).  Fails if any compilation fails.
"""
import hashlib, json, os, shutil, subprocess, sys

def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()

def run(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if p.returncode != 0:
        sys.stderr.write(p.stdout[-3000:] + p.stderr[-2000:])
        raise SystemExit(f"FAILED: {' '.join(cmd)}")

def main(gen, srcdir, out):
    gen, srcdir, out = (os.path.abspath(x) for x in (gen, srcdir, out))
    art = json.load(open(os.path.join(gen, "article.json"), encoding="utf-8"))
    os.makedirs(out, exist_ok=True)
    work = os.path.join(gen, "figbuild")
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    macros = "".join(f"\\newcommand{{{k}}}{{{v}}}\n" for k, v in art["macros"].items())
    manifest = []
    for name, info in art["tikz"].items():
        body = open(os.path.join(gen, "tikz", name + ".tex"), encoding="utf-8").read()
        # Measure the actual picture and ship one page with a 6pt border. This uses
        # standard LaTeX/pdfTeX and does not require the optional standalone class.
        doc = ("\\documentclass[11pt]{article}\n"
               "\\usepackage{amsmath,amssymb,mathtools}\n\\usepackage{tikz}\n"
               f"\\usetikzlibrary{{{art['tikz_libraries']}}}\n" + macros +
               "\\newsavebox{\\figurebox}\n\\begin{document}\n"
               "\\sbox{\\figurebox}{\\begin{tikzpicture}" + body + "\\end{tikzpicture}}\n"
               "\\pdfpagewidth=\\dimexpr\\wd\\figurebox+12pt\\relax\n"
               "\\pdfpageheight=\\dimexpr\\ht\\figurebox+\\dp\\figurebox+12pt\\relax\n"
               "\\pdfhorigin=0pt\\pdfvorigin=0pt\n"
               "\\shipout\\vbox{\\kern6pt\\hbox{\\kern6pt\\usebox{\\figurebox}\\kern6pt}\\kern6pt}\n"
               "\\end{document}\n")
        tex = os.path.join(work, name + ".tex")
        open(tex, "w", encoding="utf-8").write(doc)
        run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", name + ".tex"], work)
        svg = os.path.join(out, name + ".svg")
        run(["pdftocairo", "-svg", name + ".pdf", svg], work)
        manifest.append({"label": info["label"], "kind": "tikz", "source": f"paper_jmlr.tex lines {info['lines'][0]}-{info['lines'][1]}",
                         "source_sha256": hashlib.sha256(body.encode()).hexdigest(),
                         "output": f"assets/figures/{name}.svg", "output_sha256": sha(svg),
                         "method": "pdflatex (measured picture, 6pt border, paper macros) + pdftocairo -svg"})
    for fig in art["figures"]:
        if fig["kind"] != "img":
            continue
        pdf = os.path.join(srcdir, "figures", fig["source"])
        name = os.path.basename(fig["asset"])[:-4]
        svg = os.path.join(out, name + ".svg")
        run(["pdftocairo", "-svg", pdf, svg], work)
        manifest.append({"label": fig["label"], "kind": "plot", "source": f"figures/{fig['source']}",
                         "source_sha256": sha(pdf), "output": fig["asset"], "output_sha256": sha(svg),
                         "method": "pdftocairo -svg of the manuscript's vector PDF (no re-plotting)"})
    json.dump(manifest, open(os.path.join(gen, "figures_manifest.json"), "w"), indent=1)
    print(f"built {len(manifest)} figure SVGs into {out}")

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print(__doc__); sys.exit(2)
    main(*sys.argv[1:])
