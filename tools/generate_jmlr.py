from pathlib import Path
import re,json,hashlib,shutil
root=Path(__file__).resolve().parent.parent; here=root/'input'
src=here/'canonical_paper.tex'; s=src.read_text()
# Formatting-only adapter. Edit the canonical manuscript, then regenerate this copy.
s=s.replace(r'\documentclass[11pt]{article}',r'\documentclass[twoside,11pt]{article}')
s=s.replace('% Article layout shared with the term-coding preprints.\n'+r'\usepackage[margin=1in]{geometry}', '% JMLR reading copy; no publication/editor metadata is asserted.')
s=s.replace(r'\usepackage{amsmath,amssymb,amsthm,mathtools}',r'''\usepackage{amsmath,amssymb,amsthm,mathtools}
\let\savedproof\proof
\let\endsavedproof\endproof
\usepackage[preprint]{jmlr2e}
\let\proof\savedproof
\let\endproof\endsavedproof
\hypersetup{hidelinks,pdftitle={Overcoming a Learning Bottleneck in Impartial Games: A Circuit Complexity Approach},pdfauthor={Soren Riis},pdfkeywords={impartial games, NIM, circuit complexity, quantised inference, learning bottlenecks}}
\usepackage{tabularx}
\newcolumntype{Y}{>{\raggedright\arraybackslash}X}''')
s=s.replace(r'\usepackage[numbers]{natbib}','').replace(r'\usepackage[hidelinks]{hyperref}','').replace(r'\bibpunct{[}{]}{,}{n}{}{,}',r'\bibpunct{(}{)}{;}{a}{,}{,}')
a=s.index(r'\theoremstyle{plain}');b=s.index(r'\numberwithin{equation}',a)
s=s[:a]+r'\numberwithin{theorem}{section}'+'\n'+s[b:]
a=s.index(r'\author{');b=s.index(r'\begin{document}',a)
s=s[:a]+r'''\author{\name S{\o}ren Riis \email s.riis@qmul.ac.uk \\
\addr Centre for Fundamentals of AI and Computational Theory\\
Queen Mary University of London\\
Mile End Road, London E1 4NS, United Kingdom}
\ShortHeadings{Learning Bottlenecks in Impartial Games}{Riis}
\firstpageno{1}

'''+s[b:]
s=s.replace(r'\paragraph{Keywords.}'+'\n'+'Impartial games; NIM; circuit complexity; quantised inference; learning bottlenecks.',r'''\begin{keywords}
Impartial games; NIM; circuit complexity; quantised inference; learning bottlenecks.
\end{keywords}''')
# Preserve prose/citation keys; use parenthetical author-year citation display.
s=s.replace(r'\cite{',r'\citep{')
# Preserve all entries, add natbib metadata and alphabetise; references follow appendices.
labels={
'friedman2017challenge':'Friedman(2017a)', 'friedman2017deeplearning':'Friedman(2017b)',
'cizek2026sprouts':r'\v{C}{\'i}\v{z}ek et~al.(2026)\v{C}{\'i}\v{z}ek, Balko, and Schmid',
'nowakowski2025unsolved':'Nowakowski(2025)',
'ajtai1993approxcount':'Ajtai(1993)', 'berlekamp2001winningways':'Berlekamp et~al.(2001--2004)Berlekamp, Conway, and Guy',
'daniely2020parities':'Daniely and Malach(2020)', 'furst1984parity':'Furst et~al.(1984)Furst, Saxe, and Sipser',
'hao2022hardattention':'Hao et~al.(2022)Hao, Angluin, and Frank','hastad2014correlation':r'H{\aa}stad(2014)','hastad1986thesis':r'H{\aa}stad(1986)',
'linial1993constant':'Linial et~al.(1993)Linial, Mansour, and Nisan','karpov2023setalternating':r'Karpov et~al.(2023)Karpov, Markstr{\"o}m, Riis, and Zhou',
'merrill2021transformer':'Merrill and Sabharwal(2024)','minsky1969perceptrons':'Minsky and Papert(1969)','mnih2015humanlevel':'Mnih et~al.(2015)',
'jacob2018integeronly':'Jacob et~al.(2018)','dettmers2022llmint8':'Dettmers et~al.(2022)','nesterov1983method':'Nesterov(1983)',
'ngo2018worstcasejoins':'Ngo et~al.(2018)','rahaman2019spectral':'Rahaman et~al.(2019)','razborov1987lower':'Razborov(1987)',
'schaefer1978games':'Schaefer(1978)','schrittwieser2020muzero':'Schrittwieser et~al.(2020)','silver2016alphago':'Silver et~al.(2016)',
'silver2018alphazero':'Silver et~al.(2018)','silver2017alphagozero':'Silver et~al.(2017)','smolensky1987algebraic':'Smolensky(1987)',
'tal2015tight':'Tal(2015)','thornton1996parity':'Thornton(1996b)','thornton1996bp':'Thornton(1996a)',
'xu2019frequency':'Xu et~al.(2019)','zhou2024phd':'Zhou(2024)','zhou2024cdl':r'Zhou et~al.(2024)Zhou, Markstr{\"o}m, and Riis',
'zhou2022impartial':'Zhou and Riis(2026)','zhou2023parity':'Zhou and Riis(2023)'}
a=s.index(r'\begin{thebibliography}');b=s.index(r'\end{thebibliography}',a)+len(r'\end{thebibliography}')
entries=re.findall(r'\\bibitem\{([^}]+)\}(.*?)(?=\\bibitem|\\end\{thebibliography\})',s[a:b],re.S)
assert len(entries)==len(labels)
def sortkey(e):
 k=e[0]
 if k.startswith('zhou'): return ('Zhou',{'zhou2024phd':'0','zhou2024cdl':'1','zhou2023parity':'2','zhou2022impartial':'3'}[k])
 label=labels[k].replace(r'H{\aa}stad','Hastad').replace(r'\v{C}{\'i}\v{z}ek','Cizek');return (label.split('(')[0].replace(' et~al.','~'),label.split('(')[1])
bib='\\begin{thebibliography}{99}\n\n'+''.join('\\bibitem['+labels[k]+']{'+k+'}'+v for k,v in sorted(entries,key=sortkey))+'\\end{thebibliography}\n'
s=s[:a]+s[b:];s=s.replace(r'\end{document}',bib+'\n'+r'\end{document}')
# Funding is an author declaration, not something inferred from lack of a record.
s=s.replace(r'\appendix',r'''\noindent\begin{minipage}{\linewidth}
\acks{The author received no dedicated funding for this work.}
\end{minipage}

\appendix''',1)
# Ensure diagram labels are at least 9pt; do not shrink the restoration figure.
s=s.replace(r'font=\scriptsize',r'font=\footnotesize').replace(r'font=\tiny',r'font=\footnotesize')
a=s.index(r'\resizebox{\linewidth}{!}{%');b=s.index(r'\caption{A worked restoration example',a)
fig=s[a:b].replace('\\resizebox{\\linewidth}{!}{%\n','',1).replace('\\end{tikzpicture}%\n}\n','\\end{tikzpicture}\n').replace('right=3.2cm','right=2.8cm')
s=s[:a]+fig+s[b:]
# Wrap the architecture table rather than scaling text below 9pt.
a=s.index(r'\resizebox{\linewidth}{!}{%');b=s.index(r'\caption{Neural network architecture',a)
s=s[:a]+r'''{\footnotesize
\begin{tabularx}{\linewidth}{@{}lYYY@{}}
\hline
\textbf{Component} & \textbf{Type} & \textbf{Dimensions} & \textbf{Activation/}\allowbreak\textbf{Normalisation} \\
\hline
Input & State representation & Two-frame: $2Nk$ bits (1F: $Nk$) & None \\
Hidden 1 & Fully Connected & 1F: $Nk\to H$; 2F: $2Nk\to H$ & LayerNorm + ReLU \\
Hidden 2 & Fully Connected & $H\to H$ & ReLU \\
Policy Head & Linear Output & $H\to N\cdot2^k$ & Raw logits; Log-Softmax in loss \\
\hline
\end{tabularx}}
'''+s[b:]
s=s.replace('figValAccH20k4.png','figValAccH20k4.pdf').replace('figTestAccCkptsH20k4.png','figTestAccCkptsH20k4.pdf')
out=here/'jmlr_source/paper_jmlr.tex';out.write_text(s)
(here/'jmlr_source/figures').mkdir(exist_ok=True)
for name in re.findall(r'\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}',s):
 assert (here/'jmlr_source/figures'/name).exists(), 'Run render_figures.py first'
assert re.findall(r'\\label\{([^}]+)\}',s)==re.findall(r'\\label\{([^}]+)\}',src.read_text())
(here/'source_manifest.json').write_text(json.dumps(dict(canonical_source=str(src),canonical_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),jmlr_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),style_sha256=hashlib.sha256((here/'jmlr_source/jmlr2e.sty').read_bytes()).hexdigest(),style_url='https://raw.githubusercontent.com/JmlrOrg/jmlr-style-file/master/jmlr2e.sty',changes='Formatting adapter only: title, address, style, running heads, citation labels/order, reference placement, figure/table typography; author funding declaration included.'),indent=2)+'\n')
print(out)
