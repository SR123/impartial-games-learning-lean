#!/usr/bin/env python3
"""Phase-8 source statistics (run from anywhere: python3 source_stats.py PHASE8_SOURCE_STATS.json) and axiom-report checks (conventions of the phase-7 audit's
scan_audit.py: comment/string-aware stripping; theorem/lemma declarations counted in code)."""
import re, json, sys
from pathlib import Path

lean = Path(__file__).resolve().parent.parent
p8 = lean / 'phase8'
modules = [
 ('phase1', lean, 'NimCore'), ('phase1', lean, 'NimRollout'),
 ('phase2', lean/'phase2', 'NimGame'), ('phase2', lean/'phase2', 'NimProbability'),
] + [('phase3', lean/'phase3', m) for m in 'NimAttain Circuit NimRecurrent BitBridge NimCorrBridge AttainCircuit'.split()] \
  + [('phase4', lean/'phase4', m) for m in 'FiniteNet BinaryReadout ParityCircuit Controller ControllerBits SharedCircuit SelectCircuit LocalRestore Foundation Coverage'.split()] \
  + [('phase5', lean/'phase5', m) for m in 'PriorityEncoder ThresholdNet ThresholdInst WholeGame'.split()] \
  + [('phase6', lean/'phase6', m) for m in 'Family Barrier RolloutExec Bypass Classical BoardStore Windows Misc'.split()] \
  + [('phase7', lean/'phase7', m) for m in 'NoiseModel Shootout'.split()] \
  + [('phase8', p8, m) for m in 'WeakMastery Fourier RealNoise RealFourier'.split()]

def strip(s):
    out=[];i=0;nest=0;instr=False
    while i<len(s):
        if nest:
            if s[i:i+2]=='/-':nest+=1;i+=2
            elif s[i:i+2]=='-/':nest-=1;i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif instr:
            if s[i]=='\\':out.extend('  ');i+=2
            elif s[i]=='"':instr=False;out.append(' ');i+=1
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s[i:i+2]=='/-':nest=1;out.extend('  ');i+=2
        elif s[i:i+2]=='--':
            j=s.find('\n',i)
            if j<0:j=len(s)
            out.extend(' '*(j-i));i=j
        elif s[i]=='"':instr=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    return ''.join(out)

rows=[]
for phase, d, m in modules:
    s=(d/(m+'.lean')).read_text(); clean=strip(s)
    log=(p8/'logs'/(m+'.log')).read_text()
    names=re.findall(r"\b(?:theorem|lemma)\s+([\w'.]+)",clean)
    reports=re.findall(r"'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    printed={n for n,_ in reports}
    missing=[n for n in names if not any(p==n or p.endswith('.'+n) for p in printed)]
    axsets={}
    bad=[]
    for n,ax in reports:
        k=', '.join(x.strip() for x in ax.split(',') if x.strip()) or '(none)'
        axsets[k]=axsets.get(k,0)+1
        extra=set(x.strip() for x in ax.split(',') if x.strip())-{'propext','Classical.choice','Quot.sound'}
        if extra: bad.append([n,sorted(extra)])
    susp=[x.group() for x in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|run_tac)\b|#eval|#run',clean)]
    errors=len(re.findall(r'\berror\b', log))
    rows.append(dict(module=m, phase=phase, theorems=len(names), axiom_reports=len(reports), missing_reports=missing,
        unexpected_axioms=bad, suspicious=susp, log_errors=errors, axiom_sets=axsets,
        lines=len(s.splitlines()), nonblank_lines=sum(bool(l.strip()) for l in s.splitlines()),
        code_lines=sum(bool(l.strip()) for l in clean.splitlines()),
        code_lines_without_axiom_prints=sum(bool(l.strip()) and not l.lstrip().startswith('#print axioms') for l in clean.splitlines()),
        definitions=len(re.findall(r"\bdef\s+[\w'.]+",clean))))

def tot(rs, k): return sum(r[k] for r in rs)
out=[]
out.append('%-8s %7s %9s %8s %8s %7s' % ('phase','modules','theorems','lines','code*','defs'))
for ph in ['phase1','phase2','phase3','phase4','phase5','phase6','phase7','phase8']:
    rs=[r for r in rows if r['phase']==ph]
    out.append('%-8s %7d %9d %8d %8d %7d' % (ph, len(rs), tot(rs,'theorems'), tot(rs,'lines'), tot(rs,'code_lines_without_axiom_prints'), tot(rs,'definitions')))
out.append('%-8s %7d %9d %8d %8d %7d' % ('TOTAL', len(rows), tot(rows,'theorems'), tot(rows,'lines'), tot(rows,'code_lines_without_axiom_prints'), tot(rows,'definitions')))
out.append('')
out.append('nonblank source lines: %d; code lines incl. #print axioms: %d; axiom reports: %d' % (tot(rows,'nonblank_lines'), tot(rows,'code_lines'), tot(rows,'axiom_reports')))
out.append('')
out.append('Per module (phase 8): ' + '; '.join('%s %d theorems, %d lines, %d code*' % (r['module'], r['theorems'], r['lines'], r['code_lines_without_axiom_prints']) for r in rows if r['phase']=='phase8'))
issues=[r['module'] for r in rows if r['missing_reports'] or r['unexpected_axioms'] or r['suspicious'] or r['log_errors']]
out.append('Issues (missing reports / unexpected axioms / forbidden tokens / log errors): ' + (', '.join(issues) if issues else 'none'))
agg={}
for r in rows:
    if r['phase']=='phase8':
        for k,v in r['axiom_sets'].items(): agg[k]=agg.get(k,0)+v
out.append('Phase-8 axiom tallies: ' + '; '.join('%d [%s]' % (v,k) for k,v in sorted(agg.items(), key=lambda x:-x[1])))
print('\n'.join(out))
json.dump(rows, open(sys.argv[1],'w'), indent=1) if len(sys.argv)>1 else None
