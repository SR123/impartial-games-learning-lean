from pathlib import Path
import re,json,hashlib
root=Path('/Users/sorenriis/Documents/ChatGpt_codex_folder/NIM_paper/Astra_Review_2026-10-09/05_revision_cycle')
audit=root/'phase8_audit_2026-10-10'
manifest=json.loads((audit/'input_manifest.json').read_text())
old=json.loads((root/'phase7_audit_2026-10-10/input_manifest.json').read_text())
print('Old manifest type',type(old).__name__)
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
for row in manifest:
 m=row['module'];s=(audit/(m+'.lean')).read_text();clean=strip(s);log=(audit/(m+'.rebuild.log')).read_text()
 names=re.findall(r'\b(?:theorem|lemma)\s+([\w\'.]+)',clean)
 reports=re.findall(r"'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
 printed={name for name,_ in reports}
 unexpected=[]
 for name,ax in reports:
  bad=set(x.strip() for x in ax.split(',') if x.strip())-{'propext','Classical.choice','Quot.sound'}
  if bad:unexpected.append([name,sorted(bad)])
 suspicious=[{'token':x.group(),'line':clean[:x.start()].count('\n')+1} for x in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|run_tac)\b|#eval|#run',clean)]
 # #print axioms is intentionally not forbidden.
 src=Path(row['source']); delivered=src.with_suffix('.log')
 if row['phase']=='phase8': delivered=src.parent/'logs'/(m+'.log')
 results=dict(module=m,phase=row['phase'],theorems=len(names),axiom_reports=len(reports),missing_reports=sorted(name for name in names if not any(p == name or p.endswith('.'+name) for p in printed)),unexpected_axioms=unexpected,suspicious_tokens=suspicious,source_hash_unchanged=hashlib.sha256(src.read_bytes()).hexdigest()==row['sha256'],snapshot_hash_matches=hashlib.sha256((audit/src.name).read_bytes()).hexdigest()==row['sha256'],delivered_log_matches=delivered.exists() and re.sub(r'(?m)^\./(?=\w+\.lean:\d+:)', '', delivered.read_text())==re.sub(r'(?m)^\./(?=\w+\.lean:\d+:)', '', log))
 if row['phase']!='phase8':results['matches_phase7_snapshot']=src.read_bytes()==(root/'phase7_audit_2026-10-10'/src.name).read_bytes()
 results.update(lines=len(s.splitlines()), nonblank_lines=sum(bool(l.strip()) for l in s.splitlines()), code_lines=sum(bool(l.strip()) for l in clean.splitlines()), code_lines_without_axiom_prints=sum(bool(l.strip()) and not l.lstrip().startswith('#print axioms') for l in clean.splitlines()), definitions=len(re.findall(r'\bdef\s+[\w\'.]+',clean)))
 rows.append(results)
checks=[]
for line in (root/'lean/phase8/PHASE8_HASHES.txt').read_text().splitlines():
 mt=re.match(r'^([0-9a-f]{64})\s+(.+?)\s*$',line)
 if mt:
  src=(root/'lean/phase8'/mt[2]).resolve()
  if not src.exists(): src=(root/'lean'/mt[2]).resolve()
  checks.append({'path':str(src),'exists':src.exists(),'matches':src.exists() and hashlib.sha256(src.read_bytes()).hexdigest()==mt[1]})
build=json.loads((audit/'reproduction_results.json').read_text())
summary={'module_count':len(rows),'theorem_count':sum(x['theorems'] for x in rows),'phase8_theorems':sum(x['theorems'] for x in rows if x['phase']=='phase8'),'axiom_reports':sum(x['axiom_reports'] for x in rows),'build_passed':len(build)==38 and all(x['exit_code']==0 for x in build),'all_hashes_pass':all(x['matches'] for x in checks),'all_prior_sources_unchanged':all(x.get('matches_phase7_snapshot',True) for x in rows),'all_delivered_logs_match':all(x['delivered_log_matches'] for x in rows),'issues':[x for x in rows if x['missing_reports'] or x['unexpected_axioms'] or x['suspicious_tokens']]}
summary.update(lines=sum(x['lines'] for x in rows),nonblank_lines=sum(x['nonblank_lines'] for x in rows),code_lines=sum(x['code_lines'] for x in rows),definitions=sum(x['definitions'] for x in rows),code_lines_without_axiom_prints=sum(x['code_lines_without_axiom_prints'] for x in rows))
(audit/'audit_results.json').write_text(json.dumps({'summary':summary,'modules':rows,'delivered_hash_checks':checks},indent=2)+'\n')
print(json.dumps(summary,indent=2))
