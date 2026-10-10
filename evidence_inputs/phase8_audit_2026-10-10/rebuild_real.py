from pathlib import Path
import os, subprocess, json, time
root=Path(__file__).resolve().parent
lean=Path.home()/'.elan/bin/lean'
build=root/'build_reproduction'
build.mkdir(exist_ok=True)
lake_env=dict(os.environ, PATH=str(Path.home()/'.elan/bin')+':'+os.environ['PATH'])
mathpath=subprocess.check_output([str(Path.home()/'.elan/bin/lake'),'env','printenv','LEAN_PATH'],cwd=root,env=lake_env,text=True).strip()
env=dict(os.environ, LEAN_PATH=str(build)+':'+mathpath)
results=json.loads((root/'reproduction_results.json').read_text())
modules=['RealNoise','RealFourier']
for module in modules:
    start=time.monotonic()
    proc=subprocess.run([str(lean),'-o',str(build/(module+'.olean')),module+'.lean'],cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (root/(module+'.rebuild.log')).write_text(proc.stdout)
    row=dict(module=module,exit_code=proc.returncode,seconds=round(time.monotonic()-start,2))
    results.append(row)
    (root/'reproduction_results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(row,flush=True)
    if proc.returncode: raise SystemExit(proc.returncode)
