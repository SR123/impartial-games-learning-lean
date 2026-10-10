from pathlib import Path
import os, subprocess, json, time
root=Path(__file__).resolve().parent
lean=Path.home()/'.elan/bin/lean'
build=root/'build_reproduction'
build.mkdir(exist_ok=True)
env=dict(os.environ, LEAN_PATH=str(build))
results=[]
modules=['NimCore', 'NimRollout', 'NimGame', 'NimProbability', 'NimAttain', 'Circuit', 'NimRecurrent', 'BitBridge', 'NimCorrBridge', 'AttainCircuit', 'FiniteNet', 'BinaryReadout', 'ParityCircuit', 'Controller', 'ControllerBits', 'SharedCircuit', 'SelectCircuit', 'LocalRestore', 'Foundation', 'Coverage', 'PriorityEncoder', 'ThresholdNet', 'ThresholdInst', 'WholeGame', 'Family', 'Barrier', 'RolloutExec', 'Bypass', 'Classical', 'BoardStore', 'Windows', 'Misc', 'NoiseModel', 'Shootout', 'WeakMastery', 'Fourier']
for module in modules:
    start=time.monotonic()
    proc=subprocess.run([str(lean),'-o',str(build/(module+'.olean')),module+'.lean'],cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (root/(module+'.rebuild.log')).write_text(proc.stdout)
    row=dict(module=module,exit_code=proc.returncode,seconds=round(time.monotonic()-start,2))
    results.append(row)
    (root/'reproduction_results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(row,flush=True)
    if proc.returncode: raise SystemExit(proc.returncode)
