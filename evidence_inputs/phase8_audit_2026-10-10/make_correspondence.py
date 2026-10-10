from pathlib import Path
import re,json,hashlib,csv
root=Path(__file__).resolve().parents[2]; audit=Path(__file__).resolve().parent
paper=root/'02_working_copy/candidate/paper_revised_final.tex'; s=paper.read_text()
manifest=json.loads((audit/'input_manifest.json').read_text()); idx=[]
for m in manifest:
 text=(audit/(m['module']+'.lean')).read_text()
 for name in re.findall(r"'(.+?)' (?:depends on axioms|does not depend on any axioms)",(audit/(m['module']+'.rebuild.log')).read_text()):
  short=name.rsplit('.',1)[-1]; match=re.search(r'\b(?:theorem|lemma)\s+(?:[\w]+\.)*'+re.escape(short)+r'(?=\s|:|\{|\()',text)
  idx.append(dict(name=name,module=m['module'],source=str(Path(m['source']).relative_to(root)),line=text[:match.start()].count('\n')+1 if match else None,sha256=m['sha256']))
(audit/'declaration_index.json').write_text(json.dumps(idx,indent=2)+'\n')
rows=[]
def add(labels,status,claims,refs,scope):
 proofs=[]
 for ref in refs.split():
  module,short=ref.split(':'); found=[x for x in idx if x['module']==module and x['name'].endswith('.'+short)]
  assert len(found)==1,(ref,len(found))
  proofs.append(found[0])
 for label in labels.split():
  assert '\\label{'+label+'}' in s,label
  rows.append(dict(label=label,status=status,claim=claims,proofs=proofs,hypotheses_and_boundary=scope))
add('def:quantised-inference app:defs app:precision app:NN def:NN-formal','definition/checked-model','Literal-threshold gate and network model','Circuit:gate_ac0 FiniteNet:netFormula_spec','Nonnegative literal weights, bounded threshold in minimum-weight units; not arbitrary quantised networks.')
add('rem:ac0-scope','scope','Majority outside the fixed bound','Windows:majGate_not_valid','A growing threshold is excluded by the declared gate model.')
add('rem:local-vs-global-parity','checked/conditional','Constant-block XOR versus global parity','Windows:blockXor_res Classical:parityNotAC0_of_hastad','Global obstruction uses the named classical parity-correlation premise.')
add('thm:sim-ac0 app:ac0proof','checked','Network to AC0 simulation','Circuit:network_ac0 FiniteNet:family_finite Family:netFam_ac0 Windows:window_ac0 Windows:staged_ac0','Fixed depth, latency, quantisation bounds; staged attention requires gate-realised operations.')
add('def:impartial','external-background','General impartial games','','General Sprague-Grundy theory is cited background; NIM is the formalised game.')
add('def:nim def:nimsum thm:nim-win','checked','NIM moves, XOR and winning positions','NimGame:lose_iff NimGame:win_iff NimGame:exists_move_to_zero','Finite normal-play NIM, nonnegative heap sizes.')
add('def:mastery app:weak','checked','History-dependent weak and strong mastery, pairing, separation','WeakMastery:secure_iff_guarantee WeakMastery:weakMastery_iff_optimal WeakMastery:pairing_net_weak WeakMastery:strong_weak WeakMastery:sep3_weak WeakMastery:sep3_not_strong','Designated role, initial family, deterministic policies, legal opponents, illegal/missing actions forfeit; losing starts give vacuous weak mastery.')
add('thm:singleframe-impossible','checked/conditional','Winning-move parity reduction and family obstruction','NimGame:winning_selector_parity Barrier:barrier_net Classical:parityNotAC0_of_hastad','Parity hardness is an explicit classical input; all reduction boards are winning.')
add('def:nimber-difference','checked','Single-heap XOR difference','NimCore:one_heap_difference','Fixed aligned heap indices.')
add('lem:nimber-diff-ac0 app:nimberdiff','checked','At most a constant number of changed heaps','LocalRestore:bdC_eval LocalRestore:bdDelta_eq LocalRestore:bdC_res','Promise at most t changes; polynomial exponent depends on fixed t.')
add('prop:restore','checked','Conditional restoration and binary selector','NimCore:conditional_restoration LocalRestore:restore_equiv Family:rest_semantics','Previous board has nim-sum zero and opponent transition is legal.')
add('def:rollout-policy def:agent-types rem:why-multi-head','definition/checked-interface','Restricted structured-channel observations','NimProbability:single_policy_affine Misc:single_policy_correction Misc:bitBoard_query','One fixed structured head; query corrections included in bounded-depth readout; no unrestricted transformed starts.')
add('par:shootout-controller par:controller-costs','checked','Early-exit and all-head compiled controllers','Shootout:ee_net Shootout:ahSel_wins Shootout:ahL_counts Shootout:sh_ac0 Shootout:sh_net','Read-only original board each tick; all-head move selection distinct from early classification. M+2B+2 includes reset and readout.')
add('prop:rollout-sufficiency app:rollout-proofs','checked','Executed rollouts recover invariant and select winning move','NimGame:rolloutWinner_channel RolloutExec:mhExec_wins RolloutExec:mhExec_evals','B channels; simulated legal moves bounded by BN(2^B-1); total horizon grows.')
add('prop:single-policy-bound','checked','One channel gives one affine invariant bit','NimProbability:rollout_outcome_linear NimProbability:single_policy_affine','Structured fixed head and known one-heap modifications.')
add('rem:noisy-rollout-decay app:noise-samples prop:noise-samples','checked','Real probability law and minimum sample complexity','RealNoise:flip_law RealNoise:flip_repeated RealNoise:mMin_spec RealNoise:mMin_bounds RealNoise:mMin_theta RealNoise:flip_mMin RealNoise:eventually_small RealNoise:reuse_any_rule RealNoise:remark_real','0<=epsilon<1/2; fresh independent blocks; 0<a<=1/2 for bounds; worst-case error 1/4; arbitrary randomized decision rules. Not a model of erroneous legal moves.')
add('thm:search-gap app:search-gap-proof eq:finite-correlation-bound','checked/conditional','Finite success bound, asymptotic application and attainability','NimProbability:success_bound NimCorrBridge:circuit_readout_bound Classical:search_gap_asymptotic Classical:search_gap_asymptotic_net NimAttain:attain_exact','Fixed B>=2 and uniform winning boards; named HastadNegl input implies needed indicator correlation. External analytic negligible-rate deduction.')
add('prop:streaming-nimsum','checked','Streamed summary and separator protocol','NimRecurrent:stream_reports_delta NimRecurrent:circuit_update NimRecurrent:circuit_resources','Aligned B-bit rows, completed frames, validity flag and reset; stores summaries rather than entire history.')
add('prop:bypass-interfaces','checked/conditional','All three constructions, resource families, whole-game composition','Bypass:prop_bypass_interfaces Bypass:bypass_barriers WholeGame:replay_game BoardStore:bits_store_wins','Two-frame promise; recurrent replay supplied by environment; complete rollout/recurrent maps excluded from AC0 conditional on parity hardness. ReplayWins uses its existing game semantics, not new Hist predicate.')
add('def:fourier-tail eq:tail-correlation','checked','Fourier basis, expansion, tail and parity-correlation inequality','RealFourier:orthonormal_fin RealFourier:inversion_fin RealFourier:parseval_fin RealFourier:tailF_eq RealFourier:bandLimited_corr_real','Uniform Boolean cube; epsilon>=0; character degree exceeds cutoff.')
add('eq:delta-extension','checked','Specified total OR-of-XOR extension','RealFourier:dSign_enc_real RealFourier:dC_not_character_real RealFourier:dC_one_exactDeg_real','Equals delta on at-most-one-change domain; not a signed character for N>=2, bit j<B; N=1 degree two.')
add('sec:spectral-view','checked/external','Nim-bit spectrum and classical tail discussion','RealFourier:nimBit_spectrum_real RealFourier:delta_spectrum_real Fourier:nimBit_corr_of_tail','LMN/Tal TailPremise not instantiated against exact published size/depth conventions. This discussion is not needed for main search bound.')
add('app:RNN def:RNN-formal','checked-model','Finite-window recurrence','Windows:window_ac0 Windows:window_size_closed','Fixed total unrolling; full row scan deliberately leaves this restriction.')
add('app:LTST def:LTST-formal','checked-model','Gate-realised staged composition','Windows:staged_ac0','No reduction of standard softmax attention is claimed.')
add('app:oneunit lem:unit-ac0','checked','Constant witness and DNF','Circuit:bounded_witness Circuit:gate_ac0 Classical:dnf_aoDepth','Classical depth counts AND/OR layers; NOT-counting bound may add one.')
add('app:network lem:layer-ac0','checked','Layer simulation','Circuit:eval_compileLayer Circuit:compileLayer_size Circuit:compileLayer_depth','Fixed gate bound and polynomial widths.')
add('app:impl','checked','Binary outputs and threshold compiler resources','PriorityEncoder:encode_correct ThresholdNet:compileF_spec ThresholdNet:compileF_length ThresholdNet:compileF_gates ThresholdNet:compileF_bounded ThresholdNet:compileF_fixed_grid BoardStore:bs_net','Counts total output formula nodes; weights/thresholds 0/1; board-storage and replay have different space/time.')
add('sec:supervised-restoration sec:exp-fsm-shootout','empirical/partly-checked-mathematics','Experiments and arithmetic baselines','Misc:baseline_numbers Misc:board_recall','Numerical baseline theorem does not certify checkpoints or the causal mechanism of the 0.54 plateau. Saved-data diagnostics remain empirical.')
missing=set(re.findall(r'\\label\{((?:def|thm|lem|prop|rem|eq|app|par):[^}]+)\}',s))-{x['label'] for x in rows}
assert not missing,missing
out=dict(manuscript_sha256=hashlib.sha256(paper.read_bytes()).hexdigest(),date='2026-10-10',description='Audited statement correspondence; exact source references, not generated live website links. Includes auxiliary formal definitions and empirical/external boundaries.',rows=rows)
(audit/'paper_proof_correspondence.json').write_text(json.dumps(out,indent=2)+'\n')
with (audit/'paper_proof_correspondence.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['LaTeX label','status','claim','Lean declarations','hypotheses and boundary'])
 for r in rows:w.writerow([r['label'],r['status'],r['claim'],'; '.join(x['name'] for x in r['proofs']),r['hypotheses_and_boundary']])
print(len(idx),'declarations;',len(rows),'label entries; all mathematical labels covered')
