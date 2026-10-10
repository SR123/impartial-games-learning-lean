#!/usr/bin/env node
/* Compare the browser engine (nimvis-core.js) with Lean's own evaluation of the same definitions.
 *
 *   node tools/visuals/check_engine.js data/visual_reference_lean.jsonl
 *
 * Prints a JSON summary {cases, mismatches, first} and exits 1 on any mismatch.  Used by
 * tools/build_site.py (the build stops on a mismatch) and tools/validate_site.py.
 */
"use strict";
const fs = require("fs");
const C = require("./nimvis-core.js");

const file = process.argv[2];
const rows = fs.readFileSync(file, "utf8").trim().split("\n").filter((l) => l.startsWith("{")).map((l) => JSON.parse(l));
const eq = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const cases = {}, bad = {}, first = [];
function fail(kind, what) { bad[kind] = (bad[kind] || 0) + 1; if (first.length < 10) first.push({ kind, ...what }); }

for (const r of rows) {
  cases[r.kind] = (cases[r.kind] || 0) + 1;
  bad[r.kind] = bad[r.kind] || 0;
  if (r.kind === "rest") {
    const t = C.twoFrame(r.B, r.Q, r.Qp);
    if (!eq(t.wires, r.wires) || !eq(t.move, r.sem) || t.delta !== r.delta || t.r !== r.r)
      fail("rest", { B: r.B, Q: r.Q, Qp: r.Qp, lean: [r.wires, r.sem, r.delta], js: [t.wires, t.move, t.delta] });
  } else if (r.kind === "net") {
    for (const row of r.table) {
      const out = C.netEval(r.layers, row.in), last = out[out.length - 1];
      const pv = C.progEval(r.prog, row.in), fv = r.outs.map((o) => pv[o]);
      if (!eq(last.slice(0, row.net.length), row.net) || !eq(fv, row.formula) || !eq(row.net, row.formula))
        fail("net", { name: r.name, input: row.in });
    }
    // every wire role the browser derives must match the shape of the exported gate
    const L = r.layers.length;
    for (let t = 1; t < L; t++) {
      for (let g = 0; g < r.prog.length; g++) {
        const role = C.compileRole(r.prog, r.levels, g, t, L - 1), gate = r.layers[t - 1][g];
        const sel = gate.w.map((w, j) => (w ? j : -1)).filter((j) => j >= 0);
        const neg = gate.neg.some(Boolean);
        let ok = true;
        if (role === "copy") ok = eq(sel, [g]) && !neg && gate.thr === 1;
        else if (role === "idle") ok = sel.length === 0 && gate.thr === 1;
        else if (role === "negate (AND, 2nd layer)" || role === "NOT") ok = sel.length === 1 && neg && gate.thr === 1;
        else if (role === "OR of negated inputs (AND, 1st layer)") ok = eq(sel, r.prog[g].as.slice().sort((a, b) => a - b)) && neg && gate.thr === 1;
        else if (role === "OR") ok = eq(sel, r.prog[g].as.slice().sort((a, b) => a - b)) && !neg && gate.thr === 1;
        else if (role === "read input") ok = eq(sel, [r.prog[g].i]) && !neg && gate.thr === 1;
        if (!ok) fail("net", { name: r.name, layer: t, gate: g, role, w: gate.w, neg: gate.neg, thr: gate.thr });
      }
    }
  } else if (r.kind === "shoot") {
    const s = C.shootout(r.B, r.P, r.early);
    const st = s.ticks.map((t) => t.state);
    const okAll = r.early || (eq(s.outs, r.outcomes) && eq(s.movesPerHead, r.moves) && eq(s.readout, r.readout) &&
      eq(s.readout, r.decision) && s.evaluations === r.moves.reduce((a, b) => a + b, 0) + 2 * r.B + 2);
    if (!eq(st, r.states) || !okAll) fail("shoot", { B: r.B, P: r.P, early: r.early });
  } else if (r.kind === "ctrl" || r.kind === "store" || r.kind === "summ") {
    const steps = r.kind === "ctrl" ? C.crun(r.steps.map((x) => x.tok)) : r.kind === "store" ? C.bsRun(r.N, r.steps.map((x) => x.tok)) : C.summRun(r.positions);
    if (steps.length !== r.steps.length) { fail(r.kind, { name: r.name, length: [steps.length, r.steps.length] }); continue; }
    for (let i = 0; i < steps.length; i++) {
      if (!eq(steps[i].state, r.steps[i].state) || !eq(steps[i].out, r.steps[i].out)) { fail(r.kind, { name: r.name, step: i }); break; }
    }
  }
}
const total = Object.values(bad).reduce((a, b) => a + b, 0);
process.stdout.write(JSON.stringify({ cases, mismatches: bad, total_mismatches: total, first }));
process.exit(total ? 1 : 0);
