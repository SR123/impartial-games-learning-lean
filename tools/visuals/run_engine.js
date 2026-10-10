#!/usr/bin/env node
/* Batch evaluation of the browser engine for tests (tools/validate_visuals.py).
 * stdin: [{op: "restore", B, Q, Qp} | {op: "rollout", B, P, early} | {op: "decisions", protocol, boards}
 *         | {op: "edge", ...}]
 * stdout: one result per request. */
"use strict";
const C = require("./nimvis-core.js");
let buf = "";
process.stdin.setEncoding("utf8");
process.stdin.on("data", (d) => { buf += d; });
process.stdin.on("end", () => {
  const reqs = JSON.parse(buf);
  const out = reqs.map((q) => {
    if (q.op === "restore") {
      const t = C.twoFrame(q.B, q.Q, q.Qp);
      return { delta: t.delta, move: t.move, branch: t.branch, wires: t.wires, candidates: t.candidates, promise: t.promise.ok };
    }
    if (q.op === "rollout") {
      const s = C.shootout(q.B, q.P, q.early);
      return { moves: s.movesPerHead, outs: s.outs, evaluations: s.evaluations, heads: s.headsRun, decision: s.dec,
               sigma: s.sigma, readout: s.readout, branch: s.readoutBranch, ticks: s.ticks.length };
    }
    if (q.op === "decisions") {
      const toks = [{ t: "reset" }];
      q.boards.forEach((P) => { toks.push(...(q.protocol === "replay" ? C.dtoks(P) : C.btoks(P))); });
      const steps = q.protocol === "replay" ? C.crun(toks) : C.bsRun(q.boards[0].length, toks);
      const outs = steps.filter((s) => s.out).map((s) => s.out);
      return { outs, updates: steps.length };
    }
    if (q.op === "reset") {             // reset from an arbitrary state
      const r = C.cstep(q.state, { t: "reset" });
      const b = C.bsStep(q.N, q.bstate, { t: "reset" });
      return { ctrl: r.state, store: b.state, init: C.cinit(), binit: C.bsInit(q.N) };
    }
    if (q.op === "scenario") {
      const rt = C.recurrenceScenario(q.protocol, q.scenario, q.B, q.P, q.opp);
      return { steps: rt.steps.map((s) => ({ tok: s.tok, state: s.state, out: s.out, phase: s.phase })), boards: rt.boards };
    }
    return { error: "unknown op " + q.op };
  });
  process.stdout.write(JSON.stringify(out));
});
