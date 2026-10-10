/* Interactive edition of the NIM paper: computations behind the illustrations.
 *
 * Pure functions, no DOM.  Each function re-implements, in a few lines, one definition of the
 * Lean development, named in its comment.  These re-implementations are NOT checked by Lean.
 * tools/validate_site.py compares them with the values that Lean itself computes for the same
 * definitions on small inputs (data/visual_reference_lean.jsonl, from tools/lean/VisualRef.lean)
 * and with an independent Python implementation (tools/visuals/reference.py).
 *
 * Runs unchanged in the browser (window.NimVisCore) and in Node (require).
 */
(function (root, factory) {
  if (typeof module === "object" && module.exports) module.exports = factory();
  else root.NimVisCore = factory();
})(typeof self !== "undefined" ? self : this, function () {
  "use strict";

  /* ---------- bits ---------- */

  /** Big-endian bits of x, B of them (Lean: NimCorrBridge.boardBits, BitBridge.toNatBE). */
  function bitsBE(x, B) {
    var out = [];
    for (var p = 0; p < B; p++) out.push(Math.floor(x / Math.pow(2, B - 1 - p)) % 2 === 1);
    return out;
  }
  function toNatBE(bits) {
    var v = 0;
    for (var i = 0; i < bits.length; i++) v = 2 * v + (bits[i] ? 1 : 0);
    return v;
  }
  function nimSum(P) {
    var s = 0;
    for (var i = 0; i < P.length; i++) s ^= P[i];
    return s;
  }
  /** Index width used for N heaps (Lean: WholeGame.rIdx N = Nat.log2 N + 1). */
  function rIdx(N) {
    var l = 0;
    while (Math.pow(2, l + 1) <= N) l++;
    return l + 1;
  }
  function bitStr(bits) { return bits.map(function (b) { return b ? "1" : "0"; }).join(""); }
  function setAt(P, i, v) {
    var Q = P.slice();
    if (i >= 0 && i < Q.length) Q[i] = v;
    return Q;
  }

  /** First nonzero heap minus one (Lean: NimAttain.decIdx). */
  function decIdx(P) {
    for (var i = 0; i < P.length; i++) if (P[i] > 0) return [i, P[i] - 1];
    return null;
  }
  /** First heap with x XOR t < x, new value x XOR t (Lean: NimAttain.cancelIdx). */
  function cancelIdx(t, P) {
    for (var i = 0; i < P.length; i++) if ((P[i] ^ t) < P[i]) return [i, P[i] ^ t];
    return null;
  }
  /** Cancelling move for target t, else the fallback (Lean: AttainCircuit.attainT). */
  function attainT(t, P) { return cancelIdx(t, P) || decIdx(P); }

  /** Classify a two-frame input against the promise of Theorem 5.12(iii). */
  function promiseOf(Q, Qp) {
    if (Q.length !== Qp.length) return { ok: false, reason: "The two frames have different numbers of heaps." };
    var changed = [], up = false;
    for (var i = 0; i < Q.length; i++) {
      if (Q[i] !== Qp[i]) { changed.push(i); if (Qp[i] > Q[i]) up = true; }
    }
    var zero = nimSum(Q) === 0;
    var legal = changed.length === 1 && !up;
    var reasons = [];
    if (!zero) reasons.push("the earlier board has nim-sum " + nimSum(Q) + ", not 0");
    if (changed.length === 0) reasons.push("no heap changed");
    else if (changed.length > 1) reasons.push(changed.length + " heaps changed");
    else if (up) reasons.push("the changed heap grew");
    return { ok: zero && legal, zeroPredecessor: zero, legalMove: legal, changed: changed,
             reason: reasons.length ? reasons.join("; ") : "" };
  }

  /* ---------- 1. two-frame selector ---------- */

  /**
   * The binary two-frame selector Family.restS (B, N) = PriorityEncoder.encode (LocalRestore.restC B N) N r,
   * gate by gate on the input LocalRestore.tf B N Q Q':
   *   y[i][p]  = bit p of heap i in Q  XOR  bit p of heap i in Q'        (LocalRestore.yC)
   *   chg[i]   = OR_p y[i][p]                                               (LocalRestore.chgC)
   *   delta[p] = OR_i y[i][p]  (big-endian)                                 (LocalRestore.dC)
   *   cand[i]  = Q'_i XOR delta;  cancel[i] = cand[i] < Q'_i               (SelectCircuit.varSel)
   *   s[i]     = cancel[i] OR (no cancel AND Q'_i != 0)                     (SelectCircuit.genSel)
   *   value    = first cancelling candidate, else first nonzero heap minus 1
   *   f[i]     = s[i] AND NOT s[j] for all j < i;  I_q = OR of f[i] with bit (r-1-q) of i   (PriorityEncoder)
   *   valid    = (some heap nonzero) AND (some s[i])
   */
  function twoFrame(B, Q, Qp) {
    var N = Q.length, r = rIdx(N);
    var x = Q.map(function (v) { return bitsBE(v, B); });
    var xp = Qp.map(function (v) { return bitsBE(v, B); });
    var y = [], chg = [];
    for (var i = 0; i < N; i++) {
      var row = [];
      for (var p = 0; p < B; p++) row.push(x[i][p] !== xp[i][p]);
      y.push(row);
      chg.push(row.some(Boolean));
    }
    var deltaBE = [];
    for (var p2 = 0; p2 < B; p2++) {
      var any = false;
      for (var i2 = 0; i2 < N; i2++) if (y[i2][p2]) any = true;
      deltaBE.push(any);
    }
    var delta = toNatBE(deltaBE);
    // highest set bit of delta (big-endian position), the bit that decides every candidate test
    var top = deltaBE.indexOf(true);
    var cand = Qp.map(function (v) { return v ^ delta; });
    var cancel = Qp.map(function (v, k) { return cand[k] < v; });
    var anyCancel = cancel.some(Boolean);
    var nz = Qp.map(function (v) { return v !== 0; });
    var validA = nz.some(Boolean);
    var dec = Qp.map(function (v) { return v > 0 ? v - 1 : 0; });
    var s = cancel.map(function (c, k) { return c || (!anyCancel && nz[k]); });
    var f = [], seen = false;
    for (var k = 0; k < N; k++) { f.push(s[k] && !seen); if (s[k]) seen = true; }
    var firstCancel = cancel.indexOf(true), firstNz = nz.indexOf(true);
    var value = anyCancel ? cand[firstCancel] : (validA ? dec[firstNz] : 0);
    var valBits = bitsBE(value, B);
    var idxBits = [];
    for (var q = 0; q < r; q++) {
      var bit = false;
      for (var i3 = 0; i3 < N; i3++) if (f[i3] && Math.floor(i3 / Math.pow(2, r - 1 - q)) % 2 === 1) bit = true;
      idxBits.push(bit);
    }
    var valid = validA && s.some(Boolean);
    var idx = toNatBE(idxBits);
    var move = valid && idx < N ? [idx, toNatBE(valBits)] : null;
    var branch = !validA ? "terminal" : (anyCancel ? "cancel" : "fallback");
    var R = move ? setAt(Qp, move[0], move[1]) : null;
    return {
      B: B, N: N, r: r, Q: Q.slice(), Qp: Qp.slice(), x: x, xp: xp, y: y, chg: chg,
      deltaBE: deltaBE, delta: delta, top: top, cand: cand, cancel: cancel, anyCancel: anyCancel,
      nz: nz, dec: dec, s: s, f: f, idxBits: idxBits, valBits: valBits, valid: valid,
      wires: [valid].concat(idxBits, valBits), move: move, branch: branch, R: R,
      nimQ: nimSum(Q), nimQp: nimSum(Qp), nimR: R ? nimSum(R) : null,
      candidates: cancel.filter(Boolean).length, promise: promiseOf(Q, Qp)
    };
  }

  /** Bit-by-bit comparison behind one candidate test x' = x XOR delta < x (AttainCircuit.cancel_iff_bit). */
  function compareTrace(B, x, c) {
    var xb = bitsBE(x, B), cb = bitsBE(c, B), k = -1;
    for (var p = 0; p < B; p++) if (xb[p] !== cb[p]) { k = p; break; }
    return { xb: xb, cb: cb, first: k, less: k >= 0 && xb[k] && !cb[k] };
  }

  /* ---------- 2. threshold networks ---------- */

  /** One literal-threshold gate (Lean: AC0.Gate.eval): fires iff thr <= sum_j w_j [z_j XOR neg_j]. */
  function gateEval(g, z) {
    var sum = 0;
    for (var j = 0; j < g.w.length; j++) if (g.w[j] && (!!z[j] !== !!g.neg[j])) sum += g.w[j];
    return g.thr <= sum;
  }
  /** Layer by layer (Lean: AC0.evalNet); returns the wires after every layer. */
  function netEval(layers, input) {
    var z = input.slice(), all = [];
    for (var t = 0; t < layers.length; t++) {
      var next = layers[t].map(function (g) { return gateEval(g, z); });
      all.push(next);
      z = next;
    }
    return all;
  }
  /** Role of program gate g at layer t (1-based) in ThresholdNet.compileF, from the gate program. */
  function compileRole(prog, levels, g, t, nComputing) {
    if (t > nComputing) return "output";
    var d = prog[g], lv = levels[g];
    if (t === 1) {
      if (d.op === "inp") return "read input";
      if (d.op === "cst") return "constant";
      return "idle";
    }
    if (lv < t) return "copy";
    if (lv === t) {
      if (d.op === "and") return "negate (AND, 2nd layer)";
      if (d.op === "neg") return "NOT";
      if (d.op === "or") return "OR";
      if (d.op === "cst") return "constant";
      return "idle";
    }
    if (lv === t + 1 && d.op === "and") return "OR of negated inputs (AND, 1st layer)";
    return "idle";
  }
  /** Program gate values (Lean: Shared gate program semantics). */
  function progEval(prog, input) {
    var v = [];
    prog.forEach(function (d) {
      if (d.op === "inp") v.push(!!input[d.i]);
      else if (d.op === "cst") v.push(!!d.b);
      else if (d.op === "neg") v.push(!v[d.a]);
      else if (d.op === "and") v.push(d.as.every(function (a) { return v[a]; }));
      else v.push(d.as.some(function (a) { return v[a]; }));
    });
    return v;
  }

  /* ---------- 3. structured rollouts and the shootout controller ---------- */

  /** One step of pi_j (Lean: SelectCircuit.policyIdx j / Rollout.policyStep j). */
  function policyIdx(j, P) {
    var u = Math.pow(2, j);
    for (var i = 0; i < P.length; i++) if (P[i] >= u) return { i: i, v: P[i] - u, rule: "subtract " + u + " from the first heap of size at least " + u };
    for (var k = 0; k < P.length; k++) if (P[k] > 0) return { i: k, v: P[k] - 1, rule: "no heap has " + u + " or more: subtract 1 from the first nonzero heap" };
    return null;
  }
  function recoverBits(outs) {
    return outs.map(function (o, j) { return j === 0 ? o : (o !== outs[0]); });
  }
  /** sigma from the outcome bits: sigma_0 = o_0, sigma_j = o_j XOR o_0 (Lean: Game.reconstruct). */
  function reconstruct(outs) {
    var bits = recoverBits(outs), v = 0;
    for (var j = 0; j < bits.length; j++) if (bits[j]) v += Math.pow(2, j);
    return v;
  }
  function osCopy(s) {
    return { board: s.board.slice(), par: s.par, halted: s.halted, run: s.run, dec: s.dec, j: s.j, outs: s.outs.slice() };
  }
  /**
   * The outer controller of Shootout.ostep, tick by tick from the reset tick, with its embedded
   * rollout registers (RolloutExec.rsStep).  early = true is the early-exit classifier, false the
   * all-head schedule followed by the binary readout (PriorityEncoder.mhBin).
   */
  function shootout(B, P, early) {
    var outsInit = [];
    for (var h = 0; h < B; h++) outsInit.push(false);
    var s = { board: P.slice(), par: false, halted: false, run: B >= 1, dec: false, j: 0, outs: outsInit };
    var ticks = [{ kind: "reset", text: "Reset: load the board, select head 0, clear the outcomes.", state: osCopy(s) }];
    var limit = B * (P.length * Math.pow(2, B) + 3) + 4;
    while (s.run && ticks.length < limit) {
      var t;
      if (!s.halted) {
        var m = policyIdx(s.j, s.board);
        if (!m) {
          s.halted = true;
          t = { kind: "terminal", head: s.j, text: "Head " + s.j + ": no legal move, so the rollout has ended after an " +
                (s.par ? "odd" : "even") + " number of moves; the outcome bit is " + (s.par ? 1 : 0) + "." };
        } else {
          var from = s.board[m.i];
          s.board = setAt(s.board, m.i, m.v);
          s.par = !s.par;
          t = { kind: "move", head: s.j, heap: m.i, from: from, to: m.v, rule: m.rule,
                text: "Head " + s.j + " moves: heap " + m.i + " from " + from + " to " + m.v + " (" + m.rule + ")." };
        }
      } else {
        var stop = (early && s.par) || s.j === B - 1;
        var o = s.par, j0 = s.j;
        s.outs = s.outs.slice(); s.outs[j0] = o;
        s.dec = s.dec || o;
        if (stop) {
          s.run = false;
          t = { kind: "stop", head: j0, outcome: o, text: "Store outcome o" + j0 + " = " + (o ? 1 : 0) + " and stop" +
                (early && o ? " (an outcome 1 certifies that the nim-sum is nonzero)." : " (last head).") };
        } else {
          s.board = P.slice(); s.par = false; s.halted = false; s.j = j0 + 1;
          t = { kind: "consume", head: j0, outcome: o, text: "Store outcome o" + j0 + " = " + (o ? 1 : 0) +
                ", reload the original board and select head " + (j0 + 1) + "." };
        }
      }
      t.state = osCopy(s);
      ticks.push(t);
    }
    var outs = s.outs, sigma = reconstruct(outs);
    var res = { B: B, P: P.slice(), early: early, ticks: ticks, outs: outs.slice(), dec: s.dec,
                moves: ticks.filter(function (x) { return x.kind === "move"; }).length };
    res.movesPerHead = [];
    for (var hh = 0; hh < B; hh++) res.movesPerHead.push(ticks.filter(function (x) { return x.kind === "move" && x.head === hh; }).length);
    res.headsRun = ticks.filter(function (x) { return x.kind === "stop" || x.kind === "consume"; }).length;
    if (!early) {
      res.sigmaBits = recoverBits(outs);
      res.sigma = sigma;
      res.readout = attainT(sigma, P);
      res.readoutBranch = !decIdx(P) ? "terminal" : (cancelIdx(sigma, P) ? "cancel" : "fallback");
      res.evaluations = ticks.length + 1;        // ticks including the reset, plus one readout
    } else {
      res.evaluations = ticks.length;
    }
    res.nim = nimSum(P);
    return res;
  }

  /* ---------- 4. recurrence ---------- */

  function rowsOf(P) { return P.map(function (x) { return { t: "row", x: x }; }); }
  /** One decision of the replay protocol (Controller.dtoks): rows, SEP, rows, SEP. */
  function dtoks(P) { return rowsOf(P).concat([{ t: "sep" }], rowsOf(P), [{ t: "sep" }]); }
  /** One decision of the board-storage protocol (BoardStore.btoks): rows, SEP. */
  function btoks(P) { return rowsOf(P).concat([{ t: "sep" }]); }

  function cinit() { return { replay: false, acc: 0, prev: 0, valid: false, sig: 0, idx: 0, sel: null, fnz: null }; }
  /** Replay controller update (Lean: Controller.cstep, with Recurrent.replayStep). */
  function cstep(s, tok) {
    var n = { replay: s.replay, acc: s.acc, prev: s.prev, valid: s.valid, sig: s.sig, idx: s.idx, sel: s.sel, fnz: s.fnz };
    if (tok.t === "reset") return { state: cinit(), out: null, action: "reset: every register returns to its initial value" };
    if (tok.t === "row") {
      if (s.replay) {
        var x = tok.x;
        n.idx = s.idx + 1;
        if (!s.sel && s.sig !== 0 && (x ^ s.sig) < x) n.sel = [s.idx, x ^ s.sig];
        if (!s.fnz && x > 0) n.fnz = [s.idx, x - 1];
        return { state: n, out: null, action: "replay row " + s.idx + ": test x XOR sig < x; keep the first candidate and the first fallback" };
      }
      n.acc = s.acc ^ tok.x;
      return { state: n, out: null, action: "scan row: acc := acc XOR " + tok.x };
    }
    if (s.replay) {
      n.replay = false; n.idx = 0; n.sel = null; n.fnz = null;
      return { state: n, out: { move: s.sel || s.fnz }, action: "separator after replay: output the move, return to scan mode" };
    }
    n.replay = true; n.acc = 0; n.prev = s.acc; n.valid = true; n.sig = s.acc; n.idx = 0; n.sel = null; n.fnz = null;
    return { state: n, out: { summary: s.acc, diff: s.valid ? (s.prev ^ s.acc) : null },
             action: "separator after scan: output the summary (and the difference from the previous summary), store it, switch to replay" };
  }
  function crun(toks) {
    var s = cinit(), steps = [];
    toks.forEach(function (tok) { var r = cstep(s, tok); steps.push({ tok: tok, state: r.state, out: r.out, action: r.action }); s = r.state; });
    return steps;
  }

  /** Board-storage update (Lean: BoardStore.bsStep). */
  function bsInit(N) { var b = []; for (var i = 0; i < N; i++) b.push(0); return { board: b, acc: 0, idx: 0 }; }
  function bsStep(N, s, tok) {
    if (tok.t === "reset") return { state: bsInit(N), out: null, action: "reset: clear the stored board, accumulator and pointer" };
    if (tok.t === "row") {
      return { state: { board: setAt(s.board, s.idx, tok.x), acc: s.acc ^ tok.x, idx: s.idx + 1 }, out: null,
               action: "store row " + s.idx + " and acc := acc XOR " + tok.x };
    }
    return { state: { board: s.board.slice(), acc: 0, idx: 0 }, out: { summary: s.acc, move: attainT(s.acc, s.board) },
             action: "separator: select the move from the stored board with target acc; clear acc and pointer" };
  }
  function bsRun(N, toks) {
    var s = bsInit(N), steps = [];
    toks.forEach(function (tok) { var r = bsStep(N, s, tok); steps.push({ tok: tok, state: r.state, out: r.out, action: r.action }); s = r.state; });
    return steps;
  }

  /** Summary mechanism of prop:streaming-nimsum (Lean: Recurrent.step): state (acc, prev, valid). */
  function summRun(positions) {
    var s = { acc: 0, prev: 0, valid: false }, steps = [];
    positions.forEach(function (P) {
      P.forEach(function (x) {
        s = { acc: s.acc ^ x, prev: s.prev, valid: s.valid };
        steps.push({ tok: { t: "row", x: x }, state: s, out: null });
      });
      var out = { summary: s.acc, diff: s.valid ? (s.prev ^ s.acc) : null };
      s = { acc: 0, prev: s.acc, valid: true };
      steps.push({ tok: { t: "sep" }, state: s, out: out });
    });
    return steps;
  }

  /**
   * Token streams for the recurrence illustration, annotated with the phase of every token.
   * protocol "replay" uses Controller.dtoks (2N + 2 updates per decision); "store" uses
   * BoardStore.btoks (N + 1 updates per decision, the board is kept in registers).
   */
  function recurrenceScenario(protocol, scenario, B, P1, opp) {
    var N = P1.length, toks = [{ t: "reset" }], boards = [P1.slice()], note = "";
    function reply(P) { var m = attainT(nimSum(P), P); return m ? setAt(P, m[0], m[1]) : P.slice(); }
    var R1 = reply(P1), P2 = setAt(R1, opp[0], opp[1]);
    if (protocol === "summary") {
      // Recurrent.step: rows of each position, then SEP; this machine has no reset token
      var positions = [P1.slice()];
      if (scenario === "game" || scenario === "reset") { positions = [P1.slice(), P2]; boards = [P1.slice(), R1, P2]; }
      if (scenario === "separator") positions = [P1.slice(), []];
      if (scenario === "reset") note = "The summary mechanism of the proposition has no reset token in the Lean model; the replay and board-storage controllers have one. Shown here: the game scenario.";
      if (scenario === "separator") note = "An extra separator is read as an empty position. No theorem is stated for such streams; the update rule is simply applied.";
      var ss = summRun(positions), prev = { acc: 0, prev: 0, valid: false };
      ss.forEach(function (st) {
        st.phase = st.tok.t === "row" ? "scan" : "summary";
        st.action = st.tok.t === "row" ? "row: acc := acc XOR " + st.tok.x
          : "separator: output the summary (and, if one is stored, the difference from it); keep the summary as the previous one; clear the accumulator";
        prev = st.state;
      });
      return { protocol: protocol, scenario: scenario, B: B, N: N, boards: boards, steps: ss, note: note };
    }
    var dec = protocol === "replay" ? dtoks : btoks;
    if (scenario === "game") {
      boards = [P1.slice(), R1, P2];
      toks = toks.concat(dec(P1), dec(P2));
    } else if (scenario === "separator") {
      toks = toks.concat(dec(P1), [{ t: "sep" }], protocol === "replay" ? [{ t: "sep" }] : []);
      note = "Edge case outside the protocol: the extra separator is read as an empty position. No theorem is stated for such streams; the update rule is simply applied.";
    } else if (scenario === "reset") {
      toks = toks.concat(dec(P1), [{ t: "reset" }], dec(R1));
      boards = [P1.slice(), R1];
      note = "A reset between games returns every register, validity included, to its initial value.";
    } else {
      toks = toks.concat(dec(P1));
    }
    var steps = protocol === "replay" ? crun(toks) : bsRun(N, toks);
    var before = protocol === "replay" ? cinit() : bsInit(N);
    steps.forEach(function (st) {
      var ph;
      if (st.tok.t === "reset") ph = "reset";
      else if (protocol === "replay") ph = st.tok.t === "row" ? (before.replay ? "replay" : "scan") : (before.replay ? "move" : "summary");
      else ph = st.tok.t === "row" ? "store" : "move";
      st.phase = ph;
      before = st.state;
    });
    return { protocol: protocol, scenario: scenario, B: B, N: N, boards: boards, steps: steps, note: note };
  }

  /** Preset examples shared by the static pages and the browser controls. */
  var EXAMPLES = {
    restore: [
      { id: "paper", label: "Paper example: (3, 5, 6) → (3, 4, 6)", B: 3, Q: [3, 5, 6], Qp: [3, 4, 6] },
      { id: "several", label: "Several candidates: (4, 5, 6, 7) → (4, 5, 6, 3)", B: 3, Q: [4, 5, 6, 7], Qp: [4, 5, 6, 3] },
      { id: "other", label: "Reply in another heap: (1, 2, 3) → (1, 2, 0)", B: 3, Q: [1, 2, 3], Qp: [1, 2, 0] },
      { id: "fallback", label: "Outside the promise, fallback: (2) → (1)", B: 2, Q: [2], Qp: [1] },
      { id: "terminal", label: "Outside the promise, terminal: (1, 0) → (0, 0)", B: 3, Q: [1, 0], Qp: [0, 0] },
      { id: "custom", label: "Your own boards…" }
    ],
    rollout: [
      { id: "346", label: "(3, 4, 6), nim-sum 1", B: 3, P: [3, 4, 6] },
      { id: "567", label: "(5, 6, 7), nim-sum 4", B: 3, P: [5, 6, 7] },
      { id: "356", label: "(3, 5, 6), nim-sum 0", B: 3, P: [3, 5, 6] },
      { id: "custom", label: "Your own board…" }
    ],
    recurrence: [
      { id: "decision", label: "One decision on (3, 4, 6)" },
      { id: "game", label: "A game: decisions on (3, 4, 6) and (2, 4, 1)" },
      { id: "separator", label: "Edge case: an extra separator" },
      { id: "reset", label: "Edge case: a reset between games" },
      { id: "custom", label: "One decision on your own board…" }
    ]
  };

  function example(type, id) {
    return EXAMPLES[type].filter(function (x) { return x.id === id; })[0] || EXAMPLES[type][0];
  }

  return {
    EXAMPLES: EXAMPLES, example: example,
    recurrenceScenario: recurrenceScenario,
    bitsBE: bitsBE, toNatBE: toNatBE, nimSum: nimSum, rIdx: rIdx, bitStr: bitStr, setAt: setAt,
    decIdx: decIdx, cancelIdx: cancelIdx, attainT: attainT, promiseOf: promiseOf,
    twoFrame: twoFrame, compareTrace: compareTrace,
    gateEval: gateEval, netEval: netEval, compileRole: compileRole, progEval: progEval,
    policyIdx: policyIdx, reconstruct: reconstruct, recoverBits: recoverBits, shootout: shootout,
    rowsOf: rowsOf, dtoks: dtoks, btoks: btoks, cinit: cinit, cstep: cstep, crun: crun,
    bsInit: bsInit, bsStep: bsStep, bsRun: bsRun, summRun: summRun
  };
});
