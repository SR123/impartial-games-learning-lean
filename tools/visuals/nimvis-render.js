/* Interactive edition of the NIM paper: HTML for the illustrations.
 *
 * Pure string rendering from the traces of nimvis-core.js.  The same functions produce the static
 * HTML written into the pages at build time (Node) and the HTML shown after a reader changes an
 * example or a step (browser), so the two can never disagree.
 */
(function (root, factory) {
  if (typeof module === "object" && module.exports) module.exports = factory(require("./nimvis-core.js"));
  else root.NimVisRender = factory(root.NimVisCore);
})(typeof self !== "undefined" ? self : this, function (C) {
  "use strict";

  function esc(s) {
    return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
  }
  function b01(b) { return b ? "1" : "0"; }
  function bits(arr, opts) {
    opts = opts || {};
    return '<span class="nv-bits">' + arr.map(function (b, k) {
      var cls = "nv-bit" + (b ? " on" : "") + (opts.mark === k ? " mark" : "");
      return '<span class="' + cls + '">' + b01(b) + "</span>";
    }).join("") + "</span>";
  }
  function tuple(P) { return "(" + P.join(", ") + ")"; }
  function mv(m) { return m ? "heap " + m[0] + " → " + m[1] : "none"; }
  function yes(b, y, n) { return b ? '<span class="nv-yes">' + (y || "yes") + "</span>" : '<span class="nv-no">' + (n || "no") + "</span>"; }
  function weights(B) {
    var w = [];
    for (var p = 0; p < B; p++) w.push(Math.pow(2, B - 1 - p));
    return '<span class="nv-bits nv-w" aria-hidden="true">' + w.map(function (x) { return '<span class="nv-bit">' + x + "</span>"; }).join("") + "</span>";
  }

  /** A board drawn as rows of stones; `mark` maps heap index -> css class. */
  function boardSVG(P, B, label, mark) {
    mark = mark || {};
    var maxv = Math.max(Math.pow(2, B) - 1, 1), cw = 11, rh = 15, lw = 22;
    var w = lw + maxv * cw + 6, h = P.length * rh + 4;
    var parts = ['<svg class="nv-board" viewBox="0 0 ' + w + " " + h + '" width="' + w + '" height="' + h +
      '" role="img" aria-label="' + esc(label + " " + tuple(P)) + '">'];
    P.forEach(function (x, i) {
      var y = 2 + i * rh, cls = mark[i] ? " " + mark[i] : "";
      parts.push('<text x="0" y="' + (y + 11) + '" class="nv-hl' + cls + '">' + i + "</text>");
      for (var k = 0; k < maxv; k++) {
        parts.push('<circle cx="' + (lw + k * cw + 4) + '" cy="' + (y + 7) + '" r="4" class="' +
          (k < x ? "nv-stone" + cls : "nv-slot") + '"/>');
      }
    });
    parts.push("</svg>");
    return parts.join("");
  }
  function boardFig(P, B, title, sub, mark) {
    return '<figure class="nv-bfig"><figcaption><span class="nv-bt">' + esc(title) + "</span> " +
      '<span class="nv-bv">' + tuple(P) + "</span>" + (sub ? '<span class="nv-bs">' + sub + "</span>" : "") +
      "</figcaption>" + boardSVG(P, B, title, mark) + "</figure>";
  }

  /* ======================= 1. two-frame restoration ======================= */

  function restore(t, opts) {
    opts = opts || {};
    var B = t.B, N = t.N, h = [];
    var pr = t.promise;
    h.push('<p class="nv-promise ' + (pr.ok ? "ok" : "off") + '">' + (pr.ok
      ? "<strong>Inside the promise.</strong> The earlier board has nim-sum 0 and the opponent decreased one heap, " +
        "so the restoration theorem guarantees that the output restores nim-sum 0."
      : "<strong>Outside the promise:</strong> " + esc(pr.reason) + ". The circuit still produces an output, " +
        "but the restoration theorem says nothing about it. This is not a promised zero predecessor.") + "</p>");
    var chgMark = {}, resMark = {};
    t.chg.forEach(function (c, i) { if (c) chgMark[i] = "nv-chg"; });
    if (t.move) resMark[t.move[0]] = "nv-res";
    h.push('<div class="nv-boards">' + boardFig(t.Q, B, "Earlier board Q", "nim-sum " + t.nimQ, {}) +
      '<span class="nv-arrow" aria-hidden="true">→</span>' +
      boardFig(t.Qp, B, "Current board Q′", "nim-sum " + t.nimQp + (t.chg.some(Boolean) ? "; changed: heap " + t.chg.map(function (c, i) { return c ? i : -1; }).filter(function (i) { return i >= 0; }).join(", ") : "; nothing changed"), chgMark) +
      '<span class="nv-arrow" aria-hidden="true">→</span>' +
      (t.R ? boardFig(t.R, B, "After the reply", "nim-sum " + t.nimR + "; reply in heap " + t.move[0], resMark)
           : '<figure class="nv-bfig nv-none"><figcaption><span class="nv-bt">No reply</span></figcaption>' +
             '<p>The current board is terminal: there is no legal move.</p></figure>') + "</div>");

    h.push('<ol class="nv-stages">');
    // 1. frames
    var rows = t.Q.map(function (_, i) {
      return "<tr><th scope=\"row\">" + i + "</th><td>" + t.Q[i] + " " + bits(t.x[i]) + "</td><td>" + t.Qp[i] + " " +
        bits(t.xp[i]) + "</td><td>" + bits(t.y[i]) + "</td><td>" + (t.chg[i] ? '<strong class="nv-chg-t">changed</strong>' : '<span class="nv-dim">same</span>') + "</td></tr>";
    }).join("");
    h.push('<li class="nv-stage"><h4>Compare the frames bit by bit</h4><p>Each heap is a ' + B +
      "-bit block. For every heap and every bit position, one two-input XOR compares Q with Q′, all in parallel.</p>" +
      '<div class="nv-scroll"><table class="nv-t"><thead><tr><th scope="col">Heap</th><th scope="col">Q ' + weights(B) +
      '</th><th scope="col">Q′ ' + weights(B) + '</th><th scope="col">XOR</th><th scope="col">Heap</th></tr></thead><tbody>' +
      rows + "</tbody></table></div></li>");
    // 2. delta
    var xorAll = 0;
    t.y.forEach(function (row) { xorAll ^= C.toNatBE(row); });
    var multi = t.chg.filter(Boolean).length > 1;
    h.push('<li class="nv-stage"><h4>Extract the difference δ</h4><p>Bit k of δ is the OR of column k of the XOR table: ' +
      bits(t.deltaBE) + " = <strong>δ = " + t.delta + "</strong>.</p><p class=\"nv-note\">" +
      (multi ? "Here " + t.chg.filter(Boolean).length + " heaps changed, so OR and XOR can differ (the XOR of all rows is " +
        xorAll + "). The single-change promise is what makes the OR circuit correct."
             : "At most one heap changed, so at most one row is nonzero and the OR equals the XOR of the rows, which is " +
               "nim(Q) ⊕ nim(Q′).") + "</p></li>");
    // 3. candidates
    var crow = t.Qp.map(function (x, i) {
      return "<tr><th scope=\"row\">" + i + "</th><td>" + x + " " + bits(t.xp[i], { mark: t.top }) + "</td><td>" + t.cand[i] +
        " " + bits(C.bitsBE(t.cand[i], B), { mark: t.top }) + "</td><td>" + yes(t.cancel[i], "passes: " + t.cand[i] + " < " + x,
        t.delta === 0 ? "equal" : "fails: " + t.cand[i] + " > " + x) + "</td></tr>";
    }).join("");
    var cmp = t.Qp.map(function (x, i) {
      var ct = C.compareTrace(B, x, t.cand[i]);
      return "<li>Heap " + i + ": " + bits(ct.xb, { mark: ct.first }) + " vs " + bits(ct.cb, { mark: ct.first }) + " — " +
        (ct.first < 0 ? "no bit differs, so the value is unchanged (not a decrease)."
          : "the highest differing bit has weight " + Math.pow(2, B - 1 - ct.first) + "; the heap has " + b01(ct.xb[ct.first]) +
            " there, so the replacement is " + (ct.less ? "smaller." : "larger.")) + "</li>";
    }).join("");
    h.push('<li class="nv-stage"><h4>Propose replacements and test them in parallel</h4><p>For every heap at once: ' +
      "replace Q′<sub>i</sub> by Q′<sub>i</sub> ⊕ δ and test whether that is a decrease. " +
      (t.top >= 0 ? "The decisive bit is the highest set bit of δ (weight " + Math.pow(2, B - 1 - t.top) + "): a heap passes exactly when it has that bit set."
                  : "Here δ = 0, so no replacement is a decrease.") + "</p>" +
      '<div class="nv-scroll"><table class="nv-t"><thead><tr><th scope="col">Heap</th><th scope="col">Q′ ' + weights(B) +
      '</th><th scope="col">Q′ ⊕ δ</th><th scope="col">Test</th></tr></thead><tbody>' + crow + "</tbody></table></div>" +
      '<details class="nv-more"' + (opts.open === "compare" ? " open" : "") + "><summary>Show the bit comparisons</summary>" +
      "<p>The test x ⊕ δ &lt; x is a fixed-depth circuit: an OR over the possible highest differing bit, requiring equality " +
      "above it, a 1 in x and a 0 in the replacement at that bit.</p><ul class=\"nv-cmp\">" + cmp + "</ul></details>" +
      "<p>Candidates passing: <strong>" + t.candidates + "</strong>" + (t.candidates > 1 ? " (the next step takes the first)." : ".") + "</p></li>");
    // 4. selection
    var srow = t.Qp.map(function (x, i) {
      return "<tr><th scope=\"row\">" + i + "</th><td>" + b01(t.cancel[i]) + "</td><td>" + b01(t.nz[i]) + "</td><td>" +
        (t.nz[i] ? x + " − 1 = " + t.dec[i] : "—") + "</td><td><strong>" + b01(t.s[i]) + "</strong></td></tr>";
    }).join("");
    var branchText = {
      cancel: "At least one replacement passes, so the flags are the passing tests and the fallback is masked off.",
      fallback: "No replacement passes. The selector falls back to the first nonzero heap minus one. " +
        (pr.ok ? "" : "Inside the promise this branch is never used; here it is, because the input is outside the promise."),
      terminal: "No heap is nonzero: the current board is terminal, so the validity output is 0 and there is no move."
    }[t.branch];
    h.push('<li class="nv-stage"><h4>Choose between cancelling and the fallback</h4><p><span class="nv-branch nv-br-' + t.branch + '">' +
      { cancel: "cancelling move", fallback: "fallback move", terminal: "terminal board" }[t.branch] + "</span> " + branchText + "</p>" +
      '<div class="nv-scroll"><table class="nv-t"><thead><tr><th scope="col">Heap</th><th scope="col">passes</th><th scope="col">nonzero</th>' +
      '<th scope="col">fallback value</th><th scope="col">flag s<sub>i</sub></th></tr></thead><tbody>' + srow + "</tbody></table></div></li>");
    // 5. priority encoding
    var prow = t.s.map(function (sv, i) {
      return "<tr><th scope=\"row\">" + i + "</th><td>" + bits(C.bitsBE(i, t.r)) + "</td><td>" + b01(sv) + "</td><td><strong>" + b01(t.f[i]) + "</strong></td></tr>";
    }).join("");
    var firstI = t.f.indexOf(true);
    h.push('<li class="nv-stage"><h4>Encode the first flagged heap as a binary index</h4><p>For N = ' + N + (N === 1 ? " heap" : " heaps") +
      " the construction uses r = ⌊log<sub>2</sub> N⌋ + 1 = " + t.r + " index bit" + (t.r === 1 ? "" : "s") + " (the encoder itself needs only N ≤ 2<sup>r</sup>). " +
      (firstI >= 0 ? "The first flag is at heap " + firstI + ", so the index bits are " + bits(t.idxBits) + "."
                   : "No flag is set, so all index bits are 0 and validity is 0.") + "</p>" +
      '<details class="nv-more"' + (opts.open === "priority" ? " open" : "") + "><summary>Show the priority encoder</summary>" +
      "<p>f<sub>i</sub> = s<sub>i</sub> ∧ ¬s<sub>j</sub> for all j &lt; i keeps only the first flag; index bit k is the OR of f<sub>i</sub> " +
      "over the heaps i whose binary index has a 1 at bit k. This is a fixed-depth circuit, not a search.</p>" +
      '<div class="nv-scroll"><table class="nv-t"><thead><tr><th scope="col">Heap i</th><th scope="col">i in binary</th>' +
      '<th scope="col">s<sub>i</sub></th><th scope="col">first f<sub>i</sub></th></tr></thead><tbody>' + prow + "</tbody></table></div>" +
      "<p>Index bits (OR of the f<sub>i</sub> in each 1-column): " + bits(t.idxBits) + "</p></details></li>");
    // 6. output
    h.push('<li class="nv-stage"><h4>Output the move</h4><p class="nv-fields" aria-label="Output fields">' +
      '<span class="nv-field"><span class="nv-fl">validity</span>' + bits([t.valid]) + "</span>" +
      '<span class="nv-sep" aria-hidden="true">|</span><span class="nv-field"><span class="nv-fl">index (' + t.r + (t.r === 1 ? " bit)" : " bits)") + "</span>" + bits(t.idxBits) + "</span>" +
      '<span class="nv-sep" aria-hidden="true">|</span><span class="nv-field"><span class="nv-fl">value (' + B + " bits)</span>" + bits(t.valBits) + "</span></p>" +
      "<p>" + (t.move ? "Decoded move: set heap " + t.move[0] + " to " + t.move[1] + ". New board " + tuple(t.R) + ", nim-sum <strong>" + t.nimR +
        "</strong>." + (pr.ok ? "" : (t.nimR === 0 ? " Here the reply happens to reach nim-sum 0; outside the promise nothing guarantees this " +
        '(compare the paper’s <a href="claims/c-init-boundary.html">initialisation-boundary example</a>).' : " The nim-sum is not 0: nothing was promised here."))
        : "Validity 0: no move.") + "</p></li>");
    h.push("</ol>");
    return h.join("");
  }

  /* ======================= 2. Boolean-to-threshold compilation ======================= */

  var FORMULAS = {
    and: { label: "AND(a, b)", lean: "and [input 0, input 1]", n: 2 },
    or: { label: "OR(a, b)", lean: "or [input 0, input 1]", n: 2 },
    not: { label: "NOT a", lean: "not (input 0)", n: 1 },
    xor: { label: "XOR(a, b)", lean: "xor2 (input 0) (input 1) = or [and [a, not b], and [not a, b]]", n: 2 }
  };
  /* Hand-made teaching circuits in the same gate model (weights and thresholds in {0, 1}).
     These are NOT the compiler's output; they show how few layers suffice for a tiny formula. */
  var TEACH = {
    and: [[{ w: [1, 1], neg: [true, true], thr: 1, label: "OR(¬a, ¬b) = NAND" }],
          [{ w: [1], neg: [true], thr: 1, label: "OR(¬h) = AND" }]],
    or: [[{ w: [1, 1], neg: [false, false], thr: 1, label: "OR(a, b)" }]],
    not: [[{ w: [1], neg: [true], thr: 1, label: "OR(¬a) = NOT a" }]],
    xor: [[{ w: [1, 1], neg: [true, false], thr: 1, label: "u = OR(¬a, b)" }, { w: [1, 1], neg: [false, true], thr: 1, label: "v = OR(a, ¬b)" }],
          [{ w: [1, 1], neg: [true, true], thr: 1, label: "OR(¬u, ¬v) = XOR(a, b)" }]]
  };
  function gateText(g) {
    if (!g.w.length) return g.thr === 0 ? "constant 1" : "constant 0";
    var lits = [];
    g.w.forEach(function (w, j) { if (w) lits.push((g.neg[j] ? "¬" : "") + "w" + j); });
    return "fires if " + (lits.length ? lits.join(" + ") : "0") + " ≥ " + g.thr;
  }
  function opText(prog, g) {
    var d = prog[g], names = ["a", "b", "c", "d"];
    if (d.op === "inp") return "input " + (names[d.i] || "x" + d.i);
    if (d.op === "cst") return "constant " + b01(d.b);
    if (d.op === "neg") return "NOT g" + d.a;
    return (d.op === "and" ? "AND(" : "OR(") + d.as.map(function (a) { return "g" + a; }).join(", ") + ")";
  }
  var ROLE_ABBR = { "read input": "in", "constant": "c", "idle": "·", "copy": "copy", "NOT": "NOT", "OR": "OR",
    "negate (AND, 2nd layer)": "AND₂", "OR of negated inputs (AND, 1st layer)": "AND₁", "output": "out" };

  function compile(state, data) {
    var f = state.formula, F = FORMULAS[f], net = data.nets[f];
    var input = state.input.slice(0, F.n);
    var h = [];
    var depth = net.depths[0], S = net.prog.length, L = net.layers.length;
    h.push('<p class="nv-formula">Formula: <strong>' + esc(F.label) + "</strong> <span class=\"nv-lean\">(Lean term: <code>" + esc(F.lean) +
      "</code>)</span>. Boolean depth d = " + depth + ", formula size " + net.sizes[0] + ".</p>");
    var ins = input.map(function (v, k) { return '<span class="nv-in">' + ["a", "b"][k] + " = " + b01(v) + "</span>"; }).join(" ");
    h.push('<p class="nv-inputs">Input: ' + ins + "</p>");
    // teaching circuit
    var tl = TEACH[f], z = input.slice(), trows = [];
    tl.forEach(function (layer, li) {
      var out = layer.map(function (g) { return C.gateEval(g, z); });
      trows.push("<tr><th scope=\"row\">" + (li + 1) + "</th><td>" + layer.map(function (g, k) {
        return esc(g.label) + " → <strong>" + b01(out[k]) + "</strong>";
      }).join("<br>") + "</td></tr>");
      z = out;
    });
    h.push('<div class="nv-pair"><section class="nv-sub"><h4><span class="vis-kind vis-kind-teaching">Teaching example</span> A hand-made circuit</h4>' +
      "<p>" + tl.length + " threshold layer" + (tl.length === 1 ? "" : "s") + ", the fewest possible in this gate model. Every gate is an OR of literals with " +
      "weights 1 and threshold 1, so an AND needs two layers (De Morgan).</p><table class=\"nv-t\"><thead><tr><th scope=\"col\">Layer</th><th scope=\"col\">Gates</th></tr></thead><tbody>" +
      trows.join("") + "</tbody></table><p>Output: <strong>" + b01(z[0]) + "</strong></p></section>");
    // compiled network
    var vals = C.netEval(net.layers, input), nComp = L - 1, head = "<th scope=\"col\">Program gate</th>";
    for (var t = 1; t <= L; t++) head += '<th scope="col">' + (t === L ? "out" : t) + "</th>";
    var grows = [];
    for (var g = 0; g < S; g++) {
      var cells = "";
      for (var t2 = 1; t2 <= L; t2++) {
        if (t2 === L) {
          var k = net.outs.indexOf(g);
          cells += k >= 0 ? '<td class="nv-cell nv-r-out" title="' + esc(gateText(net.layers[L - 1][k])) + '">out<br><strong>' + b01(vals[L - 1][k]) + "</strong></td>" : "<td></td>";
          continue;
        }
        var role = C.compileRole(net.prog, net.levels, g, t2, nComp), ab = ROLE_ABBR[role] || role;
        var gate = net.layers[t2 - 1][g];
        cells += '<td class="nv-cell nv-r-' + ab.replace(/[^a-z0-9]/gi, "") + '" title="' + esc(role + ": " + gateText(gate)) + '">' + esc(ab) +
          "<br><strong>" + b01(vals[t2 - 1][g]) + "</strong></td>";
      }
      grows.push('<tr><th scope="row">g' + g + " = " + esc(opText(net.prog, g)) + "</th>" + cells + "</tr>");
    }
    var gates = net.layers.reduce(function (acc, l) { return acc + l.length; }, 0);
    var bound = (2 * depth + 1) * S + net.outs.length;
    h.push('<section class="nv-sub"><h4><span class="vis-kind vis-kind-exact">Exact construction trace</span> What the checked compiler builds</h4>' +
      "<p>The network <code>ThresholdNet.compileF</code> produces for this formula, as Lean computes it: " + L + " layers (the bound is 2d + 2 = " + (2 * depth + 2) + "); " +
      "each of the " + nComp + " computing layers has one wire per program gate (S = " + S + "); " + gates +
      " gates in total (the bound is (2d + 1)S + K = " + bound + "). Each cell shows what that wire does at that layer and its value on the input above. " +
      "“·” is an idle wire (constant 0 until its inputs are ready); “copy” is an identity buffer. Layer 1 reads the inputs into the " +
      "construction and the last layer arranges the outputs: these are the two extra layers in 2d + 2, and the factor 2 lets every " +
      "Boolean level cost as much as an AND.</p>" +
      '<div class="nv-scroll"><table class="nv-t nv-grid"><thead><tr>' + head + "</tr></thead><tbody>" + grows.join("") + "</tbody></table></div>" +
      "<p>Output: <strong>" + b01(vals[L - 1][0]) + "</strong></p></section></div>");
    // truth table
    var tt = net.table.map(function (row) {
      var zz = row.in.slice();
      tl.forEach(function (layer) { zz = layer.map(function (gg) { return C.gateEval(gg, zz); }); });
      var nv = C.netEval(net.layers, row.in), out = nv[nv.length - 1][0];
      var agree = out === row.formula[0] && zz[0] === row.formula[0];
      return "<tr><td>" + row.in.map(b01).join(" ") + "</td><td>" + b01(row.formula[0]) + "</td><td>" + b01(zz[0]) + "</td><td>" + b01(out) +
        "</td><td>" + yes(agree, "agree", "DIFFER") + "</td></tr>";
    }).join("");
    h.push('<h4 class="nv-h">Truth table</h4><div class="nv-scroll"><table class="nv-t"><thead><tr><th scope="col">' + (F.n === 1 ? "a" : "a b") +
      '</th><th scope="col">formula</th><th scope="col">teaching circuit</th><th scope="col">compiled network</th><th scope="col"></th></tr></thead><tbody>' +
      tt + "</tbody></table></div>");
    return h.join("");
  }

  function depthAccounting(data) {
    var parts = [["frame difference", 4], ["candidate tests and replacement bits", 4], ["selection, fallback and output", 9], ["binary index", 3]];
    var total = 20, bar = parts.map(function (p, k) {
      return '<span class="nv-seg nv-seg' + k + '" style="flex:' + p[1] + '"><span>' + p[1] + "</span></span>";
    }).join("");
    var legend = parts.map(function (p, k) { return '<li><span class="nv-key nv-seg' + k + '" aria-hidden="true"></span>' + p[1] + " · " + esc(p[0]) + "</li>"; }).join("");
    var rs = (data.restsize || []).map(function (r) {
      return "<tr><td>B = " + r.B + ", N = " + r.N + "</td><td>" + r.D + "</td><td>" + r.layers + "</td><td>" + r.S.toLocaleString("en-GB") +
        "</td><td>" + r.gates.toLocaleString("en-GB") + "</td></tr>";
    }).join("");
    return '<div class="nv-acct"><p>The two-frame selector’s depth bound is a sum of bounds for composed subcircuits:</p>' +
      '<div class="nv-bar" role="img" aria-label="Boolean depth bound 4 plus 4 plus 9 plus 3 equals 20">' + bar + "</div>" +
      '<ul class="nv-legend">' + legend + "</ul>" +
      "<p><strong>Boolean depth ≤ " + total + "</strong> → the compiler’s rule 2d + 2 → <strong>at most " + (2 * total + 2) + " threshold layers</strong>.</p>" +
      (rs ? "<p>For comparison, the actual formulas for small boards, measured by Lean (the compiler uses their real depth D, not the bound):</p>" +
        '<div class="nv-scroll"><table class="nv-t"><thead><tr><th scope="col">Board size</th><th scope="col">depth D</th><th scope="col">layers 2D + 2</th>' +
        '<th scope="col">width S (formula nodes)</th><th scope="col">gates (2D + 1)S + K</th></tr></thead><tbody>' + rs + "</tbody></table></div>" +
        "<p class=\"nv-note\">The width counts every node of every output formula, duplicates included, so it is far from economical. " +
        "These numbers describe the uniform construction, not an optimised network and not a trained one.</p>" : "") + "</div>";
  }

  /* ======================= 3. structured rollouts ======================= */

  var KIND_LABEL = { reset: "reset", move: "move", terminal: "terminal test", consume: "store outcome and reload", stop: "store outcome and stop", readout: "readout" };

  function rollout(tr, step, opts) {
    opts = opts || {};
    var B = tr.B, P = tr.P, last = tr.ticks.length - 1, h = [];
    var total = tr.early ? tr.ticks.length : tr.ticks.length + 1;
    if (step === undefined || step === null) step = total - 1;
    var isReadout = !tr.early && step === tr.ticks.length;
    var tk = isReadout ? null : tr.ticks[Math.min(step, last)];
    var st = isReadout ? tr.ticks[last].state : tk.state;
    // timeline
    var cells = tr.ticks.map(function (t, k) {
      var lab = KIND_LABEL[t.kind] + (t.head !== undefined ? ", head " + t.head : "");
      return '<li class="nv-tk nv-k-' + t.kind + (t.kind === "consume" || t.kind === "stop" ? " endhead" : "") + (k === step ? " cur" : "") + (k > step ? " later" : "") + '" data-step="' + k + '" title="tick ' + (k + 1) + ": " + esc(lab) + '"><span class="nv-sr">tick ' + (k + 1) + ": " + esc(lab) + "</span></li>";
    });
    if (!tr.early) cells.push('<li class="nv-tk nv-k-readout' + (isReadout ? " cur" : "") + '" data-step="' + tr.ticks.length + '" title="readout"><span class="nv-sr">readout</span></li>');
    h.push('<div class="nv-tl-wrap"><p class="nv-tl-cap">' + total + " component evaluations" + (tr.early ? "" : " (" + tr.ticks.length + " controller ticks and one readout)") +
      '. Colours: <span class="nv-key nv-k-reset"></span>reset <span class="nv-key nv-k-move"></span>move <span class="nv-key nv-k-terminal"></span>terminal test ' +
      '<span class="nv-key nv-k-consume"></span>store and reload <span class="nv-key nv-k-stop"></span>store and stop' + (tr.early ? "" : ' <span class="nv-key nv-k-readout"></span>readout') +
      '.</p><ol class="nv-tl" aria-label="Ticks">' + cells.join("") + "</ol></div>");
    // current tick
    var now = isReadout ? "Readout: one evaluation of the readout circuit on the original board and the " + B + " stored outcome bits."
                        : tk.text;
    h.push('<p class="nv-now"><span class="nv-step">' + (isReadout ? total : step + 1) + " / " + total + "</span> " + esc(now) + "</p>");
    var mark = {};
    if (tk && tk.kind === "move") mark[tk.heap] = "nv-res";
    var stored = {};
    for (var q = 0; q <= Math.min(step, last); q++) {
      var tq = tr.ticks[q];
      if (tq.kind === "consume" || tq.kind === "stop") stored[tq.head] = true;
    }
    var outs = st.outs.map(function (o, j) {
      return '<span class="nv-o' + (stored[j] ? " set" : "") + '">o<sub>' + j + "</sub> = " + (stored[j] ? b01(o) : "?") + "</span>";
    }).join(" ");
    h.push('<div class="nv-regs"><div class="nv-boards">' + boardFig(st.board, B, "Working board", "", mark) +
      boardFig(P, B, "Original board (read-only input)", "", {}) + "</div>" +
      '<dl class="nv-dl"><div><dt>head j</dt><dd>' + st.j + "</dd></div><div><dt>parity of moves</dt><dd>" + b01(st.par) + "</dd></div>" +
      "<div><dt>rollout finished</dt><dd>" + b01(st.halted) + "</dd></div><div><dt>running</dt><dd>" + b01(st.run) + "</dd></div>" +
      "<div><dt>some outcome 1</dt><dd>" + b01(st.dec) + "</dd></div><div><dt>stored outcomes</dt><dd>" + outs + "</dd></div></dl></div>");
    // readout / decision
    if (tr.early) {
      h.push('<div class="nv-readout"><h4>Classification</h4><p>' + (st.run ? "Still running." : (tr.dec
        ? "An outcome 1 was observed at head " + (tr.headsRun - 1) + ", so σ(P) ≠ 0 and the controller stops after " + tr.headsRun + " of " + B + " heads."
        : "All " + B + " outcomes are 0, so σ(P) = 0.")) + " This schedule decides whether the position is winning; it does not collect the bits a move needs.</p></div>");
    } else {
      var done = !st.run;
      var sb = tr.sigmaBits.map(function (b, j) { return "σ<sub>" + j + "</sub> = " + (j === 0 ? "o<sub>0</sub>" : "o<sub>" + j + "</sub> ⊕ o<sub>0</sub>") + " = " + b01(b); }).join("; ");
      var tests = P.map(function (x, i) { var c = x ^ tr.sigma; return "<li>heap " + i + ": " + x + " ⊕ " + tr.sigma + " = " + c + " " + (c < x ? yes(true, "smaller") : yes(false, "", "not smaller")) + "</li>"; }).join("");
      h.push('<div class="nv-readout' + (done ? "" : " pending") + '"><h4>Readout</h4>' + (done
        ? "<p>" + sb + ", so <strong>σ = " + tr.sigma + "</strong>. The readout tests every heap in parallel and takes the first that decreases:</p><ul class=\"nv-cmp\">" + tests + "</ul><p>" +
          (tr.readout ? "Move: set heap " + tr.readout[0] + " to " + tr.readout[1] + " → " + tuple(C.setAt(P, tr.readout[0], tr.readout[1])) + ", nim-sum " + C.nimSum(C.setAt(P, tr.readout[0], tr.readout[1])) +
            (tr.readoutBranch === "fallback" ? " (σ = 0: no cancelling move, so the fallback subtracts one from the first nonzero heap)." : ".") : "The board is terminal: no move.") + "</p>"
        : "<p>The readout runs after the last outcome has been stored.</p>") + "</div>");
    }
    // counts
    var perHead = tr.movesPerHead.slice(0, tr.headsRun), hr = tr.headsRun;
    h.push('<div class="nv-counts"><h4>Counting the work</h4><ul>' +
      "<li>Simulated moves M = " + (perHead.length > 1 ? perHead.join(" + ") + " = " : "") + "<strong>" + tr.moves + "</strong> (" + hr + " head" + (hr === 1 ? "" : "s") + " run).</li>" +
      (tr.early ? "<li>Evaluations: 1 reset + M moves + " + hr + " terminal test" + (hr === 1 ? "" : "s") + " + " + hr + " outcome update" + (hr === 1 ? "" : "s") +
                  " = <strong>" + tr.evaluations + "</strong>. The early-exit schedule ends with its classification; it reads out no move.</li>"
                : "<li>Evaluations M + 2B + 2 = " + tr.moves + " + " + 2 * B + " + 2 = <strong>" + tr.evaluations + "</strong>: " + tr.moves + " move updates, " + B + " terminal tests, " + B +
                  " outcome updates, 1 reset, 1 readout.</li><li>Bound on M: BN(2<sup>B</sup> − 1) = " + B * P.length * (Math.pow(2, B) - 1) + ".</li>") +
      "<li>Each single evaluation is a shallow circuit: one policy step has Boolean depth ≤ 17 (≤ 36 threshold layers), the readout ≤ 19 (≤ 40), " +
      "one controller tick ≤ 34 (≤ 70). Those bounds are per evaluation; the number of evaluations grows with the board. That no shallow family computes " +
      "the complete board-to-move map is a separate statement, conditional on the named classical input that parity is not in AC<sup>0</sup>.</li></ul></div>");
    // full table
    var rows = tr.ticks.map(function (t, k) {
      return "<tr" + (k === step ? ' class="cur"' : "") + "><td>" + (k + 1) + "</td><td>" + esc(KIND_LABEL[t.kind]) + "</td><td>" + tuple(t.state.board) + "</td><td>" + t.state.j +
        "</td><td>" + b01(t.state.par) + "</td><td>" + t.state.outs.map(b01).join("") + "</td><td>" + esc(t.text) + "</td></tr>";
    }).join("");
    h.push('<details class="nv-more"><summary>All ' + tr.ticks.length + " controller ticks as a table</summary><div class=\"nv-scroll\"><table class=\"nv-t nv-small\"><thead><tr>" +
      '<th scope="col">Tick</th><th scope="col">Kind</th><th scope="col">Working board</th><th scope="col">j</th><th scope="col">parity</th><th scope="col">o₀…</th><th scope="col">What happens</th></tr></thead><tbody>' +
      rows + "</tbody></table></div></details>");
    return h.join("");
  }

  /* ======================= 4. recurrence ======================= */

  function tokLabel(t) { return t.t === "row" ? "row " + t.x : (t.t === "sep" ? "SEP" : "RESET"); }
  function moveOut(m) { return m ? "heap " + m[0] + " → " + m[1] : "no move"; }

  function recurrence(rt, step, opts) {
    opts = opts || {};
    var steps = rt.steps, total = steps.length, h = [];
    if (step === undefined || step === null) step = total - 1;
    var cur = steps[step];
    // token strip with decision grouping
    var chips = steps.map(function (s, k) {
      var cls = "nv-tok nv-t-" + s.tok.t + (s.phase ? " nv-ph-" + s.phase : "") + (s.phase === "move" ? " enddec" : "") + (k === step ? " cur" : "") + (k > step ? " later" : "");
      return '<li class="' + cls + '" data-step="' + k + '"><span class="nv-tok-l">' + esc(tokLabel(s.tok)) + "</span>" + (s.phase ? '<span class="nv-tok-p">' + esc(s.phase) + "</span>" : "") + "</li>";
    }).join("");
    h.push('<ol class="nv-toks" aria-label="Input tokens">' + chips + "</ol>");
    h.push('<p class="nv-now"><span class="nv-step">' + (step + 1) + " / " + total + "</span> " + esc(tokLabel(cur.tok)) + ": " + esc(cur.action) + "</p>");
    var s = cur.state, regs;
    if (rt.protocol === "summary") {
      regs = '<dl class="nv-dl">' +
        "<div><dt>accumulator s</dt><dd>" + s.acc + " " + bits(C.bitsBE(s.acc, rt.B)) + "</dd></div>" +
        "<div><dt>previous summary q</dt><dd>" + s.prev + " " + bits(C.bitsBE(s.prev, rt.B)) + "</dd></div>" +
        "<div><dt>validity v</dt><dd>" + b01(s.valid) + "</dd></div></dl>";
    } else if (rt.protocol === "replay") {
      regs = '<dl class="nv-dl">' +
        "<div><dt>mode</dt><dd>" + (s.replay ? "replay" : "scan") + "</dd></div>" +
        "<div><dt>accumulator</dt><dd>" + s.acc + " " + bits(C.bitsBE(s.acc, rt.B)) + "</dd></div>" +
        "<div><dt>previous summary</dt><dd>" + s.prev + " " + bits(C.bitsBE(s.prev, rt.B)) + (s.valid ? "" : " (none yet)") + "</dd></div>" +
        "<div><dt>stored summary used in replay</dt><dd>" + s.sig + "</dd></div>" +
        "<div><dt>heap counter</dt><dd>" + s.idx + "</dd></div>" +
        "<div><dt>first candidate</dt><dd>" + moveOut(s.sel) + "</dd></div>" +
        "<div><dt>first fallback</dt><dd>" + moveOut(s.fnz) + "</dd></div></dl>";
    } else {
      regs = '<dl class="nv-dl">' +
        "<div><dt>stored board</dt><dd>" + tuple(s.board) + "</dd></div>" +
        "<div><dt>accumulator</dt><dd>" + s.acc + " " + bits(C.bitsBE(s.acc, rt.B)) + "</dd></div>" +
        "<div><dt>write pointer</dt><dd>" + s.idx + "</dd></div></dl>";
    }
    var outs = [];
    for (var k = 0; k <= step; k++) {
      var o = steps[k].out;
      if (!o) continue;
      if (o.summary !== undefined && o.move === undefined) outs.push("<li>after token " + (k + 1) + ": summary σ = " + o.summary + (o.diff === null ? " (no previous summary)" : ", difference from the previous summary " + o.diff) + "</li>");
      else if (o.summary !== undefined) outs.push("<li>after token " + (k + 1) + ": summary σ = " + o.summary + ", move " + moveOut(o.move) + "</li>");
      else outs.push("<li>after token " + (k + 1) + ": move " + moveOut(o.move) + "</li>");
    }
    h.push('<div class="nv-regs2"><section class="nv-sub"><h4>Registers after this update</h4>' + regs + "</section>" +
      '<section class="nv-sub"><h4>Outputs so far</h4>' + (outs.length ? '<ul class="nv-outs">' + outs.join("") + "</ul>" : "<p>None yet.</p>") + "</section></div>");
    var N = rt.N;
    if (rt.note) h.push('<p class="nv-note">' + esc(rt.note) + "</p>");
    var seq = "The number of sequential updates grows with N. That no shallow family computes the complete board-to-move map is a separate " +
      "statement, conditional on the named classical input that parity is not in AC<sup>0</sup>.";
    if (rt.protocol === "summary") {
      h.push('<div class="nv-counts"><h4>Counting the work</h4><ul>' +
        "<li>Each position of " + N + " heaps takes N + 1 = <strong>" + (N + 1) + "</strong> updates: its rows and a separator. The state is (s, q, v): 2B + 1 = " +
        (2 * rt.B + 1) + " bits.</li><li>The summary alone does not choose a move: that needs the rows again (replay) or a stored board.</li>" +
        "<li>Each output bit of one update is a formula of depth ≤ 4. " + seq + "</li></ul></div>");
    } else h.push('<div class="nv-counts"><h4>Counting the work</h4><ul>' +
      (rt.protocol === "replay"
        ? "<li>One decision on " + N + " heaps takes 2N + 2 = <strong>" + (2 * N + 2) + "</strong> updates: N scan rows, a separator, the same N rows again, a separator (plus one reset at the start of a game). The board is supplied twice; the controller does not store it.</li>" +
          "<li>Memory: accumulator, previous summary, stored summary, counter, candidate and fallback registers: 4 + 5B + 3r bits with N &lt; 2<sup>r</sup>; here B = " + rt.B + ", r = " + C.rIdx(N) + ", so " + (4 + 5 * rt.B + 3 * C.rIdx(N)) + " bits.</li>"
        : "<li>One decision on " + N + " heaps takes N + 1 = <strong>" + (N + 1) + "</strong> updates: one pass over the rows and a separator. The price is storing the whole board: NB + B + r bits; here " + (N * rt.B + rt.B + C.rIdx(N)) + " bits.</li>") +
      (rt.protocol === "replay"
        ? "<li>Each single update is a shallow circuit (replay controller: Boolean depth ≤ 8, ≤ 18 threshold layers). " + seq + "</li></ul></div>"
        : "<li>Each single update is a shallow circuit (board storage: state updates of Boolean depth ≤ 8, outputs ≤ 16; ≤ 34 threshold layers). " + seq + "</li></ul></div>"));
    var rows = steps.map(function (st, k) {
      var o = st.out, os = !o ? "" : (o.move !== undefined && o.summary === undefined ? "move " + moveOut(o.move) : "σ = " + o.summary + (o.diff !== undefined && o.diff !== null ? ", diff " + o.diff : "") + (o.move !== undefined ? ", move " + moveOut(o.move) : ""));
      var sv = rt.protocol === "replay" ? (st.state.replay ? "replay" : "scan") + ", acc " + st.state.acc + ", prev " + st.state.prev + (st.state.valid ? "" : "*") + ", idx " + st.state.idx + ", cand " + moveOut(st.state.sel) + ", fb " + moveOut(st.state.fnz)
        : rt.protocol === "summary" ? "s " + st.state.acc + ", q " + st.state.prev + ", v " + b01(st.state.valid)
        : "board " + tuple(st.state.board) + ", acc " + st.state.acc + ", ptr " + st.state.idx;
      return "<tr" + (k === step ? ' class="cur"' : "") + "><td>" + (k + 1) + "</td><td>" + esc(tokLabel(st.tok)) + "</td><td>" + esc(sv) + "</td><td>" + esc(os) + "</td></tr>";
    }).join("");
    h.push('<details class="nv-more"><summary>All ' + total + " updates as a table</summary><div class=\"nv-scroll\"><table class=\"nv-t nv-small\"><thead><tr>" +
      '<th scope="col">#</th><th scope="col">Token</th><th scope="col">Registers after</th><th scope="col">Output</th></tr></thead><tbody>' + rows + "</tbody></table></div>" +
      (rt.protocol === "replay" ? "<p class=\"nv-note\">* no previous summary yet (validity bit 0).</p>" : "") + "</details>");
    return h.join("");
  }

  function summaryCompare(game, machine) {
    machine = machine || "replay";
    function table(title, positions, note) {
      var outs;
      if (machine === "summary") {      // Recurrent.step on serialised positions
        outs = C.summRun(positions).filter(function (x) { return x.out; }).map(function (x) { return x.out; });
      } else {                          // the replay controller on Controller.stream (as in Bypass.diff_with_postMove)
        var toks = [];
        positions.forEach(function (P) { toks = toks.concat(C.dtoks(P)); });
        outs = C.crun(toks).filter(function (x) { return x.out && x.out.summary !== undefined; }).map(function (x) { return x.out; });
      }
      var rows = positions.map(function (P, k) {
        var o = outs[k];
        return "<tr><td>" + tuple(P) + "</td><td>" + o.summary + "</td><td>" + (o.diff === null ? "—" : "<strong>" + o.diff + "</strong>") + "</td></tr>";
      }).join("");
      return '<section class="nv-sub"><h4>' + esc(title) + '</h4><table class="nv-t"><thead><tr><th scope="col">Position fed</th><th scope="col">summary σ</th>' +
        '<th scope="col">difference</th></tr></thead><tbody>' + rows + "</tbody></table><p>" + note + "</p></section>";
    }
    var P1 = game.P1, R1 = game.R1, P2 = game.P2, dA = C.nimSum(P1) ^ C.nimSum(R1), dO = C.nimSum(R1) ^ C.nimSum(P2);
    var who = machine === "summary" ? "Computed with the summary mechanism (s, q, v)." :
      "Computed with the replay controller; feeding your post-move board costs another 2N + 2 updates, and the move it then outputs is discarded.";
    return '<p class="nv-game">Game: ' + tuple(P1) + " —your move (δ = " + dA + ")→ " + tuple(R1) + " —opponent (δ = " + dO + ")→ " + tuple(P2) + "</p>" +
      '<div class="nv-pair">' +
      table("Only the boards at your decision times", [P1, P2], "The difference " + (C.nimSum(P1) ^ C.nimSum(P2)) + " = " + dA + " ⊕ " + dO +
        " spans two moves: yours and the opponent’s.") +
      table("Including your own post-move board", [P1, R1, P2], "Now the last difference is " + dO + ", the opponent’s move alone, because your post-move board " + tuple(R1) +
        " is the preceding frame.") +
      '</div><p class="nv-note">' + who + "</p>";
  }

  /* ======================= 5. overview ======================= */

  function overview(links) {
    links = links || {};
    function a(key, text) { return links[key] ? '<a href="' + esc(links[key]) + '">' + text + "</a>" : text; }
    var lanes = [
      { k: "one", t: "One frame, one evaluation", inp: "the current board", st: "none", time: "1 evaluation", ok: false,
        what: "In the restricted model no such network family strongly masters NIM: it would give a shallow circuit for parity (using the named classical input on parity).", link: a("barrier", "Theorem on single-frame inference") },
      { k: "two", t: "Two-frame restoration", inp: "previous zero-nim-sum board and current board", st: "the restored board, kept as the next previous frame", time: "1 evaluation per decision", ok: true,
        what: "Shallow selector (Boolean depth ≤ 20). Maintains a winning position once established; does not find the first winning move.", link: a("restore", "worked restoration") },
      { k: "roll", t: "Multi-head rollouts", inp: "the current board (read-only); the controller runs the B rollouts itself", st: "working board, head index, outcome bits", time: "M + 2B + 2 evaluations, M ≤ BN(2<sup>B</sup> − 1)", ok: true,
        what: "Each policy step, tick and the readout is shallow; the rollouts supply the nim-sum bits.", link: a("rollout", "worked rollouts") },
      { k: "rec", t: "Row-wise recurrence", inp: "the board as a stream of rows, supplied twice (board storage: once)", st: "O(B + log N) bits: summary, counter, candidate (board storage: NB + B + r bits)", time: "2N + 2 updates (board storage: N + 1)", ok: true,
        what: "Each update is shallow (Boolean depth ≤ 8); the number of updates grows with N.", link: a("recurrence", "worked recurrence") }
    ];
    var rows = lanes.map(function (l) {
      return '<li class="nv-lane nv-lane-' + l.k + (l.ok ? "" : " blocked") + '"><h4>' + esc(l.t) + "</h4><dl>" +
        "<div><dt>Input</dt><dd>" + esc(l.inp) + "</dd></div><div><dt>Kept state</dt><dd>" + esc(l.st) + "</dd></div>" +
        "<div><dt>Sequential time per decision</dt><dd>" + l.time + "</dd></div></dl><p>" + esc(l.what) + "</p><p class=\"nv-lane-link\">" + l.link + "</p></li>";
    }).join("");
    return '<ol class="nv-lanes">' + rows + "</ol>" +
      '<p class="nv-note">All three routes use shallow (AC<sup>0</sup>) components. The complete rollout and recurrent board-to-move computations are ' +
      "not AC<sup>0</sup> families, given the named classical input that parity is not in AC<sup>0</sup>: otherwise they would give shallow parity circuits. " +
      "Their sequential time grows with the board; that growing computation is the resource the single-frame model lacks. The two-frame route instead " +
      "changes the input and relies on a promise.</p>";
  }

  return { esc: esc, bits: bits, restore: restore, compile: compile, depthAccounting: depthAccounting,
           rollout: rollout, recurrence: recurrence, summaryCompare: summaryCompare, overview: overview,
           boardSVG: boardSVG, FORMULAS: FORMULAS, TEACH: TEACH };
});
