/* Interactive edition of the NIM paper: controls for the illustrations.
 *
 * Progressive enhancement.  Without JavaScript every illustration shows its default example in
 * full (written into the page at build time).  With JavaScript a reader can choose another
 * example or enter boards, and step through the controller traces.  Nothing animates on its own,
 * so reduced-motion settings need no special case; nothing is fetched from a server.
 */
(function () {
  "use strict";
  var C = window.NimVisCore, R = window.NimVisRender;
  if (!C || !R) return;

  var EX = C.EXAMPLES;

  function el(tag, attrs, html) {
    var e = document.createElement(tag);
    Object.keys(attrs || {}).forEach(function (k) {
      if (k === "text") e.textContent = attrs[k]; else e.setAttribute(k, attrs[k]);
    });
    if (html) e.innerHTML = html;
    return e;
  }
  function parseBoard(s, B, maxN) {
    var parts = String(s).split(/[\s,;()]+/).filter(Boolean);
    if (!parts.length || parts.length > maxN) return { err: "Enter between 1 and " + maxN + " heap sizes." };
    var lim = Math.pow(2, B) - 1, out = [];
    for (var i = 0; i < parts.length; i++) {
      if (!/^\d+$/.test(parts[i])) return { err: "Heap sizes must be whole numbers." };
      var v = parseInt(parts[i], 10);
      if (v > lim) return { err: "With B = " + B + " bits a heap holds at most " + lim + "." };
      out.push(v);
    }
    return { P: out };
  }
  var uid = 0;
  function selectBox(app, label, opts, value) {
    var id = "nv-s" + (++uid), wrap = el("label", { "for": id, "class": "nv-ctl" });
    wrap.appendChild(el("span", { text: label }));
    var s = el("select", { id: id });
    opts.forEach(function (o) { var op = el("option", { value: o.id, text: o.label }); if (o.id === value) op.selected = true; s.appendChild(op); });
    wrap.appendChild(s);
    return { wrap: wrap, sel: s };
  }
  function textBox(label, value, size) {
    var id = "nv-t" + (++uid), wrap = el("label", { "for": id, "class": "nv-ctl" });
    wrap.appendChild(el("span", { text: label }));
    var i = el("input", { id: id, type: "text", value: value, size: String(size || 12), inputmode: "numeric", autocomplete: "off", spellcheck: "false" });
    wrap.appendChild(i);
    return { wrap: wrap, input: i };
  }

  /* A stepper: first / previous / slider / next / last, plus a live region. */
  function stepper(onChange) {
    var box = el("div", { "class": "nv-stepper", role: "group", "aria-label": "Step through" });
    var first = el("button", { type: "button", "class": "nv-b", "aria-label": "First step", text: "⏮" });
    var prev = el("button", { type: "button", "class": "nv-b", text: "◀ Previous" });
    var id = "nv-r" + (++uid);
    var range = el("input", { type: "range", id: id, min: "0", max: "0", value: "0", "aria-label": "Step" });
    var next = el("button", { type: "button", "class": "nv-b", text: "Next ▶" });
    var last = el("button", { type: "button", "class": "nv-b", "aria-label": "Last step", text: "⏭" });
    var live = el("p", { "class": "nv-live", "aria-live": "polite" });
    [first, prev, range, next, last].forEach(function (b) { box.appendChild(b); });
    var st = { box: box, live: live, n: 1, k: 0 };
    function go(k) { st.k = Math.max(0, Math.min(st.n - 1, k)); range.value = String(st.k); onChange(st.k); }
    first.addEventListener("click", function () { go(0); });
    prev.addEventListener("click", function () { go(st.k - 1); });
    next.addEventListener("click", function () { go(st.k + 1); });
    last.addEventListener("click", function () { go(st.n - 1); });
    range.addEventListener("input", function () { go(parseInt(range.value, 10)); });
    st.set = function (n, k) { st.n = n; range.max = String(n - 1); st.k = Math.max(0, Math.min(n - 1, k)); range.value = String(st.k); };
    st.go = go;
    return st;
  }
  function wireJumps(out, st) {
    Array.prototype.forEach.call(out.querySelectorAll("[data-step]"), function (c) {
      c.addEventListener("click", function () { st.go(parseInt(c.getAttribute("data-step"), 10)); });
    });
  }
  function announce(st, out) {
    var now = out.querySelector(".nv-now");
    if (now) st.live.textContent = now.textContent;
  }

  /* ---------- per illustration ---------- */

  function initRestore(app, cfg, ctl, out) {
    var ex = selectBox(app, "Example", EX.restore, cfg.example || "paper");
    var bsel = selectBox(app, "Bits B", [1, 2, 3, 4].map(function (b) { return { id: String(b), label: String(b) }; }), "3");
    var q = textBox("Earlier board Q", "3, 5, 6"), qp = textBox("Current board Q′", "3, 4, 6");
    var custom = el("div", { "class": "nv-custom", hidden: "" });
    [bsel.wrap, q.wrap, qp.wrap].forEach(function (w) { custom.appendChild(w); });
    var msg = el("p", { "class": "nv-msg", role: "status" });
    custom.appendChild(msg);
    ctl.appendChild(ex.wrap); ctl.appendChild(custom);
    function render() {
      var e = EX.restore.filter(function (x) { return x.id === ex.sel.value; })[0], B, Q, Qp;
      custom.hidden = e.id !== "custom";
      if (e.id === "custom") {
        B = parseInt(bsel.sel.value, 10);
        var a = parseBoard(q.input.value, B, 6), b = parseBoard(qp.input.value, B, 6);
        if (a.err || b.err) { msg.textContent = a.err || b.err; out.hidden = true; return; }
        if (a.P.length !== b.P.length) { msg.textContent = "Both boards need the same number of heaps."; out.hidden = true; return; }
        msg.textContent = ""; Q = a.P; Qp = b.P;
      } else { B = e.B; Q = e.Q; Qp = e.Qp; }
      out.hidden = false;
      out.innerHTML = R.restore(C.twoFrame(B, Q, Qp), { open: cfg.open });
    }
    [ex.sel, bsel.sel].forEach(function (s) { s.addEventListener("change", render); });
    [q.input, qp.input].forEach(function (i) { i.addEventListener("input", render); });
  }

  function initRollout(app, cfg, ctl, out) {
    var ex = selectBox(app, "Board", EX.rollout, cfg.example || "346");
    var sch = selectBox(app, "Schedule", [{ id: "all", label: "All heads, then the move readout" }, { id: "early", label: "Early exit (classification only)" }], cfg.schedule || "all");
    var bsel = selectBox(app, "Bits B", [1, 2, 3].map(function (b) { return { id: String(b), label: String(b) }; }), "3");
    var p = textBox("Board", "3, 4, 6");
    var custom = el("div", { "class": "nv-custom", hidden: "" });
    custom.appendChild(bsel.wrap); custom.appendChild(p.wrap);
    var msg = el("p", { "class": "nv-msg", role: "status" });
    custom.appendChild(msg);
    ctl.appendChild(ex.wrap); ctl.appendChild(sch.wrap); ctl.appendChild(custom);
    var tr = null, st = stepper(function (k) { draw(k); });
    ctl.appendChild(st.box); ctl.appendChild(st.live);
    function draw(k) { out.innerHTML = R.rollout(tr, k); wireJumps(out, st); announce(st, out); }
    function rebuild() {
      var e = EX.rollout.filter(function (x) { return x.id === ex.sel.value; })[0], B, P;
      custom.hidden = e.id !== "custom";
      if (e.id === "custom") {
        B = parseInt(bsel.sel.value, 10);
        var a = parseBoard(p.input.value, B, 5);
        if (a.err) { msg.textContent = a.err; out.hidden = true; st.box.hidden = true; st.live.hidden = true; return; }
        msg.textContent = ""; P = a.P;
      } else { B = e.B; P = e.P; }
      out.hidden = false; st.box.hidden = false; st.live.hidden = false;
      tr = C.shootout(B, P, sch.sel.value === "early");
      var n = tr.early ? tr.ticks.length : tr.ticks.length + 1;
      st.set(n, n - 1);
      draw(n - 1);
    }
    [ex.sel, sch.sel, bsel.sel].forEach(function (s) { s.addEventListener("change", rebuild); });
    p.input.addEventListener("input", rebuild);
    rebuild();
  }

  function initRecurrence(app, cfg, ctl, out) {
    var ex = selectBox(app, "Scenario", EX.recurrence, cfg.scenario || "game");
    var pro = selectBox(app, "Protocol", [{ id: "replay", label: "Replay: 2N + 2 updates, no stored board" }, { id: "store", label: "Board storage: N + 1 updates, board in memory" },
      { id: "summary", label: "Summary mechanism (s, q, v) only: no move" }], cfg.protocol || "replay");
    var bsel = selectBox(app, "Bits B", [1, 2, 3, 4].map(function (b) { return { id: String(b), label: String(b) }; }), "3");
    var p = textBox("Board", "3, 4, 6");
    var custom = el("div", { "class": "nv-custom", hidden: "" });
    custom.appendChild(bsel.wrap); custom.appendChild(p.wrap);
    var msg = el("p", { "class": "nv-msg", role: "status" });
    custom.appendChild(msg);
    ctl.appendChild(ex.wrap); ctl.appendChild(pro.wrap); ctl.appendChild(custom);
    var rt = null, st = stepper(function (k) { draw(k); });
    ctl.appendChild(st.box); ctl.appendChild(st.live);
    function draw(k) { out.innerHTML = R.recurrence(rt, k); wireJumps(out, st); announce(st, out); }
    function rebuild() {
      var sc = ex.sel.value, B = 3, P = [3, 4, 6];
      custom.hidden = sc !== "custom";
      if (sc === "custom") {
        B = parseInt(bsel.sel.value, 10);
        var a = parseBoard(p.input.value, B, 6);
        if (a.err) { msg.textContent = a.err; out.hidden = true; st.box.hidden = true; st.live.hidden = true; return; }
        msg.textContent = ""; P = a.P; sc = "decision";
      }
      out.hidden = false; st.box.hidden = false; st.live.hidden = false;
      rt = C.recurrenceScenario(pro.sel.value, sc, B, P, [2, 1]);
      st.set(rt.steps.length, rt.steps.length - 1);
      draw(rt.steps.length - 1);
    }
    [ex.sel, pro.sel, bsel.sel].forEach(function (s) { s.addEventListener("change", rebuild); });
    p.input.addEventListener("input", rebuild);
    rebuild();
  }

  function initCompile(app, cfg, ctl, out) {
    var data = cfg.data;
    var fs = selectBox(app, "Formula", Object.keys(R.FORMULAS).filter(function (k) { return data.nets[k]; }).map(function (k) {
      return { id: k, label: R.FORMULAS[k].label };
    }), cfg.formula || "xor");
    ctl.appendChild(fs.wrap);
    var input = (cfg.input || [true, false]).slice();
    var ins = el("div", { "class": "nv-toggles", role: "group", "aria-label": "Inputs" });
    ctl.appendChild(ins);
    function buttons() {
      ins.innerHTML = "";
      var n = R.FORMULAS[fs.sel.value].n;
      for (var k = 0; k < n; k++) {
        (function (k) {
          var b = el("button", { type: "button", "class": "nv-b nv-tog", "aria-pressed": String(!!input[k]), text: ["a", "b"][k] + " = " + (input[k] ? 1 : 0) });
          b.addEventListener("click", function () { input[k] = !input[k]; b.setAttribute("aria-pressed", String(!!input[k])); b.textContent = ["a", "b"][k] + " = " + (input[k] ? 1 : 0); render(); });
          ins.appendChild(b);
        })(k);
      }
    }
    function render() { out.innerHTML = R.compile({ formula: fs.sel.value, input: input }, data); }
    fs.sel.addEventListener("change", function () { buttons(); render(); });
    buttons();
  }

  var INIT = { restore: initRestore, rollout: initRollout, recurrence: initRecurrence, compile: initCompile };

  function enhance(root) {
    Array.prototype.forEach.call((root || document).querySelectorAll(".nv-app[data-type]"), function (app) {
      if (app.getAttribute("data-ready")) return;
      var type = app.getAttribute("data-type"), init = INIT[type];
      if (!init) return;
      var cfg = {};
      try { cfg = JSON.parse(app.getAttribute("data-config") || "{}"); } catch (e) { return; }
      var ctl = app.querySelector(".nv-controls"), out = app.querySelector(".nv-out");
      if (!ctl || !out) return;
      ctl.hidden = false;
      init(app, cfg, ctl, out);
      app.setAttribute("data-ready", "1");
    });
  }
  window.NimVisUI = { enhance: enhance };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", function () { enhance(document); });
  else enhance(document);
})();
