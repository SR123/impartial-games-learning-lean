#!/usr/bin/env node
/* Build-time rendering of the illustrations (called by tools/build_site.py).
 *
 * stdin:  {"instances": [{"key": ..., "type": ..., "config": {...}}], "data": {"nets": {...}, "restsize": [...]}}
 * stdout: {"<key>": {"app": "<html of the default state>", "extra": "<static html after the app>"}}
 *
 * The browser later re-renders with the same functions (nimvis-render.js), so the page shows
 * the complete default example before, and without, any script.
 */
"use strict";
const C = require("./nimvis-core.js");
const R = require("./nimvis-render.js");

function render(inst, data) {
  const cfg = inst.config || {};
  switch (inst.type) {
    case "restore": {
      const e = C.example("restore", cfg.example || "paper");
      return { app: R.restore(C.twoFrame(e.B, e.Q, e.Qp), { open: cfg.open }), extra: "" };
    }
    case "compile":
      return { app: R.compile({ formula: cfg.formula || "xor", input: cfg.input || [true, false] }, data),
               extra: cfg.accounting === false ? "" : R.depthAccounting(data) };
    case "rollout": {
      const e = C.example("rollout", cfg.example || "346");
      return { app: R.rollout(C.shootout(e.B, e.P, cfg.schedule === "early")), extra: "" };
    }
    case "recurrence": {
      const rt = C.recurrenceScenario(cfg.protocol || "replay", cfg.scenario || "game", 3, [3, 4, 6], [2, 1]);
      const g = C.recurrenceScenario("replay", "game", 3, [3, 4, 6], [2, 1]);
      const machine = cfg.protocol === "summary" ? "summary" : "replay";
      return { app: R.recurrence(rt), extra: cfg.compare === false ? "" : R.summaryCompare({ P1: g.boards[0], R1: g.boards[1], P2: g.boards[2] }, machine) };
    }
    case "overview":
      return { app: "", extra: R.overview(cfg.links || {}) };
    default:
      throw new Error("unknown illustration type " + inst.type);
  }
}

let buf = "";
process.stdin.setEncoding("utf8");
process.stdin.on("data", (d) => { buf += d; });
process.stdin.on("end", () => {
  const req = JSON.parse(buf);
  const out = {};
  for (const inst of req.instances) out[inst.key] = render(inst, req.data || {});
  process.stdout.write(JSON.stringify(out));
});
