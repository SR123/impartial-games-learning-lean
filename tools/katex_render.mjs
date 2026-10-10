// Build-time math rendering with the pinned KaTeX (tools/package.json).
// stdin:  {"macros": {...}, "items": [{"id": "...", "tex": "...", "display": true|false}, ...]}
// stdout: {"html": {"id": "<span class=katex...>", ...}, "errors": [{"id","tex","message"}]}
// Output is HTML plus MathML, so formulas are selectable, accessible and need no JavaScript.
import katex from "katex";

let input = "";
process.stdin.setEncoding("utf8");
process.stdin.on("data", (c) => (input += c));
process.stdin.on("end", () => {
  const req = JSON.parse(input);
  const out = { html: {}, errors: [], katexVersion: katex.version };
  for (const item of req.items) {
    try {
      out.html[item.id] = katex.renderToString(item.tex, {
        displayMode: !!item.display,
        macros: { ...req.macros },
        throwOnError: true,
        output: "htmlAndMathml",
        strict: "error",
        trust: false,
      });
    } catch (e) {
      out.errors.push({ id: item.id, tex: item.tex, message: String(e.message || e) });
    }
  }
  process.stdout.write(JSON.stringify(out));
});
