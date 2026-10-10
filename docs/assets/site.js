/* Interactive edition of the NIM paper: progressive disclosure of explanation levels.
   Without JavaScript every control is an ordinary link to the claim's own page. */
(function () {
  "use strict";
  var LEVELS = { explain: "Explain this", formal: "How this is formalised", lean: "Lean statement and source" };
  var cache = {};
  var current = null; // {id, level, panel}

  function $(sel, root) { return (root || document).querySelector(sel); }
  function $all(sel, root) { return Array.prototype.slice.call((root || document).querySelectorAll(sel)); }
  function esc(s) { return window.CSS && CSS.escape ? CSS.escape(s) : s.replace(/([:.~])/g, "\\$1"); }
  function fileid(id) { return id.replace(/:/g, "__"); }

  function parseHash() {
    var h = "";
    try { h = decodeURIComponent(location.hash.slice(1)); } catch (e) { h = location.hash.slice(1); }
    var i = h.lastIndexOf("~");
    if (i > 0 && LEVELS[h.slice(i + 1)]) return { id: h.slice(0, i), level: h.slice(i + 1) };
    return { id: h, level: null };
  }
  function rowFor(id) { return $('.claim-row[data-claim="' + esc(id) + '"]'); }

  /* --- turn level links into disclosure buttons --- */
  function enhance() {
    $all("a.lvl").forEach(function (a) {
      var b = document.createElement("button");
      b.type = "button";
      b.className = "lvl";
      b.textContent = a.textContent;
      b.dataset.level = a.dataset.level;
      b.dataset.claim = a.dataset.claim;
      b.dataset.href = a.getAttribute("href").split("#")[0];
      b.setAttribute("aria-expanded", "false");
      b.setAttribute("aria-controls", "panel-" + fileid(a.dataset.claim));
      b.addEventListener("click", function () {
        if (current && current.id === b.dataset.claim && current.level === b.dataset.level) {
          closePanel(true);
        } else {
          openPanel(b.dataset.claim, b.dataset.level, { push: true, focus: true });
        }
      });
      a.parentNode.replaceChild(b, a);
    });
  }

  function load(id) {
    if (cache[id]) return Promise.resolve(cache[id]);
    var row = rowFor(id);
    var btn = row && $("button.lvl", row);
    if (!btn) return Promise.reject(new Error("no claim " + id));
    return fetch(btn.dataset.href, { credentials: "same-origin" }).then(function (r) {
      if (!r.ok) throw new Error("HTTP " + r.status);
      return r.text();
    }).then(function (txt) {
      var doc = new DOMParser().parseFromString(txt, "text/html");
      var h1 = $("h1", doc);
      var out = { page: btn.dataset.href, title: (h1 && (h1.getAttribute("data-title") || h1.textContent)) || id };
      Object.keys(LEVELS).forEach(function (k) {
        var s = doc.getElementById(k);
        out[k] = s ? $(".lvl-body", s).innerHTML : null;
      });
      cache[id] = out;
      return out;
    });
  }

  function setExpanded(id, level) {
    $all("button.lvl").forEach(function (b) {
      b.setAttribute("aria-expanded", String(b.dataset.claim === id && b.dataset.level === level));
    });
  }

  function buildPanel(id) {
    var row = rowFor(id);
    var bar = row.closest(".claim-bar");
    var p = document.createElement("section");
    p.className = "claim-panel";
    p.id = "panel-" + fileid(id);
    p.innerHTML =
      '<div class="panel-head"><p class="panel-title"><span class="pt-claim"></span> <span class="pt-level"></span></p>' +
      '<div class="panel-tools"><a class="panel-link" href="#">Link to this level</a>' +
      '<a class="panel-page" href="#">Full record page</a>' +
      '<button type="button" class="panel-close">Close</button></div></div>' +
      '<div class="panel-body" tabindex="-1"></div>';
    $(".panel-close", p).addEventListener("click", function () { closePanel(true); });
    p.addEventListener("keydown", function (e) {
      if (e.key === "Escape") { e.preventDefault(); closePanel(true); }
    });
    bar.parentNode.insertBefore(p, bar.nextSibling);
    return p;
  }

  function openPanel(id, level, opts) {
    opts = opts || {};
    var row = rowFor(id);
    if (!row) return;
    if (current && current.id !== id) removePanel();
    var p = current && current.id === id ? current.panel : buildPanel(id);
    current = { id: id, level: level, panel: p };
    setExpanded(id, level);
    $(".pt-level", p).textContent = "· " + LEVELS[level];
    var body = $(".panel-body", p);
    p.setAttribute("aria-label", LEVELS[level]);
    $(".panel-link", p).setAttribute("href", "#" + id + "~" + level);
    body.innerHTML = '<p class="panel-loading">Loading…</p>';
    if (opts.push) {
      push({ panel: id, level: level }, "#" + id + "~" + level);
    } else if (opts.replace) {
      history.replaceState({ panel: id, level: level }, "", "#" + id + "~" + level);
    }
    return load(id).then(function (d) {
      if (!current || current.id !== id || current.level !== level) return;
      $(".pt-claim", p).textContent = d.title.replace(/\s+/g, " ").trim();
      $(".panel-page", p).setAttribute("href", d.page + "#" + level);
      body.innerHTML = d[level] || '<p class="panel-error">This level is not available for this claim.</p>';
      if (window.NimVisUI) window.NimVisUI.enhance(body);
      if (opts.focus) body.focus({ preventScroll: true });
      if (opts.scrollTo) scrollToAnchor(id);
    }).catch(function () {
      body.innerHTML = '<p class="panel-error">This panel could not be loaded here (for example when the page is ' +
        'opened directly from disk). <a href="' + $("button.lvl", row).dataset.href + "#" + level +
        '">Open the full record page</a>.</p>';
    });
  }

  function removePanel() {
    if (current && current.panel && current.panel.parentNode) current.panel.parentNode.removeChild(current.panel);
    current = null;
    setExpanded(null, null);
  }

  function closePanel(push) {
    if (!current) return;
    var id = current.id, level = current.level;
    var y = window.scrollY;
    removePanel();
    if (push) pushEntry({ panel: null }, "#" + id, y);
    window.scrollTo(0, y);
    var row = rowFor(id);
    var b = row && $('button.lvl[data-level="' + level + '"]', row);
    if (b) b.focus({ preventScroll: true });
  }

  /* Every history entry remembers the scroll position at which it was left. */
  function pushEntry(state, url, y) {
    history.replaceState(Object.assign({}, history.state || {}, { y: y }), "");
    history.pushState(state, "", url);
  }
  function push(state, url) { pushEntry(state, url, window.scrollY); }

  function scrollToAnchor(id) {
    var el = document.getElementById(id);
    if (el) el.scrollIntoView({ block: "start" });
  }

  function applyState(state) {
    if (state && "panel" in state) {
      var restore = function () { if (typeof state.y === "number") window.scrollTo(0, state.y); };
      if (state.panel && rowFor(state.panel)) {
        var p = openPanel(state.panel, state.level, {});
        restore();
        if (p) p.then(restore);
      } else {
        removePanel();
        restore();
      }
      return;
    }
    // an ordinary fragment navigation (link click, typed URL): the URL describes the state
    var h = parseHash();
    if (h.level && rowFor(h.id)) {
      openPanel(h.id, h.level, { replace: true, scrollTo: true });
      scrollToAnchor(h.id);
    } else {
      removePanel();
      history.replaceState({ panel: null }, "");
    }
  }

  document.addEventListener("DOMContentLoaded", function () {
    // Browsers restrict fetch() for file URLs. Keep the ordinary record-page links
    // when this edition is opened from disk; its illustrations still work locally.
    if (!$(".claim-bar") || location.protocol === "file:") return;
    enhance();
    var toc = $(".toc details");
    if (toc && window.matchMedia("(max-width: 1179px)").matches) toc.open = false;
    window.addEventListener("popstate", function (e) { applyState(e.state); });
    var h = parseHash();
    if (h.level && rowFor(h.id)) {
      openPanel(h.id, h.level, { replace: true, scrollTo: true });
      scrollToAnchor(h.id);
    } else if (!history.state) {
      history.replaceState({ panel: null }, "");
    }
  });
})();
