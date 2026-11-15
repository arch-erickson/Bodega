/* Gonzales Bodega — 3D storefront sign. Vanilla JS, no dependencies.
   Self-initializes every .bodega-sign on DOMContentLoaded (markup + API: see sign.css). */
(function () {
  "use strict";

  var MAX_Y = 7, MAX_X = 5;              // max tilt in degrees
  var COMPACT_ON = 64, COMPACT_OFF = 24;  // scroll hysteresis (px)
  var STEP = 3.6;                         // seconds per palette colour
  var COLOR_MS = 66;                      // colour updates ~15 fps (slow drift, cheap repaints)
  var PAL = [[255, 46, 46], [255, 138, 0], [255, 212, 0], [28, 226, 92], [38, 140, 255], [236, 52, 196]];
  var LED = [[255, 150, 150], [255, 205, 140], [250, 240, 165], [160, 235, 180], [160, 200, 255], [245, 170, 225], [225, 225, 225]];
  var WORD_OFFSET = 2.5;                  // palette steps between words
  var FACES = ["bs-back", "bs-bottom", "bs-right", "bs-aw-end", "bs-aw-sbot", "bs-aw-rend",
    "bs-aw-slope", "bs-aw-under", "bs-aw-inner", "bs-aw-left", "bs-aw-front"];

  var mm = function (q) { return window.matchMedia ? window.matchMedia(q) : { matches: false }; };
  var mqReduce = mm("(prefers-reduced-motion: reduce)");
  var noHover = mm("(hover: none)").matches;
  var root = document.documentElement;
  var signs = [], raf = 0, lastT = 0, lastColor = -1e9;
  var P = { x: 0, y: 0, on: false, mouse: false };
  var O = { init: false, dx: 0, dy: 0, t: -1e9, bg: 0, bb: 0 };   // device orientation
  var rootVals = {};
  var light = { x: -1, y: -1 };
  var tiles = { seen: new WeakSet(), vis: new Set(), io: null, lastScan: -1e9 };

  function el(tag, cls, parent, before) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (parent) parent.insertBefore(e, before || null);
    return e;
  }
  function hidden(e) { e.setAttribute("aria-hidden", "true"); return e; }
  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
  function setRoot(name, val) {
    if (rootVals[name] !== val) { rootVals[name] = val; root.style.setProperty(name, val); }
  }
  function setStyle(node, prop, val, cache) {
    if (node && node[cache] !== val) { node[cache] = val; node.style[prop] = val; }
  }
  function setVar(node, name, val) {
    var k = "_" + name;
    if (node[k] !== val) { node[k] = val; node.style.setProperty(name, val); }
  }

  /* ---------- colour ---------- */
  function palAt(x) {
    var n = PAL.length;
    x = ((x % n) + n) % n;
    var i = Math.floor(x), f = x - i, a = PAL[i], b = PAL[(i + 1) % n];
    f = f * f * (3 - 2 * f);                                 // ease: colours linger, then glide
    return [a[0] + (b[0] - a[0]) * f, a[1] + (b[1] - a[1]) * f, a[2] + (b[2] - a[2]) * f];
  }
  function mix(c, d, t) { return [c[0] + (d[0] - c[0]) * t, c[1] + (d[1] - c[1]) * t, c[2] + (d[2] - c[2]) * t]; }
  function rgb(c) { return Math.round(c[0]) + " " + Math.round(c[1]) + " " + Math.round(c[2]); }

  function paint(s, t, still) {
    var glow = null;
    s.words.forEach(function (w, i) {
      var x = still ? i * 3 : t / STEP + i * WORD_OFFSET;    // still: red / green
      var c1 = palAt(x), c2 = mix(palAt(x + .8), [0, 0, 0], .12), hi = mix(c1, [255, 255, 255], .55);
      setVar(w, "--c1", rgb(c1));
      setVar(w, "--c2", rgb(c2));
      setVar(w, "--hi", rgb(hi));
      if (!glow) glow = c1;
    });
    s.leds.forEach(function (l, j) {
      var c = still ? LED[6] : LED[Math.floor(t / l.dur + l.ph) % LED.length];
      setStyle(l.el, "color", "rgb(" + rgb(c) + " / .62)", "_c");
    });
    return glow;
  }

  /* ---------- letters (two layers per word: lit edge/glow + gradient face) ---------- */
  function buildName(s) {
    var h = s.name;
    if (s.mo) s.mo.disconnect();
    var sr = h.querySelector(".bs-sr");
    var text = (sr ? sr.textContent : h.textContent).replace(/\s+/g, " ").trim();
    h.textContent = "";
    el("span", "bs-sr", h).textContent = text;
    var vis = hidden(el("span", "bs-letters", h));
    s.words = [];
    text.split(" ").forEach(function (word, i) {
      if (i) el("span", "bs-gap", vis);
      var w = el("span", "bs-word", vis);
      el("span", "bs-wg", w).textContent = word;
      el("span", "bs-wf", w).textContent = word;
      s.words.push(w);
    });
    s.glows = h.querySelectorAll(".bs-wg");
    if (s.mo) s.mo.observe(h, { childList: true, characterData: true, subtree: true });
  }
  function buildLeds(s) {
    var p = s.sub;
    s.leds = [];
    if (!p) return;
    if (s.mo2) s.mo2.disconnect();
    var text = p.textContent.replace(/\s+/g, " ").trim().replace(/\s*[·•|]\s*/g, " • ");
    p.textContent = "";
    text.split(/( • )/).forEach(function (part, i) {
      if (!part) return;
      var e = el("span", "bs-led", p);
      e.textContent = part;
      s.leds.push({ el: e, dur: .55 + ((i * 37) % 9) / 10, ph: (i * 2.3) % LED.length });
    });
    if (s.mo2) s.mo2.observe(p, { childList: true, characterData: true, subtree: true });
  }

  function buildFaces(s) {
    if (s.box.querySelector(".bs-aw-front")) return;
    FACES.forEach(function (cls) { hidden(el("div", cls, s.box, s.face)); });
  }

  function init(rootEl) {
    if (rootEl._bodegaSign) return;
    var q = function (c) { return rootEl.querySelector(c); };
    var s = { root: rootEl, stage: q(".bs-stage"), box: q(".bs-box"), face: q(".bs-face"), name: q(".bs-name"),
      sub: q(".bs-sub"), glare: q(".bs-glare"), words: [], leds: [], glows: [],
      rx: 0, ry: 0, gx: .5, gy: .2, near: 0, compact: false, W: 0, H: 0 };
    if (!s.stage || !s.box || !s.face) return;
    rootEl._bodegaSign = s;
    if (!s.glare) s.glare = hidden(el("div", "bs-glare", s.face));
    buildFaces(s);
    if (window.MutationObserver) {
      s.mo = new MutationObserver(function () { buildName(s); paint(s, performance.now() / 1000, mqReduce.matches); });
      s.mo2 = new MutationObserver(function () { buildLeds(s); paint(s, performance.now() / 1000, mqReduce.matches); });
    }
    if (s.name) buildName(s);
    buildLeds(s);
    var size = function () { s.W = s.face.offsetWidth; s.H = s.face.offsetHeight; };
    size();
    if (window.ResizeObserver) new ResizeObserver(function () { size(); measure(); }).observe(s.face);
    rootEl.addEventListener("transitionend", function (e) { if (e.target === rootEl) measure(); });
    signs.push(s);
  }

  /* ---------- page-level state ---------- */
  function measure() {
    var s = signs[0];
    if (s) setRoot("--sign-h", Math.round(s.root.getBoundingClientRect().height) + "px");
  }
  function onScroll() {
    var y = window.pageYOffset || root.scrollTop, changed = false;
    signs.forEach(function (s) {
      var c = s.compact ? y > COMPACT_OFF : y > COMPACT_ON;
      if (c !== s.compact) { s.compact = c; s.root.classList.toggle("is-compact", c); changed = true; }
    });
    if (changed && mqReduce.matches) requestAnimationFrame(measure);
    if (!mqReduce.matches) start();
  }
  function scanTiles(now) {
    if (now - tiles.lastScan < 1000 || !tiles.io) return;
    tiles.lastScan = now;
    var list = document.querySelectorAll(".tile");
    for (var i = 0; i < list.length; i++) {
      if (!tiles.seen.has(list[i])) { tiles.seen.add(list[i]); tiles.io.observe(list[i]); }
    }
  }

  /* ---------- the one rAF loop ---------- */
  function tick(now) {
    raf = 0;
    if (mqReduce.matches || !signs.length) return;
    var dt = Math.min(.05, lastT ? (now - lastT) / 1000 : .016);
    lastT = now;
    var kT = 1 - Math.exp(-dt * 6), kN = 1 - Math.exp(-dt * 5);
    var vw = window.innerWidth, vh = window.innerHeight, t = now / 1000;
    var useOri = !P.on && now - O.t < 1500;
    var primary = signs[0], prim = null;
    scanTiles(now);

    /* reads */
    var rects = signs.map(function (s) { return s.stage.getBoundingClientRect(); });
    var signH = primary.root.getBoundingClientRect().height;
    var tileList = [], tileRects = [];
    tiles.vis.forEach(function (tl) {
      if (!tl.isConnected) { tiles.vis.delete(tl); return; }
      tileList.push(tl); tileRects.push(tl.getBoundingClientRect());
    });

    /* compute + writes */
    signs.forEach(function (s, idx) {
      var r = rects[idx], cx = r.left + r.width / 2, cy = r.top + r.height / 2;
      var tx = 0, ty = 0, gx, gy, near = 0;
      if (P.on) {
        var dx = clamp((P.x - cx) / (vw / 2), -1, 1);
        var dy = clamp((P.y - cy) / Math.max(120, P.y > cy ? vh - cy : cy), -1, 1);
        ty = dx * MAX_Y; tx = -dy * MAX_X;
        gx = clamp((P.x - r.left) / r.width, -.1, 1.1);
        gy = clamp((P.y - r.top) / r.height, -.3, 1.3);
        var ex = Math.max(r.left - P.x, 0, P.x - r.right), ey = Math.max(r.top - P.y, 0, P.y - r.bottom);
        near = clamp(1 - Math.sqrt(ex * ex + ey * ey) / 260, 0, 1);
      } else if (useOri) {
        ty = O.dx * MAX_Y; tx = -O.dy * MAX_X;
      } else if (noHover || !P.mouse) {                    // idle sway
        ty = Math.sin(t * .5 + idx) * 3;
        tx = Math.sin(t * .33 + idx) * 1.5;
      }
      if (gx === undefined) { gx = .5 + s.ry / MAX_Y * .45; gy = .2 - s.rx / MAX_X * .5; }
      s.rx += (tx - s.rx) * kT; s.ry += (ty - s.ry) * kT;
      s.gx += (gx - s.gx) * kT; s.gy += (gy - s.gy) * kT;
      s.near += (near - s.near) * kN;
      s.inten = .45 + .55 * s.near;

      setStyle(s.box, "transform", "rotateX(" + s.rx.toFixed(2) + "deg) rotateY(" + s.ry.toFixed(2) + "deg)", "_t");
      if (s.W) setStyle(s.glare, "transform", "translate3d(" + (s.gx * s.W).toFixed(1) + "px," + (s.gy * s.H).toFixed(1) + "px,0)", "_t");
      setStyle(s.glare, "opacity", (.5 + .5 * s.near).toFixed(3), "_o");
      var go = (.72 + .28 * s.near).toFixed(3);
      for (var g = 0; g < s.glows.length; g++) setStyle(s.glows[g], "opacity", go, "_o");
      if (idx === 0) prim = { cx: cx, cy: cy, s: s };
    });

    /* colour cycle (throttled) → letters, LED tagline, --sign-glow */
    if (now - lastColor >= COLOR_MS) {
      lastColor = now;
      signs.forEach(function (s, idx) {
        var c = paint(s, t, false);
        if (idx === 0 && c) setRoot("--sign-glow", rgb(c));
      });
    }

    /* light position: pointer, device tilt, else sign centre */
    var lx = prim.cx, ly = prim.cy;
    if (P.on) { lx = P.x; ly = P.y; }
    else if (useOri) { lx = prim.cx + prim.s.ry / MAX_Y * vw * .45; ly = prim.cy + vh * .35 - prim.s.rx / MAX_X * vh * .3; }
    if (light.x < 0) { light.x = lx; light.y = ly; }
    light.x += (lx - light.x) * kT; light.y += (ly - light.y) * kT;
    var LX = Math.round(light.x), LY = Math.round(light.y);
    setRoot("--sign-h", Math.round(signH) + "px");
    setRoot("--sign-intensity", primary.inten.toFixed(2));
    setRoot("--light-x", LX + "px");
    setRoot("--light-y", LY + "px");
    for (var i = 0; i < tileList.length; i++) {
      var tl = tileList[i];
      setVar(tl, "--lx", (LX - Math.round(tileRects[i].left)) + "px");
      setVar(tl, "--ly", (LY - Math.round(tileRects[i].top)) + "px");
    }
    start();
  }
  function start() { if (!raf && !document.hidden) raf = requestAnimationFrame(tick); }

  /* ---------- input ---------- */
  function onTouch(e) {
    var tp = e.touches && e.touches[0];
    if (tp) { P.x = tp.clientX; P.y = tp.clientY; P.on = true; }
  }
  function onOrient(e) {
    if (e.gamma == null || e.beta == null) return;
    var ang = (screen.orientation && screen.orientation.angle) || window.orientation || 0;
    var g = e.gamma, b = e.beta;
    if (ang === 90) { g = e.beta; b = -e.gamma; }
    else if (ang === -90 || ang === 270) { g = -e.beta; b = e.gamma; }
    var now = performance.now();
    if (!O.init) { O.init = true; O.bg = g; O.bb = b; }
    var k = 1 - Math.exp(-Math.min(.2, (now - O.t) / 1000) / 5); // re-centre on how the phone is held (~5 s)
    O.bg += (g - O.bg) * k;
    O.bb += (b - O.bb) * k;
    O.dx = clamp((g - O.bg) / 20, -1, 1);
    O.dy = clamp((b - O.bb) / 20, -1, 1);
    O.t = now;
    start();
  }
  function askOrientation() {                                // iOS 13+: needs a user gesture; never blocks
    document.removeEventListener("touchend", askOrientation);
    document.removeEventListener("click", askOrientation);
    var D = window.DeviceOrientationEvent;
    if (D && typeof D.requestPermission === "function") {
      try { D.requestPermission().catch(function () {}); } catch (err) { /* ignore */ }
    }
  }
  function bind() {
    var o = { passive: true };
    window.addEventListener("pointermove", function (e) {
      if (e.pointerType === "touch") return;
      P.x = e.clientX; P.y = e.clientY; P.on = true; P.mouse = true;
    }, o);
    window.addEventListener("touchstart", onTouch, o);
    window.addEventListener("touchmove", onTouch, o);
    window.addEventListener("touchend", function (e) { if (!e.touches.length) P.on = false; }, o);
    window.addEventListener("touchcancel", function () { P.on = false; }, o);
    document.addEventListener("mouseout", function (e) { if (!e.relatedTarget) P.on = false; });
    window.addEventListener("blur", function () { P.on = false; });
    window.addEventListener("scroll", onScroll, o);
    window.addEventListener("resize", function () { measure(); start(); }, o);
    document.addEventListener("visibilitychange", function () { lastT = 0; start(); });
    if (window.DeviceOrientationEvent) {
      window.addEventListener("deviceorientation", onOrient, o);
      document.addEventListener("touchend", askOrientation, o);
      document.addEventListener("click", askOrientation, o);
    }
    if (mqReduce.addEventListener) mqReduce.addEventListener("change", reset);
  }

  function reset() {                                         // static state for reduced motion
    if (!mqReduce.matches) { start(); return; }
    signs.forEach(function (s, idx) {
      s.rx = s.ry = s.near = 0;
      setStyle(s.box, "transform", "none", "_t");
      if (s.W) setStyle(s.glare, "transform", "translate3d(" + (.5 * s.W) + "px," + (.2 * s.H) + "px,0)", "_t");
      for (var g = 0; g < s.glows.length; g++) setStyle(s.glows[g], "opacity", ".8", "_o");
      var c = paint(s, 0, true);
      if (idx === 0 && c) setRoot("--sign-glow", rgb(c));
    });
    setRoot("--sign-intensity", ".5");
    var r = signs[0].stage.getBoundingClientRect();
    setRoot("--light-x", Math.round(r.left + r.width / 2) + "px");
    setRoot("--light-y", Math.round(r.top + r.height / 2) + "px");
    tiles.vis.forEach(function (tl) { tl.style.removeProperty("--lx"); tl.style.removeProperty("--ly"); tl["_--lx"] = tl["_--ly"] = null; });
    measure();
  }

  function initAll() {
    var list = document.querySelectorAll(".bodega-sign");
    for (var i = 0; i < list.length; i++) init(list[i]);
    if (!signs.length) return;
    if (!document.querySelector(".sign-ambient")) hidden(el("div", "sign-ambient", document.body));
    document.body.classList.add("sign-lit");
    var g0 = signs[0].root.getAttribute("data-glow");
    setRoot("--sign-glow", g0 ? g0.trim() : rgb(PAL[0]));
    signs.forEach(function (s) { paint(s, performance.now() / 1000, mqReduce.matches); });
    if (window.IntersectionObserver && !tiles.io) {
      tiles.io = new IntersectionObserver(function (entries) {
        entries.forEach(function (en) { if (en.isIntersecting) tiles.vis.add(en.target); else tiles.vis.delete(en.target); });
      }, { rootMargin: "120px 0px" });
    }
    if (!initAll.bound) { initAll.bound = true; bind(); }
    onScroll();
    measure();
    reset();
  }

  window.BodegaSign = { init: initAll };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", initAll);
  else initAll();
})();
