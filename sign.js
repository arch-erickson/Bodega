/* Gonzales Bodega — 3D lit lightbox sign. Vanilla JS, no dependencies.
   Self-initializes every .bodega-sign on DOMContentLoaded (see sign.css for markup + API). */
(function () {
  "use strict";

  var MAX_Y = 15, MAX_X = 12;           // max tilt in degrees
  var LAYERS = 10;                      // extrusion slices
  var COMPACT_ON = 64, COMPACT_OFF = 24; // scroll hysteresis (px)
  var FLICKER = [[70, .2], [55, 1], [90, .3], [40, .85], [130, .22], [80, 1]]; // [ms, opacity]

  var mm = function (q) { return window.matchMedia ? window.matchMedia(q) : { matches: false }; };
  var mqReduce = mm("(prefers-reduced-motion: reduce)");
  var noHover = mm("(hover: none)").matches;
  var root = document.documentElement;
  var signs = [], raf = 0, lastT = 0;
  var P = { x: 0, y: 0, on: false, mouse: false };
  var rootVals = {};                    // last written :root vars
  var light = { x: -1, y: -1 };
  var tiles = { seen: new WeakSet(), vis: new Set(), io: null, lastScan: 0 };

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

  /* ---------- neon letters (rebuilt if page JS later sets the h1 text) ---------- */
  function buildName(s) {
    var h = s.name;
    if (s.mo) s.mo.disconnect();
    var sr = h.querySelector(".bs-sr");
    var text = (sr ? sr.textContent : h.textContent).replace(/\s+/g, " ").trim();
    h.textContent = "";
    el("span", "bs-sr", h).textContent = text;
    var neon = hidden(el("span", "bs-neon", h));
    s.bloom = hidden(el("span", "bs-bloom", h));
    s.bloom.textContent = text;
    var letters = [];
    for (var i = 0; i < text.length; i++) {
      if (text[i] === " ") { neon.appendChild(document.createTextNode(" ")); continue; }
      var l = el("span", "bs-l", neon);
      l.textContent = text[i];
      letters.push(l);
    }
    var f = parseInt(s.root.getAttribute("data-flicker"), 10);   // letter index, -1 disables
    s.flick = letters[isNaN(f) ? Math.max(0, letters.length - 4) : f] || null;
    if (s.mo) s.mo.observe(h, { childList: true, characterData: true, subtree: true });
  }

  /* ---------- bulbs along the frame's rounded-rect centre line ---------- */
  function pointAt(d, x0, y0, w, h, r) {
    var a = Math.PI * r / 2, sw = w - 2 * r, sh = h - 2 * r;
    var seg = [sw, a, sh, a, sw, a, sh, a], i = 0;
    while (i < 7 && d > seg[i]) { d -= seg[i]; i++; }
    var t = seg[i] ? d / seg[i] : 0, ang = (i - 1) / 4 * Math.PI - Math.PI / 2 + t * Math.PI / 2;
    switch (i) {
      case 0: return [x0 + r + d, y0];
      case 2: return [x0 + w, y0 + r + d];
      case 4: return [x0 + w - r - d, y0 + h];
      case 6: return [x0, y0 + h - r - d];
    }
    var cx = i === 1 || i === 3 ? x0 + w - r : x0 + r;
    var cy = i === 1 || i === 7 ? y0 + r : y0 + h - r;
    return [cx + r * Math.cos(ang), cy + r * Math.sin(ang)];
  }
  function layoutBulbs(s) {
    var W = s.front.offsetWidth, H = s.front.offsetHeight;
    if (!W || !H) return;
    s.W = W; s.H = H;
    var band = s.panel ? s.panel.offsetLeft : W * .05;
    var R = parseFloat(getComputedStyle(s.front).borderTopLeftRadius) || 0;
    var x0 = band / 2, y0 = band / 2, w = W - band, h = H - band;
    var r = clamp(R - band / 2, 0, Math.min(w, h) / 2);
    var L = 2 * (w - 2 * r) + 2 * (h - 2 * r) + 2 * Math.PI * r;
    var n = Math.max(12, Math.round(L / Math.max(11, band * .95) / 3) * 3);
    if (n === s.bulbCount && W === s.bulbW) return;
    s.bulbCount = n; s.bulbW = W;
    var start = (w - 2 * r) / 2, html = "";
    for (var i = 0; i < n; i++) {
      var p = pointAt((start + i * L / n) % L, x0, y0, w, h, r);
      var tw = (i * 7 + 3) % 23 === 0 ? " bs-tw" : "";
      html += '<i class="bs-bulb' + tw + '" style="left:' + (p[0] / W * 100).toFixed(3) + "%;top:" +
        (p[1] / H * 100).toFixed(3) + "%;--p:" + (i % 3) + '"></i>';
    }
    s.bulbs.innerHTML = html;
  }

  /* ---------- extrusion slices: gold trim, then red fading to near black ---------- */
  function buildLayers(s) {
    if (s.box.querySelector(".bs-layer")) return;
    var from = [122, 14, 20], to = [28, 3, 5];
    for (var k = LAYERS; k >= 1; k--) {
      var lay = hidden(el("div", "bs-layer" + (k === LAYERS ? " bs-back" : ""), s.box, s.front));
      lay.style.setProperty("--k", k);
      if (k === 1) { lay.style.background = "#d6a650"; continue; }
      var t = (k - 2) / (LAYERS - 2);
      lay.style.background = "rgb(" + from.map(function (c, j) { return Math.round(c + (to[j] - c) * t); }).join(",") + ")";
    }
  }

  function init(rootEl) {
    if (rootEl._bodegaSign) return;
    var q = function (c) { return rootEl.querySelector(c); };
    var s = { root: rootEl, stage: q(".bs-stage"), box: q(".bs-box"), front: q(".bs-front"), panel: q(".bs-panel"),
      name: q(".bs-name"), halo: q(".bs-halo"), glare: q(".bs-glare"), bulbs: q(".bs-bulbs"),
      rx: 0, ry: 0, gx: .5, gy: .3, near: 0, flkNext: performance.now() + 2500, compact: false };
    if (!s.stage || !s.box || !s.front) return;
    rootEl._bodegaSign = s;
    if (!s.bulbs) s.bulbs = hidden(el("div", "bs-bulbs", s.front, s.front.firstChild));
    if (!s.glare) s.glare = hidden(el("div", "bs-glare", s.front));
    buildLayers(s);
    if (s.name) {
      if (window.MutationObserver) s.mo = new MutationObserver(function () { buildName(s); });
      buildName(s);
    }
    layoutBulbs(s);
    if (window.ResizeObserver) new ResizeObserver(function () { layoutBulbs(s); measure(); }).observe(s.front);
    rootEl.addEventListener("transitionend", function (e) { if (e.target === rootEl) measure(); });
    signs.push(s);
  }

  /* ---------- page-level state ---------- */
  function measure() {                    // --sign-h from the primary sign (read, then write)
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

  function flickerAt(s, now) {
    if (now < s.flkNext) return 1;
    var e = now - s.flkNext;
    for (var i = 0; i < FLICKER.length; i++) {
      if (e < FLICKER[i][0]) return FLICKER[i][1];
      e -= FLICKER[i][0];
    }
    s.flkNext = now + 3500 + Math.random() * 6000;
    return 1;
  }

  /* ---------- the one rAF loop ---------- */
  function tick(now) {
    raf = 0;
    if (mqReduce.matches || !signs.length) return;
    var dt = Math.min(.05, lastT ? (now - lastT) / 1000 : .016);
    lastT = now;
    var kT = 1 - Math.exp(-dt * 6), kN = 1 - Math.exp(-dt * 5);
    var vw = window.innerWidth, vh = window.innerHeight, t = now / 1000;
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
        gy = clamp((P.y - r.top) / r.height, -.2, 1.2);
        var ex = Math.max(r.left - P.x, 0, P.x - r.right), ey = Math.max(r.top - P.y, 0, P.y - r.bottom);
        near = clamp(1 - Math.sqrt(ex * ex + ey * ey) / 280, 0, 1);
      } else if (noHover || !P.mouse) {     // idle sway (touch, or before the mouse ever moved)
        ty = Math.sin(t * .55 + idx) * 4.5;
        tx = Math.sin(t * .37 + idx) * 2.2;
      }
      if (gx === undefined) { gx = .5 + s.ry / MAX_Y * .45; gy = .3 - s.rx / MAX_X * .5; }
      s.rx += (tx - s.rx) * kT; s.ry += (ty - s.ry) * kT;
      s.gx += (gx - s.gx) * kT; s.gy += (gy - s.gy) * kT;
      s.near += (near - s.near) * kN;
      var flk = s.flick ? flickerAt(s, now) : 1;
      var inten = (.45 + .55 * s.near) * (.8 + .2 * flk);
      s.inten = inten; s.flk = flk;

      setStyle(s.box, "transform", "rotateX(" + s.rx.toFixed(2) + "deg) rotateY(" + s.ry.toFixed(2) + "deg)", "_t");
      if (s.W) setStyle(s.glare, "transform", "translate3d(" + (s.gx * s.W).toFixed(1) + "px," + (s.gy * s.H).toFixed(1) + "px,0)", "_t");
      setStyle(s.glare, "opacity", (.5 + .5 * s.near).toFixed(3), "_o");
      setStyle(s.halo, "opacity", (.4 + .6 * inten).toFixed(3), "_o");
      setStyle(s.bloom, "opacity", (.25 + .5 * s.near * flk).toFixed(3), "_o");
      setStyle(s.flick, "opacity", String(flk), "_o");
      if (idx === 0) prim = { cx: cx, cy: cy };
    });

    /* light position: pointer while present, sign centre otherwise */
    var lx = P.on ? P.x : prim.cx, ly = P.on ? P.y : prim.cy;
    if (light.x < 0) { light.x = lx; light.y = ly; }
    light.x += (lx - light.x) * kT; light.y += (ly - light.y) * kT;
    var LX = Math.round(light.x), LY = Math.round(light.y);
    setRoot("--sign-h", Math.round(signH) + "px");
    setRoot("--sign-intensity", primary.inten.toFixed(2));
    setRoot("--light-x", LX + "px");
    setRoot("--light-y", LY + "px");
    for (var i = 0; i < tileList.length; i++) {
      var tl = tileList[i], vx = (LX - Math.round(tileRects[i].left)) + "px", vy = (LY - Math.round(tileRects[i].top)) + "px";
      if (tl._lx !== vx) { tl._lx = vx; tl.style.setProperty("--lx", vx); }
      if (tl._ly !== vy) { tl._ly = vy; tl.style.setProperty("--ly", vy); }
    }
    start();
  }
  function start() { if (!raf && !document.hidden) raf = requestAnimationFrame(tick); }

  /* ---------- input ---------- */
  function onTouch(e) {
    var tp = e.touches && e.touches[0];
    if (tp) { P.x = tp.clientX; P.y = tp.clientY; P.on = true; }
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
    if (mqReduce.addEventListener) mqReduce.addEventListener("change", reset);
  }

  function reset() {                      // apply / remove the static reduced-motion state
    signs.forEach(function (s) {
      if (!mqReduce.matches) return;
      s.rx = s.ry = s.near = 0;
      setStyle(s.box, "transform", "none", "_t");
      if (s.W) setStyle(s.glare, "transform", "translate3d(" + (.5 * s.W) + "px," + (.3 * s.H) + "px,0)", "_t");
      setStyle(s.flick, "opacity", "1", "_o");
      setStyle(s.bloom, "opacity", ".3", "_o");
      setStyle(s.halo, "opacity", ".6", "_o");
    });
    if (mqReduce.matches) {
      setRoot("--sign-intensity", ".5");
      var r = signs[0].stage.getBoundingClientRect();
      setRoot("--light-x", Math.round(r.left + r.width / 2) + "px");
      setRoot("--light-y", Math.round(r.top + r.height / 2) + "px");
      tiles.vis.forEach(function (tl) { tl.style.removeProperty("--lx"); tl.style.removeProperty("--ly"); tl._lx = tl._ly = null; });
      measure();
    } else start();
  }

  function initAll() {
    var list = document.querySelectorAll(".bodega-sign");
    for (var i = 0; i < list.length; i++) init(list[i]);
    if (!signs.length) return;
    if (!document.querySelector(".sign-ambient")) hidden(el("div", "sign-ambient", document.body));
    document.body.classList.add("sign-lit");
    setRoot("--sign-glow", (signs[0].root.getAttribute("data-glow") || "255 104 64").trim());
    if (window.IntersectionObserver) {
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
