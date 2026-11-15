/* Gonzales Bodega — free-floating 3D channel letters (Three.js / WebGL).
   Classic script, no build step. Self-initializes every .bodega-sign on DOMContentLoaded
   (markup + API: see sign.css). Loads three.js (pinned) from jsDelivr and the glyph outlines
   from fonts/archivo-black.json; if either fails, the h1 stays as plain coloured letters. */
(function () {
  "use strict";

  var THREE_URL = "https://cdn.jsdelivr.net/npm/three@0.170.0/build/three.module.min.js";
  var BASE = (document.currentScript && document.currentScript.src) || location.href;
  var FONT_URL = new URL("fonts/archivo-black.json", BASE).href;

  var DEG = Math.PI / 180;
  /* two-point perspective: the camera sits at the mid-height of the two-line block, no pitch, no roll,
     so verticals stay vertical; the sign only turns about its vertical axis */
  var REST_Y = 0;                         // resting yaw (deg): faces straight forward
  var FOCAL_MM = 5;                       // lens: focal length vs. a 36 mm-wide frame around the sign (5 mm = ultra-wide,
                                          // strongly exaggerated depth; 50 mm ≈ natural). Flat faces stay undistorted.
  var MAX_Y = 4;                          // limit of the extra yaw from pointer / touch / device (deg, each way;
                                          // small, because the ultra-wide lens exaggerates every turn)
  /* Relative control, no fixed origin: each pointer / finger / phone movement nudges the yaw by its own
     delta. The yaw stops at ±MAX_Y; moving back the other way from wherever you are turns it straight back. */
  var GAIN_PX = .022;                     // deg per px of mouse / finger movement
  var GAIN_TILT = .9;                     // deg of yaw per degree the phone is turned left/right (gamma)
  var GAIN_BETA = .7;                     // deg of pitch per degree the phone is tipped toward/away (beta)
  var MAX_X = 3;                          // desktop: limit of the pitch (up/down tilt) from vertical mouse movement (deg)
  var MAX_Y_PHONE = 9, MAX_X_PHONE = 7;   // phones: a bigger range so "orbiting" the phone clearly turns the sign
  var ORI_SMOOTH = .7, ORI_DEAD = .12;    // phones: low-pass the sensor and ignore sub-0.12° jitter (no drifting)
  var Y = { off: 0, offX: 0, lx: null, ly: null, lg: null, lb: null, fg: null, fb: null, drag: false, t: -1e9 };   // yaw / pitch offsets; last touch x, gamma, beta
  function nudge(d) { var m = noHover ? MAX_Y_PHONE : MAX_Y; Y.off = clamp(Y.off + d, -m, m); Y.t = performance.now(); start(); }
  /* iOS 13+ motion permission. It can only be requested from a real tap (a touchend that ends a scroll does
     NOT count), so we keep listening until iOS answers granted/denied, and show a small "tap to tilt" hint. */
  var PERM = { api: !!(window.DeviceOrientationEvent && typeof window.DeviceOrientationEvent.requestPermission === "function"),
               state: "unknown", events: 0, last: null, hint: null };
  var DBG = /[?&]debug(=|&|$)/.test(location.search), dbgLog = [];
  function dbg(m) { if (!DBG) return; dbgLog.push(new Date().toTimeString().slice(0, 8) + " " + m); if (dbgLog.length > 8) dbgLog.shift(); }
  function nudgeX(d) { var m = noHover ? MAX_X_PHONE : MAX_X; Y.offX = clamp(Y.offX + d, -m, m); Y.t = performance.now(); start(); }
  var COMPACT_ON = 64, COMPACT_OFF = 24;  // scroll hysteresis (px)
  var STEP = 3.6;                         // seconds per palette colour
  var COLOR_MS = 66;                      // colour updates ~15 fps
  var PAL = [[255, 46, 46], [255, 132, 0], [255, 206, 0], [28, 214, 92], [38, 136, 255], [236, 52, 196]];
  var LED = [[214, 58, 52], [226, 120, 18], [190, 146, 0], [34, 150, 84], [42, 112, 214], [196, 56, 160], [128, 128, 134]];
  var WORD_OFFSET = 2.5;                  // palette steps between words (never the same colour)
  var SATURATION = .8;                    // scale on the palettes' HSL saturation (1 = original; .8 = 20% less)
  function desat(c) {                     // keep hue and lightness, scale saturation
    var r = c[0] / 255, g = c[1] / 255, b = c[2] / 255;
    var mx = Math.max(r, g, b), mn = Math.min(r, g, b), l = (mx + mn) / 2, d = mx - mn;
    if (!d) return c.slice();
    var s = d / (1 - Math.abs(2 * l - 1)), h;
    if (mx === r) h = ((g - b) / d) % 6; else if (mx === g) h = (b - r) / d + 2; else h = (r - g) / d + 4;
    s *= SATURATION;
    var C = (1 - Math.abs(2 * l - 1)) * s, X = C * (1 - Math.abs((h % 2 + 2) % 2 - 1)), m = l - C / 2, o;
    h = (h + 6) % 6;
    o = h < 1 ? [C, X, 0] : h < 2 ? [X, C, 0] : h < 3 ? [0, C, X] : h < 4 ? [0, X, C] : h < 5 ? [X, 0, C] : [C, 0, X];
    return [Math.round((o[0] + m) * 255), Math.round((o[1] + m) * 255), Math.round((o[2] + m) * 255)];
  }
  PAL = PAL.map(desat);
  LED = LED.map(desat);

  /* letter construction, in em (cap height = .688em) */
  var DEPTH = .17;                        // extrusion ≈ 25% of the cap height
  var TRACK = .03, LINE = .84, CAM_K = 1.08;   // camera distance = block width × CAM_K (close: strong convergence)
  var WALL_Z = -.2;                       // the "wall" the glow / shadow lands on, behind the letters
  var MASK_R = 48, MASK_PAD = .95;        // glow mask: px per em, padding in em

  var mm = function (q) { return window.matchMedia ? window.matchMedia(q) : { matches: false }; };
  var mqReduce = mm("(prefers-reduced-motion: reduce)");
  var noHover = mm("(hover: none)").matches;
  var root = document.documentElement;
  var signs = [], raf = 0, lastT = 0, lastColor = -1e9;
  var P = { x: 0, y: 0, on: false, mouse: false };
  var O = { init: false, dx: 0, dy: 0, t: -1e9, bg: 0, bb: 0 };   // device orientation
  var rootVals = {};
  var light = { x: -1, y: -1 };
  var tiles = { seen: new WeakSet(), vis: new Set(), dirty: new Set(), io: null, ro: null, lastScan: -1e9, pass: 0 };
  var tileList = [], tileRects = [];
  var pulse = 1, scrollT = -1e9;          // light "energy": bumps on scroll / tilt / hue shift, then dissolves
  var LIT_REST = .16, LIT_STILL = .4;     // resting level of the light on products; fixed level when motion is reduced
  var T = null, FONT = null;              // three.js module + glyph data, once loaded
  var tmpA = [0, 0, 0], tmpB = [0, 0, 0];

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
  function palAt(x, out) {
    var n = PAL.length;
    x = ((x % n) + n) % n;
    var i = Math.floor(x), f = x - i, a = PAL[i], b = PAL[(i + 1) % n];
    f = f * f * (3 - 2 * f);                                 // ease: colours linger, then glide
    out[0] = a[0] + (b[0] - a[0]) * f; out[1] = a[1] + (b[1] - a[1]) * f; out[2] = a[2] + (b[2] - a[2]) * f;
    return out;
  }
  function rgb(c) { return Math.round(c[0]) + " " + Math.round(c[1]) + " " + Math.round(c[2]); }

  function paint(s, t, still) {
    for (var i = 0; i < s.words.length; i++) {
      var x = t / STEP + i * WORD_OFFSET;
      var col = s.cols[i] || (s.cols[i] = { c1: [0, 0, 0], c2: [0, 0, 0] });
      palAt(x, col.c1); palAt(x + .8, col.c2);
      setVar(s.words[i], "--c1", rgb(col.c1));               // fallback letters follow the cycle too
    }
    for (var j = 0; j < s.leds.length; j++) {
      var l = s.leds[j], c = still ? LED[(j * 2) % 6] : LED[Math.floor(t / l.dur + l.ph) % LED.length];   // still: fixed dim colours
      if (l.c !== c) {
        l.c = c;
        l.el.style.color = "rgb(" + rgb(c) + " / .72)";
        l.el.style.textShadow = still ? "none" : "0 0 .55em rgb(" + rgb(c) + " / .3)";
      }
    }
    return s.cols[0] ? s.cols[0].c1 : null;
  }

  /* ---------- h1: accessible text + fallback letters ---------- */
  function buildName(s) {
    var h = s.name;
    if (s.mo) s.mo.disconnect();
    var sr = h.querySelector(".bs-sr");
    var text = (sr ? sr.textContent : h.textContent).replace(/\s+/g, " ").trim();
    h.textContent = "";
    el("span", "bs-sr", h).textContent = text;
    var vis = hidden(el("span", "bs-letters", h));
    s.words = [];
    s.text = text.toUpperCase().split(" ");
    s.text.forEach(function (word) {
      var w = el("span", "bs-word", vis);
      w.textContent = word;
      s.words.push(w);
    });
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
      s.leds.push({ el: e, c: null, dur: .55 + ((i * 37) % 9) / 10, ph: (i * 2.3) % LED.length });
    });
    if (s.mo2) s.mo2.observe(p, { childList: true, characterData: true, subtree: true });
  }

  function init(rootEl) {
    if (rootEl._bodegaSign) return;
    var q = function (c) { return rootEl.querySelector(c); };
    var s = { root: rootEl, stage: q(".bs-stage"), name: q(".bs-name"), sub: q(".bs-sub"),
      words: [], text: [], leds: [], cols: [], gl: null,
      ry: REST_Y, rx: 0, near: 0, inten: .5, compact: false };
    if (!s.stage || !s.name) return;
    rootEl._bodegaSign = s;
    rootEl.classList.add("bs-pending");
    if (window.MutationObserver) {
      s.mo = new MutationObserver(function () {
        buildName(s); paint(s, performance.now() / 1000, mqReduce.matches);
        if (s.gl) { buildWords(s); s.gl.key = ""; sizeGL(s); draw(s); }
      });
      s.mo2 = new MutationObserver(function () { buildLeds(s); paint(s, performance.now() / 1000, mqReduce.matches); });
    }
    buildName(s);
    buildLeds(s);
    if (window.ResizeObserver) new ResizeObserver(function () { sizeGL(s); measure(); start(); }).observe(s.stage);
    rootEl.addEventListener("transitionend", function (e) { if (e.target === rootEl) measure(); });
    signs.push(s);
  }

  /* =====================================================================
     Three.js: real extruded channel letters
     ===================================================================== */
  function glyphOf(ch) {
    var g = FONT.glyphs[ch] || FONT.glyphs[ch.toUpperCase()] || FONT.glyphs["?"];
    if (g && !g.t) g.t = g.o ? g.o.split(" ") : [];
    return g;
  }
  /* walk a word's outlines: cb(cmd, x1, y1, x2, y2, x3, y3) in em, x already advanced */
  function walkWord(word, cb) {
    var k = 1 / FONT.unitsPerEm, x = 0;
    for (var n = 0; n < word.length; n++) {
      var g = glyphOf(word[n]);
      if (!g) continue;
      var t = g.t, i = 0;
      while (i < t.length) {
        var c = t[i++];
        if (c === "M" || c === "L") { cb(c, x + t[i] * k, t[i + 1] * k); i += 2; }
        else if (c === "Q") { cb(c, x + t[i] * k, t[i + 1] * k, x + t[i + 2] * k, t[i + 3] * k); i += 4; }
        else if (c === "C") { cb(c, x + t[i] * k, t[i + 1] * k, x + t[i + 2] * k, t[i + 3] * k, x + t[i + 4] * k, t[i + 5] * k); i += 6; }
      }
      x += g.a * k + (n < word.length - 1 ? TRACK : 0);
    }
    return x;                                                // advance width
  }
  function wordShapes(word) {
    var sp = new T.ShapePath();
    var w = walkWord(word, function (c, a, b, d, e, f, g) {
      if (c === "M") sp.moveTo(a, b);
      else if (c === "L") sp.lineTo(a, b);
      else if (c === "Q") sp.quadraticCurveTo(a, b, d, e);
      else sp.bezierCurveTo(a, b, d, e, f, g);
    });
    return { shapes: sp.toShapes(), width: w };
  }
  /* blurred silhouettes for the wall glow (R) and the tight bloom at the face (G) */
  function wordMask(word, box) {
    var R = MASK_R, pad = MASK_PAD * R;
    var w = Math.ceil((box.max.x - box.min.x) * R + pad * 2), h = Math.ceil((box.max.y - box.min.y) * R + pad * 2);
    var cv = document.createElement("canvas");
    cv.width = w; cv.height = h;
    var ctx = cv.getContext("2d"), OFF = w + 64;
    var path = new Path2D();
    var X = function (x) { return (x - box.min.x) * R + pad - OFF; }, Y = function (y) { return h - pad - (y - box.min.y) * R; };
    walkWord(word, function (c, a, b, d, e, f, g) {
      if (c === "M") path.moveTo(X(a), Y(b));
      else if (c === "L") path.lineTo(X(a), Y(b));
      else if (c === "Q") path.quadraticCurveTo(X(a), Y(b), X(d), Y(e));
      else path.bezierCurveTo(X(a), Y(b), X(d), Y(e), X(f), Y(g));
    });
    ctx.fillStyle = "#000";
    ctx.fillRect(0, 0, w, h);
    ctx.globalCompositeOperation = "lighter";
    ctx.shadowOffsetX = OFF;                                 // only the blurred "shadow" lands on the canvas
    ctx.fillStyle = "#fff";
    ctx.shadowColor = "#f00"; ctx.shadowBlur = R * .5; ctx.fill(path);
    ctx.shadowColor = "#0f0"; ctx.shadowBlur = R * .09; ctx.fill(path);
    var tex = new T.CanvasTexture(cv);
    tex.generateMipmaps = false;
    tex.minFilter = tex.magFilter = T.LinearFilter;
    return { tex: tex, w: w / R, h: h / R };
  }

  var VERT = "varying vec2 vUv; varying vec2 vP; void main(){ vUv = uv; vP = position.xy; gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0); }";
  /* lit acrylic face: colour gradient across the word, whitened hot centre, moving soft sheen (sRGB out) */
  var FACE_FRAG = "uniform vec3 uC1; uniform vec3 uC2; uniform vec4 uB; uniform float uSheen; varying vec2 vP;" +
    "void main(){ float t = clamp((vP.x - uB.x) / uB.y, 0.0, 1.0); float v = clamp((vP.y - uB.z) / uB.w, 0.0, 1.0);" +
    "vec3 c = mix(uC1, uC2, t);" +
    "float hot = 1.0 - smoothstep(0.0, 0.62, abs(v - 0.54));" +
    "c = mix(c, vec3(1.0), 0.10 + 0.40 * hot);" +
    "c *= 0.90 + 0.10 * smoothstep(0.0, 0.35, v);" +
    "float sh = exp(-pow((t - uSheen + (v - 0.5) * 0.25) * 2.6, 2.0));" +
    "c += vec3(0.09) * sh;" +
    "gl_FragColor = vec4(min(c, vec3(1.0)), 1.0); }";
  /* wall: coloured glow + soft grey shadow, one quad per word */
  var WALL_FRAG = "uniform sampler2D uMap; uniform vec3 uC1; uniform vec3 uC2; uniform float uGlow; uniform float uShadow; uniform vec2 uOff; varying vec2 vUv;" +
    "void main(){ float g = texture2D(uMap, vUv).r; float s = texture2D(uMap, vUv + uOff).r;" +
    "float e = smoothstep(0.0, 0.08, vUv.x) * smoothstep(0.0, 0.08, 1.0 - vUv.x) * smoothstep(0.0, 0.12, vUv.y) * smoothstep(0.0, 0.12, 1.0 - vUv.y);" +
    "float ag = clamp(pow(g, 1.25) * uGlow, 0.0, 1.0) * e; float as = clamp(s * uShadow, 0.0, 1.0) * e;" +
    "vec3 c = mix(uC1, uC2, vUv.x); float a = ag + as * (1.0 - ag);" +
    "gl_FragColor = vec4((c * ag + vec3(0.07, 0.07, 0.09) * as * (1.0 - ag)) / max(a, 0.0001), a); }";
  /* bloom: tight halo hugging the face */
  var BLOOM_FRAG = "uniform sampler2D uMap; uniform vec3 uC1; uniform vec3 uC2; uniform float uGlow; varying vec2 vUv;" +
    "void main(){ float g = texture2D(uMap, vUv).g; vec3 c = mix(mix(uC1, uC2, vUv.x), vec3(1.0), 0.25);" +
    "gl_FragColor = vec4(c, clamp(g * g * uGlow, 0.0, 1.0)); }";

  function makeEnv(g) {                                      // small studio: grey room + soft light panels
    var sc = new T.Scene(), geo = new T.BoxGeometry(1, 1, 1), mats = [];
    function box(v, sx, sy, sz, x, y, z, back) {
      var m = new T.MeshBasicMaterial({ color: new T.Color(v, v, v * 1.02), side: back ? T.BackSide : T.FrontSide });
      var mesh = new T.Mesh(geo, m);
      mesh.scale.set(sx, sy, sz); mesh.position.set(x, y, z);
      sc.add(mesh); mats.push(m);
    }
    box(.2, 20, 20, 20, 0, 0, 0, true);
    box(7, 12, .2, 10, 0, 9.4, 1);                           // ceiling panel
    box(4, .2, 7, 7, -9.4, 1, 2);                            // left softbox
    box(1.6, .2, 7, 7, 9.4, 0, 2);                           // right fill
    box(2.2, 12, 4, .2, 0, 3, 9.4);                          // behind the camera
    box(.9, 14, .2, 10, 0, -9.4, 0);                         // floor bounce (the white page)
    var pm = new T.PMREMGenerator(g.renderer);
    var rt = pm.fromScene(sc, .035);
    pm.dispose(); geo.dispose();
    mats.forEach(function (m) { m.dispose(); });
    if (g.envRT) g.envRT.dispose();
    g.envRT = rt;
    g.scene.environment = rt.texture;
  }

  function setup3D(s) {
    if (s.gl || !T || !FONT) return;
    var canvas = hidden(el("canvas", "bs-canvas", s.stage, s.stage.firstChild));
    var renderer;
    try { renderer = new T.WebGLRenderer({ canvas: canvas, alpha: true, antialias: true }); }
    catch (err) { canvas.remove(); throw err; }
    renderer.setClearColor(0x000000, 0);
    renderer.outputColorSpace = T.SRGBColorSpace;
    renderer.toneMapping = T.ACESFilmicToneMapping;
    renderer.toneMappingExposure = 1.15;
    var g = s.gl = { canvas: canvas, renderer: renderer, scene: new T.Scene(), words: [], key: "", lines: 0, blockW: 1,
      camera: new T.PerspectiveCamera(30, 2, .1, 80), tilt: new T.Group(), rootG: new T.Group() };
    g.rootG.add(g.tilt);
    g.scene.add(g.rootG);
    var key = new T.DirectionalLight(0xffffff, 2.4);
    key.position.set(-2.5, 3.5, 4);
    var fill = new T.DirectionalLight(0xdfe6ff, .7);
    fill.position.set(3, -1, 3);
    g.scene.add(key, fill, new T.HemisphereLight(0xffffff, 0x9a9aa2, .7));
    makeEnv(g);
    g.matBody = new T.MeshStandardMaterial({ color: 0x2b2b30, roughness: .55, metalness: .35, envMapIntensity: 1.1 });
    g.matRim = new T.MeshPhysicalMaterial({ color: 0x0c0c0e, roughness: .34, metalness: .45, clearcoat: .7, clearcoatRoughness: .22, envMapIntensity: 1.1 });
    canvas.addEventListener("webglcontextlost", function (e) { e.preventDefault(); });
    canvas.addEventListener("webglcontextrestored", function () { makeEnv(g); draw(s); });
    buildWords(s);
    sizeGL(s);
    draw(s);
    s.root.classList.add("is-3d");
    s.root.classList.remove("bs-pending");
  }

  function buildWords(s) {
    var g = s.gl;
    g.words.forEach(function (w) {                           // text changed: drop the old meshes
      g.tilt.remove(w.grp); g.tilt.remove(w.wall);
      w.geos.forEach(function (x) { x.dispose(); });
      w.mats.forEach(function (x) { x.dispose(); });
      w.mask.tex.dispose();
    });
    g.words = [];
    var bt = .009;                                           // edge bevel
    s.text.forEach(function (word) {
      var ws = wordShapes(word);
      var body = new T.ExtrudeGeometry(ws.shapes, { depth: DEPTH - .012 - bt * 2, curveSegments: 14,
        bevelEnabled: true, bevelThickness: bt, bevelSize: bt, bevelOffset: -bt, bevelSegments: 3 });
      body.translate(0, 0, -DEPTH + bt);                     // returns: z = -DEPTH … -.012
      var rim = new T.ExtrudeGeometry(ws.shapes, { depth: .014, curveSegments: 14,
        bevelEnabled: true, bevelThickness: .006, bevelSize: .006, bevelOffset: .001, bevelSegments: 3 });
      rim.translate(0, 0, -.014);                            // trim-cap lip: slightly proud of the returns, z = -.02 … .006
      var face = new T.ExtrudeGeometry(ws.shapes, { depth: .004, curveSegments: 14,
        bevelEnabled: true, bevelThickness: .004, bevelSize: .005, bevelOffset: -.026, bevelSegments: 2 });
      face.translate(0, 0, .002);                            // acrylic face, inset from the rim, z = -.002 … .010
      body.computeBoundingBox();
      var bb = body.boundingBox, mask = wordMask(word, bb);
      var plane = new T.PlaneGeometry(mask.w, mask.h);
      var cx = (bb.min.x + bb.max.x) / 2, cy = (bb.min.y + bb.max.y) / 2;
      var uC1 = { value: new T.Vector3(1, .2, .2) }, uC2 = { value: new T.Vector3(1, .5, 0) }, uGlow = { value: .22 };
      var mFace = new T.ShaderMaterial({ vertexShader: VERT, fragmentShader: FACE_FRAG, toneMapped: false,
        uniforms: { uC1: uC1, uC2: uC2, uSheen: { value: .5 }, uB: { value: new T.Vector4(bb.min.x, bb.max.x - bb.min.x, 0, FONT.capHeight / FONT.unitsPerEm) } } });
      var mWall = new T.ShaderMaterial({ vertexShader: VERT, fragmentShader: WALL_FRAG, transparent: true, depthWrite: false, toneMapped: false,
        uniforms: { uMap: { value: mask.tex }, uC1: uC1, uC2: uC2, uGlow: uGlow, uShadow: { value: .15 }, uOff: { value: new T.Vector2(0, .17 / mask.h) } } });
      var mBloom = new T.ShaderMaterial({ vertexShader: VERT, fragmentShader: BLOOM_FRAG, transparent: true, depthWrite: false, toneMapped: false,
        uniforms: { uMap: { value: mask.tex }, uC1: uC1, uC2: uC2, uGlow: { value: .5 } } });
      var grp = new T.Group();
      grp.add(new T.Mesh(body, g.matBody), new T.Mesh(rim, g.matRim), new T.Mesh(face, mFace));
      var bloom = new T.Mesh(plane, mBloom);
      bloom.position.set(cx, cy, .012);
      bloom.renderOrder = 2;
      grp.add(bloom);
      var wall = new T.Mesh(plane, mWall);
      wall.renderOrder = -1;
      wall.scale.setScalar(1.1);
      g.tilt.add(grp, wall);
      g.words.push({ grp: grp, wall: wall, cx: cx, cy: cy, width: ws.width, mFace: mFace, mBloom: mBloom, uC1: uC1.value, uC2: uC2.value, uGlow: uGlow,
        geos: [body, rim, face, plane], mats: [mFace, mWall, mBloom], mask: mask });
    });
    g.lines = 0;
  }

  /* place the words: always stacked, one word per line, centred as a block */
  function layout(s) {
    var g = s.gl, cap = FONT.capHeight / FONT.unitsPerEm, n = g.words.length, i, w, maxW = 0;
    for (i = 0; i < n; i++) maxW = Math.max(maxW, g.words[i].width);
    var blockH = (n - 1) * LINE + cap;
    for (i = 0; i < n; i++) {
      w = g.words[i];
      var px = -w.width / 2, py = blockH / 2 - cap - i * LINE;
      w.grp.position.set(px, py, DEPTH / 2);                 // the yaw axis runs through the middle of the solid
      w.wall.position.set(px + w.cx, py + w.cy - .02, DEPTH / 2 - DEPTH + WALL_Z);   // glow / shadow plane just behind
    }
    g.lines = n;
    g.blockW = maxW;
  }

  /* canvas follows the stage; its centre (= the camera's eye level) sits on the centre of the h1 */
  function sizeGL(s) {
    var g = s.gl;
    if (!g) return;
    var W = s.stage.offsetWidth, SH = s.stage.offsetHeight;
    if (!W || !SH) return;
    var fs = parseFloat(getComputedStyle(s.name).fontSize) || 48;
    var yc = s.name.offsetTop + s.name.offsetHeight / 2;
    var half = Math.ceil(Math.max(yc, SH - yc) + fs * .7);
    var dpr = Math.min(window.devicePixelRatio || 1, 2);
    var key = [W, half, yc, fs, dpr].join("|");
    if (key === g.key) return;
    g.key = key;
    g.canvas.style.width = W + "px";
    g.canvas.style.height = half * 2 + "px";
    g.canvas.style.top = (yc - half) + "px";
    g.renderer.setPixelRatio(dpr);
    g.renderer.setSize(W, half * 2, false);
    if (!g.lines) layout(s);
    /* camera straight ahead at eye level, centred on the block. Its distance comes from the focal length:
       the frame (block + a margin) is treated as a 36 mm-wide sensor, so d = frameHalf × FOCAL_MM / 18.
       Short lens → very close camera → the letter sides fan out strongly toward the centre vanishing point.
       The block is nudged sideways so that, at the resting yaw, its two ends are equally far from the centre. */
    var th = REST_Y * DEG, hw = g.blockW / 2, d = Math.max(.6, (hw + .6) * FOCAL_MM / 18);
    var a = hw * Math.cos(th), zp = -hw * Math.sin(th), xo = -a * zp / d;
    var zf = DEPTH / 2;                                                        // front faces sit this far in front of z = 0
    var halfW = (a + xo) * d / (d - zp - zf) + .22;                          // projected half width at rest (em)
    if (noHover) halfW *= 1.3;                                                // phones: room for the near end to grow when tilted
    var fit = Math.min(1, (W - 24) / 2 / fs / halfW);                        // never wider than the page
    g.camera.aspect = W / (half * 2);
    g.camera.fov = 2 * Math.atan((half * 2 / fs) / (2 * d * fit)) / DEG;     // 1 world unit = 1em on screen at z = 0
    g.camera.position.set(0, 0, d * fit);
    g.camera.updateProjectionMatrix();
    g.rootG.scale.setScalar(fit);
    g.rootG.position.x = xo * fit;
    g.dirty = true;
  }

  function draw(s) {
    var g = s.gl;
    if (!g) return;
    g.tilt.rotation.set(s.rx * DEG, s.ry * DEG, 0);          // yaw (+ a little pitch from the phone tipping)
    for (var i = 0; i < g.words.length; i++) {
      var w = g.words[i], c = s.cols[i];
      if (c) {
        w.uC1.set(c.c1[0] / 255, c.c1[1] / 255, c.c1[2] / 255);
        w.uC2.set(c.c2[0] / 255, c.c2[1] / 255, c.c2[2] / 255);
      }
      w.uGlow.value = .15 + .1 * s.near;
      w.mBloom.uniforms.uGlow.value = .3 + .15 * s.near;
      w.mFace.uniforms.uSheen.value = .5 - (s.ry - REST_Y) / 30;
    }
    g.renderer.render(g.scene, g.camera);
    g.dirty = false;
  }

  function fallback() {                                      // no WebGL / module: plain coloured letters
    signs.forEach(function (s) { if (!s.gl) s.root.classList.remove("bs-pending"); });
    measure();
  }
  function load3D() {
    var imp;
    try {
      if (!window.WebGLRenderingContext || !window.Path2D || !window.fetch) throw 0;
      imp = new Function("u", "return import(u)");           // keeps old parsers from choking on import()
    } catch (err) { fallback(); return; }
    setTimeout(fallback, 3000);                              // slow network: show the fallback meanwhile
    Promise.all([imp(THREE_URL), fetch(FONT_URL).then(function (r) { if (!r.ok) throw new Error("font " + r.status); return r.json(); })])
      .then(function (r) {
        T = r[0]; FONT = r[1];
        signs.forEach(setup3D);
        measure();
        start();
      })
      .catch(function (err) {
        if (window.console) console.warn("[bodega-sign] 3D letters unavailable, using text fallback:", err);
        fallback();
      });
  }

  /* ---------- page-level state ---------- */
  function measure() {
    var s = signs[0];
    if (s) setRoot("--sign-h", Math.round(s.root.getBoundingClientRect().height) + "px");
  }
  function onScroll() {
    var y = window.pageYOffset || root.scrollTop, changed = false;
    scrollT = performance.now();
    signs.forEach(function (s) {
      var c = s.compact ? y > COMPACT_OFF : y > COMPACT_ON;
      if (c !== s.compact) { s.compact = c; s.root.classList.toggle("is-compact", c); changed = true; }
    });
    kick();
  }
  function scanTiles(now) {
    if (now - tiles.lastScan < 1000 || !tiles.io) return;
    tiles.lastScan = now;
    var list = document.querySelectorAll(".tile");
    for (var i = 0; i < list.length; i++) {
      if (!tiles.seen.has(list[i])) {
        tiles.seen.add(list[i]); tiles.io.observe(list[i]);
        if (tiles.ro) tiles.ro.observe(list[i]);
      }
    }
  }

  /* ---------- sign light landing on the food ----------
     Every product image in a visible tile gets three aria-hidden siblings:
       .bs-lit   colour cast masked by the image's own alpha (soft-light): a directional gradient that starts
                 on the edge facing the sign and dissolves across the object
       .bs-rim   thin highlight on the facing edge (image mask minus the same mask nudged away from the light)
       .bs-cast  soft tinted shadow on the tile floor, on the side away from the light
     Strength (--lit) falls off with the tile's distance from the sign (inverse-square-ish) and with time:
     it lifts a little when the light changes (scroll, tilt, a new hue) and eases back to a faint rest. */
  var alphaBoxes = {}, alphaCv = null;
  function alphaBox(img) {                                   // where the object sits inside its (transparent) image, 0–1
    var k = img.currentSrc || img.src, b = alphaBoxes[k];
    if (b) return b;
    b = alphaBoxes[k] = { x0: 0, y0: 0, x1: 1, y1: 1 };
    try {
      var N = 48;
      if (!alphaCv) { alphaCv = document.createElement("canvas"); alphaCv.width = alphaCv.height = N; }
      var ctx = alphaCv.getContext("2d", { willReadFrequently: true });
      ctx.clearRect(0, 0, N, N);
      ctx.drawImage(img, 0, 0, N, N);
      var d = ctx.getImageData(0, 0, N, N).data, x0 = N, y0 = N, x1 = -1, y1 = -1;
      for (var y = 0; y < N; y++) for (var x = 0; x < N; x++) {
        if (d[(y * N + x) * 4 + 3] > 40) { if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; }
      }
      if (x1 >= x0 && y1 >= y0) { b.x0 = x0 / N; b.y0 = y0 / N; b.x1 = (x1 + 1) / N; b.y1 = (y1 + 1) / N; }
    } catch (err) { /* cross-origin image: use the whole box */ }
    return b;
  }
  function litImg(img) {                                     // create the overlays once the image has pixels
    if (img._lit) return;
    if (!img.complete || !img.naturalWidth) {
      if (!img._litWait && !img.complete) {
        img._litWait = true;
        img.addEventListener("load", function () { var tl = img.closest(".tile"); if (tl) { tiles.dirty.add(tl); kick(); } }, { once: true });
      }
      return;
    }
    var m = "url(" + JSON.stringify(img.currentSrc || img.src) + ")";
    var cast = hidden(el("span", "bs-cast", img.parentNode, img));
    var rim = hidden(el("span", "bs-rim", img.parentNode, img.nextSibling));
    var lit = hidden(el("span", "bs-lit", img.parentNode, img.nextSibling));
    lit.style.setProperty("--m", m); rim.style.setProperty("--m", m);
    img._lit = { lit: lit, rim: rim, cast: cast, box: null, bb: alphaBox(img), nw: img.naturalWidth, nh: img.naturalHeight };
  }
  function readTile(tl) {                                    // layout reads only
    var imgs = tl.querySelectorAll("img"), out = [];
    for (var i = 0; i < imgs.length; i++) {
      var im = imgs[i];
      if (!im._lit) continue;
      var cs = getComputedStyle(im), op = cs.objectPosition.split(" ");
      out.push({ o: im._lit, l: im.offsetLeft, t: im.offsetTop, w: im.offsetWidth, h: im.offsetHeight,
        z: cs.zIndex, fit: cs.objectFit === "cover" ? "cover" : "contain", px: op[0] || "50%", py: op[1] || "50%" });
    }
    return out;
  }
  function writeTile(boxes) {
    for (var i = 0; i < boxes.length; i++) {
      var b = boxes[i], o = b.o, k = [b.l, b.t, b.w, b.h, b.z, b.px, b.py].join("|");
      if (o.box === k) continue;
      o.box = k;
      /* the object's own rectangle (alpha bounds) inside the img box, honouring object-fit / object-position */
      var sc = b.fit === "cover" ? Math.max(b.w / o.nw, b.h / o.nh) : Math.min(b.w / o.nw, b.h / o.nh);
      var iw = o.nw * sc, ih = o.nh * sc;
      var fx = /%$/.test(b.px) ? parseFloat(b.px) / 100 : .5, fy = /%$/.test(b.py) ? parseFloat(b.py) / 100 : .5;
      var ix = (b.w - iw) * fx, iy = (b.h - ih) * fy;
      var bx = ix + o.bb.x0 * iw, by = iy + o.bb.y0 * ih, bw = (o.bb.x1 - o.bb.x0) * iw, bh = (o.bb.y1 - o.bb.y0) * ih;
      var ch = Math.max(10, Math.min(bw * .2, bh * .36));
      for (var j = 0; j < 2; j++) {
        var e = j ? o.rim : o.lit;
        e.style.left = b.l + "px"; e.style.top = b.t + "px"; e.style.width = b.w + "px"; e.style.height = b.h + "px";
        e.style.zIndex = b.z === "auto" ? "" : b.z;
        e.style.setProperty("--mpx", b.px); e.style.setProperty("--mpy", b.py); e.style.setProperty("--ms", b.fit);
        e.style.backgroundSize = bw.toFixed(1) + "px " + bh.toFixed(1) + "px";   // the light gradient spans the object itself
        e.style.backgroundPosition = bx.toFixed(1) + "px " + by.toFixed(1) + "px";
      }
      o.cast.style.left = (b.l + bx + bw * .03).toFixed(1) + "px"; o.cast.style.width = (bw * .94).toFixed(1) + "px";
      o.cast.style.top = (b.t + by + bh - ch * .6).toFixed(1) + "px"; o.cast.style.height = ch.toFixed(1) + "px";
    }
  }
  /* reads (rects + dirty boxes), then writes (per-tile vars). The light is the sign itself: it comes from
     the sign's position above each tile; lx (pointer / tilt) only nudges it sideways a little. */
  function lightTiles(now, lx, gain) {
    scanTiles(now);
    var i, tl, n = 0, pending = [];
    var sr = signs[0].root.getBoundingClientRect();
    tiles.vis.forEach(function (t) {
      if (!t.isConnected) { tiles.vis.delete(t); tiles.dirty.delete(t); return; }
      tileList[n] = t; tileRects[n++] = t.getBoundingClientRect();
    });
    tileList.length = tileRects.length = n;
    if (tiles.dirty.size) {
      tiles.dirty.forEach(function (t) {
        if (!tiles.vis.has(t)) return;                       // measured when it scrolls into view
        tiles.dirty.delete(t);
        var imgs = t.querySelectorAll("img");
        for (var j = 0; j < imgs.length; j++) litImg(imgs[j]);
        pending.push(t);
      });
      for (i = 0; i < pending.length; i++) pending[i] = readTile(pending[i]);   // all reads…
      for (i = 0; i < pending.length; i++) writeTile(pending[i]);               // …then all writes
    }
    var scx = sr.left + sr.width / 2, sx = scx + clamp((lx - scx) * .1, -60, 60), sy = sr.bottom - 10;
    for (i = 0; i < n; i++) {
      tl = tileList[i];
      var r = tileRects[i], dx = sx - (r.left + r.width / 2), dy = sy - (r.top + r.height / 2);
      var d = Math.sqrt(dx * dx + dy * dy) || 1, ux = dx / d, uy = dy / d;
      var lit = clamp(1.25 / (1 + (d / 340) * (d / 340)), .05, 1) * gain;
      setVar(tl, "--lit", lit.toFixed(2));
      setVar(tl, "--ang", Math.round(Math.atan2(-ux, uy) / DEG) + "deg");   // CSS gradient angle: away from the sign
      setVar(tl, "--rx", (-ux * 2.6).toFixed(1) + "px");
      setVar(tl, "--ry", (-uy * 2.6).toFixed(1) + "px");
      setVar(tl, "--cx", Math.round(-ux * 12) + "px");
    }
  }
  function kick() { start(); }                               // something about the tiles changed

  /* ---------- the one rAF loop (stops when the tab is hidden) ----------
     Reduced motion: the sign still turns with the pointer / device (the user's own input, eased more gently)
     and the colours still drift, but nothing moves on its own: no idle sway, no LED flashing, no light pulse. */
  function tick(now) {
    raf = 0;
    if (!signs.length) return;
    var reduce = mqReduce.matches;
    var dt = Math.min(.05, lastT ? (now - lastT) / 1000 : .016);
    lastT = now;
    var kT = 1 - Math.exp(-dt * (reduce ? 2.6 : 6)), kN = 1 - Math.exp(-dt * 5);
    var vw = window.innerWidth, vh = window.innerHeight, t = now / 1000;
    var useOri = !P.on && now - O.t < 1500;
    var primary = signs[0], pcx = 0, pcy = 0, tiltSpeed = 0;

    /* reads */
    var signH = primary.root.getBoundingClientRect().height;
    var colorTick = now - lastColor >= COLOR_MS;
    if (colorTick) lastColor = now;

    for (var idx = 0; idx < signs.length; idx++) {
      var s = signs[idx], r = s.name.getBoundingClientRect();
      var cx = r.left + r.width / 2, cy = r.top + r.height / 2;
      /* one-point perspective, facing forward: it turns and tips only with the user's own movement
         (never by itself), by the accumulated, clamped offsets */
      var ty = REST_Y + Y.off, near = 0;
      if (P.on) {
        var ex = Math.max(r.left - P.x, 0, P.x - r.right), ey = Math.max(r.top - P.y, 0, P.y - r.bottom);
        near = clamp(1 - Math.sqrt(ex * ex + ey * ey) / 260, 0, 1);
      }
      var pry = s.ry, prx = s.rx, pn = s.near;
      s.ry = ty;                                             // instant: follows the movement in the same frame
      s.near += (near - s.near) * kN;
      s.inten = .45 + .55 * s.near;
      s.rx = Y.offX;
      var moved = Math.abs(s.ry - pry) > .002 || Math.abs(s.rx - prx) > .002 || Math.abs(s.near - pn) > .002;
      if (idx === 0) tiltSpeed = (Math.abs(s.ry - pry) + Math.abs(s.rx - prx)) / dt;

      if (colorTick) {
        var c = paint(s, t, reduce);
        if (idx === 0 && c) setRoot("--sign-glow", rgb(c));
      }
      if (s.gl && (moved || colorTick || s.gl.dirty)) draw(s);   // render only when something changed
      if (idx === 0) { pcx = cx; pcy = cy; }
    }

    /* light position: pointer, device tilt, else sign centre */
    var lx = pcx, ly = pcy;
    if (P.on) { lx = P.x; ly = P.y; }
    else if (useOri) { lx = pcx + (primary.ry - REST_Y) / MAX_Y * vw * .45; ly = pcy + vh * .35; }
    if (light.x < 0) { light.x = lx; light.y = ly; }
    light.x += (lx - light.x) * kT; light.y += (ly - light.y) * kT;
    var LX = Math.round(light.x), LY = Math.round(light.y);
    setRoot("--sign-h", Math.round(signH) + "px");
    setRoot("--sign-intensity", primary.inten.toFixed(2));
    setRoot("--light-x", LX + "px");
    setRoot("--light-y", LY + "px");
    /* the light on the products dissolves over time: lifts when something changes, eases to a faint rest */
    var act = now - scrollT < 140 ? 1 : 0;
    if ((P.on || useOri) && tiltSpeed > 5) act = Math.max(act, Math.min(1, tiltSpeed / 22));
    var ph = (t / STEP) % 1;
    if (ph > .3 && ph < .7) act = Math.max(act, .22);         // the sign is gliding into a new hue
    pulse += (act - pulse) * (act > pulse ? 1 - Math.exp(-dt * 3.5) : 1 - Math.exp(-dt / 1.6));
    lightTiles(now, light.x, reduce ? LIT_STILL : LIT_REST + (1 - LIT_REST) * pulse);
    start();
  }
  function start() { if (!raf && !document.hidden) raf = requestAnimationFrame(tick); }

  /* ---------- input ---------- */
  function onTouch(e) {
    var tp = e.touches && e.touches[0];
    if (!tp) return;
    /* fingers never rotate the sign (scrolling must not move it): on phones only rotating the phone does */
    P.x = tp.clientX; P.y = tp.clientY; P.on = true;
  }
  function onOrient(e) {
    if (e.gamma == null || e.beta == null) return;
    PERM.events++; PERM.last = [e.alpha, e.beta, e.gamma];
    if (PERM.events === 1) { dbg("first orientation event"); if (PERM.state !== "granted") PERM.state = PERM.api ? "granted" : "not needed"; motionHint(); }
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
    /* relative: turning (gamma) and tipping (beta) the phone nudge the sign; the sensor is low-passed and
       tiny changes are ignored, so a phone held still never makes the sign drift */
    if (Y.fg == null) { Y.fg = g; Y.fb = b; Y.lg = g; Y.lb = b; }
    if (Math.abs(g - Y.fg) > 30 || Math.abs(b - Y.fb) > 45) { Y.fg = g; Y.fb = b; Y.lg = g; Y.lb = b; }   // jump (gamma wrap)
    Y.fg += (g - Y.fg) * ORI_SMOOTH; Y.fb += (b - Y.fb) * ORI_SMOOTH;
    var dg = Y.fg - Y.lg, db = Y.fb - Y.lb;
    if (Math.abs(dg) > ORI_DEAD) { nudge(dg * GAIN_TILT); Y.lg = Y.fg; }
    if (Math.abs(db) > ORI_DEAD) { nudgeX(-db * GAIN_BETA); Y.lb = Y.fb; }
    O.t = now;
    start();
  }
  function askOrientation(src) {                             // must run synchronously inside a real tap
    if (!PERM.api || PERM.state === "granted" || PERM.state === "denied" || PERM.state === "asking") return;
    PERM.state = "asking"; dbg("requestPermission() from " + src);
    try {
      window.DeviceOrientationEvent.requestPermission().then(function (r) {
        PERM.state = r; dbg("permission: " + r); motionHint();
      }).catch(function (err) {
        PERM.state = "unknown"; dbg("permission error: " + (err && (err.name + " " + err.message)));
      });
    } catch (err) { PERM.state = "unknown"; dbg("permission threw: " + err); }
  }
  var tap0 = null;                                           // only a real tap (not a scroll) may ask for permission
  function onTapStart(e) { var t = e.touches && e.touches[0]; tap0 = t ? { x: t.clientX, y: t.clientY, t: performance.now() } : null; }
  function onTapEnd(e) {
    var t = e.changedTouches && e.changedTouches[0];
    if (tap0 && t && Math.abs(t.clientX - tap0.x) < 12 && Math.abs(t.clientY - tap0.y) < 12 && performance.now() - tap0.t < 800) askOrientation("tap");
    tap0 = null;
  }
  function motionHint() {                                     // small "tap to tilt" hint under the sign (iOS only, until answered)
    var want = PERM.api && PERM.state !== "granted" && PERM.state !== "denied" && !PERM.events;
    if (want && !PERM.hint && signs[0]) {
      var b = PERM.hint = el("button", "bs-motion", signs[0].root.querySelector(".bs-stage"));
      b.type = "button";
      b.textContent = "Tap to tilt the sign with your phone";
      b.addEventListener("click", function (e) { e.stopPropagation(); askOrientation("hint"); });
    }
    if (PERM.hint) PERM.hint.hidden = !want;
    if (signs[0]) signs[0].root.classList.toggle("has-hint", !!(PERM.hint && want));
  }
  function debugPanel() {                                     // ?debug: on-screen log for testing on a real iPhone
    if (!DBG) return;
    var box = el("pre", "bs-debug", document.body);
    box.style.cssText = "position:fixed;left:6px;right:6px;bottom:6px;z-index:99;margin:0;padding:8px 10px;max-height:46vh;overflow:auto;" +
      "background:rgba(0,0,0,.82);color:#9f9;font:11px/1.35 ui-monospace,Menlo,monospace;white-space:pre-wrap;border-radius:8px;pointer-events:auto";
    window.addEventListener("error", function (e) { dbg("JS error: " + e.message + " @" + (e.filename || "").split("/").pop() + ":" + e.lineno); });
    window.addEventListener("unhandledrejection", function (e) { dbg("rejection: " + (e.reason && (e.reason.message || e.reason))); });
    var frames = 0, fps = 0, t0 = performance.now();
    (function count() { frames++; var n = performance.now(); if (n - t0 > 1000) { fps = frames; frames = 0; t0 = n; } requestAnimationFrame(count); })();
    setInterval(function () {
      var s0 = signs[0], L = PERM.last, f = function (v) { return v == null ? "-" : (+v).toFixed(1); };
      box.textContent = [
        "SIGN DEBUG  " + navigator.userAgent.replace(/^Mozilla\/5\.0 /, "").slice(0, 90),
        "secure: " + window.isSecureContext + "   hover:none: " + noHover + "   reduce-motion: " + mqReduce.matches,
        "DeviceOrientationEvent: " + !!window.DeviceOrientationEvent + "   requestPermission: " + PERM.api + "   permission: " + PERM.state,
        "orientation events: " + PERM.events + "   alpha/beta/gamma: " + (L ? f(L[0]) + " / " + f(L[1]) + " / " + f(L[2]) : "none yet"),
        "screen angle: " + ((screen.orientation && screen.orientation.angle) != null ? screen.orientation.angle : window.orientation) + "   viewport: " + innerWidth + "x" + innerHeight,
        "offset yaw/pitch: " + Y.off.toFixed(2) + " / " + Y.offX.toFixed(2) + "   sign ry/rx: " + (s0 ? s0.ry.toFixed(2) + " / " + s0.rx.toFixed(2) : "-"),
        "3D: three " + (T ? "loaded" : "not loaded") + ", font " + (FONT ? "ok" : "-") + ", WebGL " + (s0 && s0.gl ? "on" : "off (fallback text)") + "   fps: " + fps,
        "log:"
      ].concat(dbgLog.length ? dbgLog : ["(nothing yet - tap the page, then rotate the phone)"]).join(String.fromCharCode(10));
    }, 250);
    dbg("debug on");
  }
  window.BodegaSignDebug = { perm: PERM, offsets: Y };
  function bind() {
    var o = { passive: true };
    window.addEventListener("pointermove", function (e) {
      if (e.pointerType === "touch") return;
      var mx = typeof e.movementX === "number" ? e.movementX : (P.mouse ? e.clientX - P.x : 0);
      var my = typeof e.movementY === "number" ? e.movementY : (P.mouse ? e.clientY - P.y : 0);
      if (P.mouse && Math.abs(mx) < 200) nudge(mx * GAIN_PX);   // relative: the movement, not the position
      if (P.mouse && Math.abs(my) < 200) nudgeX(my * GAIN_PX);  // up / down tips it (one-point perspective)
      P.x = e.clientX; P.y = e.clientY; P.on = true; P.mouse = true;
    }, o);
    window.addEventListener("touchstart", function () { Y.lx = null; }, o);
    window.addEventListener("touchstart", onTouch, o);
    window.addEventListener("touchmove", onTouch, o);
    window.addEventListener("touchend", function (e) { if (!e.touches.length) P.on = false; }, o);
    window.addEventListener("touchcancel", function () { P.on = false; }, o);
    document.addEventListener("mouseout", function (e) { if (!e.relatedTarget) P.on = false; });
    window.addEventListener("blur", function () { P.on = false; });
    window.addEventListener("scroll", onScroll, o);
    window.addEventListener("resize", function () { signs.forEach(sizeGL); measure(); kick(); }, o);
    window.addEventListener("hashchange", function () { tiles.lastScan = -1e9; kick(); });
    window.addEventListener("load", function () { tiles.lastScan = -1e9; kick(); });
    if (window.MutationObserver) {                           // the menu re-renders: pick up new tiles right away
      new MutationObserver(function (muts) {
        for (var i = 0; i < muts.length; i++) {
          var a = muts[i].addedNodes;
          for (var j = 0; j < a.length; j++) {
            if (a[j].nodeType === 1 && !/^bs-/.test(a[j].className)) { tiles.lastScan = -1e9; kick(); return; }
          }
        }
      }).observe(document.body, { childList: true, subtree: true });
    }
    document.addEventListener("visibilitychange", function () { lastT = 0; start(); });
    if (window.DeviceOrientationEvent) {
      window.addEventListener("deviceorientation", onOrient, o);
      document.addEventListener("touchstart", onTapStart, o);
      document.addEventListener("touchend", onTapEnd, o);
      document.addEventListener("click", function () { askOrientation("click"); }, o);
    }
    if (mqReduce.addEventListener) mqReduce.addEventListener("change", reset);
  }

  function reset() {                                         // (re)start; also when the motion preference flips
    lastColor = -1e9;
    signs.forEach(function (s) { s.leds.forEach(function (l) { l.c = null; }); });
    measure();
    start();
  }

  function initAll() {
    var list = document.querySelectorAll(".bodega-sign");
    for (var i = 0; i < list.length; i++) init(list[i]);
    if (!signs.length) return;
    if (!document.querySelector(".sign-ambient")) hidden(el("div", "sign-ambient", document.body));
    document.body.classList.add("sign-lit");
    motionHint(); debugPanel();
    var g0 = signs[0].root.getAttribute("data-glow");
    setRoot("--sign-glow", g0 ? g0.trim() : rgb(PAL[0]));
    signs.forEach(function (s) { paint(s, performance.now() / 1000, mqReduce.matches); });
    if (window.IntersectionObserver && !tiles.io) {
      tiles.io = new IntersectionObserver(function (entries) {
        entries.forEach(function (en) {
          if (en.isIntersecting) { tiles.vis.add(en.target); tiles.dirty.add(en.target); } else tiles.vis.delete(en.target);
        });
        kick();
      }, { rootMargin: "120px 0px" });
      if (window.ResizeObserver) tiles.ro = new ResizeObserver(function (entries) {
        entries.forEach(function (en) { tiles.dirty.add(en.target); });
        kick();
      });
    }
    if (!initAll.bound) { initAll.bound = true; bind(); load3D(); }
    else if (T && FONT) signs.forEach(function (s) { try { setup3D(s); } catch (err) { fallback(); } });
    onScroll();
    measure();
    reset();
  }

  window.BodegaSign = { init: initAll };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", initAll);
  else initAll();
})();
