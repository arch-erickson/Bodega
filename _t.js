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
  var REST_Y = -18, REST_X = 9;           // resting angle (deg): yaw (+ faces right), pitch (+ faces down)
  var MAX_Y = 12, MAX_X = 8;              // extra tilt from pointer / device (deg)
  var COMPACT_ON = 64, COMPACT_OFF = 24;  // scroll hysteresis (px)
  var STEP = 3.6;                         // seconds per palette colour
  var COLOR_MS = 66;                      // colour updates ~15 fps
  var PAL = [[255, 46, 46], [255, 132, 0], [255, 206, 0], [28, 214, 92], [38, 136, 255], [236, 52, 196]];
  var LED = [[214, 58, 52], [226, 120, 18], [190, 146, 0], [34, 150, 84], [42, 112, 214], [196, 56, 160], [128, 128, 134]];
  var WORD_OFFSET = 2.5;                  // palette steps between words (never the same colour)

  /* letter construction, in em (cap height = .688em) */
  var DEPTH = .17;                        // extrusion ≈ 25% of the cap height
  var TRACK = .03, LINE = .84, FOV = 30;
  var WALL_Z = -.5;                       // the "wall" the glow / shadow lands on, behind the letters
  var MASK_R = 48, MASK_PAD = .95;        // glow mask: px per em, padding in em

  var mm = function (q) { return window.matchMedia ? window.matchMedia(q) : { matches: false }; };
  var mqReduce = { matches: false };
  var noHover = mm("(hover: none)").matches;
  var root = document.documentElement;
  var signs = [], raf = 0, lastT = 0, lastColor = -1e9;
  var P = { x: 0, y: 0, on: false, mouse: false };
  var O = { init: false, dx: 0, dy: 0, t: -1e9, bg: 0, bb: 0 };   // device orientation
  var rootVals = {};
  var light = { x: -1, y: -1 };
  var tiles = { seen: new WeakSet(), vis: new Set(), dirty: new Set(), io: null, ro: null, lastScan: -1e9, pass: 0 };
  var tileList = [], tileRects = [];
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
      var x = still ? i * 3 : t / STEP + i * WORD_OFFSET;    // still: red / green
      var col = s.cols[i] || (s.cols[i] = { c1: [0, 0, 0], c2: [0, 0, 0] });
      palAt(x, col.c1); palAt(x + .8, col.c2);
      setVar(s.words[i], "--c1", rgb(col.c1));               // fallback letters follow the cycle too
    }
    for (var j = 0; j < s.leds.length; j++) {
      var l = s.leds[j], c = still ? LED[6] : LED[Math.floor(t / l.dur + l.ph) % LED.length];
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
      rx: REST_X, ry: REST_Y, near: 0, inten: .5, compact: false };
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
    if (window.ResizeObserver) new ResizeObserver(function () { sizeGL(s); measure(); if (mqReduce.matches) draw(s); }).observe(s.stage);
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
    ctx.shadowColor = "#f00"; ctx.shadowBlur = R * .6; ctx.fill(path);
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
      camera: new T.PerspectiveCamera(FOV, 2, .1, 60), tilt: new T.Group(), wall: new T.Group(), rootG: new T.Group() };
    g.rootG.add(g.wall, g.tilt);
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
      g.tilt.remove(w.grp); g.wall.remove(w.wall);
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
        uniforms: { uMap: { value: mask.tex }, uC1: uC1, uC2: uC2, uGlow: uGlow, uShadow: { value: .2 }, uOff: { value: new T.Vector2(0, .17 / mask.h) } } });
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
      wall.scale.setScalar(1.22);
      g.tilt.add(grp); g.wall.add(wall);
      g.words.push({ grp: grp, wall: wall, cx: cx, cy: cy, width: ws.width, mFace: mFace, mBloom: mBloom, uC1: uC1.value, uC2: uC2.value, uGlow: uGlow,
        geos: [body, rim, face, plane], mats: [mFace, mWall, mBloom], mask: mask });
    });
    g.lines = 0;
  }

  /* place the words: one line, or stacked when the CSS says --bs-lines: 2 */
  function layout(s, lines) {
    var g = s.gl, cap = FONT.capHeight / FONT.unitsPerEm, n = g.words.length;
    var space = (glyphOf(" ") ? glyphOf(" ").a / FONT.unitsPerEm : .33) + TRACK;
    var stacked = lines > 1 && n > 1, i, w, total = 0, maxW = 0;
    for (i = 0; i < n; i++) { total += g.words[i].width + (i ? space : 0); maxW = Math.max(maxW, g.words[i].width); }
    var blockH = stacked ? (n - 1) * LINE + cap : cap, x = -total / 2;
    for (i = 0; i < n; i++) {
      w = g.words[i];
      var px = stacked ? -w.width / 2 : x, py = stacked ? blockH / 2 - cap - i * LINE : -cap / 2;
      w.grp.position.set(px, py, DEPTH / 2);                 // tilt pivot runs through the middle of the solid
      w.wx = px + w.cx; w.wy = py + w.cy;
      x += w.width + space;
    }
    g.lines = lines;
    g.blockW = stacked ? maxW : total;
  }

  /* canvas follows the stage; its centre sits on the centre of the h1 so the view is head-on */
  function sizeGL(s) {
    var g = s.gl;
    if (!g) return;
    var W = s.stage.offsetWidth, SH = s.stage.offsetHeight;
    if (!W || !SH) return;
    var fs = parseFloat(getComputedStyle(s.name).fontSize) || 48;
    var lines = parseInt(getComputedStyle(s.root).getPropertyValue("--bs-lines"), 10) || 1;
    var yc = s.name.offsetTop + s.name.offsetHeight / 2;
    var half = Math.ceil(Math.max(yc, SH - yc) + fs * .7);
    var dpr = Math.min(window.devicePixelRatio || 1, 2);
    var key = [W, half, yc, fs, lines, dpr].join("|");
    if (key === g.key) return;
    g.key = key;
    g.canvas.style.width = W + "px";
    g.canvas.style.height = half * 2 + "px";
    g.canvas.style.top = (yc - half) + "px";
    g.renderer.setPixelRatio(dpr);
    g.renderer.setSize(W, half * 2, false);
    g.camera.aspect = W / (half * 2);
    g.camera.position.z = (half * 2 / fs) / (2 * Math.tan(FOV * DEG / 2));   // 1 world unit = 1em on screen
    g.camera.updateProjectionMatrix();
    if (lines !== g.lines) layout(s, lines);
    g.rootG.scale.setScalar(Math.min(1, (W - 28) / (g.blockW * fs)));       // never wider than the page
    g.dirty = true;
  }

  function draw(s) {
    var g = s.gl;
    if (!g) return;
    var yaw = s.ry * DEG, pitch = s.rx * DEG, glow = .34 + .14 * s.near;
    g.tilt.rotation.set(pitch, yaw, 0);
    var sx = -Math.sin(yaw) * .32, sy = Math.sin(pitch) * .32 - .03;       // glow / shadow slide with the tilt
    for (var i = 0; i < g.words.length; i++) {
      var w = g.words[i], c = s.cols[i];
      if (c) {
        w.uC1.set(c.c1[0] / 255, c.c1[1] / 255, c.c1[2] / 255);
        w.uC2.set(c.c2[0] / 255, c.c2[1] / 255, c.c2[2] / 255);
      }
      w.uGlow.value = glow;
      w.mBloom.uniforms.uGlow.value = .3 + .15 * s.near;
      w.mFace.uniforms.uSheen.value = .5 - s.ry / 30;
      w.wall.position.set(w.wx + sx, w.wy + sy, WALL_Z);
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
    signs.forEach(function (s) {
      var c = s.compact ? y > COMPACT_OFF : y > COMPACT_ON;
      if (c !== s.compact) { s.compact = c; s.root.classList.toggle("is-compact", c); changed = true; }
    });
    if (changed && mqReduce.matches) requestAnimationFrame(measure);
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
       .bs-lit   colour cast masked by the image's own alpha (soft-light), brightest on the side facing the sign
       .bs-rim   thin highlight on the facing edge (image mask minus the same mask nudged away from the light)
       .bs-cast  soft tinted shadow on the tile floor, on the side away from the light
     Strength (--lit) falls off with the tile's distance from the sign (inverse-square-ish). */
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
    img._lit = { lit: lit, rim: rim, cast: cast, box: null };
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
      for (var j = 0; j < 2; j++) {
        var e = j ? o.rim : o.lit;
        e.style.left = b.l + "px"; e.style.top = b.t + "px"; e.style.width = b.w + "px"; e.style.height = b.h + "px";
        e.style.zIndex = b.z === "auto" ? "" : b.z;
        e.style.setProperty("--mpx", b.px); e.style.setProperty("--mpy", b.py); e.style.setProperty("--ms", b.fit);
      }
      o.cast.style.left = (b.l + b.w * .06) + "px"; o.cast.style.width = (b.w * .88) + "px";
      o.cast.style.top = (b.t + b.h * .8) + "px"; o.cast.style.height = Math.max(14, b.h * .3) + "px";
    }
  }
  /* reads (rects + dirty boxes), then writes (per-tile vars). lx/ly: light in viewport px; follow: pointer highlight on */
  function lightTiles(now, lx, ly, follow) {
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
    var scx = sr.left + sr.width / 2, sx = scx + (lx - scx) * .35, sy = sr.bottom - 10;
    for (i = 0; i < n; i++) {
      tl = tileList[i];
      var r = tileRects[i], dx = sx - (r.left + r.width / 2), dy = sy - (r.top + r.height / 2);
      var d = Math.sqrt(dx * dx + dy * dy) || 1, ux = dx / d, uy = dy / d;
      var lit = clamp(1.25 / (1 + (d / 340) * (d / 340)), .05, 1);
      setVar(tl, "--lit", lit.toFixed(2));
      setVar(tl, "--ox", Math.round(50 + ux * 60) + "%");
      setVar(tl, "--oy", Math.round(50 + uy * 60) + "%");
      setVar(tl, "--rx", (-ux * 2.6).toFixed(1) + "px");
      setVar(tl, "--ry", (-uy * 2.6).toFixed(1) + "px");
      setVar(tl, "--cx", Math.round(-ux * 12) + "px");
      if (follow) {
        setVar(tl, "--lx", (Math.round(lx) - Math.round(r.left)) + "px");
        setVar(tl, "--ly", (Math.round(ly) - Math.round(r.top)) + "px");
      }
    }
  }
  function staticPass() {                                    // reduced motion: same light, no pointer tracking
    tiles.pass = 0;
    if (!signs.length || !mqReduce.matches) return;
    var r = signs[0].root.getBoundingClientRect();
    lightTiles(performance.now(), r.left + r.width / 2, r.bottom, false);
  }
  function kick() {                                          // something about the tiles changed
    if (mqReduce.matches) { if (!tiles.pass) tiles.pass = requestAnimationFrame(staticPass); }
    else start();
  }

  /* ---------- the one rAF loop (stops when the tab is hidden or motion is reduced) ---------- */
  function tick(now) {
    raf = 0;
    if (mqReduce.matches || !signs.length) return;
    var dt = Math.min(.05, lastT ? (now - lastT) / 1000 : .016);
    lastT = now;
    var kT = 1 - Math.exp(-dt * 6), kN = 1 - Math.exp(-dt * 5);
    var vw = window.innerWidth, vh = window.innerHeight, t = now / 1000;
    var useOri = !P.on && now - O.t < 1500;
    var primary = signs[0], pcx = 0, pcy = 0;

    /* reads */
    var signH = primary.root.getBoundingClientRect().height;
    var colorTick = now - lastColor >= COLOR_MS;
    if (colorTick) lastColor = now;

    for (var idx = 0; idx < signs.length; idx++) {
      var s = signs[idx], r = s.name.getBoundingClientRect();
      var cx = r.left + r.width / 2, cy = r.top + r.height / 2;
      var ty = REST_Y, tx = REST_X, near = 0;
      if (P.on) {
        var dx = clamp((P.x - cx) / (vw / 2), -1, 1);
        var dy = clamp((P.y - cy) / Math.max(120, P.y > cy ? vh - cy : cy), -1, 1);
        ty = dx * MAX_Y + REST_Y * (1 - Math.abs(dx));       // faces the pointer; rest angle fades out toward the edges
        tx = dy * MAX_X + REST_X * (1 - Math.abs(dy));
        var ex = Math.max(r.left - P.x, 0, P.x - r.right), ey = Math.max(r.top - P.y, 0, P.y - r.bottom);
        near = clamp(1 - Math.sqrt(ex * ex + ey * ey) / 260, 0, 1);
      } else if (useOri) {
        ty = REST_Y * .5 + O.dx * MAX_Y; tx = REST_X + O.dy * MAX_X;
      } else if (noHover || !P.mouse) {                      // idle sway
        ty = REST_Y + Math.sin(t * .5 + idx) * 4;
        tx = REST_X + Math.sin(t * .33 + idx) * 2;
      }
      var prx = s.rx, pry = s.ry, pn = s.near;
      s.rx += (tx - s.rx) * kT; s.ry += (ty - s.ry) * kT;
      s.near += (near - s.near) * kN;
      s.inten = .45 + .55 * s.near;
      var moved = Math.abs(s.rx - prx) + Math.abs(s.ry - pry) > .002 || Math.abs(s.near - pn) > .002;

      if (colorTick) {
        var c = paint(s, t, false);
        if (idx === 0 && c) setRoot("--sign-glow", rgb(c));
      }
      if (s.gl && (moved || colorTick || s.gl.dirty)) draw(s);   // render only when something changed
      if (idx === 0) { pcx = cx; pcy = cy; }
    }

    /* light position: pointer, device tilt, else sign centre */
    var lx = pcx, ly = pcy;
    if (P.on) { lx = P.x; ly = P.y; }
    else if (useOri) { lx = pcx + (primary.ry - REST_Y * .5) / MAX_Y * vw * .45; ly = pcy + vh * .35 + (primary.rx - REST_X) / MAX_X * vh * .3; }
    if (light.x < 0) { light.x = lx; light.y = ly; }
    light.x += (lx - light.x) * kT; light.y += (ly - light.y) * kT;
    var LX = Math.round(light.x), LY = Math.round(light.y);
    setRoot("--sign-h", Math.round(signH) + "px");
    setRoot("--sign-intensity", primary.inten.toFixed(2));
    setRoot("--light-x", LX + "px");
    setRoot("--light-y", LY + "px");
    lightTiles(now, light.x, light.y, true);
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
    window.addEventListener("resize", function () { signs.forEach(sizeGL); measure(); if (mqReduce.matches) signs.forEach(draw); kick(); }, o);
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
      document.addEventListener("touchend", askOrientation, o);
      document.addEventListener("click", askOrientation, o);
    }
    if (mqReduce.addEventListener) mqReduce.addEventListener("change", reset);
  }

  function reset() {                                         // static state for reduced motion
    if (!mqReduce.matches) { start(); return; }
    signs.forEach(function (s, idx) {
      s.rx = REST_X; s.ry = REST_Y; s.near = 0;
      var c = paint(s, 0, true);
      if (idx === 0 && c) setRoot("--sign-glow", rgb(c));
      draw(s);
    });
    setRoot("--sign-intensity", ".5");
    var r = signs[0].name.getBoundingClientRect();
    setRoot("--light-x", Math.round(r.left + r.width / 2) + "px");
    setRoot("--light-y", Math.round(r.top + r.height / 2) + "px");
    tiles.vis.forEach(function (tl) { tl.style.removeProperty("--lx"); tl.style.removeProperty("--ly"); tl["_--lx"] = tl["_--ly"] = null; });
    measure();
    kick();
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
