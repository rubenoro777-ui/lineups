
/*ALG-START*/
// Pure lineup algorithms: no DOM, no app state. Shared by the page and its tests.
const ALG = (function () {
  const FIELD = ["P", "C", "1B", "2B", "3B", "SS", "LF", "LC", "RC", "RF"];
  const isField = p => FIELD.indexOf(p) >= 0;
  const OPEN = { RC: 0, LC: 1, RF: 2, LF: 3, "2B": 5, "1B": 6, "3B": 6, SS: 7, C: 8, P: 9 };

  // Min-cost assignment for a square cost matrix; returns row -> column.
  function hungarian(cost) {
    const n = cost.length, INF = 1e15;
    const u = new Array(n + 1).fill(0), v = new Array(n + 1).fill(0), p = new Array(n + 1).fill(0), way = new Array(n + 1).fill(0);
    for (let i = 1; i <= n; i++) {
      p[0] = i; let j0 = 0;
      const minv = new Array(n + 1).fill(INF), used = new Array(n + 1).fill(false);
      do {
        used[j0] = true; const i0 = p[j0]; let delta = INF, j1 = 0;
        for (let j = 1; j <= n; j++) {
          if (used[j]) continue;
          const cur = cost[i0 - 1][j - 1] - u[i0] - v[j];
          if (cur < minv[j]) { minv[j] = cur; way[j] = j0; }
          if (minv[j] < delta) { delta = minv[j]; j1 = j; }
        }
        for (let j = 0; j <= n; j++) { if (used[j]) { u[p[j]] += delta; v[j] -= delta; } else minv[j] -= delta; }
        j0 = j1;
      } while (p[j0] !== 0);
      do { const j1 = way[j0]; p[j0] = p[j1]; j0 = j1; } while (j0);
    }
    const ans = new Array(n).fill(-1);
    for (let j = 1; j <= n; j++) if (p[j]) ans[p[j] - 1] = j - 1;
    return ans;
  }

  // Keep men in their order and women in theirs; pull a woman up only when needed so no run of men passes `max`.
  // With `wrap`, the run from the bottom of the order back to the top counts too.
  function spaceOrder(items, isMan, max, wrap) {
    const men = items.filter(isMan), wom = items.filter(x => !isMan(x));
    if (!men.length || !wom.length) return items.slice();
    const at = new Map(items.map((x, i) => [x, i]));
    const feas = (Ml, Wl, r, lead, L) => {
      if (r > max) return false;
      if (!wrap) return Ml <= (max - r) + Wl * max;
      if (lead) return Wl >= 1 && Ml <= Wl * max - r;
      return Ml <= (max - r) + Wl * max - L;
    };
    const res = []; let mi = 0, wi = 0, r = 0, lead = true, L = 0;
    while (mi < men.length || wi < wom.length) {
      const m = men[mi], w = wom[wi];
      const Ml = men.length - mi, Wl = wom.length - wi;
      const canM = m !== undefined && feas(Ml - 1, Wl, r + 1, lead, L);
      const canW = w !== undefined && feas(Ml, Wl - 1, 0, false, lead ? r : L);
      const preferW = w !== undefined && (m === undefined || at.get(w) < at.get(m));
      let takeW = preferW ? (canW || !canM) : (!canM && canW);
      if (m === undefined) takeW = true;
      if (w === undefined) takeW = false;
      if (takeW) { if (lead) { L = r; lead = false; } res.push(w); wi++; r = 0; }
      else { res.push(m); mi++; r++; }
    }
    return res;
  }

  // Runs of men longer than `max`; each run is a list of order indexes.
  function spacingRuns(isManArr, max, wrap) {
    const n = isManArr.length;
    if (!n || isManArr.every(Boolean) || !isManArr.some(Boolean)) return [];
    const start = wrap ? (isManArr.indexOf(false) + 1) % n : 0;
    const runs = []; let run = [];
    for (let c = 0; c < n; c++) {
      const i = (start + c) % n;
      if (isManArr[i]) run.push(i); else { if (run.length > max) runs.push(run); run = []; }
    }
    if (run.length > max) runs.push(run);
    return runs;
  }

  // What each player has done in earlier games, newest weighted most (each older game counts 0.8x).
  // games: [{id, date, order:[{p, pos[]}]}]. Only games dated before `before` count.
  function learn(games, before, excludeId) {
    const list = games.filter(g => g.id !== excludeId && g.date && (!before || g.date < before)).sort((a, b) => b.date.localeCompare(a.date));
    const H = {};
    list.forEach((g, k) => {
      const w = Math.pow(0.8, k), n = g.order.length;
      g.order.forEach((e, idx) => {
        const h = H[e.p] || (H[e.p] = { pos: {}, raw: {}, tot: 0, sit: 0, spot: 0, spotW: 0, games: 0 });
        h.games++; h.spot += w * (n > 1 ? idx / (n - 1) : 0.5); h.spotW += w;
        e.pos.forEach(p => { if (isField(p)) { h.pos[p] = (h.pos[p] || 0) + w; h.raw[p] = (h.raw[p] || 0) + 1; h.tot += w; } else if (p === "EH") h.sit += w; });
      });
    });
    Object.keys(H).forEach(id => {
      const h = H[id]; h.share = {};
      Object.keys(h.pos).forEach(q => { h.share[q] = h.pos[q] / h.tot; });
      h.conf = Math.min(1, h.tot / 10);
      h.sitPct = h.sit + h.tot ? h.sit / (h.sit + h.tot) : 0;
      h.avgSpot = h.spotW ? h.spot / h.spotW : 0.5;
    });
    return { games: list.length, last: list.length ? list[0].date : "", H: H };
  }

  // Cost of putting player x at position q in inning i (lower is better).
  // Roster order first, then experience (wins contested listed spots), then where they've played before.
  function posCost(x, q, i, o) {
    if (x.dnp.indexOf(q) >= 0) return 1e6;
    const r = x.positions.indexOf(q);
    let c = !x.positions.length ? 4 : r === 0 ? 0 : r > 0 ? 1.5 + r : 8;
    if (r >= 0) c -= 0.6 * x.exp;
    if (q === "P" || q === "SS" || q === "C") c -= 0.3 * x.exp;
    if (x.hist && o.histW) c -= o.histW * x.hist.conf * (x.hist.share[q] || 0);
    if (i > 0 && x.pos[i - 1] === q) c -= 2.5;
    return c;
  }

  // Rebuild innings `from`..n-1 in place. rows: {pos[], sex, inj, maxInn, exp, positions[], dnp[], idx}.
  // Innings before `from` stay as they are; "OUT" (left the game) is never touched.
  function planDefense(rows, o) {
    const n = o.n, menMax = Math.max(0, 10 - o.minW);
    rows.forEach(x => { for (let i = o.from; i < n; i++) if (x.pos[i] !== "OUT") x.pos[i] = ""; });
    for (let i = o.from; i < n; i++) {
      const R = n - i;
      const fielded = x => { let c = 0; for (let k = 0; k < i; k++) if (isField(x.pos[k])) c++; return c; };
      const sat = x => { let c = 0; for (let k = 0; k < i; k++) if (x.pos[k] === "EH") c++; return c; };
      const present = rows.filter(x => x.pos[i] !== "OUT");
      const E = present.filter(x => x.inj !== "batonly" && !(x.inj === "limited" && fielded(x) >= x.maxInn));
      present.forEach(x => { if (E.indexOf(x) < 0) x.pos[i] = "EH"; });
      const W = E.filter(x => x.sex === "F"), M = E.filter(x => x.sex !== "F");
      const f = Math.min(10, W.length + Math.min(M.length, menMax));
      const s = E.length - f;
      const reqW = Math.min(o.minW, W.length);
      // `lo` bench seats are men-only so no more than menMax men field; the other s - lo seats
      // never exceed the women who can sit, so reqW women always field.
      const lo = Math.max(0, M.length - menMax, s - (W.length - reqW));
      // Cost of sitting this inning: fairness first (each earlier sit costs 10, a sit past the
      // bench max costs 1000), then position fit decides between equally fair choices.
      const benchCost = x => {
        const prev = i > 0 && x.pos[i - 1] === "EH";
        if (x.inj === "limited") {
          const need = R - (x.maxInn - fielded(x));
          if (need >= R) return -1e4;
          if (need > 0) return -(30 * need / R) + (prev ? 20 : 0);
        }
        const ss = sat(x);
        let c = (ss >= o.maxSits ? 1000 : 0) + (prev ? 4 : 0);
        c += o.strategy === "experience" ? x.exp * 10 + ss * 2 : ss * 10 + x.exp * 0.5;
        // Season balance: whoever sat more in earlier games is a little less likely to sit now.
        if (o.strategy !== "experience" && x.hist && o.histW) c += 14 * x.hist.sitPct * x.hist.conf;
        return c - x.idx * 0.01;
      };
      const BIG = 1e7;
      const cost = E.map(x => FIELD.map(q => posCost(x, q, i, o)).concat(Array.from({ length: s }, (_, b) => (b < lo && x.sex === "F") ? BIG : benchCost(x))));
      for (let d = f; d < 10; d++) cost.push(FIELD.map(q => OPEN[q] * 3).concat(Array(s).fill(BIG)));
      const asg = hungarian(cost);
      E.forEach((x, r) => { x.pos[i] = asg[r] < 10 ? FIELD[asg[r]] : "EH"; });
    }
  }

  return { FIELD, hungarian, spaceOrder, spacingRuns, planDefense, learn };
})();
/*ALG-END*/

(function () {
  "use strict";

  /* ---------- Constants ---------- */
  const FIELD = ALG.FIELD;
  const VALID = new Set(FIELD.concat(["EH", "OUT", ""]));
  const POSNAME = { P: "pitcher", C: "catcher", "1B": "first base", "2B": "second base", "3B": "third base", SS: "shortstop", LF: "left field", LC: "left center", RC: "right center", RF: "right field", EH: "bench, still bats", OUT: "left the game" };
  const FITNAME = { primary: "Primary", alt: "Alt", unlisted: "Unlisted", bench: "Bench", dnp: "Do not play", out: "Out", blank: "Not set" };
  // Top-center of each fielder's name pin on the 360-wide field drawing (also used for the PDF diamonds).
  const SPOT = { P: [180, 220], C: [180, 286], "1B": [292, 168], "2B": [234, 124], SS: [126, 124], "3B": [68, 168], LF: [62, 92], LC: [128, 50], RC: [232, 50], RF: [298, 92] };
  const DEFAULTS = { teamName: "Arroz con Coronas", innings: 6, maxMenInRow: 3, wrapOrder: true, minWomenOnField: 3, maxSits: 2, sitStrategy: "even", histWeight: 2, seasonStart: "" };
  const HIST_W = [0, 2, 4, 6];
  const HIST_LABEL = ["Off", "Light", "Normal", "Strong"];
  const LS_KEY = "acc-lineups-local-v1";
  const PREF_KEY = "acc-lineups-prefs-v1";
  const JSPDF_URL = "https://cdnjs.cloudflare.com/ajax/libs/jspdf/2.5.1/jspdf.umd.min.js";
  const PLATE = '<svg class="plate" width="22" height="22" viewBox="0 0 24 24" aria-hidden="true"><path d="M4 3h16v9.5L12 21 4 12.5z"/></svg>';
  const PLATE_BIG = '<svg class="plate" width="40" height="40" viewBox="0 0 24 24" aria-hidden="true"><path d="M4 3h16v9.5L12 21 4 12.5z"/></svg>';

  /* ---------- State ---------- */
  const S = {
    mode: "connecting", players: new Map(), games: new Map(), settings: Object.assign({}, DEFAULTS),
    got: { players: false, games: false, settings: false }, confirmed: new Set(),
    slow: false, liveErr: false, canWrite: false, writeKnown: true, rev: -1,
    pending: new Set(), deleted: new Set(), lastSaved: 0, saveErr: false,
    dragging: false, needRender: false, pointerDown: false, focusId: null, suppressClick: false,
    ui: { newOpen: false, ng: null, pick: null, inn: 0, confirm: null, copyText: null, copyFocus: false, pdfUrl: null, sort: "name", since: "",
      np: { name: "", sex: "", pos: "" }, qa: null, openPl: null, rb: null, pd: null }
  };
  const U = { gid: null, stack: [] };
  let prefs = { auto: false };
  try { const p = JSON.parse(localStorage.getItem(PREF_KEY) || "null"); if (p && typeof p === "object") prefs = Object.assign(prefs, p); } catch (e) { /* storage blocked: defaults */ }
  function savePrefs() { try { localStorage.setItem(PREF_KEY, JSON.stringify(prefs)); } catch (e) { /* storage blocked */ } }

  /* ---------- Helpers ---------- */
  const esc = s => String(s == null ? "" : s).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  const clone = o => JSON.parse(JSON.stringify(o));
  const range = n => Array.from({ length: n }, (_, i) => i);
  const rid = n => Math.random().toString(36).slice(2, 2 + n);
  const sleep = ms => new Promise(r => setTimeout(r, ms));
  const isDate = s => typeof s === "string" && /^\d{4}-\d{2}-\d{2}$/.test(s);
  const isField = p => FIELD.indexOf(p) >= 0;
  const plural = (n, one, many) => (n === 1 ? one : many);
  function clampInt(v, lo, hi, def) { const n = parseInt(v, 10); return Number.isFinite(n) ? Math.min(hi, Math.max(lo, n)) : def; }
  function fit(arr, n) { const out = []; for (let i = 0; i < n; i++) { const v = String(arr && arr[i] != null ? arr[i] : ""); out.push(VALID.has(v) ? v : ""); } return out; }
  function listText(a) { return a.length <= 2 ? a.join(" and ") : a.slice(0, -1).join(", ") + " and " + a[a.length - 1]; }
  function opts(lo, hi, cur, blankLabel) { let h = blankLabel != null ? `<option value=""${!cur ? " selected" : ""}>${blankLabel}</option>` : ""; for (let k = lo; k <= hi; k++) h += `<option value="${k}"${k === cur ? " selected" : ""}>${k}</option>`; return h; }
  function posOpts(cur, blankLabel) { return `<option value="">${blankLabel}</option>` + FIELD.map(p => `<option value="${p}"${p === cur ? " selected" : ""}>${p}</option>`).join(""); }

  function parseD(s) { if (!isDate(s)) return null; const p = s.split("-").map(Number); return new Date(p[0], p[1] - 1, p[2]); }
  function isoD(d) { return d.getFullYear() + "-" + String(d.getMonth() + 1).padStart(2, "0") + "-" + String(d.getDate()).padStart(2, "0"); }
  function todayIso() { return isoD(new Date()); }
  function fmtLong(s) { const d = parseD(s); return d ? d.toLocaleDateString("en-US", { weekday: "short", month: "short", day: "numeric", year: "numeric" }) : "Date not set"; }
  function stubParts(s) { const d = parseD(s); if (!d) return { dow: "TBD", day: "?", mon: "" }; return { dow: d.toLocaleDateString("en-US", { weekday: "short" }).toUpperCase(), day: String(d.getDate()), mon: d.toLocaleDateString("en-US", { month: "short" }) + " " + String(d.getFullYear()).slice(2) }; }
  function defaultNextDate(last) {
    const t = new Date(); t.setHours(0, 0, 0, 0);
    const d = last ? parseD(last.date) : null;
    if (!d) return isoD(t);
    const n = new Date(d); n.setDate(n.getDate() + 7);
    if (n >= t) return isoD(n);
    const x = new Date(t); while (x.getDay() !== d.getDay()) x.setDate(x.getDate() + 1);
    return isoD(x);
  }

  function splitName(name) {
    const s = String(name || "").trim(); const i = s.indexOf(",");
    if (i >= 0) return { first: s.slice(i + 1).trim(), last: s.slice(0, i).trim() };
    const parts = s.split(/\s+/); return { first: parts[0] || "", last: parts.slice(1).join(" ") };
  }
  function fullName(pl) { if (!pl) return "Removed player"; const n = splitName(pl.name); return [n.first, n.last].filter(Boolean).join(" ") || "Unnamed"; }
  const byFull = (a, b) => fullName(a).localeCompare(fullName(b));
  function sexKey(pid) { const p = S.players.get(pid); return p ? p.sex : "U"; }
  function sexLabel(k) { return k === "F" ? "Female" : k === "M" ? "Male" : "Not set"; }
  function nameMap(g) {
    const firsts = {};
    const info = g.order.map(e => {
      const pl = S.players.get(e.p); const nm = pl ? splitName(pl.name) : { first: "Removed", last: "" };
      const f = nm.first || (pl && pl.name) || "Unnamed"; const k = f.toLowerCase();
      (firsts[k] = firsts[k] || []).push(e.p); return { p: e.p, f: f, last: nm.last };
    });
    const m = new Map();
    info.forEach(x => m.set(x.p, firsts[x.f.toLowerCase()].length > 1 && x.last ? x.f + " " + x.last[0] + "." : x.f));
    return m;
  }
  function slug(s) { return String(s).toLowerCase().normalize("NFKD").replace(/\p{M}/gu, "").replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "").slice(0, 40); }
  function teamName() { return (S.settings.teamName || "").trim() || DEFAULTS.teamName; }
  function fitOf(pl, p) {
    if (p === "EH") return "bench";
    if (p === "OUT") return "out";
    if (!p) return "blank";
    if (!pl) return "alt";
    if (pl.dnp.indexOf(p) >= 0) return "dnp";
    const r = pl.positions.indexOf(p);
    if (r === 0) return "primary";
    if (r > 0 || !pl.positions.length) return "alt";
    return "unlisted";
  }
  function injTag(pl) { if (!pl) return ""; if (pl.injury === "batonly") return "Bat only"; if (pl.injury === "limited") return "Lim " + pl.maxInnings; return ""; }
  function miniPos(pl) {
    if (!pl) return "";
    const a = pl.positions.map((p, k) => `<span class="${k === 0 ? "p1" : ""}">${p}</span>`).join("");
    const b = pl.dnp.length ? `<span class="no">✕ ${pl.dnp.join(" ")}</span>` : "";
    return a || b ? `<span class="mini">${a}${b}</span>` : "";
  }

  /* ---------- Normalizing untrusted stored data ---------- */
  function posList(arr) { const out = []; (Array.isArray(arr) ? arr : []).forEach(p => { if (isField(p) && out.indexOf(p) < 0) out.push(p); }); return out.slice(0, 10); }
  function normPlayer(id, d) {
    d = d || {};
    const positions = posList(d.positions);
    const dnp = posList(d.dnp).filter(p => positions.indexOf(p) < 0);
    return {
      id: id, name: typeof d.name === "string" ? d.name.slice(0, 80) : "",
      sex: d.sex === "F" ? "F" : d.sex === "M" ? "M" : "U",
      active: d.active !== false, available: d.available === true,
      bat: clampInt(d.bat, 0, 99, 0), batExp: clampInt(d.batExp, 0, 5, 0), fieldExp: clampInt(d.fieldExp, 0, 5, 0),
      positions: positions, dnp: dnp,
      injury: d.injury === "limited" || d.injury === "batonly" ? d.injury : "healthy",
      maxInnings: clampInt(d.maxInnings, 1, 12, 3)
    };
  }
  function normGame(id, d) {
    d = d || {}; const n = clampInt(d.innings, 3, 12, 6); const seen = new Set();
    const order = (Array.isArray(d.order) ? d.order : [])
      .filter(e => e && typeof e.p === "string" && e.p && !seen.has(e.p) && seen.add(e.p))
      .map(e => ({ p: e.p, pos: fit(e.pos, n) }));
    return { id: id, date: isDate(d.date) ? d.date : "", opponent: typeof d.opponent === "string" ? d.opponent.slice(0, 80) : "", innings: n, order: order, createdAt: typeof d.createdAt === "string" ? d.createdAt : "" };
  }
  function normSettings(d) {
    d = d || {};
    return {
      teamName: typeof d.teamName === "string" ? d.teamName.slice(0, 60) : DEFAULTS.teamName,
      innings: clampInt(d.innings, 3, 12, DEFAULTS.innings), maxMenInRow: clampInt(d.maxMenInRow, 1, 12, DEFAULTS.maxMenInRow),
      wrapOrder: d.wrapOrder !== false, minWomenOnField: clampInt(d.minWomenOnField, 0, 10, DEFAULTS.minWomenOnField),
      maxSits: clampInt(d.maxSits, 0, 12, DEFAULTS.maxSits), sitStrategy: d.sitStrategy === "experience" ? "experience" : "even",
      histWeight: clampInt(d.histWeight, 0, 3, DEFAULTS.histWeight),
      seasonStart: isDate(d.seasonStart) ? d.seasonStart : ""
    };
  }

  /* ---------- Storage: the team's data API. Anyone can read; writes need the captain key. ---------- */
  const API = (typeof window.LINEUPS_API === "string" && /^https:\/\/script\.google\.com\/|^http:\/\/localhost:/.test(window.LINEUPS_API)) ? window.LINEUPS_API : "";
  const KEY_LS = "acc-lineups-captain-key";
  const CACHE_LS = "acc-lineups-cache-v1";
  let captainKey = "";
  try { captainKey = localStorage.getItem(KEY_LS) || ""; } catch (e) { /* storage blocked */ }
  if (!/^[A-Za-z0-9]{20,100}$/.test(captainKey)) captainKey = "";

  // A captain link looks like https://site/#key=... . Opening it once unlocks this device; the key then leaves the address bar.
  function takeKey() {
    const m = /^#key=([A-Za-z0-9]{20,100})$/.exec(location.hash || "");
    if (!m) return false;
    captainKey = m[1];
    try { localStorage.setItem(KEY_LS, captainKey); } catch (e) { /* storage blocked: works until the tab closes */ }
    try { history.replaceState(null, "", location.pathname + location.search); } catch (e) { location.hash = ""; }
    return true;
  }
  function forgetKey() { captainKey = ""; try { localStorage.removeItem(KEY_LS); } catch (e) { /* storage blocked */ } }

  async function apiGet(q) {
    let j = null;
    try { const r = await fetch(API + q, { redirect: "follow", cache: "no-store" }); if (r.ok) j = await r.json(); } catch (e) { j = null; }
    if (!j || !j.ok) throw { code: "unavailable" };
    return j;
  }
  async function apiPost(body) {
    let j = null;
    try {
      // text/plain keeps this a "simple" cross-site request, which Apps Script can answer.
      const r = await fetch(API, { method: "POST", redirect: "follow", headers: { "Content-Type": "text/plain;charset=utf-8" }, body: JSON.stringify(body) });
      if (r.ok) j = await r.json();
    } catch (e) { j = null; }
    if (!j) throw { code: "unavailable" };
    if (!j.ok) {
      const e = j.error;
      throw { code: e === "forbidden" ? "not_granted" : e === "rate_limited" ? "resource_exhausted" : e === "too_large" ? "quota_exceeded" : e === "unavailable" ? "unavailable" : "bad_request" };
    }
    return j;
  }
  function noteRev(j) { if (j.rev === S.rev + 1) S.rev = j.rev; }
  const store = {
    async set(path, data) { const p = path.split("/"); noteRev(await apiPost({ a: "save", key: captainKey, kind: p[0], id: p[1], data: data })); },
    async del(path) { const p = path.split("/"); noteRev(await apiPost({ a: "delete", key: captainKey, kind: p[0], id: p[1] })); }
  };

  const toDocs = o => Object.keys(o || {}).map(id => ({ id: id, data: o[id] }));
  function applyState(j) {
    applyCol("players", toDocs(j.players)); applyCol("games", toDocs(j.games));
    if (!S.pending.has("team/settings")) S.settings = normSettings(j.team && j.team.settings);
    S.got.players = S.got.games = S.got.settings = true;
  }
  let refreshing = false, unchanged = 0, keyUnchecked = false;
  async function refresh() {
    if (refreshing) return;
    refreshing = true;
    try {
      const j = await apiGet("?a=state&rev=" + S.rev);
      const wasSlow = S.slow; S.slow = false;
      if (!j.same && j.rev >= S.rev) {
        S.rev = j.rev; unchanged = 0;
        applyState(j);
        try { localStorage.setItem(CACHE_LS, JSON.stringify({ players: j.players, games: j.games, team: j.team })); } catch (e) { /* storage blocked or full */ }
        schedRender(true);
      } else { unchanged++; if (wasSlow) schedRender(true); }
      if (keyUnchecked) checkKey(false);
    } catch (e) {
      if (!S.slow) { S.slow = true; schedRender(true); }
    } finally { refreshing = false; }
  }
  let pollT = 0;
  function poll() {
    clearTimeout(pollT);
    pollT = setTimeout(async () => { if (!document.hidden) await refresh(); poll(); }, unchanged > 20 ? 30000 : 12000);
  }
  document.addEventListener("visibilitychange", () => { if (!document.hidden && API) { unchanged = 0; refresh(); } });

  async function checkKey(fresh) {
    if (!captainKey) { S.canWrite = false; return; }
    try {
      const j = await apiPost({ a: "who", key: captainKey });
      keyUnchecked = false;
      if (j.canEdit) { S.canWrite = true; if (fresh) toast("Captain mode is on for this device."); }
      else { forgetKey(); S.canWrite = false; toast("That captain link no longer works. Ask for the new one."); }
    } catch (e) { keyUnchecked = true; }
    render();
  }

  async function boot() {
    const fresh = takeKey();
    S.canWrite = !!captainKey;
    if (!API) { S.mode = "nodb"; render(); return; }
    S.mode = "db";
    // Paint the last lineup this device saw right away, then replace it with the live one.
    try { const c = JSON.parse(localStorage.getItem(CACHE_LS) || "null"); if (c && typeof c === "object") applyState(c); } catch (e) { /* no cache */ }
    render();
    if (captainKey) checkKey(fresh);
    await refresh();
    render();
    poll();
  }
  function ready() { return S.got.players && S.got.games && S.got.settings; }

  function applyCol(col, docs) {
    const cur = col === "players" ? S.players : S.games; const next = new Map();
    for (const d of docs) {
      const path = col + "/" + d.id;
      if (S.deleted.has(path)) continue;
      if (S.pending.has(path) && cur.has(d.id)) { next.set(d.id, cur.get(d.id)); continue; }
      next.set(d.id, col === "players" ? normPlayer(d.id, d.data) : normGame(d.id, d.data));
    }
    cur.forEach((v, id) => { if (!next.has(id) && S.pending.has(col + "/" + id)) next.set(id, v); });
    if (col === "players") S.players = next; else S.games = next;
  }

  /* ---------- Saving: one write at a time per document, coalesced ---------- */
  const SV = {};
  function save(path, delay) {
    if (!S.canWrite || !store) return;
    S.deleted.delete(path);
    const st = SV[path] = SV[path] || { timer: null, inflight: false, dirty: false };
    S.pending.add(path); S.saveErr = false; updateSaveBadge();
    clearTimeout(st.timer);
    st.timer = setTimeout(() => { st.timer = null; flush(path); }, delay == null ? 500 : delay);
  }
  const touch = g => save("games/" + g.id);
  async function flush(path) {
    const st = SV[path]; if (!st) return;
    if (st.inflight) { st.dirty = true; return; }
    const body = bodyFor(path);
    if (!body) { S.pending.delete(path); updateSaveBadge(); return; }
    st.inflight = true;
    try { await writeOnce(path, body); S.lastSaved = Date.now(); }
    catch (e) { onWriteErr(e); }
    finally {
      st.inflight = false;
      if (st.dirty) { st.dirty = false; flush(path); }
      else if (!st.timer) S.pending.delete(path);
      updateSaveBadge();
    }
  }
  async function writeOnce(path, body) {
    try { await store.set(path, body); }
    catch (e) { if (e && e.code === "unavailable") { await sleep(400 + Math.random() * 900); await store.set(path, body); } else throw e; }
  }
  function onWriteErr(e) {
    const code = e && e.code; S.saveErr = true;
    if (code === "invalid_argument" && !S.writeKnown) { S.canWrite = false; toast("You can view these lineups but not change them."); schedRender(); return; }
    if (code === "revoked" || code === "not_granted" || code === "capability_disabled" || code === "capability_removed") { S.canWrite = false; toast("Editing isn't available on this page right now."); schedRender(); return; }
    if (code === "quota_exceeded") { toast("Storage is full. Delete a few old games, then try again."); return; }
    if (code === "resource_exhausted") { toast("Saving too fast. Wait a moment, then try again."); return; }
    toast("Couldn't save that change. Check your connection and try again.");
  }
  function bodyFor(path) {
    const i = path.indexOf("/"); const c = path.slice(0, i), id = path.slice(i + 1);
    if (c === "players") {
      const p = S.players.get(id);
      return p ? { name: p.name, sex: p.sex, active: p.active, available: p.available, bat: p.bat, batExp: p.batExp, fieldExp: p.fieldExp, positions: p.positions.slice(), dnp: p.dnp.slice(), injury: p.injury, maxInnings: p.maxInnings } : null;
    }
    if (c === "games") {
      const g = S.games.get(id);
      return g ? { date: g.date, opponent: g.opponent, innings: g.innings, order: g.order.map(e => ({ p: e.p, pos: e.pos.slice() })), createdAt: g.createdAt || new Date().toISOString(), updatedAt: new Date().toISOString() } : null;
    }
    if (path === "team/settings") return Object.assign({}, S.settings);
    return null;
  }
  function cancelSave(path) { const st = SV[path]; if (st) { clearTimeout(st.timer); st.timer = null; st.dirty = false; } S.pending.delete(path); }
  function removeDoc(path) { cancelSave(path); S.deleted.add(path); updateSaveBadge(); return store.del(path).catch(onWriteErr); }

  /* ---------- Undo (this device, this game) ---------- */
  function snap(g) {
    if (U.gid !== g.id) { U.gid = g.id; U.stack = []; }
    U.stack.push(JSON.stringify({ order: g.order, innings: g.innings }));
    if (U.stack.length > 40) U.stack.shift();
  }
  const canUndo = g => !!g && U.gid === g.id && U.stack.length > 0;
  function undo(g) {
    if (!canUndo(g)) return false;
    const s = JSON.parse(U.stack.pop());
    g.order = s.order.map(e => ({ p: e.p, pos: fit(e.pos, s.innings) })); g.innings = s.innings;
    touch(g); return true;
  }

  /* ---------- Rules ---------- */
  function analyze(g) {
    const n = g.innings, st = S.settings, minW = st.minWomenOnField, menMax = Math.max(0, 10 - minW);
    const P = g.order.map(e => { const pl = S.players.get(e.p); return { e: e, pl: pl, sex: pl ? pl.sex : "U", inj: pl ? pl.injury : "healthy", maxInn: pl ? pl.maxInnings : n }; });
    const names = nameMap(g);
    const C = {};
    const add = (key, level, inn, text) => { (C[key] = C[key] || []).push({ level: level, inn: inn, text: text }); };
    const innings = [];
    for (let i = 0; i < n; i++) {
      const holders = {}; let women = 0, men = 0, blanks = 0, wE = 0, mE = 0;
      P.forEach((x, idx) => {
        const p = x.e.pos[i] || "";
        if (p === "OUT") return;
        if (x.inj !== "batonly") { if (x.sex === "F") wE++; else mE++; }
        if (!p) { blanks++; return; }
        if (p === "EH") return;
        (holders[p] = holders[p] || []).push(idx);
        if (x.sex === "F") women++; else men++;
        const f = fitOf(x.pl, p);
        if (f === "dnp") add("dnp", "fail", i, `${names.get(x.e.p)} is at ${p}, a Do Not Play spot`);
        else if (f === "unlisted") add("listed", "note", i, `${names.get(x.e.p)} is at ${p}, not one of their positions`);
        if (x.inj === "batonly") add("injury", "fail", i, `${names.get(x.e.p)} is bat only but fields`);
      });
      const fielders = women + men;
      const maxPossible = Math.min(10, wE + Math.min(mE, menMax));
      const missing = FIELD.filter(p => !holders[p]);
      const dupes = FIELD.filter(p => holders[p] && holders[p].length > 1);
      const dupIdx = new Set(); dupes.forEach(p => holders[p].forEach(x => dupIdx.add(x)));
      const reqW = Math.min(minW, wE);
      if (missing.length && 10 - missing.length < maxPossible) add("fielders", "fail", i, `${listText(missing)} ${plural(missing.length, "is", "are")} open`);
      else if (missing.length) add("fielders", "note", i, `Playing short: ${listText(missing)} open (not enough players)`);
      if (dupes.length) add("dupes", "fail", i, `${listText(dupes)} ${plural(dupes.length, "has", "have")} two players`);
      if (women < reqW) add("women", "fail", i, `${women} ${plural(women, "woman", "women")} on defense, ${reqW} needed`);
      if (men > menMax) add("men", "fail", i, `${men} men on defense, max ${menMax}`);
      if (blanks) add("blanks", "note", i, `${blanks} ${plural(blanks, "player has", "players have")} no spot`);
      innings.push({ holders, women, men, fielders, missing, dupes, dupIdx, reqW, blanks });
    }
    const sits = g.order.map(e => e.pos.filter(p => p === "EH").length);
    const fielded = g.order.map(e => e.pos.filter(isField).length);
    P.forEach((x, idx) => {
      if (x.inj === "healthy" && sits[idx] > st.maxSits) add("bench", "fail", null, `${names.get(x.e.p)} sits ${sits[idx]} innings (max ${st.maxSits})`);
      if (x.inj === "limited" && fielded[idx] > x.maxInn) add("injury", "fail", null, `${names.get(x.e.p)} fields ${fielded[idx]} innings (limit ${x.maxInn})`);
    });
    const runs = ALG.spacingRuns(g.order.map(e => sexKey(e.p) === "M"), st.maxMenInRow, st.wrapOrder);
    const streakIdx = new Set();
    runs.forEach(r => { r.forEach(k => streakIdx.add(k)); const wraps = r[r.length - 1] < r[0]; add("spacing", "fail", null, `Spots ${r[0] + 1}-${r[r.length - 1] + 1}: ${r.length} men bat in a row${wraps ? " (wrapping to the top)" : ""}, limit ${st.maxMenInRow}`); });
    const defs = [
      ["fielders", "10 fielders"], ["dupes", "No duplicates"], ["women", `${minW}+ women on D`], ["men", `Max ${menMax} men on D`],
      ["bench", `Bench max ${st.maxSits}`], ["dnp", "Do Not Play"], ["injury", "Injury limits"], ["spacing", "Batting spacing"],
      ["listed", "Listed positions"], ["blanks", "No blanks"]
    ];
    const chips = defs.map(d => { const items = C[d[0]] || []; const level = items.some(x => x.level === "fail") ? "fail" : items.length ? "note" : "ok"; return { key: d[0], label: d[1], level: level, items: items }; });
    const fails = chips.reduce((a, c) => a + c.items.filter(x => x.level === "fail").length, 0);
    const notes = chips.reduce((a, c) => a + c.items.filter(x => x.level === "note").length, 0);
    const innFlag = range(n).map(i => { let lv = ""; chips.forEach(c => c.items.forEach(x => { if (x.inn === i) lv = x.level === "fail" || lv === "fail" ? "fail" : "note"; })); return lv; });
    return { innings, chips, fails, notes, innFlag, sits, fielded, streakIdx, womenAvail: P.filter(x => x.sex === "F").length };
  }
  function statusPill(A) {
    if (A.fails) return `<span class="state bad">${A.fails} rule ${plural(A.fails, "issue", "issues")}</span>`;
    if (A.notes) return `<span class="state warn">Rules pass · ${A.notes} ${plural(A.notes, "note", "notes")}</span>`;
    return `<span class="state ok">Rules pass</span>`;
  }

  /* ---------- Lineup actions ---------- */
  function assign(g, idx, i, pos) {
    const me = g.order[idx]; const cur = me.pos[i] || "";
    if (cur === pos) return "";
    let msg = "";
    if (isField(pos)) {
      const j = g.order.findIndex((e, k) => k !== idx && e.pos[i] === pos);
      if (j >= 0) {
        g.order[j].pos[i] = cur === "OUT" ? "" : cur;
        const nm = nameMap(g).get(g.order[j].p);
        msg = !cur || cur === "OUT" ? `${nm} has no spot in inning ${i + 1} now` : cur === "EH" ? `${nm} sits inning ${i + 1} now` : `${nm} moves to ${cur} in inning ${i + 1}`;
      }
    }
    me.pos[i] = pos;
    return msg;
  }
  function spaced(order) { return ALG.spaceOrder(order, e => sexKey(e.p) === "M", S.settings.maxMenInRow, S.settings.wrapOrder); }
  // Learning from saved games. A game only learns from games dated before it.
  let learnCache = { key: null, val: null };
  function learnedBefore(g) { return ALG.learn(Array.from(S.games.values()), g ? g.date : "", g ? g.id : ""); }
  function learnedAll() {
    if (learnCache.key !== S.games) learnCache = { key: S.games, val: ALG.learn(Array.from(S.games.values()), "", "") };
    return learnCache.val;
  }
  function playedText(h, max) {
    if (!h || !h.tot) return "";
    const total = Object.values(h.raw).reduce((a, v) => a + v, 0);
    return Object.keys(h.raw).sort((a, b) => h.raw[b] - h.raw[a]).slice(0, max || 4).map(q => `${q} ${Math.round(100 * h.raw[q] / total)}%`).join(" · ");
  }
  // Roster batting order first; anyone without one slots in at their usual spot from past games; batting experience breaks ties.
  function battingOrder(order, L) {
    const n = order.length;
    const key = e => { const pl = S.players.get(e.p); if (pl && pl.bat) return pl.bat; const h = L && L.H[e.p]; return h ? 1 + h.avgSpot * (n - 1) : 99; };
    const sorted = order.slice().sort((a, b) => {
      const pa = S.players.get(a.p), pb = S.players.get(b.p);
      return (key(a) - key(b)) || ((pb ? pb.batExp : 0) - (pa ? pa.batExp : 0)) || byFull(pa, pb);
    });
    return spaced(sorted);
  }
  function rebuild(g, from) {
    const L = learnedBefore(g);
    if (from < 0) g.order = battingOrder(g.order, L);
    const rows = g.order.map((e, idx) => {
      const pl = S.players.get(e.p);
      return { pos: e.pos, sex: pl ? pl.sex : "M", inj: pl ? pl.injury : "healthy", maxInn: pl ? pl.maxInnings : g.innings, exp: pl && pl.fieldExp ? pl.fieldExp : 3, positions: pl ? pl.positions : [], dnp: pl ? pl.dnp : [], hist: L.H[e.p] || null, idx: idx };
    });
    ALG.planDefense(rows, { n: g.innings, from: Math.max(0, from), minW: S.settings.minWomenOnField, maxSits: S.settings.maxSits, strategy: S.settings.sitStrategy, histW: HIST_W[S.settings.histWeight] });
    return L;
  }
  function toggleAvail(g, pid) {
    const idx = g.order.findIndex(e => e.p === pid);
    if (idx >= 0) { g.order.splice(idx, 1); return; }
    g.order.push({ p: pid, pos: fit([], g.innings) });
  }

  function chatText(g) {
    const names = nameMap(g);
    const lines = [`${teamName()}${g.opponent ? " vs " + g.opponent : ""} · ${fmtLong(g.date)}`, "", "Batting order, then position each inning:"];
    g.order.forEach((e, idx) => lines.push(`${idx + 1}. ${names.get(e.p)}: ${range(g.innings).map(i => { const p = e.pos[i]; return p === "OUT" ? "-" : p || "?"; }).join(" ")}`));
    lines.push("", "EH = batting, sitting that inning");
    return lines.join("\n");
  }
  function sheetTsv(g) {
    const k = Math.min(g.innings, 6);
    return g.order.map((e, idx) => {
      const pl = S.players.get(e.p); const f = pl && pl.sex === "F";
      const pos = range(k).map(i => { const v = e.pos[i] || ""; return v === "EH" ? (f ? "EH-F" : "EH-M") : v === "OUT" ? "" : v; });
      return [idx + 1, f ? "Female" : "Male", pl ? pl.name : "", ""].concat(pos).join("\t");
    }).join("\n");
  }

  /* ---------- Printable lineup card (PDF) ---------- */
  let jspdfP = null;
  function loadJsPDF() {
    if (window.jspdf) return Promise.resolve();
    if (!jspdfP) jspdfP = new Promise((res, rej) => { const s = document.createElement("script"); s.src = JSPDF_URL; s.onload = () => res(); s.onerror = () => { jspdfP = null; rej(new Error("jsPDF failed to load")); }; document.head.appendChild(s); });
    return jspdfP;
  }
  async function printCard(g) {
    const cl = window.claude;
    let dl = null;
    if (cl && typeof cl.use === "function") {
      try { dl = await cl.use("downloads"); } catch (e) { dl = null; }
      if (!dl) { toast("Saving files isn't available in this view."); return; }
    }
    toast("Building the lineup card…");
    try { await loadJsPDF(); } catch (e) { toast("Couldn't load the PDF maker. Check your connection and try again."); return; }
    let blob;
    try { blob = buildPdf(g); } catch (e) { toast("Couldn't build the PDF."); return; }
    const fname = `lineup-${g.date || "game"}${g.opponent ? "-" + slug(g.opponent) : ""}.pdf`;
    if (dl) {
      try { await dl.save({ filename: fname, data: blob }); toast("Lineup card saved"); }
      catch (e) { const c = e && e.code; toast(c === "declined" ? "Download canceled" : c === "rate_limited" ? "A download prompt is already open." : "Couldn't save the PDF here."); }
    } else {
      if (S.ui.pdfUrl) URL.revokeObjectURL(S.ui.pdfUrl);
      S.ui.pdfUrl = URL.createObjectURL(blob); S.ui.pdfSize = blob.size; render(); toast("Lineup card ready");
    }
  }
  function buildPdf(g) {
    const doc = new window.jspdf.jsPDF({ unit: "pt", format: "letter" });
    const A = analyze(g); const n = g.innings; const names = nameMap(g);
    const L = 40, R = 572; let y = 52;
    const line = (x1, y1, x2, y2, w) => { doc.setLineWidth(w || 0.6); doc.line(x1, y1, x2, y2); };
    doc.setFont("helvetica", "bold"); doc.setFontSize(22); doc.text("LINEUP CARD", L, y);
    doc.setFont("helvetica", "normal"); doc.setFontSize(9); doc.setTextColor(90);
    doc.text(`${teamName()}  |  ${g.order.length} batters`, L, y + 14); doc.setTextColor(0);
    // Header fields: [label, value, x, label width, line end, baseline]
    [["Opponent", g.opponent || "", 300, 45, R, y - 12], ["Date", fmtLong(g.date), 300, 26, 452, y + 4], ["Time", "", 458, 26, R, y + 4], ["Field", "", 300, 26, R, y + 20]].forEach(f => {
      doc.setFont("helvetica", "bold"); doc.setFontSize(8); doc.text(f[0], f[2], f[5]);
      doc.setFont("helvetica", "normal"); doc.setFontSize(9); doc.text(String(f[1]), f[2] + f[3], f[5], { maxWidth: f[4] - f[2] - f[3] - 2 });
      line(f[2] + f[3] - 2, f[5] + 3, f[4], f[5] + 3, 0.4);
    });
    y += 32; line(L, y, R, y, 1.2);
    y += 18; doc.setFont("helvetica", "bold"); doc.setFontSize(11); doc.text("BATTING ORDER", L, y);
    y += 8;
    const cNum = 22, cName = 150, cSex = 28;
    const xInn0 = L + cNum + cName + cSex;
    const cInn = Math.min(48, (R - xInn0 - 70) / n);
    const xNote = xInn0 + cInn * n;
    const rowH = 18; const top = y;
    const colX = k => k === 0 ? L : k === 1 ? L + cNum : k === 2 ? L + cNum + cName : k < 3 + n ? xInn0 + cInn * (k - 3) : xNote;
    const colW = k => k === 0 ? cNum : k === 1 ? cName : k === 2 ? cSex : k < 3 + n ? cInn : R - xNote;
    const drawRow = (cells, yy, bold, shade) => {
      if (shade) { doc.setFillColor(235, 238, 243); doc.rect(L, yy, R - L, rowH, "F"); }
      doc.setFontSize(9.5);
      cells.forEach((c, k) => {
        const t = c && typeof c === "object" ? c : { t: c };
        doc.setFont("helvetica", t.dim ? "italic" : bold ? "bold" : "normal"); doc.setTextColor(t.dim ? 120 : 0);
        const left = k === 1 || k === 3 + n;
        doc.text(String(t.t == null ? "" : t.t), left ? colX(k) + 4 : colX(k) + colW(k) / 2, yy + 12.5, { align: left ? "left" : "center", maxWidth: colW(k) - 6 });
      });
      doc.setTextColor(0);
      line(L, yy + rowH, R, yy + rowH, 0.4);
    };
    drawRow(["#", "Player", "M/F"].concat(range(n).map(i => "Inn " + (i + 1))).concat(["Note"]), y, true, true);
    y += rowH;
    g.order.forEach((e, idx) => {
      const pl = S.players.get(e.p);
      const goneAt = e.pos.indexOf("OUT");
      const note = [injTag(pl), goneAt >= 0 ? "Left after " + goneAt : ""].filter(Boolean).join(", ");
      drawRow([idx + 1, fullName(pl), pl && pl.sex !== "U" ? pl.sex : ""].concat(range(n).map(i => { const p = e.pos[i]; return p === "EH" ? { t: "EH", dim: true } : p === "OUT" ? { t: "out", dim: true } : p || ""; })).concat([note]), y, false, false);
      y += rowH;
    });
    range(n + 4).forEach(k => line(colX(k), top, colX(k), y, 0.4)); line(R, top, R, y, 0.4); line(L, top, R, top, 0.4);
    y += 22; doc.setFont("helvetica", "bold"); doc.setFontSize(11); doc.text("SCORE", L, y); y += 8;
    const sCols = ["Team"].concat(range(n).map(i => String(i + 1))).concat(["Extra", "R"]);
    const sw = (R - L - 70) / (sCols.length - 1);
    const sx = k => (k === 0 ? L : L + 70 + sw * (k - 1));
    doc.setFillColor(235, 238, 243); doc.rect(L, y, R - L, 16, "F");
    doc.setFontSize(9);
    sCols.forEach((c, k) => doc.text(c, k === 0 ? L + 4 : sx(k) + sw / 2, y + 11, { align: k === 0 ? "left" : "center" }));
    ["Us", "Them"].forEach((t, r) => doc.text(t, L + 4, y + 16 + 24 * r + 15));
    const sH = 64;
    [0, 16, 40, 64].forEach(dy => line(L, y + dy, R, y + dy, 0.5));
    sCols.forEach((c, k) => line(sx(k), y, sx(k), y + sH, 0.5)); line(R, y, R, y + sH, 0.5);
    y += sH + 20;
    doc.setFont("helvetica", "normal"); doc.setFontSize(9.5);
    doc.text("[  ] Home    [  ] Away        Result:  [  ] W   [  ] L   [  ] T        Notes: ______________________________", L, y);
    y += 20; doc.setFont("helvetica", "bold"); doc.setFontSize(9);
    const failTexts = []; A.chips.forEach(c => c.items.forEach(x => { if (x.level === "fail") failTexts.push((x.inn != null ? "Inn " + (x.inn + 1) + ": " : "") + x.text); }));
    doc.text(failTexts.length ? `Rule check: ${failTexts.length} ${plural(failTexts.length, "issue", "issues")}` : "Rule check: all league rules pass", L, y);
    doc.setFont("helvetica", "normal"); doc.setFontSize(8.5); doc.setTextColor(70);
    const st = S.settings;
    const legend = `EH = on the bench, still bats. F = women. Lim N = injured, fields at most N innings. Bat only = hits, no defense. Rules: max ${st.maxMenInRow} men in a row${st.wrapOrder ? " (order wraps)" : ""}, ${st.minWomenOnField}+ women on defense, bench max ${st.maxSits}, never a Do Not Play spot.` + (failTexts.length ? " Issues: " + failTexts.slice(0, 6).join("; ") + "." : "") + ` Printed ${new Date().toLocaleString("en-US")}.`;
    doc.text(doc.splitTextToSize(legend, R - L), L, y + 12);
    doc.setTextColor(0);
    // Defense diamonds, six per page
    const bw = (R - L - 14) / 2, bh = 222;
    range(n).forEach(i => {
      const j = i % 6;
      if (j === 0) {
        doc.addPage();
        doc.setFont("helvetica", "bold"); doc.setFontSize(16); doc.text("DEFENSE BY INNING", L, 50);
        doc.setFont("helvetica", "normal"); doc.setFontSize(9); doc.setTextColor(90);
        doc.text(`${teamName()}${g.opponent ? " vs " + g.opponent : ""}  |  ${fmtLong(g.date)}`, L, 64); doc.setTextColor(0);
      }
      const bx = L + (j % 2) * (bw + 14), by = 78 + Math.floor(j / 2) * (bh + 8);
      doc.setLineWidth(0.6); doc.rect(bx, by, bw, bh);
      doc.setFont("helvetica", "bold"); doc.setFontSize(10); doc.text(`Inning ${i + 1}`, bx + 8, by + 14);
      doc.setFont("helvetica", "normal"); doc.setFontSize(8.5); doc.text(`${A.innings[i].women} women on D`, bx + bw - 8, by + 14, { align: "right" });
      const sc = Math.min((bw - 16) / 360, (bh - 46) / 300), ox = bx + (bw - 360 * sc) / 2, oy = by + 18;
      const P = (x, yy) => [ox + x * sc, oy + yy * sc];
      doc.setLineWidth(0.5);
      const a = P(180, 262), b = P(16, 98), c = P(344, 98), d1 = P(244, 198), d2 = P(180, 134), d3 = P(116, 198);
      doc.line(a[0], a[1], b[0], b[1]); doc.line(a[0], a[1], c[0], c[1]);
      doc.line(a[0], a[1], d1[0], d1[1]); doc.line(d1[0], d1[1], d2[0], d2[1]); doc.line(d2[0], d2[1], d3[0], d3[1]); doc.line(d3[0], d3[1], a[0], a[1]);
      let prev = null;
      for (let t = 0; t <= 20; t++) { const ang = Math.PI * (1.25 + 0.5 * t / 20); const q = P(180 + 232 * Math.cos(ang), 262 + 232 * Math.sin(ang)); if (prev) doc.line(prev[0], prev[1], q[0], q[1]); prev = q; }
      const holders = A.innings[i].holders;
      FIELD.forEach(p => {
        const q = P(SPOT[p][0], SPOT[p][1]);
        const who = (holders[p] || []).map(k => names.get(g.order[k].p)).join(" / ") || "open";
        doc.setFont("helvetica", "bold"); doc.setFontSize(6.5); doc.setTextColor(110); doc.text(p, q[0], q[1] - 1, { align: "center" });
        doc.setFontSize(8.5); doc.setTextColor(0); doc.text(who, q[0], q[1] + 8, { align: "center" });
      });
      const bench = g.order.filter(e => e.pos[i] === "EH").map(e => names.get(e.p));
      doc.setFont("helvetica", "normal"); doc.setFontSize(8); doc.text(doc.splitTextToSize("Bench: " + (bench.length ? bench.join(", ") : "none"), bw - 16), bx + 8, by + bh - 10);
    });
    return doc.output("blob");
  }

  /* ---------- Routing ---------- */
  function route() {
    let h = ""; try { h = decodeURIComponent((location.hash || "").slice(1)); } catch (e) { h = ""; }
    if (h.indexOf("game-") === 0) return { v: "game", id: h.slice(5) };
    if (h.indexOf("card-") === 0) return { v: "card", id: h.slice(5) };
    if (h === "season" || h === "roster") return { v: h };
    return { v: "games" };
  }
  function sortedGames() { return Array.from(S.games.values()).sort((a, b) => (b.date || "").localeCompare(a.date || "") || (b.createdAt || "").localeCompare(a.createdAt || "")); }
  function currentGame() {
    const t = todayIso();
    const up = Array.from(S.games.values()).filter(g => g.date && g.date >= t).sort((a, b) => a.date.localeCompare(b.date));
    return up[0] || sortedGames()[0] || null;
  }

  /* ---------- Rendering ---------- */
  let raf = 0;
  function inputBusy() { const a = document.activeElement; return !!(a && a.closest && (a.closest("#view") || a.closest("#sheet-root")) && /^(INPUT|SELECT|TEXTAREA)$/.test(a.tagName) && a.type !== "checkbox" && a.type !== "radio"); }
  function schedRender(fromData) {
    if (fromData && (S.pointerDown || S.dragging || inputBusy())) { S.needRender = true; return; }
    if (raf) return;
    raf = setTimeout(() => { raf = 0; render(); }, 16);
  }
  function flushDeferred() {
    if (!S.needRender) return;
    setTimeout(() => { if (S.needRender && !S.pointerDown && !S.dragging && !inputBusy()) render(); }, 40);
  }

  function render() {
    if (S.dragging) { S.needRender = true; return; }
    S.needRender = false;
    const a = document.activeElement;
    let fid = S.focusId, sel = null;
    if (!fid && a && a.id && a !== document.body) {
      fid = a.id;
      if (a.tagName === "INPUT" && a.type === "text") { try { sel = [a.selectionStart, a.selectionEnd]; } catch (e) { sel = null; } }
    }
    S.focusId = null;
    renderTop();
    document.getElementById("banner").innerHTML = bannerHtml();
    document.getElementById("view").innerHTML = viewHtml();
    document.getElementById("sheet-root").innerHTML = sheetHtml();
    if (fid) {
      const el = document.getElementById(fid);
      if (el) { try { el.focus({ preventScroll: true }); if (sel && el.setSelectionRange) el.setSelectionRange(sel[0], sel[1]); } catch (e) { /* not focusable */ } }
    }
    if (S.ui.copyFocus) { S.ui.copyFocus = false; const ta = document.getElementById("copy-ta"); if (ta) { ta.focus(); ta.select(); } }
  }

  function renderTop() {
    const r = route(); const cur = (r.v === "game" || r.v === "card") ? "games" : r.v;
    const tabs = [["games", "Lineups"], ["season", "Season"]];
    if (S.canWrite && S.mode !== "nodb") tabs.push(["roster", "Roster"]);
    document.getElementById("top").innerHTML =
      `<div class="bar-in"><a class="brand" id="tab-home" href="#games">${PLATE}<span>${brandHtml()}</span></a>` +
      `<nav class="tabs" aria-label="Sections">${tabs.map(t => `<a id="tab-${t[0]}" href="#${t[0]}"${cur === t[0] ? ' aria-current="page"' : ""}>${t[1]}</a>`).join("")}</nav>` +
      `<span class="save" id="savebadge">${esc(saveText())}</span></div>`;
  }
  function brandHtml() { const nm = teamName(); const k = nm.lastIndexOf(" "); return k > 0 ? esc(nm.slice(0, k)) + " <em>" + esc(nm.slice(k + 1)) + "</em>" : esc(nm); }
  function saveText() {
    if (S.mode === "connecting") return "Connecting…";
    if (S.mode === "nodb") return "";
    if (!S.canWrite) return S.slow ? "Offline" : "Live";
    if (S.pending.size) return "Saving…";
    if (S.saveErr) return "Not saved";
    if (S.mode === "local") return "This browser only";
    return S.lastSaved ? "All changes saved" : "Live";
  }
  function updateSaveBadge() { const el = document.getElementById("savebadge"); if (el) el.textContent = saveText(); }
  function bannerHtml() {
    const b = [];
    if (S.mode === "local") b.push("Opened outside Claude, so changes save in this browser only.");
    if (S.slow) b.push("Can't reach the saved lineups yet. What you see may be out of date.");
    if (S.liveErr) b.push("Live updates stopped. Reopen this page to reconnect.");
    return b.map(t => `<div class="banner">${esc(t)}</div>`).join("");
  }

  function viewHtml() {
    if (S.mode === "nodb") return `<section class="panel empty">${PLATE_BIG}<h1>Almost ready</h1><p class="sub">This site is not connected to its data yet.</p></section>`;
    if (S.mode === "connecting" || !ready()) return `<section class="panel loading" aria-busy="true"><div class="ld-bar"></div><p class="sub">Loading lineups…</p></section>`;
    const r = route();
    if (r.v === "game") return S.canWrite ? viewEditor(r.id) : viewCard(r.id);
    if (r.v === "card") return viewCard(r.id);
    if (r.v === "season") return viewSeason();
    if (r.v === "roster" && S.canWrite) return viewRoster();
    return viewGames();
  }
  function missingGame() { return `<section class="panel empty"><h2>Game not found</h2><p class="sub">It may have been deleted.</p><a class="btn" href="#games">Back to lineups</a></section>`; }
  function outputs() {
    const pdf = S.ui.pdfUrl ? `<section class="panel"><a class="btn primary" href="${S.ui.pdfUrl}" download="lineup-card.pdf" target="_blank" rel="noopener">Save the lineup card (PDF, ${Math.max(1, Math.round((S.ui.pdfSize || 0) / 1024))} KB)</a></section>` : "";
    const txt = S.ui.copyText != null ? `<section class="panel"><label class="fld" for="copy-ta">Copy this text</label><textarea id="copy-ta" class="copy-ta" readonly rows="8">${esc(S.ui.copyText)}</textarea></section>` : "";
    return pdf + txt;
  }

  /* Home */
  function viewGames() {
    const games = sortedGames(); const cur = currentGame(); const w = S.canWrite;
    let h = "";
    if (cur) {
      h += `<section class="nextup"><div class="sec-head"><h1>${cur.date && cur.date >= todayIso() ? "Next up" : "Latest lineup"}</h1><div class="btnrow">` +
        `<button class="btn" data-act="copy-text" data-gid="${esc(cur.id)}">Copy as text</button>` +
        `<button class="btn" data-act="print" data-gid="${esc(cur.id)}">Print card (PDF)</button>` +
        (w ? `<a class="btn primary" href="#game-${esc(cur.id)}">Edit lineup</a>` : "") +
        `</div></div>${outputs()}${cardHtml(cur)}</section>`;
    }
    h += `<section class="games-sec"><div class="sec-head"><h2>All games</h2>${w ? `<button class="btn${cur ? "" : " primary"}" id="btn-new" data-act="new-open">New game</button>` : ""}</div>`;
    if (w && S.ui.newOpen) h += newGameHtml(games[0]);
    if (!games.length) {
      h += `<div class="panel empty">${PLATE_BIG}<h2>No games yet</h2><p class="sub">${w ? (S.players.size ? "Tap New game to build your first lineup." : "Add your players on the Roster tab, then tap New game.") : "Lineups show up here once a captain adds a game."}</p></div>`;
    } else {
      h += `<ol class="glist">${games.map(gameRow).join("")}</ol>`;
    }
    return h + `</section>`;
  }
  function gameRow(g) {
    const st = stubParts(g.date); const women = g.order.filter(e => sexKey(e.p) === "F").length;
    let chip = "";
    if (S.canWrite) chip = !g.order.length ? `<span class="state">Empty</span>` : statusPill(analyze(g));
    const href = (S.canWrite ? "#game-" : "#card-") + g.id;
    return `<li><a class="grow" href="${esc(href)}"><span class="stub" aria-hidden="true"><span class="dow">${esc(st.dow)}</span><span class="day">${esc(st.day)}</span><span class="mon">${esc(st.mon)}</span></span>` +
      `<span class="ginfo"><span class="gtitle">${g.opponent ? "vs " + esc(g.opponent) : "Opponent not set"}</span><span class="gmeta">${esc(fmtLong(g.date))} · ${g.order.length} playing · ${women} ${plural(women, "woman", "women")}</span></span>${chip}</a></li>`;
  }
  function ngState() {
    if (!S.ui.ng) { const last = sortedGames()[0]; S.ui.ng = { date: defaultNextDate(last), opp: "", from: "roster" }; }
    return S.ui.ng;
  }
  function newGameHtml(last) {
    const ng = ngState();
    const avail = Array.from(S.players.values()).filter(p => p.active && p.available);
    const aw = avail.filter(p => p.sex === "F").length;
    const copyOpt = last ? `<label class="radio"><input type="radio" name="ng-from" data-field="ng-from" value="${esc(last.id)}"${ng.from === last.id ? " checked" : ""}> Copy the ${esc(fmtLong(last.date))} lineup <span class="sub">(${last.order.length} players, positions included)</span></label>` : "";
    return `<form class="panel newgame" id="newform" novalidate><h3>New game</h3><div class="fields">` +
      `<label class="fld">Date<input type="date" id="ng-date" data-field="ng-date" value="${esc(ng.date)}"></label>` +
      `<label class="fld">Opponent<input type="text" id="ng-opp" data-field="ng-opp" value="${esc(ng.opp)}" placeholder="Optional" maxlength="80" autocomplete="off"></label></div>` +
      `<fieldset class="radios"><legend>Start from</legend>` +
      `<label class="radio"><input type="radio" name="ng-from" data-field="ng-from" value="roster"${ng.from === "roster" ? " checked" : ""}> Build from the roster <span class="sub">(${avail.length} available, ${aw} ${plural(aw, "woman", "women")}; batting order and all innings filled in)</span></label>` +
      `${copyOpt}<label class="radio"><input type="radio" name="ng-from" data-field="ng-from" value=""${!ng.from ? " checked" : ""}> Blank lineup with every available player</label></fieldset>` +
      `<p class="hint">Tick who's available on the Roster tab first. You can still change who's playing inside the game.</p>` +
      `<div class="actions"><button type="submit" class="btn primary">Create lineup</button><button type="button" class="btn ghost" data-act="new-close">Cancel</button></div></form>`;
  }

  /* Dugout card */
  function cardHtml(g) {
    const names = nameMap(g); const n = g.innings;
    const rows = g.order.map((e, idx) => {
      const sx = sexKey(e.p); const pl = S.players.get(e.p); const tag = injTag(pl);
      return `<tr><td class="cnum"><span class="num">${idx + 1}</span></td><td class="cn"><span class="sx sx-${sx}" title="${sexLabel(sx)}">${sx === "U" ? "?" : sx}</span>${esc(names.get(e.p))}${tag ? `<span class="tagi">${esc(tag)}</span>` : ""}</td>` +
        range(n).map(i => { const p = e.pos[i]; const b = i % 2 === 0 ? ' class="band"' : ""; const t = p === "EH" ? `<span class="t eh">EH</span>` : p === "OUT" ? `<span class="t out">out</span>` : p ? `<span class="t">${p}</span>` : `<span class="t none">?</span>`; return `<td${b}>${t}</td>`; }).join("") + `</tr>`;
    }).join("");
    const table = g.order.length
      ? `<div class="tablewrap"><table class="cardgrid"><thead><tr><th scope="col">#</th><th scope="col" class="cn">Batter</th>${range(n).map(i => `<th scope="col"${i % 2 === 0 ? ' class="band"' : ""}>${i + 1}</th>`).join("")}</tr></thead><tbody>${rows}</tbody></table></div>`
      : `<p class="pad sub">No players in this lineup yet.</p>`;
    return `<article class="card"><header class="card-head"><span class="ch-team">${esc(teamName())}</span><span class="ch-game">${g.opponent ? `<span class="vs">vs</span><b>${esc(g.opponent)}</b>` : `<span class="vs">Game day</span>`}<span class="dt">${esc(fmtLong(g.date))}</span></span></header>` +
      `<div class="card-body"><div>${table}</div><div class="card-field">${fieldBlock(g, names)}</div></div></article>`;
  }
  function viewCard(id) {
    const g = S.games.get(id); if (!g) return missingGame();
    const w = S.canWrite;
    return `<div class="crumbs"><a class="back" href="#games">← All lineups</a><div class="btnrow">` +
      `<button class="btn" data-act="copy-text" data-gid="${esc(id)}">Copy as text</button>` +
      `<button class="btn" data-act="print" data-gid="${esc(id)}">Print card (PDF)</button>` +
      (w ? `<button class="btn" data-act="copy-tsv" data-gid="${esc(id)}">Copy for Google Sheets</button><a class="btn primary" href="#game-${esc(id)}">Edit lineup</a>` : "") +
      `</div></div>${outputs()}${cardHtml(g)}` +
      (w ? `<p class="hint">Google Sheets: duplicate the Template tab, click cell B4, then paste. Sitting players paste as EH-M or EH-F to match the sheet.${g.innings > 6 ? " The sheet has room for 6 innings, so only innings 1 to 6 are copied." : ""}</p>` : "");
  }

  function fieldBlock(g, names, A) {
    A = A || analyze(g);
    const n = g.innings; const i = Math.max(0, Math.min(S.ui.inn, n - 1)); const x = A.innings[i];
    const tabs = range(n).map(k => `<button class="inntab" id="itab-${k}" data-act="inn" data-i="${k}" aria-pressed="${k === i}" aria-label="Inning ${k + 1}${A.innFlag[k] ? ", needs attention" : ""}">${k + 1}${A.innFlag[k] ? `<span class="flag${A.innFlag[k] === "fail" ? " bad" : ""}"></span>` : ""}</button>`).join("");
    const bench = g.order.filter(e => e.pos[i] === "EH").map(e => names.get(e.p));
    const unset = g.order.filter(e => !e.pos[i]).map(e => names.get(e.p));
    return `<div class="fv-head"><h3>Inning ${i + 1}</h3><span class="sub">${x.fielders}/10 on D · ${x.women} ${plural(x.women, "woman", "women")} · ${bench.length} sitting</span></div>` +
      `<div class="inntabs" role="group" aria-label="Pick an inning">${tabs}</div>${fieldSvg(g, i, names)}` +
      `<div class="sitting"><b>Bench:</b> ${bench.length ? bench.map(b => `<span class="bchip">${esc(b)}</span>`).join("") : "nobody"}</div>` +
      (unset.length ? `<p class="sitting unset"><b>No spot yet:</b> ${esc(unset.join(", "))}</p>` : "");
  }
  function fieldSvg(g, i, names) {
    const holders = {};
    g.order.forEach(e => { const p = e.pos[i]; if (isField(p)) (holders[p] = holders[p] || []).push(e.p); });
    // Each fielder is a chalk-white name pin with a gold position tab; the dot shows fit (primary, alt, unlisted, do not play).
    const labels = FIELD.map(p => {
      const xy = SPOT[p]; const h = holders[p];
      const txt = !h ? "Open" : h.map(pid => names.get(pid)).join(" / ");
      const fitc = h && h.length === 1 ? fitOf(S.players.get(h[0]), p) : "";
      const w = Math.max(48, Math.round(txt.length * 7.2 + (fitc ? 28 : 18)));
      const x0 = xy[0] - w / 2, y0 = xy[1];
      const bg = !h ? " open" : h.length > 1 ? " dup" : "";
      return `<g class="pin"><title>${POSNAME[p]}: ${esc(txt)}${fitc ? ", " + FITNAME[fitc] : ""}</title>` +
        `<rect class="pin-bg${bg}" x="${x0}" y="${y0}" width="${w}" height="22" rx="11"/>` +
        (fitc ? `<circle class="pin-dot ${fitc}" cx="${x0 + 12}" cy="${y0 + 11}" r="4"/>` : "") +
        `<text class="pin-name${!h ? " open" : ""}" x="${xy[0] + (fitc ? 5 : 0)}" y="${y0 + 15}">${esc(txt)}</text>` +
        `<rect class="pin-tab" x="${xy[0] - 13}" y="${y0 - 12}" width="26" height="13" rx="4"/><text class="pin-code" x="${xy[0]}" y="${y0 - 2}">${p}</text></g>`;
    }).join("");
    const mow = "mow-" + rid(5);
    return `<svg class="field" viewBox="0 0 360 316" role="img" aria-label="Defense in inning ${i + 1}">` +
      `<defs><pattern id="${mow}" width="26" height="26" patternUnits="userSpaceOnUse" patternTransform="rotate(32)"><rect width="13" height="26" fill="#ffffff" fill-opacity=".055"/></pattern></defs>` +
      `<path class="grass" d="M180 262 L16 98 A232 232 0 0 1 344 98 Z"/>` +
      `<path fill="url(#${mow})" d="M180 262 L16 98 A232 232 0 0 1 344 98 Z"/>` +
      `<path class="clay" d="M180 276 L278 180 Q180 82 82 180 Z"/>` +
      `<polygon class="grass2" points="180,248 230,198 180,148 130,198"/>` +
      `<path class="chalkline" d="M180 262 L16 98 M180 262 L344 98"/>` +
      `<circle class="clay" cx="180" cy="198" r="10"/>` +
      `<rect class="base" x="238" y="192" width="12" height="12" transform="rotate(45 244 198)"/>` +
      `<rect class="base" x="174" y="128" width="12" height="12" transform="rotate(45 180 134)"/>` +
      `<rect class="base" x="110" y="192" width="12" height="12" transform="rotate(45 116 198)"/>` +
      `<path class="base" d="M174 257 h12 v6 l-6 6 l-6 -6 z"/>${labels}</svg>`;
  }

  /* Editor */
  function viewEditor(id) {
    const g = S.games.get(id); if (!g) return missingGame();
    const A = analyze(g); const names = nameMap(g); const n = g.innings;
    if (S.ui.inn >= n) S.ui.inn = n - 1;
    const inSet = new Set(g.order.map(e => e.p));
    const out = Array.from(S.players.values()).filter(p => p.active && !inSet.has(p.id)).length;
    const conf = S.ui.confirm; const qa = S.ui.qa;
    return `<div class="crumbs"><a class="back" href="#games">← All lineups</a><div class="btnrow">` +
      `<button class="btn" id="btn-undo" data-act="undo"${canUndo(g) ? "" : " disabled"}>↶ Undo</button>` +
      `<button class="btn" data-act="print" data-gid="${esc(id)}">Print (PDF)</button>` +
      `<a class="btn" href="#card-${esc(id)}">Dugout card</a>` +
      `<button class="btn go" id="btn-rebuild" data-act="rb-open">Rebuild</button></div></div>` +
      outputs() +
      `<section class="panel"><div class="sec-head"><h2>Rules</h2>${statusPill(A)}</div><div class="rules">${A.chips.map(c => `<span class="rchip ${c.level}" title="${esc(c.items.map(x => (x.inn != null ? "Inning " + (x.inn + 1) + ": " : "") + x.text).join(". "))}"><i>${c.level === "ok" ? "✓" : c.level === "note" ? "!" : "✕"}</i>${esc(c.label)}</span>`).join("")}</div></section>` +
      `<section class="panel"><div class="fields">` +
      `<label class="fld">Date<input type="date" id="g-date" data-field="g-date" value="${esc(g.date)}"></label>` +
      `<label class="fld">Opponent<input type="text" id="g-opp" data-field="g-opp" value="${esc(g.opponent)}" placeholder="Who are you playing?" maxlength="80" autocomplete="off"></label>` +
      `<label class="fld narrow">Innings<select id="g-inn" data-field="g-inn">${opts(3, 12, n)}</select></label></div></section>` +
      `<section class="panel"><div class="sec-head"><h2>Who's playing</h2><span class="sub">${g.order.length} in · ${A.womenAvail} ${plural(A.womenAvail, "woman", "women")} · ${out} out</span><button class="btn small" id="btn-qa" data-act="qa-open">+ Player</button></div>` +
      (qa ? `<form class="addrow" id="qaform" novalidate style="margin-bottom:12px"><input class="inp" type="text" id="qa-name" data-field="qa-name" value="${esc(qa.name)}" placeholder="Last, First" aria-label="New player name, last name first" maxlength="80" autocomplete="off">` +
        `<div class="seg sex" role="group" aria-label="Batter sex"><button type="button" class="m" id="qa-m" data-act="qa-sex" data-sex="M" aria-pressed="${qa.sex === "M"}">M</button><button type="button" class="f" id="qa-f" data-act="qa-sex" data-sex="F" aria-pressed="${qa.sex === "F"}">F</button></div>` +
        `<select class="inp" id="qa-pos" data-field="qa-pos" aria-label="Primary position">${posOpts(qa.pos, "Pos")}</select><button type="submit" class="btn primary">Add to game</button><button type="button" class="btn ghost" data-act="qa-close">Cancel</button></form>` : "") +
      `<div class="chips">${chipsHtml(g)}</div><p class="hint">Tap a name to mark them in or out for this game, then Rebuild. For a sub, use + Player or the SUB placeholders.</p></section>` +
      `<div class="editor"><section class="panel lineup"><div class="sec-head"><h2>Lineup · batting order</h2><span class="legend"><span class="fit-primary">Primary</span><span class="fit-alt">Alt</span><span class="fit-unlisted">Unlisted</span><span class="fit-bench">Bench</span></span></div>` +
      (conf === "clear" ? `<div class="confirm" role="alert"><span>Clear every position in this game? The batting order stays.</span><button class="btn small danger" data-act="clear-yes">Clear positions</button><button class="btn small ghost" data-act="cancel-confirm">Keep them</button></div>` : "") +
      (g.order.length ? lineupTable(g, A, names) : `<p class="sub">Nobody is in this lineup yet. Tap names above to add them.</p>`) +
      `<p class="hint">Tap a badge to pick a spot, or drag it onto another badge in the same inning to swap (mouse). Drag a batting number to reorder, or focus it and use the arrow keys. Tap a name for injury and attendance.</p></section>` +
      `<aside class="side"><section class="panel">${checksHtml(g, A, names)}</section><section class="panel">${fieldBlock(g, names, A)}</section></aside></div>` +
      `<section class="danger-zone">` +
      (conf === "delete"
        ? `<div class="confirm" role="alert"><span>Delete this game for everyone? This can't be undone.</span><button class="btn small danger" data-act="del-yes">Delete game</button><button class="btn small ghost" data-act="cancel-confirm">Keep it</button></div>`
        : `<div class="btnrow"><button class="btn small ghost" data-act="confirm" data-what="clear">Clear positions</button><button class="btn small ghost danger-text" data-act="confirm" data-what="delete">Delete this game</button></div>`) +
      `</section>`;
  }
  function chipsHtml(g) {
    const inSet = new Set(g.order.map(e => e.p));
    const ids = new Set(Array.from(S.players.values()).filter(p => p.active).map(p => p.id));
    inSet.forEach(id => ids.add(id));
    return Array.from(ids).map(id => ({ id: id, pl: S.players.get(id) }))
      .sort((a, b) => fullName(a.pl).localeCompare(fullName(b.pl)))
      .map(x => {
        const on = inSet.has(x.id); const sx = x.pl ? x.pl.sex : "U";
        return `<button class="pchip" id="chip-${esc(x.id)}" data-act="avail" data-pid="${esc(x.id)}" aria-pressed="${on}"><span class="dot sx-${sx}" aria-hidden="true"></span>${esc(fullName(x.pl))}${on ? "" : '<span class="out">out</span>'}</button>`;
      }).join("");
  }
  function lineupTable(g, A, names) {
    const n = g.innings;
    const head = `<tr><th scope="col">#</th><th scope="col" class="c-name">Player</th>` +
      range(n).map(i => `<th scope="col" class="inn${i % 2 === 0 ? " band" : ""}"><button class="innbtn" id="ibtn-${i}" data-act="inn" data-i="${i}" aria-pressed="${S.ui.inn === i}" aria-label="Show inning ${i + 1} on the field">${i + 1}${A.innFlag[i] ? `<span class="flag${A.innFlag[i] === "fail" ? " bad" : ""}"></span>` : ""}</button></th>`).join("") +
      `<th scope="col" class="c-ds" title="Innings on defense / sitting">D/S</th></tr>`;
    const rows = g.order.map((e, idx) => {
      const pl = S.players.get(e.p); const sx = sexKey(e.p);
      const nm = pl ? splitName(pl.name) : { first: "Removed", last: "player" };
      const first = names.get(e.p) || nm.first;
      const pid = esc(e.p); const tag = injTag(pl);
      const gone = e.pos.indexOf("OUT") >= 0;
      const cells = range(n).map(i => {
        const p = e.pos[i] || ""; const f = fitOf(pl, p); const dup = A.innings[i].dupIdx.has(idx);
        const cur = S.ui.pick && S.ui.pick.pid === e.p && S.ui.pick.i === i;
        return `<td class="inn${i % 2 === 0 ? " band" : ""}"><button class="cell ${p ? "fit-" + f : "blank"}${dup ? " dup" : ""}${cur ? " cur" : ""}" id="c-${pid}-${i}" data-act="pick" data-pid="${pid}" data-i="${i}" aria-label="${esc(first)}, inning ${i + 1}: ${p ? POSNAME[p] + (f === "dnp" ? ", do not play" : "") : "not set"}">${p === "OUT" ? "–" : p || "+"}</button></td>`;
      }).join("");
      const lastBit = nm.last && first === nm.first ? `<span class="ln"> ${esc(nm.last)}</span><span class="li"> ${esc(nm.last[0])}.</span>` : "";
      const sits = A.sits[idx], d = A.fielded[idx];
      return `<tr data-idx="${idx}" class="${A.streakIdx.has(idx) ? "streak" : ""}${gone ? " gone" : ""}"><td class="c-num"><button class="handle" id="drag-${pid}" data-drag="${idx}" aria-label="Batting ${idx + 1}, ${esc(first)}. Drag or use arrow keys to move.">${idx + 1}</button></td>` +
        `<td class="c-name"><button class="pbtn" id="pn-${pid}" data-act="pd-open" data-pid="${pid}" aria-label="${esc(first)}: injury and attendance"><span class="pname"><span class="sx sx-${sx}" title="${sexLabel(sx)}">${sx === "U" ? "?" : sx}</span><span class="nm"><span class="fn">${esc(first)}</span>${lastBit}</span>${tag ? `<span class="tagi">${esc(tag)}</span>` : ""}${gone ? `<span class="tagi">Left</span>` : ""}</span>${miniPos(pl)}</button></td>${cells}` +
        `<td class="c-ds"><b>${d}</b>/<span class="${sits > S.settings.maxSits && (!pl || pl.injury === "healthy") ? "hot" : ""}">${sits}</span></td></tr>`;
    }).join("");
    return `<div class="tablewrap"><table class="grid"><thead>${head}</thead><tbody>${rows}</tbody></table></div>`;
  }
  function checksHtml(g, A, names) {
    const groups = [];
    A.chips.forEach(c => {
      const byText = new Map();
      c.items.forEach(x => { const k = x.level + "|" + x.text; if (!byText.has(k)) byText.set(k, { level: x.level, text: x.text, inns: [] }); if (x.inn != null) byText.get(k).inns.push(x.inn + 1); });
      byText.forEach(v => groups.push(v));
    });
    groups.sort((a, b) => (a.level === "fail" ? 0 : 1) - (b.level === "fail" ? 0 : 1));
    const innLabel = a => !a.length ? "Game" : a.length === 1 ? "Inn " + a[0] : "Inn " + (a.every((v, k) => k === 0 || v === a[k - 1] + 1) ? a[0] + "-" + a[a.length - 1] : a.join(", "));
    const items = groups.map(v => `<li><span class="tag${v.level === "note" ? " note" : ""}">${innLabel(v.inns)}</span><span>${esc(v.text)}</span></li>`);
    let fair = "";
    if (g.order.length) {
      const maxS = Math.max.apply(null, A.sits);
      const most = maxS >= 2 ? g.order.filter((e, k) => A.sits[k] === maxS).map(e => names.get(e.p)) : [];
      const never = g.order.filter((e, k) => A.sits[k] === 0 && A.fielded[k] > 0).map(e => names.get(e.p));
      const parts = [];
      if (most.length) parts.push(`<b>Sitting ${maxS} innings:</b> ${esc(most.join(", "))}`);
      if (never.length && never.length < g.order.length) parts.push(`<b>Never sits:</b> ${esc(never.join(", "))}`);
      if (parts.length) fair = `<p class="fair">${parts.join("<br>")}</p>`;
    }
    return `<div class="sec-head"><h2>Checks</h2>${statusPill(A)}</div>` + (items.length ? `<ul class="checks">${items.join("")}</ul>` : `<p class="allgood">✓ Every rule passes in all ${g.innings} innings.</p>`) + fair;
  }

  /* Dialogs: position picker, player, rebuild */
  function sheetHtml() {
    if (S.ui.rb) return rebuildDlg();
    if (S.ui.pd) return playerDlg();
    const pk = S.ui.pick; if (!pk) return "";
    const g = S.games.get(pk.gid); const idx = g ? g.order.findIndex(e => e.p === pk.pid) : -1;
    if (!g || idx < 0 || route().id !== pk.gid) { S.ui.pick = null; return ""; }
    if (pk.i >= g.innings) pk.i = g.innings - 1;
    const names = nameMap(g); const i = pk.i; const cur = g.order[idx].pos[i] || ""; const pl = S.players.get(pk.pid);
    const holder = {}; g.order.forEach((e, j) => { if (j !== idx && isField(e.pos[i])) holder[e.pos[i]] = names.get(e.p); });
    const btn = p => {
      const h = holder[p]; const isCur = cur === p; const f = fitOf(pl, p);
      return `<button class="pk fit-${f}${isCur ? " cur" : ""}${h ? " taken" : ""}" id="pk-${p}" data-act="set" data-pos="${p}" aria-pressed="${isCur}" aria-label="${POSNAME[p]}, ${FITNAME[f]}${isCur ? ", current" : h ? ", now " + esc(h) + ", swap" : ", open"}"><b>${p}</b><em>${f === "dnp" ? "✕ No" : FITNAME[f]}</em><small>${isCur ? "Current" : h ? "Swap " + esc(h) : "Open"}</small></button>`;
    };
    return `<div class="scrim" data-act="close-pick"></div><div class="sheet" role="dialog" aria-modal="true" aria-labelledby="pk-title">` +
      `<div class="sheet-head"><div><div class="pk-who" id="pk-title">${esc(names.get(pk.pid))}</div><div class="pk-sub">Batting ${idx + 1} · inning ${i + 1} of ${g.innings}</div></div>` +
      `<div class="pk-nav"><button id="pk-prev" data-act="pk-step" data-d="-1" aria-label="Previous inning"${i === 0 ? " disabled" : ""}>‹</button><span>Inn ${i + 1}</span><button id="pk-next" data-act="pk-step" data-d="1" aria-label="Next inning"${i >= g.innings - 1 ? " disabled" : ""}>›</button></div></div>` +
      `<div class="pk-grid"><div class="pk-label">Outfield</div>${["LF", "LC", "RC", "RF"].map(btn).join("")}` +
      `<div class="pk-label">Infield</div>${["3B", "SS", "2B", "1B"].map(btn).join("")}` +
      `<div class="pk-label">Battery and bench</div>${["P", "C"].map(btn).join("")}` +
      `<button class="pk fit-bench${cur === "EH" ? " cur" : ""}" id="pk-EH" data-act="set" data-pos="EH" aria-pressed="${cur === "EH"}"><b>EH</b><small>Bench, still bats</small></button>` +
      `<button class="pk clear" id="pk-clear" data-act="set" data-pos=""><b>Clear</b><small>No spot</small></button></div>` +
      `<div class="sheet-foot"><label class="sw"><input type="checkbox" id="pk-auto" data-field="pk-auto"${prefs.auto ? " checked" : ""}> Jump to the next inning after each pick</label><button class="btn" id="pk-done" data-act="close-pick">Done</button></div></div>`;
  }
  function rebuildDlg() {
    const g = S.games.get(S.ui.rb.gid); if (!g) { S.ui.rb = null; return ""; }
    const f = S.ui.rb.from; const n = g.innings;
    const optsHtml = `<button id="rb-whole" data-act="rb-from" data-f="-1" aria-pressed="${f < 0}">Whole game</button>` + range(n).map(i => `<button id="rb-${i}" data-act="rb-from" data-f="${i}" aria-pressed="${f === i}">From ${i + 1}</button>`).join("");
    const kept = f === 1 ? " and inning 1" : f > 1 ? ` and innings 1-${f}` : "";
    const desc = f < 0 ? `Rewrites the batting order (default order, spaced so no more than ${S.settings.maxMenInRow} men bat in a row) and all ${n} innings from the roster. Manual moves are replaced; Undo brings them back.`
      : `Keeps the batting order${kept}, then rebuilds innings ${f + 1}-${n} for whoever is still playing. Undo brings the current lineup back.`;
    const L = learnedBefore(g); const hw = S.settings.histWeight;
    const learnLine = !hw ? "Learning from past games is off (Roster, League rules)."
      : L.games ? `Learning from ${L.games} earlier ${plural(L.games, "game", "games")} (latest ${esc(fmtLong(L.last))}), newest counted most.`
      : "No earlier games to learn from yet, so it uses roster positions and experience.";
    return `<div class="scrim" data-act="rb-close"></div><div class="sheet" role="dialog" aria-modal="true" aria-labelledby="rb-title">` +
      `<div class="sheet-head"><div><div class="pk-who" id="rb-title">Rebuild the lineup?</div><div class="pk-sub">Uses positions, Do Not Play spots, injuries and experience from the roster.</div></div><button class="xbtn" data-act="rb-close" aria-label="Close">×</button></div>` +
      `<div class="seg wide" role="group" aria-label="What to rebuild">${optsHtml}</div><p class="desc">${desc}</p>` +
      `<div class="learnbox"><b>How it picks spots</b><ol><li>Roster positions in your order (primary first); never a Do Not Play spot.</li><li>Higher fielding experience wins a spot two players both list.</li><li>${learnLine}</li><li>Sits are spread evenly${S.settings.sitStrategy === "experience" ? " but go to less experienced players first" : ", and players who sat more earlier sit a little less"}; nobody past the bench max.</li></ol></div>` +
      `<div class="sheet-foot"><button class="btn" data-act="rb-close">Cancel</button><button class="btn go" id="rb-go" data-act="rb-go">${f < 0 ? "Rebuild whole game" : "Rebuild from inning " + (f + 1)}</button></div></div>`;
  }
  function playerDlg() {
    const d = S.ui.pd; const g = S.games.get(d.gid); const pl = S.players.get(d.pid);
    if (!g) { S.ui.pd = null; return ""; }
    const idx = g.order.findIndex(e => e.p === d.pid); if (idx < 0) { S.ui.pd = null; return ""; }
    const e = g.order[idx]; const n = g.innings;
    const sits = e.pos.filter(p => p === "EH").length, fld = e.pos.filter(isField).length;
    const injDesc = d.inj === "batonly" ? "Stays in the batting order and sits every inning on defense." : "Normal rotation.";
    return `<div class="scrim" data-act="pd-close"></div><div class="sheet" role="dialog" aria-modal="true" aria-labelledby="pd-title">` +
      `<div class="sheet-head"><div><div class="pk-who" id="pd-title">${esc(fullName(pl))}</div><div class="pk-sub">Batting ${idx + 1} · fields ${fld} · sits ${sits}</div></div><button class="xbtn" data-act="pd-close" aria-label="Close">×</button></div>` +
      (pl ? `<dl class="kv"><dt>Positions</dt><dd>${esc(pl.positions.join(", ") || "any")}</dd><dt>Do not play</dt><dd>${esc(pl.dnp.join(", ") || "none")}</dd><dt>Fielding exp</dt><dd>${pl.fieldExp || "not set"}</dd><dt>Batting exp</dt><dd>${pl.batExp || "not set"}</dd>` +
        `<dt>Usually plays</dt><dd>${esc(playedText(learnedBefore(g).H[d.pid]) || "no earlier games yet")}</dd></dl>` : "") +
      (pl ? `<div><div class="lbl">Injury</div><div class="seg wide" role="group" aria-label="Injury"><button id="pd-healthy" data-act="pd-inj" data-v="healthy" aria-pressed="${d.inj === "healthy"}">Healthy</button><button id="pd-limited" data-act="pd-inj" data-v="limited" aria-pressed="${d.inj === "limited"}">Limited</button><button id="pd-batonly" data-act="pd-inj" data-v="batonly" aria-pressed="${d.inj === "batonly"}">Bat only</button></div>` +
        (d.inj === "limited" ? `<div class="stepper"><button id="pd-minus" data-act="pd-max" data-d="-1" aria-label="Fewer innings">−</button><b>${d.max}</b><button id="pd-plus" data-act="pd-max" data-d="1" aria-label="More innings">+</button> max innings in the field</div>` : `<p class="desc">${injDesc}</p>`) + `</div>` : "") +
      `<div><div class="lbl">This game</div><div class="seg wide" role="group" aria-label="Attendance"><button id="pd-here" data-act="pd-att" data-v="here" aria-pressed="${d.att === "here"}">Playing</button><button id="pd-left" data-act="pd-att" data-v="left" aria-pressed="${d.att === "left"}">Left early</button><button id="pd-gone" data-act="pd-att" data-v="gone" aria-pressed="${d.att === "gone"}">Not here</button></div>` +
      (d.att === "left" ? `<label class="fld" style="margin-top:8px">Left after inning<select id="pd-after" data-field="pd-after">${opts(1, n - 1, d.after)}</select></label>` : "") +
      (d.att === "gone" ? `<p class="desc">Removes them from this game's lineup.</p>` : "") + `</div>` +
      `<div class="sheet-foot"><button class="btn" data-act="pd-close">Cancel</button><button class="btn go" id="pd-save" data-act="pd-save">Save</button></div>` +
      `<p class="desc">Injury saves to the roster and stays until you change it. Rebuild afterwards to rebalance, or move innings by hand.</p></div>`;
  }
  function pickFocusId(g, pid, i) { const e = g.order.find(x => x.p === pid); const p = e ? e.pos[i] : ""; return p && p !== "OUT" ? "pk-" + p : "pk-LF"; }
  function closePick() { const pk = S.ui.pick; S.ui.pick = null; if (pk) S.focusId = "c-" + pk.pid + "-" + pk.i; render(); }

  /* Season */
  function viewSeason() {
    const games = Array.from(S.games.values());
    const earliest = games.map(g => g.date).filter(Boolean).sort()[0] || "";
    const since = S.ui.since || S.settings.seasonStart || earliest;
    const counted = games.filter(g => !since || !g.date || g.date >= since);
    const blank = () => { const pos = {}; FIELD.forEach(p => { pos[p] = 0; }); return { g: 0, f: 0, sit: 0, pos: pos }; };
    const st = new Map();
    counted.forEach(g => g.order.forEach(e => {
      const s = st.get(e.p) || blank(); st.set(e.p, s); s.g++;
      e.pos.forEach(p => { if (isField(p)) { s.f++; s.pos[p]++; } else if (p === "EH") s.sit++; });
    }));
    const ids = new Set(st.keys()); S.players.forEach(p => { if (p.active && !/^sub-/.test(p.id)) ids.add(p.id); });
    const rows = Array.from(ids).map(id => { const s = st.get(id) || blank(); return { id: id, pl: S.players.get(id), s: s, pct: s.f + s.sit ? s.sit / (s.f + s.sit) : 0 }; });
    const sorters = { name: (a, b) => byFull(a.pl, b.pl), sit: (a, b) => (b.pct - a.pct) || (b.s.sit - a.s.sit) || byFull(a.pl, b.pl), games: (a, b) => (b.s.g - a.s.g) || byFull(a.pl, b.pl) };
    rows.sort(sorters[S.ui.sort] || sorters.name);
    const mxSit = Math.max(1, ...rows.map(r => r.s.sit)); const mxp = {}; FIELD.forEach(p => { mxp[p] = Math.max(1, ...rows.map(r => r.s.pos[p])); });
    const cell = (v, m, cls) => v ? `<td class="heat${cls ? " " + cls : ""}" style="--h:${(v / m).toFixed(2)}">${v}</td>` : `<td class="zero${cls === "grp" ? " grp" : ""}">·</td>`;
    const body = rows.map(r => {
      const sx = r.pl ? r.pl.sex : "U";
      return `<tr><td><span class="sx sx-${sx}" title="${sexLabel(sx)}">${sx === "U" ? "?" : sx}</span>${esc(fullName(r.pl))}</td><td>${r.s.g || '<span class="zero">·</span>'}</td><td>${r.s.f || '<span class="zero">·</span>'}</td>` +
        cell(r.s.sit, mxSit, "sitc") + `<td>${r.s.f + r.s.sit ? Math.round(r.pct * 100) + "%" : '<span class="zero">·</span>'}</td>` +
        FIELD.map((p, k) => cell(r.s.pos[p], mxp[p], k === 0 ? "grp" : "")).join("") + `</tr>`;
    }).join("");
    return `<section class="panel"><div class="sec-head"><h1>Season</h1><span class="sub">${counted.length} ${plural(counted.length, "game", "games")} counted</span></div>` +
      `<div class="fields"><label class="fld">Count games from<input type="date" id="ss-since" data-field="ss-since" value="${esc(since)}"></label>` +
      `<label class="fld">Sort by<select id="ss-sort" data-field="ss-sort"><option value="name"${S.ui.sort === "name" ? " selected" : ""}>Name</option><option value="sit"${S.ui.sort === "sit" ? " selected" : ""}>Most time sitting</option><option value="games"${S.ui.sort === "games" ? " selected" : ""}>Most games</option></select></label></div>` +
      `<div class="tablewrap" style="margin-top:14px"><table class="stats"><thead><tr><th scope="col">Player</th><th scope="col" title="Games">G</th><th scope="col" title="Innings in the field">Field</th><th scope="col" title="Innings sitting">Sit</th><th scope="col" title="Share of innings sitting">Sit %</th>${FIELD.map((p, k) => `<th scope="col"${k === 0 ? ' class="grp"' : ""}>${p}</th>`).join("")}</tr></thead><tbody>${body}</tbody></table></div>` +
      `<p class="hint">Innings played at each spot across the counted games. Sit % compares players who missed different games fairly.</p></section>`;
  }

  /* Roster */
  function viewRoster() {
    const pl = Array.from(S.players.values()).sort((a, b) => (Number(b.active) - Number(a.active)) || (Number(b.available) - Number(a.available)) || byFull(a, b));
    const act = pl.filter(p => p.active); const av = act.filter(p => p.available); const avw = av.filter(p => p.sex === "F").length;
    const np = S.ui.np; const st = S.settings;
    const items = pl.map(p => {
      const sid = esc(p.id); const open = S.ui.openPl === p.id; const tag = injTag(p);
      const meta = [p.bat ? "Bats #" + p.bat : "", p.fieldExp ? "Field " + p.fieldExp : "", p.batExp ? "Bat " + p.batExp : "", p.active ? "" : "Inactive"].filter(Boolean).join(" · ");
      return `<li class="prow${p.active ? "" : " inactive"}"><div class="prow-main"><label class="avail" title="Available this week"><input type="checkbox" id="pl-av-${sid}" data-field="pl-avail" data-id="${sid}"${p.available ? " checked" : ""} aria-label="${esc(fullName(p))} available this week"></label>` +
        `<button class="pr-btn" id="pl-open-${sid}" data-act="pl-open" data-id="${sid}" aria-expanded="${open}"><span class="pr-line"><span class="sx sx-${p.sex}">${p.sex === "U" ? "?" : p.sex}</span><span class="pr-name">${esc(fullName(p))}</span>${tag ? `<span class="tagi">${esc(tag)}</span>` : ""}</span>${miniPos(p)}${meta ? `<span class="pr-meta">${esc(meta)}</span>` : ""}</button>` +
        `<span class="pr-meta">${open ? "Close" : "Edit"}</span></div>${open ? playerEditor(p) : ""}</li>`;
    }).join("");
    return `<section class="panel"><div class="sec-head"><h2>Master roster</h2><span class="sub">${act.length} active · ${av.length} available this week (${avw} ${plural(avw, "woman", "women")})</span></div>` +
      `<form class="addrow" id="addform" novalidate><input class="inp" type="text" id="np-name" data-field="np-name" value="${esc(np.name)}" placeholder="Last, First" aria-label="New player name, last name first" maxlength="80" autocomplete="off">` +
      `<div class="seg sex" role="group" aria-label="New player batter sex"><button type="button" class="m" id="np-m" data-act="np-sex" data-sex="M" aria-pressed="${np.sex === "M"}">M</button><button type="button" class="f" id="np-f" data-act="np-sex" data-sex="F" aria-pressed="${np.sex === "F"}">F</button></div>` +
      `<select class="inp" id="np-pos" data-field="np-pos" aria-label="Primary position">${posOpts(np.pos, "Pos")}</select><button type="submit" class="btn primary">Add player</button></form>` +
      `<ul class="plist">${items}</ul><p class="hint">The checkbox marks who's available this week; "Build from the roster" uses it. Tap a player to set positions (in order of preference, 1 = primary), Do Not Play spots, experience, default batting order and injury.</p></section>` +
      `<section class="panel"><div class="sec-head"><h2>League rules</h2></div><div class="fields">` +
      `<label class="fld">Team name<input type="text" id="set-team" data-field="set-team" value="${esc(st.teamName)}" maxlength="60" autocomplete="off"></label>` +
      `<label class="fld narrow">Innings<select id="set-innings" data-field="set-innings">${opts(3, 12, st.innings)}</select></label>` +
      `<label class="fld narrow">Max men in a row<select id="set-maxmen" data-field="set-maxmen">${opts(1, 6, st.maxMenInRow)}</select></label>` +
      `<label class="fld narrow">Women on D<select id="set-minw" data-field="set-minw">${opts(0, 6, st.minWomenOnField)}</select></label>` +
      `<label class="fld narrow">Bench max<select id="set-maxsits" data-field="set-maxsits">${opts(0, 6, st.maxSits)}</select></label>` +
      `<label class="fld">Who sits first<select id="set-strategy" data-field="set-strategy"><option value="even"${st.sitStrategy === "even" ? " selected" : ""}>Spread sits evenly</option><option value="experience"${st.sitStrategy === "experience" ? " selected" : ""}>Less experienced players first</option></select></label>` +
      `<label class="fld">Learn from past games<select id="set-hist" data-field="set-hist">${HIST_LABEL.map((l, k) => `<option value="${k}"${st.histWeight === k ? " selected" : ""}>${l}</option>`).join("")}</select></label></div>` +
      `<label class="sw" style="margin-top:12px"><input type="checkbox" id="set-wrap" data-field="set-wrap"${st.wrapOrder ? " checked" : ""}> Count the wrap from the bottom of the order to the top as "in a row"</label>` +
      `<p class="hint">Rebuild and the rule checks use these. Max ${Math.max(0, 10 - st.minWomenOnField)} men on defense follows from the women minimum.</p></section>` +
      `<section class="panel"><div class="sec-head"><h2>Share links</h2></div>` +
      `<div class="linkrow"><div><b>Team link</b><span class="sub">Anyone can open it and see the live lineup. No login.</span></div><button class="btn" id="btn-copy-team" data-act="copy-team">Copy team link</button></div>` +
      `<div class="linkrow"><div><b>Captain link</b><span class="sub">Whoever has it can edit. Send it only to co-captains, never the group chat.</span></div><button class="btn" id="btn-copy-cap" data-act="copy-captain">Copy captain link</button></div>` +
      `<div class="linkrow"><div><b>This device</b><span class="sub">Captain mode is on here. Turn it off on a borrowed phone.</span></div><button class="btn ghost danger-text" data-act="lock">Turn off captain mode</button></div></section>${outputs()}`;
  }
  // Positions this player has actually played in saved games, with a one-tap way to add the unlisted ones.
  function learnedRow(p) {
    const h = learnedAll().H[p.id];
    if (!h || !h.tot) return `<div class="learned"><span class="lbl">Played in saved games</span><span class="sub">No games yet. Rebuild learns from every game you save.</span></div>`;
    const extra = Object.keys(h.raw).filter(q => h.raw[q] >= 2 && p.positions.indexOf(q) < 0 && p.dnp.indexOf(q) < 0).sort((a, b) => h.raw[b] - h.raw[a]);
    return `<div class="learned"><span class="lbl">Played in ${h.games} saved ${plural(h.games, "game", "games")}</span><span class="lplay">${esc(playedText(h, 6))}</span>` +
      (extra.length ? `<button class="btn small" id="pl-learn-${esc(p.id)}" data-act="pl-learn" data-id="${esc(p.id)}">Add ${esc(listText(extra))} to positions</button>` : "") + `</div>`;
  }
  function playerEditor(p) {
    const sid = esc(p.id); const conf = S.ui.confirm === "pl:" + p.id;
    const gamesFor = Array.from(S.games.values()).filter(g => g.order.some(e => e.p === p.id)).length;
    const cyc = FIELD.map(q => {
      const r = p.positions.indexOf(q), no = p.dnp.indexOf(q) >= 0;
      return `<button class="pcyc${r >= 0 ? " on" : ""}${r === 0 ? " first" : ""}${no ? " no" : ""}" id="cyc-${sid}-${q}" data-act="pl-cyc" data-id="${sid}" data-q="${q}" aria-label="${POSNAME[q]}: ${r >= 0 ? "plays, choice " + (r + 1) : no ? "do not play" : "not listed"}">${q}${r >= 0 ? `<sup>${r + 1}</sup>` : no ? "<sup>✕</sup>" : ""}</button>`;
    }).join("");
    return `<div class="ped"><div class="fields"><label class="fld">Name<input type="text" id="pl-name-${sid}" data-field="pl-name" data-id="${sid}" value="${esc(p.name)}" maxlength="80" autocomplete="off"></label>` +
      `<div class="fld narrow"><span>Sex</span><div class="seg sex" role="group" aria-label="Batter sex"><button class="m" id="sx-m-${sid}" data-act="pl-sex" data-id="${sid}" data-sex="M" aria-pressed="${p.sex === "M"}">M</button><button class="f" id="sx-f-${sid}" data-act="pl-sex" data-id="${sid}" data-sex="F" aria-pressed="${p.sex === "F"}">F</button></div></div>` +
      `<label class="fld narrow">Batting order<select id="pl-bat-${sid}" data-field="pl-bat" data-id="${sid}">${opts(1, 30, p.bat, "–")}</select></label>` +
      `<label class="fld narrow">Batting exp<select id="pl-bx-${sid}" data-field="pl-bx" data-id="${sid}">${opts(1, 5, p.batExp, "–")}</select></label>` +
      `<label class="fld narrow">Fielding exp<select id="pl-fx-${sid}" data-field="pl-fx" data-id="${sid}">${opts(1, 5, p.fieldExp, "–")}</select></label></div>` +
      `<div><div class="lbl">Positions · tap to cycle: plays (1 = primary) → do not play → off</div><div class="posgrid">${cyc}</div></div>` +
      learnedRow(p) +
      `<div><div class="lbl">Injury</div><div class="btnrow"><div class="seg" role="group" aria-label="Injury"><button id="pi-h-${sid}" data-act="pl-inj" data-id="${sid}" data-v="healthy" aria-pressed="${p.injury === "healthy"}">Healthy</button><button id="pi-l-${sid}" data-act="pl-inj" data-id="${sid}" data-v="limited" aria-pressed="${p.injury === "limited"}">Limited</button><button id="pi-b-${sid}" data-act="pl-inj" data-id="${sid}" data-v="batonly" aria-pressed="${p.injury === "batonly"}">Bat only</button></div>` +
      (p.injury === "limited" ? `<label class="fld narrow">Max innings<select id="pl-max-${sid}" data-field="pl-max" data-id="${sid}">${opts(1, 11, p.maxInnings)}</select></label>` : "") + `</div></div>` +
      `<div class="btnrow"><label class="sw"><input type="checkbox" id="pl-act-${sid}" data-field="pl-active" data-id="${sid}"${p.active ? " checked" : ""}> On the team (active)</label>` +
      `<button class="btn small ghost danger-text" data-act="confirm" data-what="pl:${sid}">Delete player</button></div>` +
      (conf ? `<div class="confirm" role="alert"><span>Delete ${esc(fullName(p))}?${gamesFor ? ` They appear in ${gamesFor} saved ${plural(gamesFor, "game", "games")}; those rows will show as Removed player. Unchecking active hides them instead.` : ""}</span><button class="btn small danger" data-act="pl-del-yes" data-id="${sid}">Delete</button><button class="btn small ghost" data-act="cancel-confirm">Keep</button></div>` : "") +
      `</div>`;
  }

  /* ---------- Actions ---------- */
  function guard() { if (!S.canWrite) { toast("This view is read-only."); return false; } return true; }
  function moveRow(g, from, to) { snap(g); const e = g.order.splice(from, 1)[0]; g.order.splice(to, 0, e); touch(g); S.focusId = "drag-" + e.p; render(); }
  function newPlayerId(name) { const base = slug(name) || "player"; let id = base; while (S.players.has(id) || S.deleted.has("players/" + id)) id = base + "-" + rid(3); return id; }
  function createGame() {
    if (!guard()) return;
    const ng = ngState(); const date = isDate(ng.date) ? ng.date : todayIso(); const n = S.settings.innings;
    const src = ng.from && ng.from !== "roster" ? S.games.get(ng.from) : null;
    const avail = Array.from(S.players.values()).filter(p => p.active && p.available);
    let order;
    if (src) order = src.order.filter(e => { const p = S.players.get(e.p); return p && p.active; }).map(e => ({ p: e.p, pos: fit(e.pos.map(x => x === "OUT" ? "" : x), n) }));
    else order = avail.map(p => ({ p: p.id, pos: fit([], n) }));
    if (!src && !order.length) { toast("Nobody is marked available. Tick players on the Roster tab first."); return; }
    let id = "g-" + date.replace(/-/g, "") + "-" + rid(4);
    while (S.games.has(id)) id = "g-" + date.replace(/-/g, "") + "-" + rid(4);
    const g = { id: id, date: date, opponent: (ng.opp || "").trim().slice(0, 80), innings: n, order: order, createdAt: new Date().toISOString() };
    if (ng.from === "roster") rebuild(g, -1);
    else if (!src) g.order = battingOrder(g.order, learnedBefore(g));
    S.games.set(id, g);
    save("games/" + id, 0);
    S.ui.newOpen = false; S.ui.ng = null; S.ui.inn = 0;
    location.hash = "game-" + id;
  }
  function addPlayer(src, toGame) {
    if (!guard()) return null;
    const name = (src.name || "").trim().replace(/\s+/g, " ").slice(0, 80); const sex = src.sex;
    if (!name) { toast("Type the player's name first, like Last, First."); return null; }
    if (sex !== "M" && sex !== "F") { toast("Pick M or F so the co-ed rules work."); return null; }
    if (Array.from(S.players.values()).some(p => p.name.toLowerCase() === name.toLowerCase())) { toast(name + " is already on the roster."); return null; }
    const id = newPlayerId(name);
    S.players.set(id, normPlayer(id, { name: name, sex: sex, active: true, available: !!toGame, positions: src.pos ? [src.pos] : [] }));
    save("players/" + id, 0);
    toast(fullName({ name: name }) + " added");
    return id;
  }
  function copy(text, label) {
    const done = () => { S.ui.copyText = null; toast(label + " copied"); render(); };
    const fail = () => { S.ui.copyText = text; S.ui.copyFocus = true; render(); toast("Copying is blocked here. Select the text below and copy it."); };
    try { const p = navigator.clipboard && navigator.clipboard.writeText(text); if (p && p.then) p.then(done, fail); else fail(); } catch (e) { fail(); }
  }
  function savePlayerDlg() {
    const d = S.ui.pd; const g = S.games.get(d.gid); const pl = S.players.get(d.pid);
    if (!g || !guard()) return;
    const idx = g.order.findIndex(e => e.p === d.pid); if (idx < 0) { S.ui.pd = null; render(); return; }
    let changed = false;
    if (pl && (pl.injury !== d.inj || (d.inj === "limited" && pl.maxInnings !== d.max))) { pl.injury = d.inj; if (d.inj === "limited") pl.maxInnings = d.max; save("players/" + pl.id); changed = true; }
    snap(g);
    const e = g.order[idx]; const wasGone = e.pos.indexOf("OUT");
    if (d.att === "gone") { g.order.splice(idx, 1); changed = true; }
    else if (d.att === "left") { e.pos = e.pos.map((p, i) => i >= d.after ? "OUT" : p === "OUT" ? "" : p); changed = true; }
    else { e.pos = e.pos.map(p => p === "OUT" ? "" : p); if (wasGone >= 0) changed = true; }
    touch(g);
    S.ui.pd = null;
    if (changed) { S.ui.rb = { gid: g.id, from: d.att === "left" ? Math.min(d.after, g.innings - 1) : Math.min(S.ui.inn, g.innings - 1) }; S.focusId = "rb-go"; }
    else { S.focusId = "pn-" + d.pid; toast("Saved"); }
    render();
  }

  document.addEventListener("click", ev => {
    if (S.suppressClick) { S.suppressClick = false; ev.preventDefault(); return; }
    const t = ev.target.closest("[data-act]"); if (!t) return;
    const act = t.dataset.act; const r = route();
    const g = r.id ? S.games.get(r.id) : null;
    switch (act) {
      case "new-open": if (!guard()) return; S.ui.newOpen = true; S.ui.ng = null; S.focusId = "ng-date"; render(); break;
      case "new-close": S.ui.newOpen = false; S.focusId = "btn-new"; render(); break;
      case "avail": if (!g || !guard()) return; snap(g); toggleAvail(g, t.dataset.pid); touch(g); S.focusId = t.id; render(); break;
      case "pick": {
        if (!g || !guard()) return;
        const i = +t.dataset.i; S.ui.pick = { gid: g.id, pid: t.dataset.pid, i: i }; S.ui.inn = i;
        S.focusId = pickFocusId(g, t.dataset.pid, i); render(); break;
      }
      case "set": {
        const pk = S.ui.pick; const gp = pk ? S.games.get(pk.gid) : null;
        if (!gp || !guard()) return;
        const idx = gp.order.findIndex(e => e.p === pk.pid); if (idx < 0) { closePick(); return; }
        snap(gp);
        const msg = assign(gp, idx, pk.i, t.dataset.pos); touch(gp);
        if (msg) toast(msg);
        if (prefs.auto && pk.i < gp.innings - 1) { pk.i++; S.ui.inn = pk.i; S.focusId = pickFocusId(gp, pk.pid, pk.i); render(); }
        else closePick();
        break;
      }
      case "pk-step": {
        const pk = S.ui.pick; const gp = pk ? S.games.get(pk.gid) : null; if (!gp) return;
        pk.i = Math.max(0, Math.min(gp.innings - 1, pk.i + Number(t.dataset.d))); S.ui.inn = pk.i;
        S.focusId = t.id; render(); break;
      }
      case "close-pick": closePick(); break;
      case "inn": S.ui.inn = +t.dataset.i; S.focusId = t.id || null; render(); break;
      case "undo": if (!g || !guard()) return; if (undo(g)) toast("Undone"); S.focusId = "btn-undo"; render(); break;
      case "rb-open": if (!g || !guard()) return; S.ui.rb = { gid: g.id, from: -1 }; S.focusId = "rb-go"; render(); break;
      case "rb-from": if (S.ui.rb) { S.ui.rb.from = +t.dataset.f; S.focusId = t.id; render(); } break;
      case "rb-close": S.ui.rb = null; S.focusId = "btn-rebuild"; render(); break;
      case "rb-go": {
        const rb = S.ui.rb; const gg = rb ? S.games.get(rb.gid) : null; if (!gg || !guard()) return;
        snap(gg); rebuild(gg, rb.from); touch(gg); S.ui.rb = null;
        const A2 = analyze(gg);
        toast(A2.fails ? `Rebuilt. ${A2.fails} rule ${plural(A2.fails, "issue", "issues")} left; see Checks.` : rb.from < 0 ? "Rebuilt the whole game. Undo brings the old lineup back." : `Rebuilt innings ${rb.from + 1}-${gg.innings}.`);
        S.focusId = "btn-rebuild"; render(); break;
      }
      case "pd-open": {
        if (!g || !guard()) return;
        const pl = S.players.get(t.dataset.pid); const e = g.order.find(x => x.p === t.dataset.pid); if (!e) return;
        const k = e.pos.indexOf("OUT");
        S.ui.pd = { gid: g.id, pid: t.dataset.pid, inj: pl ? pl.injury : "healthy", max: pl ? pl.maxInnings : 3, att: k >= 0 ? "left" : "here", after: k > 0 ? k : Math.max(1, Math.min(S.ui.inn + 1, g.innings - 1)) };
        S.focusId = "pd-save"; render(); break;
      }
      case "pd-inj": if (S.ui.pd) { S.ui.pd.inj = t.dataset.v; S.focusId = t.id; render(); } break;
      case "pd-max": if (S.ui.pd) { const gg = S.games.get(S.ui.pd.gid); S.ui.pd.max = Math.max(1, Math.min((gg ? gg.innings : 6) - 1, S.ui.pd.max + Number(t.dataset.d))); S.focusId = t.id; render(); } break;
      case "pd-att": if (S.ui.pd) { S.ui.pd.att = t.dataset.v; S.focusId = t.id; render(); } break;
      case "pd-close": { const d = S.ui.pd; S.ui.pd = null; if (d) S.focusId = "pn-" + d.pid; render(); break; }
      case "pd-save": savePlayerDlg(); break;
      case "qa-open": if (!guard()) return; S.ui.qa = { name: "", sex: "", pos: "" }; S.focusId = "qa-name"; render(); break;
      case "qa-close": S.ui.qa = null; S.focusId = "btn-qa"; render(); break;
      case "qa-sex": if (S.ui.qa) { S.ui.qa.sex = t.dataset.sex; S.focusId = t.id; render(); } break;
      case "confirm": if (!guard()) return; S.ui.confirm = t.dataset.what; render(); break;
      case "cancel-confirm": S.ui.confirm = null; render(); break;
      case "clear-yes": if (!g || !guard()) return; snap(g); g.order.forEach(e => { e.pos = e.pos.map(p => p === "OUT" ? "OUT" : ""); }); S.ui.confirm = null; touch(g); toast("Positions cleared. Undo brings them back."); render(); break;
      case "del-yes": if (!g || !guard()) return; S.games.delete(g.id); S.ui.confirm = null; removeDoc("games/" + g.id); toast("Game deleted"); location.hash = "games"; break;
      case "copy-text": { const gg = S.games.get(t.dataset.gid) || g; if (gg) copy(chatText(gg), "Lineup text"); break; }
      case "copy-tsv": { const gg = S.games.get(t.dataset.gid) || g; if (gg) copy(sheetTsv(gg), "Sheet rows"); break; }
      case "print": { const gg = S.games.get(t.dataset.gid) || g; if (gg) printCard(gg); break; }
      case "pl-open": S.ui.openPl = S.ui.openPl === t.dataset.id ? null : t.dataset.id; S.ui.confirm = null; S.focusId = t.id; render(); break;
      case "pl-sex": { if (!guard()) return; const p = S.players.get(t.dataset.id); if (!p) return; p.sex = t.dataset.sex; save("players/" + p.id); S.focusId = t.id; render(); break; }
      case "pl-inj": { if (!guard()) return; const p = S.players.get(t.dataset.id); if (!p) return; p.injury = t.dataset.v; save("players/" + p.id); S.focusId = t.id; render(); break; }
      case "pl-cyc": {
        if (!guard()) return; const p = S.players.get(t.dataset.id); const q = t.dataset.q; if (!p) return;
        if (p.positions.indexOf(q) >= 0) { p.positions = p.positions.filter(x => x !== q); p.dnp.push(q); }
        else if (p.dnp.indexOf(q) >= 0) p.dnp = p.dnp.filter(x => x !== q);
        else p.positions.push(q);
        save("players/" + p.id); S.focusId = t.id; render(); break;
      }
      case "pl-learn": {
        if (!guard()) return; const p = S.players.get(t.dataset.id); const h = p && learnedAll().H[p.id]; if (!p || !h) return;
        const extra = Object.keys(h.raw).filter(q => h.raw[q] >= 2 && p.positions.indexOf(q) < 0 && p.dnp.indexOf(q) < 0).sort((a, b) => h.raw[b] - h.raw[a]);
        p.positions = p.positions.concat(extra).slice(0, 10); save("players/" + p.id); toast(`Added ${listText(extra)} to ${fullName(p)}'s positions`);
        S.focusId = "pl-open-" + p.id; render(); break;
      }
      case "pl-del-yes": { if (!guard()) return; const p = S.players.get(t.dataset.id); if (!p) return; S.players.delete(p.id); S.ui.confirm = null; S.ui.openPl = null; removeDoc("players/" + p.id); toast(fullName(p) + " deleted"); render(); break; }
      case "copy-team": copy(location.origin + location.pathname, "Team link"); break;
      case "copy-captain": if (captainKey) copy(location.origin + location.pathname + "#key=" + captainKey, "Captain link"); break;
      case "lock": forgetKey(); S.canWrite = false; toast("Captain mode is off on this device."); location.hash = "games"; render(); break;
      case "np-sex": S.ui.np.sex = t.dataset.sex; S.focusId = t.id; render(); break;
    }
  });

  document.addEventListener("input", ev => {
    const el = ev.target; const f = el.dataset && el.dataset.field; if (!f) return;
    const r = route(); const g = r.v === "game" ? S.games.get(r.id) : null;
    switch (f) {
      case "g-opp": if (g && S.canWrite) { g.opponent = el.value.slice(0, 80); touch(g); } break;
      case "ng-date": ngState().date = el.value; break;
      case "ng-opp": ngState().opp = el.value; break;
      case "np-name": S.ui.np.name = el.value; break;
      case "qa-name": if (S.ui.qa) S.ui.qa.name = el.value; break;
      case "pl-name": { const p = S.players.get(el.dataset.id); if (p && S.canWrite) { p.name = el.value.slice(0, 80); save("players/" + p.id, 700); } break; }
      case "set-team": if (S.canWrite) { S.settings.teamName = el.value.slice(0, 60); save("team/settings", 700); const b = document.querySelector(".brand span"); if (b) b.innerHTML = brandHtml(); } break;
    }
  });

  document.addEventListener("change", ev => {
    const el = ev.target; const f = el.dataset && el.dataset.field; if (!f) return;
    const r = route(); const g = r.v === "game" ? S.games.get(r.id) : null;
    const pl = el.dataset.id ? S.players.get(el.dataset.id) : null;
    const setNum = (k, lo, hi, def) => { if (guard()) { S.settings[k] = clampInt(el.value, lo, hi, def); save("team/settings"); render(); } };
    switch (f) {
      case "g-date": if (g && guard() && isDate(el.value)) { g.date = el.value; touch(g); } break;
      case "g-inn": if (g && guard()) { snap(g); const n = clampInt(el.value, 3, 12, g.innings); g.innings = n; g.order.forEach(e => { e.pos = fit(e.pos, n); }); if (S.ui.inn >= n) S.ui.inn = n - 1; touch(g); render(); } break;
      case "ng-from": ngState().from = el.value; break;
      case "ng-date": ngState().date = el.value; break;
      case "qa-pos": if (S.ui.qa) S.ui.qa.pos = el.value; break;
      case "np-pos": S.ui.np.pos = el.value; break;
      case "set-innings": setNum("innings", 3, 12, 6); break;
      case "set-maxmen": setNum("maxMenInRow", 1, 12, 3); break;
      case "set-minw": setNum("minWomenOnField", 0, 10, 3); break;
      case "set-maxsits": setNum("maxSits", 0, 12, 2); break;
      case "set-strategy": if (guard()) { S.settings.sitStrategy = el.value === "experience" ? "experience" : "even"; save("team/settings"); render(); } break;
      case "set-wrap": if (guard()) { S.settings.wrapOrder = el.checked; save("team/settings"); render(); } break;
      case "set-hist": setNum("histWeight", 0, 3, 2); break;
      case "ss-since": if (isDate(el.value) || el.value === "") { if (S.canWrite) { S.settings.seasonStart = el.value; S.ui.since = ""; save("team/settings"); } else S.ui.since = el.value; render(); } break;
      case "ss-sort": S.ui.sort = el.value; render(); break;
      case "pl-avail": if (pl && guard()) { pl.available = el.checked; save("players/" + pl.id); render(); } break;
      case "pl-active": if (pl && guard()) { pl.active = el.checked; save("players/" + pl.id); render(); } break;
      case "pl-bat": if (pl && guard()) { pl.bat = clampInt(el.value, 0, 99, 0); save("players/" + pl.id); render(); } break;
      case "pl-bx": if (pl && guard()) { pl.batExp = clampInt(el.value, 0, 5, 0); save("players/" + pl.id); render(); } break;
      case "pl-fx": if (pl && guard()) { pl.fieldExp = clampInt(el.value, 0, 5, 0); save("players/" + pl.id); render(); } break;
      case "pl-max": if (pl && guard()) { pl.maxInnings = clampInt(el.value, 1, 12, 3); save("players/" + pl.id); render(); } break;
      case "pd-after": if (S.ui.pd) S.ui.pd.after = clampInt(el.value, 1, 11, 1); break;
      case "pk-auto": prefs.auto = el.checked; savePrefs(); break;
    }
  });

  document.addEventListener("submit", ev => {
    ev.preventDefault();
    if (ev.target.id === "newform") createGame();
    else if (ev.target.id === "addform") {
      if (addPlayer(S.ui.np, false)) { S.ui.np = { name: "", sex: "", pos: "" }; S.focusId = "np-name"; render(); }
    } else if (ev.target.id === "qaform") {
      const g = S.games.get(route().id); if (!g || !S.ui.qa) return;
      const id = addPlayer(S.ui.qa, true);
      if (id) { snap(g); g.order.push({ p: id, pos: fit([], g.innings) }); touch(g); S.ui.qa = null; S.focusId = "pn-" + id; render(); }
    }
  });

  document.addEventListener("keydown", ev => {
    if (ev.key === "Escape") {
      if (S.ui.rb) { ev.preventDefault(); S.ui.rb = null; S.focusId = "btn-rebuild"; render(); return; }
      if (S.ui.pd) { ev.preventDefault(); const d = S.ui.pd; S.ui.pd = null; S.focusId = "pn-" + d.pid; render(); return; }
      if (S.ui.pick) { ev.preventDefault(); closePick(); return; }
    }
    const h = ev.target.closest && ev.target.closest("[data-drag]");
    if (h && (ev.key === "ArrowUp" || ev.key === "ArrowDown")) {
      ev.preventDefault();
      const g = S.games.get(route().id); if (!g || !guard()) return;
      const from = +h.dataset.drag; const to = from + (ev.key === "ArrowUp" ? -1 : 1);
      if (to >= 0 && to < g.order.length) moveRow(g, from, to);
    }
  });

  /* Drag: batting order by the number handle (mouse, pen, touch); swap two badges in one inning (mouse, pen) */
  document.addEventListener("pointerdown", ev => {
    S.pointerDown = true;
    if (!S.canWrite) return;
    const h = ev.target.closest && ev.target.closest("[data-drag]");
    const cell = !h && ev.target.closest && ev.target.closest(".cell[data-act='pick']");
    if (cell && ev.pointerType !== "touch" && ev.button === 0) { startCellDrag(ev, cell); return; }
    if (!h || (ev.pointerType === "mouse" && ev.button !== 0)) return;
    const g = S.games.get(route().id); if (!g) return;
    const tr = h.closest("tr"); const rows = Array.from(tr.parentElement.children);
    const from = rows.indexOf(tr); const rects = rows.map(x => x.getBoundingClientRect());
    const startY = ev.clientY; const hgt = rects[from].height + 3;
    let to = from, moved = false;
    S.dragging = true; tr.classList.add("dragging");
    try { h.setPointerCapture(ev.pointerId); } catch (e) { /* capture unsupported */ }
    const onMove = e => {
      const dy = e.clientY - startY; if (Math.abs(dy) > 4) moved = true;
      tr.style.transform = `translateY(${dy}px)`;
      const mid = rects[from].top + rects[from].height / 2 + dy;
      to = 0; rects.forEach((rc, j) => { if (j !== from && mid > rc.top + rc.height / 2) to++; });
      rows.forEach((row, j) => {
        if (j === from) return;
        const shift = (from < to && j > from && j <= to) ? -hgt : (from > to && j >= to && j < from) ? hgt : 0;
        row.style.transform = shift ? `translateY(${shift}px)` : "";
      });
      e.preventDefault();
    };
    const onUp = () => {
      h.removeEventListener("pointermove", onMove); h.removeEventListener("pointerup", onUp); h.removeEventListener("pointercancel", onUp);
      rows.forEach(row => { row.style.transform = ""; }); tr.classList.remove("dragging");
      S.dragging = false; S.pointerDown = false;
      if (moved && to !== from) moveRow(g, from, to); else if (S.needRender) render();
    };
    h.addEventListener("pointermove", onMove); h.addEventListener("pointerup", onUp); h.addEventListener("pointercancel", onUp);
  }, true);
  function startCellDrag(ev, cell) {
    const g = S.games.get(route().id); if (!g) return;
    const i = +cell.dataset.i; const sx = ev.clientX, sy = ev.clientY; let moved = false, target = null;
    const onMove = e => {
      if (!moved && Math.hypot(e.clientX - sx, e.clientY - sy) < 6) return;
      if (!moved) { moved = true; S.dragging = true; cell.classList.add("lift"); }
      const el = document.elementFromPoint(e.clientX, e.clientY);
      const c = el && el.closest && el.closest(".cell[data-act='pick']");
      const ok = c && c !== cell && +c.dataset.i === i ? c : null;
      if (ok !== target) { if (target) target.classList.remove("drop"); target = ok; if (target) target.classList.add("drop"); }
    };
    const onUp = () => {
      document.removeEventListener("pointermove", onMove, true); document.removeEventListener("pointerup", onUp, true); document.removeEventListener("pointercancel", onUp, true);
      if (!moved) return;
      S.suppressClick = true; setTimeout(() => { S.suppressClick = false; }, 0);
      cell.classList.remove("lift"); if (target) target.classList.remove("drop");
      S.dragging = false; S.pointerDown = false;
      if (target) {
        const a = g.order.findIndex(e => e.p === cell.dataset.pid), b = g.order.findIndex(e => e.p === target.dataset.pid);
        if (a >= 0 && b >= 0) {
          snap(g);
          const pa = g.order[a].pos[i]; g.order[a].pos[i] = g.order[b].pos[i]; g.order[b].pos[i] = pa;
          touch(g); S.ui.inn = i; toast(`Swapped in inning ${i + 1}`);
        }
      }
      render();
    };
    document.addEventListener("pointermove", onMove, true); document.addEventListener("pointerup", onUp, true); document.addEventListener("pointercancel", onUp, true);
  }
  document.addEventListener("pointerup", () => { S.pointerDown = false; flushDeferred(); }, true);
  document.addEventListener("pointercancel", () => { S.pointerDown = false; flushDeferred(); }, true);
  document.addEventListener("focusout", flushDeferred);

  window.addEventListener("hashchange", () => {
    if (takeKey()) { S.canWrite = true; checkKey(true); return; }
    S.ui.pick = null; S.ui.confirm = null; S.ui.copyText = null; S.ui.newOpen = false; S.ui.rb = null; S.ui.pd = null; S.ui.qa = null;
    render(); window.scrollTo(0, 0);
  });

  let toastT = 0;
  function toast(msg) { const el = document.getElementById("toast"); el.textContent = msg; el.classList.add("show"); clearTimeout(toastT); toastT = setTimeout(() => el.classList.remove("show"), 3000); }

  boot();
})();
