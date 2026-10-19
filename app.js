'use strict';
/* AutoPad by Friesengroup - Web-Version (Android / iPhone / iPad / PC)
   Web Audio für Pads + Click (mit Stereo-Split), Web MIDI für Fußschalter. */
(function () {

// ---------------------------------------------------------------------------
// Musik-Daten
// ---------------------------------------------------------------------------
const NOTES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
const FLAT = ['C', 'Db', 'D', 'Eb', 'E', 'F', 'Gb', 'G', 'Ab', 'A', 'Bb', 'B'];
const BASE_C = 130.8128;                                  // C3
const MAJOR_IV = [[0, 1]];                                // reiner Grundton
const MINOR_IV = [[0, 1], [3, 0.55], [7, 0.45]];          // Grundton + kleine Terz + Quinte

const KEY_TABLE = {};
[NOTES, FLAT].forEach(names => names.forEach((n, i) => { KEY_TABLE[n] = [i, false]; KEY_TABLE[n + 'm'] = [i, true]; }));
const KEY_LIST = (() => {
  const maj = [], min = [];
  for (let i = 0; i < 12; i++) new Set([NOTES[i], FLAT[i]]).forEach(n => { maj.push(n); min.push(n + 'm'); });
  return maj.concat(min);
})();

const PAD_PAGES = [
  { name: 'Dur', items: NOTES.map((n, i) => [n, i, false]) },
  { name: 'Dur ♭', items: FLAT.map((n, i) => [n, i, false]) },
  { name: 'Moll', items: ['C', 'C#', 'D', 'Eb', 'E', 'F', 'F#', 'G', 'G#', 'A', 'Bb', 'B'].map((n, i) => [n + 'm', i, true]) },
];

const saw = (n, p, sub) => { const a = []; for (let k = 1; k <= n; k++) a.push([k, 1 / Math.pow(k, p)]); if (sub) a.push([0.5, sub]); return a; };
const odd = (n, p, sub) => { const a = []; for (let k = 1; k <= n; k += 2) a.push([k, 1 / Math.pow(k, p)]); if (sub) a.push([0.5, sub]); return a; };

// partials = [Frequenzverhältnis, Amplitude]; layers = Detune in Cent
const SOUNDS = {
  'Default':       { partials: [[0.5, 0.45], [1, 1], [2, 0.35], [3, 0.18], [4, 0.08]], layers: [-5, 5] },
  'Analog Sine':   { partials: [[0.5, 0.5], [1, 1], [2, 0.12]], layers: [-3, 3] },
  'Cathedral':     { partials: [[0.5, 0.6], [1, 1], [2, 0.55], [3, 0.35], [4, 0.2], [6, 0.1]], layers: [-9, 0, 9], reverb_boost: 0.25 },
  'Clean Organ':   { partials: [[0.5, 0.7], [1, 1], [2, 0.8], [3, 0.5], [4, 0.4], [6, 0.25], [8, 0.2]], layers: [0] },
  'Dark Analog':   { partials: saw(8, 1.8, 0.7), layers: [-7, 7] },
  'Dark Uno':      { partials: saw(10, 1.4, 1.0), layers: [-4, 0, 4] },
  'Resonant':      { partials: [[0.5, 0.3], [1, 0.8], [2, 0.5], [3, 0.7], [4, 1], [5, 0.6], [6, 0.3]], layers: [-6, 6] },
  'Soft Square':   { partials: odd(11, 1.2, 0.4), layers: [-4, 4] },
  'Strings':       { partials: saw(12, 1.1, 0.3), layers: [-12, -4, 4, 12] },
  'Triangle Core': { partials: odd(9, 2.0, 0.6), layers: [-3, 3] },
};
const SOUND_NAMES = Object.keys(SOUNDS);
const CLICK_NAMES = ['Block', 'Beep', 'Holz', 'Hi-Hat', 'Cowbell'];

const ROUTES = {
  click_left: 'Click links   ·   Pads rechts',
  pads_left: 'Pads links   ·   Click rechts',
  stereo: 'Beides auf L + R (Stereo-Mix)',
};

const DEFAULT_CFG = {
  crossfade: 0.3, lowpass: 1.0, highpass: 0.0, reverb: 0.2, pad_volume: 0.8,
  click_enabled: false, click_sound: 'Block', tempo: 100, subdiv: 4, click_volume: 0.8,
  routing: 'click_left', sound: 'Default', favorites: [], pads_enabled: true,
  midi: { next: null, prev: null, stop: null, pcDirect: false },
};

const clamp = (v, a, b) => Math.min(b, Math.max(a, v));

// ---------------------------------------------------------------------------
// Audio-Engine
// ---------------------------------------------------------------------------
class Engine {
  constructor() {
    this.ctx = null; this.cfg = null;
    this.active = null;            // [note, minor] oder null  -> "läuft" / "läuft nicht"
    this.voices = []; this.waves = {};
    this.clickBufs = null; this.nextClick = 0; this.clickPos = 0; this.clickWasOn = false;
    this.sched = []; this.timer = null; this.routed = null;
    this.onChange = null;
  }

  // Audio-Graph aufbauen (ctx kann auch ein OfflineAudioContext sein -> Tests)
  setContext(ctx) {
    this.ctx = ctx;
    this.waves = {};
    this.padBus = ctx.createGain();
    this.lp = ctx.createBiquadFilter(); this.lp.type = 'lowpass'; this.lp.Q.value = 0.707;
    this.hp = ctx.createBiquadFilter(); this.hp.type = 'highpass'; this.hp.Q.value = 0.707;
    this.dry = ctx.createGain(); this.wet = ctx.createGain();
    this.conv = ctx.createConvolver(); this.conv.buffer = this.makeIR(ctx);
    this.padOut = ctx.createGain(); this.padVol = ctx.createGain();
    this.padVol.channelCount = 1; this.padVol.channelCountMode = 'explicit';
    this.padBus.connect(this.lp); this.lp.connect(this.hp);
    this.hp.connect(this.dry); this.hp.connect(this.conv); this.conv.connect(this.wet);
    this.dry.connect(this.padOut); this.wet.connect(this.padOut); this.padOut.connect(this.padVol);
    this.clickBus = ctx.createGain(); this.clickVol = ctx.createGain();
    this.clickVol.channelCount = 1; this.clickVol.channelCountMode = 'explicit';
    this.clickBus.connect(this.clickVol);
    this.merger = ctx.createChannelMerger(2);
    this.master = ctx.createGain(); this.master.gain.value = 0.9;
    this.merger.connect(this.master); this.master.connect(ctx.destination);
    this.clickBufs = this.makeClicks(ctx);
    this.routed = null;
    if (this.cfg) this.applyParams();
  }

  // Im Browser: AudioContext beim ersten Tippen erzeugen
  ensure() {
    if (!this.ctx) {
      const AC = window.AudioContext || window.webkitAudioContext;
      this.setContext(new AC({ latencyHint: 'interactive' }));
      this.timer = setInterval(() => this.tick(), 25);
    }
    if (this.ctx.state !== 'running' && this.ctx.resume) this.ctx.resume();
  }

  makeIR(ctx) {
    const sr = ctx.sampleRate, len = Math.floor(sr * 2.4);
    const buf = ctx.createBuffer(1, len, sr), d = buf.getChannelData(0);
    let seed = 12345, lpv = 0;
    for (let i = 0; i < len; i++) {
      seed = (seed * 1664525 + 1013904223) >>> 0;
      const noise = (seed / 4294967296) * 2 - 1;
      lpv += 0.45 * (noise - lpv);                        // etwas dunkler
      d[i] = lpv * Math.pow(1 - i / len, 2.6);
    }
    return buf;
  }

  makeClicks(ctx) {
    const sr = ctx.sampleRate;
    const tone = (f, dur, dec, shape) => {
      const n = Math.floor(dur * sr), a = new Float32Array(n);
      for (let i = 0; i < n; i++) {
        const t = i / sr, ph = 2 * Math.PI * f * t;
        const w = shape === 'square' ? Math.sign(Math.sin(ph)) * 0.6 : Math.sin(ph);
        let env = Math.exp(-t / dec); if (i < 40) env *= i / 40;
        a[i] = w * env;
      }
      return a;
    };
    const hat = (dur, dec, gain) => {
      const n = Math.floor(dur * sr), a = new Float32Array(n);
      let seed = 1, prev = 0;
      for (let i = 0; i < n; i++) {
        seed = (seed * 1664525 + 1013904223) >>> 0;
        const x = (seed / 4294967296) * 2 - 1;
        a[i] = (x - prev) * Math.exp(-(i / sr) / dec) * 0.5 * gain; prev = x;
      }
      return a;
    };
    const mix = (...parts) => { const n = Math.max(...parts.map(p => p[0].length)); const o = new Float32Array(n);
      parts.forEach(([arr, g]) => { for (let i = 0; i < arr.length; i++) o[i] += arr[i] * g; }); return o; };
    const buf = arr => { const b = ctx.createBuffer(1, arr.length, sr); b.getChannelData(0).set(arr); return b; };
    return {
      'Block':   [buf(tone(900, .06, .012)), buf(tone(1350, .06, .012))],
      'Beep':    [buf(tone(1000, .08, .03)), buf(tone(1500, .08, .03))],
      'Holz':    [buf(mix([tone(600, .07, .015), 1], [tone(1200, .07, .008), .5])), buf(mix([tone(800, .07, .015), 1], [tone(1600, .07, .008), .5]))],
      'Hi-Hat':  [buf(hat(.05, .012, .6)), buf(hat(.07, .02, 1))],
      'Cowbell': [buf(mix([tone(540, .15, .05, 'square'), .5], [tone(810, .15, .05, 'square'), .5])), buf(mix([tone(640, .15, .05, 'square'), .6], [tone(960, .15, .05, 'square'), .6]))],
    };
  }

  waveFor(name) {
    if (this.waves[name]) return this.waves[name];
    const s = SOUNDS[name];
    let maxK = 1; s.partials.forEach(([r]) => { if (r >= 1 && r > maxK) maxK = r; });
    const real = new Float32Array(maxK + 1), imag = new Float32Array(maxK + 1);
    s.partials.forEach(([r, a]) => { if (r >= 1) imag[r] = a; });
    return (this.waves[name] = this.ctx.createPeriodicWave(real, imag, { disableNormalization: true }));
  }

  // Alle Regler-Werte in den Audio-Graph übertragen
  applyParams() {
    if (!this.ctx || !this.cfg) return;
    const c = this.cfg, t = this.ctx.currentTime, tc = 0.03;
    const lp = c.lowpass, hp = c.highpass;
    this.lp.frequency.setTargetAtTime(lp >= 0.98 ? 20000 : 200 * Math.pow(60, lp), t, tc);
    this.hp.frequency.setTargetAtTime(hp < 0.02 ? 10 : 20 * Math.pow(75, hp), t, tc);
    const boost = (SOUNDS[c.sound] || {}).reverb_boost || 0;
    const rv = clamp(c.reverb + boost, 0, 1);
    this.wet.gain.setTargetAtTime(rv * 1.1, t, tc);
    this.dry.gain.setTargetAtTime(1 - 0.35 * rv, t, tc);
    this.padVol.gain.setTargetAtTime(c.pads_enabled ? c.pad_volume * c.pad_volume : 0, t, tc);
    this.clickVol.gain.setTargetAtTime(c.click_volume * c.click_volume, t, tc);
    if (this.routed !== c.routing) this.rewire(c.routing);
  }

  // Stereo-Routing: Kanal 0 = links, Kanal 1 = rechts
  rewire(mode) {
    this.padVol.disconnect(); this.clickVol.disconnect();
    if (mode === 'click_left') { this.clickVol.connect(this.merger, 0, 0); this.padVol.connect(this.merger, 0, 1); }
    else if (mode === 'pads_left') { this.padVol.connect(this.merger, 0, 0); this.clickVol.connect(this.merger, 0, 1); }
    else { [0, 1].forEach(i => { this.padVol.connect(this.merger, 0, i); this.clickVol.connect(this.merger, 0, i); }); }
    this.routed = mode;
  }

  fadeTime() { return 0.05 + Math.pow(this.cfg.crossfade, 2) * 10; }

  makeVoice(key, soundName) {
    const ctx = this.ctx, s = SOUNDS[soundName];
    const ivs = key[1] ? MINOR_IV : MAJOR_IV;
    const totalG = ivs.reduce((x, iv) => x + iv[1], 0);
    const sumA = s.partials.reduce((x, p) => x + p[1], 0);
    const subAmp = s.partials.filter(p => p[0] < 1).reduce((x, p) => x + p[1], 0);
    const norm = 1 / (sumA * s.layers.length * Math.sqrt(totalG));
    const wave = this.waveFor(soundName);
    const out = ctx.createGain(); out.gain.value = 0;
    const oscs = [];
    ivs.forEach(([st, g], ii) => {
      const f = BASE_C * Math.pow(2, (key[0] + st) / 12);
      s.layers.forEach(cents => {
        const o = ctx.createOscillator(); o.setPeriodicWave(wave); o.frequency.value = f; o.detune.value = cents;
        const gn = ctx.createGain(); gn.gain.value = g * norm; o.connect(gn); gn.connect(out); oscs.push(o);
        if (ii === 0 && subAmp > 0) {                      // Sub-Oktave nur auf dem Grundton
          const o2 = ctx.createOscillator(); o2.type = 'sine'; o2.frequency.value = f / 2; o2.detune.value = cents;
          const g2 = ctx.createGain(); g2.gain.value = g * norm * subAmp; o2.connect(g2); g2.connect(out); oscs.push(o2);
        }
      });
    });
    out.connect(this.padBus);
    oscs.forEach(o => o.start());
    return { key, sound: soundName, out, oscs, target: 1, g0: 0, g1: 1, t0: 0, t1: 0 };
  }

  gainAt(v, t) {
    if (t >= v.t1) return v.g1;
    if (t <= v.t0) return v.g0;
    return v.g0 + (v.g1 - v.g0) * (t - v.t0) / (v.t1 - v.t0);
  }

  fadeOut(v, t, fade) {
    if (v.target === 0) return;
    const g = this.gainAt(v, t), dur = g * fade + 0.01;
    v.out.gain.cancelScheduledValues(t);
    v.out.gain.setValueAtTime(g, t);
    v.out.gain.linearRampToValueAtTime(0, t + dur);
    v.target = 0; v.g0 = g; v.g1 = 0; v.t0 = t; v.t1 = t + dur;
    const stopAt = t + dur + 0.05;
    v.oscs.forEach(o => { try { o.stop(stopAt); } catch (e) {} });
    v.oscs[0].onended = () => { try { v.out.disconnect(); } catch (e) {} this.voices = this.voices.filter(x => x !== v); };
  }

  play(key, retrigger) {
    if (!this.ctx) return;
    const t = this.ctx.currentTime, fade = this.fadeTime();
    let keep = false;
    for (const v of this.voices.slice()) {
      if (v.key[0] === key[0] && v.key[1] === key[1] && v.sound === this.cfg.sound && v.target > 0 && !retrigger) keep = true;
      else this.fadeOut(v, t, fade);
    }
    if (!keep) {
      const v = this.makeVoice(key, this.cfg.sound);
      v.out.gain.setValueAtTime(0, t); v.out.gain.linearRampToValueAtTime(1, t + fade);
      v.g0 = 0; v.g1 = 1; v.t0 = t; v.t1 = t + fade;
      this.voices.push(v);
    }
    this.active = [key[0], key[1]];
    this.applyParams();
    if (this.onChange) this.onChange();
  }

  stop() {
    if (this.ctx) {
      const t = this.ctx.currentTime, fade = this.fadeTime();
      this.voices.slice().forEach(v => this.fadeOut(v, t, fade));
      this.cancelClicks();
    }
    this.active = null;
    this.clickWasOn = false;
    if (this.onChange) this.onChange();
  }

  cancelClicks() {
    const now = this.ctx.currentTime;
    this.sched.forEach(s => { if (s.t > now) { try { s.src.stop(); } catch (e) {} } });
    this.sched = [];
  }

  // Click-Scheduler (läuft alle 25 ms, plant ~120 ms voraus -> sample-genau)
  tick(nowOverride) {
    if (!this.ctx || !this.cfg) return;
    const c = this.cfg, now = nowOverride != null ? nowOverride : this.ctx.currentTime;
    // Der Click läuft NUR, solange Pads laufen (ein Pad aktiv ist)
    const on = !!c.click_enabled && this.active !== null;
    if (on) {
      if (!this.clickWasOn) { this.nextClick = this.ctx.currentTime + 0.06; this.clickPos = 0; }
      const interval = 60 / Math.max(20, c.tempo), subdiv = Math.max(1, c.subdiv | 0);
      const bufs = this.clickBufs[c.click_sound] || this.clickBufs['Block'];
      while (this.nextClick < now + 0.12) {
        const src = this.ctx.createBufferSource();
        src.buffer = bufs[this.clickPos % subdiv === 0 ? 1 : 0];
        src.connect(this.clickBus);
        const at = Math.max(this.nextClick, this.ctx.currentTime);
        src.start(at);
        this.sched.push({ src, t: at });
        this.clickPos = (this.clickPos + 1) % subdiv;
        this.nextClick += interval;
      }
      this.sched = this.sched.filter(s => s.t > this.ctx.currentTime - 0.3);
    } else if (this.clickWasOn) {
      this.cancelClicks();
    }
    this.clickWasOn = on;
  }
}

// ---------------------------------------------------------------------------
// App-Zustand + Speicher
// ---------------------------------------------------------------------------
const store = {
  get(k, d) { try { const v = localStorage.getItem('autopad.' + k); return v ? JSON.parse(v) : d; } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem('autopad.' + k, JSON.stringify(v)); } catch (e) {} },
};

const state = {
  cfg: Object.assign({}, DEFAULT_CFG, store.get('cfg', {})),
  songs: [], setlistName: '', currentSong: null,
  padPage: 0, activeLabel: '', screen: 'live', lastMain: 'live',
};
state.cfg.midi = Object.assign({}, DEFAULT_CFG.midi, state.cfg.midi || {});
{ const cur = store.get('current', { name: '', songs: [] }); state.songs = cur.songs || []; state.setlistName = cur.name || ''; }

const engine = new Engine();
engine.cfg = state.cfg;

const $ = s => document.querySelector(s);
const $$ = s => Array.from(document.querySelectorAll(s));
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const saveCfg = () => store.set('cfg', state.cfg);
const saveSongs = () => store.set('current', { name: state.setlistName, songs: state.songs });

function toast(msg) {
  const t = $('#toast'); t.textContent = msg; t.classList.add('show');
  clearTimeout(toast._t); toast._t = setTimeout(() => t.classList.remove('show'), 2200);
}

// iOS: Stummschalter umgehen + Bildschirm wach halten
let silentEl = null, wakeLock = null;
function silentWavURL() {
  const sr = 8000, n = sr, buf = new ArrayBuffer(44 + n), v = new DataView(buf);
  const w = (o, s) => { for (let i = 0; i < s.length; i++) v.setUint8(o + i, s.charCodeAt(i)); };
  w(0, 'RIFF'); v.setUint32(4, 36 + n, true); w(8, 'WAVE'); w(12, 'fmt '); v.setUint32(16, 16, true);
  v.setUint16(20, 1, true); v.setUint16(22, 1, true); v.setUint32(24, sr, true); v.setUint32(28, sr, true);
  v.setUint16(32, 1, true); v.setUint16(34, 8, true); w(36, 'data'); v.setUint32(40, n, true);
  for (let i = 0; i < n; i++) v.setUint8(44 + i, 128);
  return URL.createObjectURL(new Blob([buf], { type: 'audio/wav' }));
}
async function keepAwake() {
  try { if ('wakeLock' in navigator && !wakeLock) { wakeLock = await navigator.wakeLock.request('screen'); wakeLock.addEventListener('release', () => { wakeLock = null; }); } } catch (e) {}
}
function unlockAudio() {
  engine.ensure();
  try {
    if (!silentEl) { silentEl = new Audio(silentWavURL()); silentEl.loop = true; silentEl.setAttribute('playsinline', ''); }
    if (silentEl.paused) silentEl.play().catch(() => {});
  } catch (e) {}
  keepAwake();
}
document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'visible') { keepAwake(); if (engine.ctx && engine.ctx.state !== 'running') engine.ctx.resume(); } });

function setParam(key, val) {
  state.cfg[key] = val; saveCfg();
  if (key === 'sound') { if (engine.ctx && engine.active) engine.play(engine.active, true); }
  engine.applyParams();
}

// ---------------------------------------------------------------------------
// Live: Pads
// ---------------------------------------------------------------------------
function renderPageSel() {
  $('#pageSel').innerHTML = PAD_PAGES.map((p, i) => `<button data-page="${i}" class="${i === state.padPage ? 'on' : ''}">${esc(p.name)}</button>`).join('');
}
function renderPads() {
  const act = engine.active;
  $('#padGrid').innerHTML = PAD_PAGES[state.padPage].items.map(([label, note, minor]) => {
    const on = act && act[0] === note && act[1] === minor;
    return `<button class="pad${on ? ' on' : ''}" data-label="${esc(label)}" data-note="${note}" data-minor="${minor ? 1 : 0}">${esc(label)}</button>`;
  }).join('');
}
function refreshPads() {
  const act = engine.active;
  $$('#padGrid .pad').forEach(b => {
    b.classList.toggle('on', !!act && act[0] === +b.dataset.note && act[1] === (b.dataset.minor === '1'));
  });
  const st = $('#status');
  if (!act) { st.textContent = 'Pad antippen  ·  Wischen = andere Seite'; st.classList.remove('on'); }
  else {
    let t = '▶  ' + state.activeLabel;
    if (!state.cfg.pads_enabled) t += '  (Pads stumm)';
    if (state.cfg.click_enabled) t += `  ·  Click ${state.cfg.tempo} BPM`;
    st.textContent = t; st.classList.add('on');
  }
}
function setPage(i) { state.padPage = clamp(i, 0, PAD_PAGES.length - 1); renderPageSel(); renderPads(); refreshPads(); }

function padTap(label, note, minor) {
  unlockAudio();
  const act = engine.active;
  if (act && act[0] === note && act[1] === minor) { engine.stop(); state.activeLabel = ''; }
  else {
    if (!state.cfg.pads_enabled) { state.cfg.pads_enabled = true; saveCfg(); }
    engine.play([note, minor]); state.activeLabel = label;
  }
  refreshPads();
}
function stopAll() { engine.stop(); state.activeLabel = ''; refreshPads(); }

// Tippen vs. Wischen auf dem Pad-Raster
(function () {
  const grid = $('#padGrid'); let sx = 0, sy = 0, tgt = null, id = null;
  grid.addEventListener('pointerdown', e => { sx = e.clientX; sy = e.clientY; id = e.pointerId; tgt = e.target.closest('.pad'); });
  grid.addEventListener('pointerup', e => {
    if (e.pointerId !== id) return; id = null;
    const dx = e.clientX - sx, dy = e.clientY - sy;
    if (Math.abs(dx) > 70 && Math.abs(dx) > Math.abs(dy) * 1.5) { setPage(state.padPage + (dx < 0 ? 1 : -1)); return; }
    if (Math.abs(dx) < 14 && Math.abs(dy) < 14 && tgt) padTap(tgt.dataset.label, +tgt.dataset.note, tgt.dataset.minor === '1');
    tgt = null;
  });
  grid.addEventListener('pointercancel', () => { id = null; tgt = null; });
})();
$('#pageSel').addEventListener('click', e => { const b = e.target.closest('button'); if (b) setPage(+b.dataset.page); });

// ---------------------------------------------------------------------------
// Navigation
// ---------------------------------------------------------------------------
function show(screen) {
  state.screen = screen;
  const main = screen === 'live' || screen === 'setlist';
  if (main) state.lastMain = screen;
  $$('.page').forEach(p => p.classList.toggle('on', p.id === 'page-' + screen));
  $$('#tabs button').forEach(b => b.classList.toggle('on', main && b.dataset.tab === screen));
  $('#bottomMain').hidden = !main; $('#bottomBack').hidden = main;
  const pg = $('#page-' + screen); if (pg) pg.scrollTop = 0;
}
$('#tabs').addEventListener('click', e => { const b = e.target.closest('button'); if (b) show(b.dataset.tab); });
document.querySelector('footer#bottomMain').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  if (b.dataset.nav === 'stop') stopAll(); else show(b.dataset.nav);
});
$('#bottomBack').addEventListener('click', () => show(state.lastMain));
document.addEventListener('keydown', e => {
  if (e.target.matches('input,select,textarea')) return;
  if (e.code === 'Space') { e.preventDefault(); stopAll(); }
  else if (e.code === 'ArrowRight') stepSong(1);
  else if (e.code === 'ArrowLeft') stepSong(-1);
});

// ---------------------------------------------------------------------------
// Einstellungen
// ---------------------------------------------------------------------------
function initMenu() {
  $$('input[type=range][data-cfg]').forEach(inp => {
    inp.value = state.cfg[inp.dataset.cfg];
    inp.addEventListener('input', () => setParam(inp.dataset.cfg, parseFloat(inp.value)));
  });
  $('#clickSound').innerHTML = CLICK_NAMES.map(n => `<option>${n}</option>`).join('');
  $('#clickSound').addEventListener('change', e => setParam('click_sound', e.target.value));
  $('#clickOn').addEventListener('change', e => { setParam('click_enabled', e.target.checked); refreshPads(); });
  $('#routeSel').innerHTML = Object.entries(ROUTES).map(([k, t]) => `<button data-route="${k}">${esc(t)}</button>`).join('');
  $('#routeSel').addEventListener('click', e => { const b = e.target.closest('button'); if (b) { setParam('routing', b.dataset.route); syncMenu(); } });
  $$('[data-step]').forEach(b => b.addEventListener('click', () => {
    const k = b.dataset.step, d = +b.dataset.d;
    setParam(k, k === 'tempo' ? clamp(state.cfg.tempo + d, 30, 300) : clamp(state.cfg.subdiv + d, 1, 16)); syncMenu(); refreshPads();
  }));
  let taps = [];
  $('#tap').addEventListener('click', () => {
    const now = performance.now();
    if (taps.length && now - taps[taps.length - 1] > 2000) taps = [];
    taps.push(now); taps = taps.slice(-6);
    if (taps.length >= 2) {
      const iv = []; for (let i = 1; i < taps.length; i++) iv.push(taps[i] - taps[i - 1]);
      setParam('tempo', clamp(Math.round(60000 / (iv.reduce((a, b) => a + b) / iv.length)), 30, 300)); syncMenu(); refreshPads();
    }
  });
  syncMenu();
}
function syncMenu() {
  const c = state.cfg;
  $$('input[type=range][data-cfg]').forEach(inp => { inp.value = c[inp.dataset.cfg]; });
  $('#clickOn').checked = !!c.click_enabled;
  $('#clickSound').value = c.click_sound;
  $('#tempoVal').textContent = c.tempo; $('#subdivVal').textContent = c.subdiv;
  $$('#routeSel button').forEach(b => b.classList.toggle('on', b.dataset.route === c.routing));
}

// ---------------------------------------------------------------------------
// Sounds
// ---------------------------------------------------------------------------
function renderSounds() {
  const favs = SOUND_NAMES.filter(s => state.cfg.favorites.includes(s));
  const item = (s, star) => `<button data-sound="${esc(s)}" class="${s === state.cfg.sound ? 'on' : ''}"><span class="star${favs.includes(s) ? ' f' : ''}">${star}</span>${esc(s)}</button>`;
  $('#soundList').innerHTML = '<div class="hd">FAVORITEN</div>' + favs.map(s => item(s, '★')).join('') +
    '<div class="hd">FACTORY</div>' + SOUND_NAMES.map(s => item(s, favs.includes(s) ? '★' : '☆')).join('');
}
$('#soundList').addEventListener('click', e => { const b = e.target.closest('button'); if (!b) return; unlockAudio(); setParam('sound', b.dataset.sound); renderSounds(); });
$('#btnFav').addEventListener('click', () => {
  const f = state.cfg.favorites, s = state.cfg.sound, i = f.indexOf(s);
  if (i >= 0) f.splice(i, 1); else f.push(s);
  saveCfg(); renderSounds();
});

// ---------------------------------------------------------------------------
// Dialoge
// ---------------------------------------------------------------------------
function openDialog(html) { const d = $('#dialog'); d.innerHTML = `<div class="sheet">${html}</div>`; d.classList.add('open'); return d.firstElementChild; }
function closeDialog() { const d = $('#dialog'); d.classList.remove('open'); d.innerHTML = ''; }
$('#dialog').addEventListener('click', e => { if (e.target.id === 'dialog') closeDialog(); });

function askText(title, initial, cb) {
  const el = openDialog(`<h3>${esc(title)}</h3><div class="f"><input type="text" id="dlgText"></div>
    <div class="actions"><button class="btn" id="dlgCancel">Abbrechen</button><button class="btn primary" id="dlgOk">OK</button></div>`);
  const inp = el.querySelector('#dlgText'); inp.value = initial || ''; setTimeout(() => inp.focus(), 50);
  const ok = () => { const v = inp.value.trim(); if (v) { closeDialog(); cb(v); } };
  el.querySelector('#dlgOk').onclick = ok; el.querySelector('#dlgCancel').onclick = closeDialog;
  inp.addEventListener('keydown', e => { if (e.key === 'Enter') ok(); });
}

// ---------------------------------------------------------------------------
// Setlist
// ---------------------------------------------------------------------------
function renderSongs() {
  const list = $('#songList');
  $('#setlistInfo').textContent = `${state.setlistName || '(unbenannt)'}  ·  ${state.songs.length} Songs  ·  Tippen = abspielen`;
  if (!state.songs.length) { list.innerHTML = '<div class="empty">Noch keine Songs.<br>Mit „＋ Song“ legst du den ersten an.</div>'; return; }
  list.innerHTML = state.songs.map((s, i) => {
    const info = (s.pads ? s.sound : 'Pads aus') + (s.click ? ` · ${s.tempo} BPM` : '');
    return `<div class="song${i === state.currentSong ? ' cur' : ''}">
      <button class="main" data-play="${i}"><div class="t">${esc(s.title)}</div><div class="s">${esc(info)}</div></button>
      <div class="k">${esc(s.key)}</div><button class="ed" data-edit="${i}" aria-label="Bearbeiten">✎</button></div>`;
  }).join('');
  const cur = list.querySelector('.song.cur'); if (cur) cur.scrollIntoView({ block: 'nearest' });
}
$('#songList').addEventListener('click', e => {
  const p = e.target.closest('[data-play]'), ed = e.target.closest('[data-edit]');
  if (p) playSong(+p.dataset.play); else if (ed) songDialog(+ed.dataset.edit);
});

function playSong(i) {
  const s = state.songs[i]; if (!s) return;
  unlockAudio();
  state.currentSong = i;
  Object.assign(state.cfg, { sound: s.sound, pads_enabled: s.pads, click_enabled: s.click, tempo: s.tempo, subdiv: s.subdiv });
  saveCfg();
  const key = KEY_TABLE[s.key] || [0, false];
  if (s.pads || s.click) { engine.applyParams(); engine.play(key); state.activeLabel = s.key; }   // Pads aus + Click an: nur Click läuft
  else { engine.stop(); state.activeLabel = ''; }
  engine.applyParams();
  syncMenu(); renderSounds(); renderSongs(); refreshPads();
}
function stepSong(d) {
  if (!state.songs.length) return;
  const cur = state.currentSong;
  playSong(cur == null ? (d > 0 ? 0 : state.songs.length - 1) : clamp(cur + d, 0, state.songs.length - 1));
}
$('#btnNext').addEventListener('click', () => stepSong(1));
$('#btnPrev').addEventListener('click', () => stepSong(-1));
$('#btnAddSong').addEventListener('click', () => songDialog(null));

function songDialog(idx) {
  const c = state.cfg, isNew = idx == null;
  const s = isNew ? { title: '', pads: true, sound: c.sound, key: 'C', click: false, tempo: c.tempo, subdiv: c.subdiv } : Object.assign({}, state.songs[idx]);
  const el = openDialog(`<h3>${isNew ? 'Song hinzufügen' : 'Song bearbeiten'}</h3>
    <label class="f"><span>Titel</span><input type="text" id="sTitle" maxlength="60"></label>
    <div class="f"><span>Pads aktiv</span><label class="switch"><input type="checkbox" id="sPads"><i></i></label></div>
    <label class="f"><span>Sound</span><select id="sSound"></select></label>
    <label class="f"><span>Key</span><select id="sKey"></select></label>
    <div class="f"><span>Click aktiv</span><label class="switch"><input type="checkbox" id="sClick"><i></i></label></div>
    <label class="f"><span>Tempo (BPM)</span><input type="number" id="sTempo" min="30" max="300" inputmode="numeric"></label>
    <label class="f"><span>Subdivisions</span><input type="number" id="sSub" min="1" max="16" inputmode="numeric"></label>
    <div class="actions"><button class="btn" id="dCancel">Abbrechen</button><button class="btn primary" id="dOk">OK</button></div>
    ${isNew ? '' : '<div class="actions"><button class="btn" id="dUp">▲ Hoch</button><button class="btn" id="dDown">▼ Runter</button><button class="btn danger" id="dDel">Löschen</button></div>'}`);
  el.querySelector('#sTitle').value = s.title;
  el.querySelector('#sPads').checked = s.pads;
  el.querySelector('#sSound').innerHTML = SOUND_NAMES.map(n => `<option>${n}</option>`).join(''); el.querySelector('#sSound').value = s.sound;
  el.querySelector('#sKey').innerHTML = KEY_LIST.map(n => `<option>${n}</option>`).join(''); el.querySelector('#sKey').value = KEY_LIST.includes(s.key) ? s.key : 'C';
  el.querySelector('#sClick').checked = s.click;
  el.querySelector('#sTempo').value = s.tempo; el.querySelector('#sSub').value = s.subdiv;
  el.querySelector('#dCancel').onclick = closeDialog;
  el.querySelector('#dOk').onclick = () => {
    const title = el.querySelector('#sTitle').value.trim();
    if (!title) { toast('Bitte einen Titel eingeben'); return; }
    const song = { title, pads: el.querySelector('#sPads').checked, sound: el.querySelector('#sSound').value, key: el.querySelector('#sKey').value,
      click: el.querySelector('#sClick').checked, tempo: clamp(parseInt(el.querySelector('#sTempo').value) || 100, 30, 300),
      subdiv: clamp(parseInt(el.querySelector('#sSub').value) || 4, 1, 16) };
    if (isNew) state.songs.push(song); else state.songs[idx] = song;
    saveSongs(); renderSongs(); closeDialog();
  };
  if (!isNew) {
    const move = d => { const j = idx + d; if (j < 0 || j >= state.songs.length) return;
      [state.songs[idx], state.songs[j]] = [state.songs[j], state.songs[idx]];
      if (state.currentSong === idx) state.currentSong = j; else if (state.currentSong === j) state.currentSong = idx;
      saveSongs(); renderSongs(); closeDialog(); };
    el.querySelector('#dUp').onclick = () => move(-1);
    el.querySelector('#dDown').onclick = () => move(1);
    el.querySelector('#dDel').onclick = () => {
      if (!confirm(`„${state.songs[idx].title}“ löschen?`)) return;
      state.songs.splice(idx, 1);
      if (state.currentSong != null) { if (state.currentSong === idx) state.currentSong = null; else if (state.currentSong > idx) state.currentSong--; }
      saveSongs(); renderSongs(); closeDialog();
    };
  }
}

// Setlist-Menü: neu / speichern / laden / export / import
$('#btnSetlistMenu').addEventListener('click', () => {
  const el = openDialog(`<h3>Setlist</h3><div class="menu-list">
    <button class="btn" id="mNew">Neue Setlist</button><button class="btn" id="mSave">Speichern…</button>
    <button class="btn" id="mLoad">Laden…</button><button class="btn" id="mExport">Exportieren (Datei)</button>
    <button class="btn" id="mImport">Importieren (Datei)</button><button class="btn ghost" id="mClose">Schließen</button></div>`);
  el.querySelector('#mClose').onclick = closeDialog;
  el.querySelector('#mNew').onclick = () => { closeDialog(); if (state.songs.length && !confirm('Aktuelle Songliste leeren?')) return;
    state.songs = []; state.setlistName = ''; state.currentSong = null; saveSongs(); renderSongs(); };
  el.querySelector('#mSave').onclick = () => askText('Name der Setlist', state.setlistName || 'Meine Setlist', name => {
    const all = store.get('setlists', {}); all[name] = state.songs; store.set('setlists', all);
    state.setlistName = name; saveSongs(); renderSongs(); toast(`„${name}“ gespeichert`); });
  el.querySelector('#mLoad').onclick = loadDialog;
  el.querySelector('#mExport').onclick = () => {
    const name = state.setlistName || 'AutoPad-Setlist';
    const blob = new Blob([JSON.stringify({ name, songs: state.songs }, null, 2)], { type: 'application/json' });
    const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name.replace(/[^\w\-. ]+/g, '_') + '.json';
    document.body.appendChild(a); a.click(); a.remove(); closeDialog();
  };
  el.querySelector('#mImport').onclick = () => { closeDialog(); $('#importFile').click(); };
});
$('#importFile').addEventListener('change', e => {
  const f = e.target.files[0]; if (!f) return;
  const r = new FileReader();
  r.onload = () => {
    try {
      const d = JSON.parse(r.result); if (!d || !Array.isArray(d.songs)) throw 0;
      state.songs = d.songs.map(s => ({ title: String(s.title || 'Song'), pads: s.pads !== false, sound: SOUNDS[s.sound] ? s.sound : 'Default',
        key: KEY_TABLE[s.key] ? s.key : 'C', click: !!s.click, tempo: clamp(+s.tempo || 100, 30, 300), subdiv: clamp(+s.subdiv || 4, 1, 16) }));
      state.setlistName = d.name || f.name.replace(/\.json$/i, ''); state.currentSong = null; saveSongs(); renderSongs(); toast('Setlist importiert');
    } catch (err) { toast('Datei konnte nicht gelesen werden'); }
  };
  r.readAsText(f); e.target.value = '';
});
function loadDialog() {
  const all = store.get('setlists', {}), names = Object.keys(all).sort();
  const el = openDialog(`<h3>Setlist laden</h3><div class="loadlist">${names.length ? names.map(n => `<button data-n="${esc(n)}">${esc(n)}  ·  ${all[n].length} Songs</button>`).join('') : '<div class="empty">Keine gespeicherten Setlists.</div>'}</div>
    <div class="actions"><button class="btn" id="lCancel">Abbrechen</button><button class="btn danger" id="lDel">Löschen</button><button class="btn primary" id="lOk">Laden</button></div>`);
  let sel = null;
  el.querySelectorAll('.loadlist button').forEach(b => b.onclick = () => { sel = b.dataset.n; el.querySelectorAll('.loadlist button').forEach(x => x.classList.toggle('sel', x === b)); });
  el.querySelector('#lCancel').onclick = closeDialog;
  el.querySelector('#lOk').onclick = () => { if (!sel) return; state.songs = all[sel].slice(); state.setlistName = sel; state.currentSong = null; saveSongs(); renderSongs(); closeDialog(); };
  el.querySelector('#lDel').onclick = () => { if (!sel || !confirm(`„${sel}“ löschen?`)) return; delete all[sel]; store.set('setlists', all); loadDialog(); };
}

// ---------------------------------------------------------------------------
// MIDI (Fußschalter): Nächster / Voriger Song, Stopp, Program Change -> Song
// ---------------------------------------------------------------------------
const midi = { access: null, learn: null };
const midiLabel = m => !m ? '–' : (m.t === 'note' ? 'Note ' + m.n : m.t === 'cc' ? 'CC ' + m.n : 'PC ' + m.n) + '  (Ch ' + (m.ch + 1) + ')';
function renderMidi() {
  $$('.midirow').forEach(r => {
    const k = r.dataset.m, learning = midi.learn === k;
    r.classList.toggle('learning', learning);
    r.querySelector('code').textContent = learning ? 'warte auf Taste…' : midiLabel(state.cfg.midi[k]);
    r.querySelector('[data-learn]').textContent = learning ? 'Abbrechen' : 'Lernen';
  });
  $('#pcDirect').checked = !!state.cfg.midi.pcDirect;
}
function midiAttach() {
  let names = [];
  midi.access.inputs.forEach(inp => { inp.onmidimessage = onMidi; names.push(inp.name); });
  $('#midiStatus').textContent = names.length ? 'Verbunden: ' + names.join(', ') : 'MIDI bereit – aber kein Gerät gefunden. Gerät anstecken (USB/Bluetooth).';
  $('#midiConnect').textContent = 'Neu suchen';
}
async function midiConnect() {
  if (!navigator.requestMIDIAccess) {
    $('#midiStatus').textContent = /iPhone|iPad|iPod|Macintosh/.test(navigator.userAgent) && 'ontouchend' in document
      ? 'Dieser Browser (Safari auf iPhone/iPad) unterstützt kein Web MIDI. Unter Android (Chrome) und am PC (Chrome/Edge) funktioniert es.'
      : 'Dieser Browser unterstützt kein Web MIDI. Bitte Chrome oder Edge verwenden.';
    return;
  }
  try {
    midi.access = await navigator.requestMIDIAccess();
    midi.access.onstatechange = midiAttach; midiAttach();
  } catch (e) { $('#midiStatus').textContent = 'MIDI-Zugriff wurde abgelehnt.'; }
}
function onMidi(ev) {
  const [st, d1, d2] = ev.data; if (st >= 0xF0) return;       // Clock/SysEx ignorieren
  const type = st & 0xF0, ch = st & 0x0F; let msg = null;
  if (type === 0x90 && d2 > 0) msg = { t: 'note', ch, n: d1, v: d2 };
  else if (type === 0xB0) msg = { t: 'cc', ch, n: d1, v: d2 };
  else if (type === 0xC0) msg = { t: 'pc', ch, n: d1, v: 127 };
  else return;
  $('#midiLast').textContent = 'Zuletzt empfangen: ' + midiLabel(msg) + (msg.t === 'cc' ? '  Wert ' + msg.v : '');
  if (midi.learn) {
    if (msg.t === 'cc' && msg.v < 64) return;                  // nur "Fuß drauf" lernen
    state.cfg.midi[midi.learn] = { t: msg.t, ch: msg.ch, n: msg.n }; midi.learn = null; saveCfg(); renderMidi(); toast('MIDI-Taste gelernt'); return;
  }
  if (msg.t === 'cc' && msg.v < 64) return;
  const hit = k => { const m = state.cfg.midi[k]; return m && m.t === msg.t && m.ch === msg.ch && m.n === msg.n; };
  if (hit('next')) stepSong(1);
  else if (hit('prev')) stepSong(-1);
  else if (hit('stop')) stopAll();
  else if (msg.t === 'pc' && state.cfg.midi.pcDirect && msg.n < state.songs.length) playSong(msg.n);
}
function initMidi() {
  $('#midiConnect').addEventListener('click', midiConnect);
  $$('.midirow').forEach(r => {
    r.querySelector('[data-learn]').addEventListener('click', () => { midi.learn = midi.learn === r.dataset.m ? null : r.dataset.m; renderMidi(); if (midi.learn && !midi.access) midiConnect(); });
    r.querySelector('[data-clear]').addEventListener('click', () => { state.cfg.midi[r.dataset.m] = null; saveCfg(); renderMidi(); });
  });
  $('#pcDirect').addEventListener('change', e => { state.cfg.midi.pcDirect = e.target.checked; saveCfg(); });
  renderMidi();
  if (navigator.permissions && navigator.permissions.query) {   // schon erlaubt? dann automatisch verbinden
    navigator.permissions.query({ name: 'midi' }).then(p => { if (p.state === 'granted') midiConnect(); }).catch(() => {});
  }
}

// ---------------------------------------------------------------------------
// Start
// ---------------------------------------------------------------------------
engine.onChange = () => refreshPads();
renderPageSel(); renderPads(); renderSounds(); renderSongs(); initMenu(); initMidi(); refreshPads(); show('live');
window.addEventListener('pointerdown', unlockAudio, { once: true, capture: true });
if ('serviceWorker' in navigator && location.protocol.startsWith('http')) navigator.serviceWorker.register('sw.js').catch(() => {});

window.AutoPad = { Engine, engine, state, SOUNDS, KEY_TABLE, KEY_LIST, DEFAULT_CFG, playSong, stepSong, midi, onMidi };
})();
