// The animation engine of the hero stage (components/HeroLenses.tsx). React renders the SVG once;
// this engine moves its elements by writing attributes, one requestAnimationFrame per frame, so a
// change of lens never re-renders React. Every animated quantity (node and kernel positions,
// opacities and sizes, the rings, the orbit, the block, how edges bend) lives in one flat vector.
// A change of lens or guarantee snapshots the current vector and eases each entry to the new
// target; in the guarantee lens the target itself turns (the bell rotates about its axis).

import { FRAME, ORBIT_LAYERS, KERNEL_PHASES, bellPoint, onEllipse, orbitFor, type Bell } from "@/lib/lenses";

export type LensIndex = 0 | 1 | 2;

export interface EngineSpec {
  ids: string[];
  depth: number[];
  radial: { x: number; y: number }[];
  layers: { x: number; y: number }[];
  /** Edges [user, used] as node indices. */
  edges: [number, number][];
  kernelsRadial: { x: number; y: number }[];
  rings: number[];
  orbitRadius: number;
  bells: Bell[];
}

export interface EngineEls {
  nodes: (SVGGElement | null)[];
  edges: (SVGPathElement | null)[];
  kernels: (SVGGElement | null)[];
  spokes: (SVGLineElement | null)[];
  rings: (SVGEllipseElement | null)[];
  orbit: SVGEllipseElement | null;
  core: SVGGElement | null;
}

const C = FRAME / 2;
const RING_POOL = 10;
/** One turn of the bell takes this many milliseconds. */
const TURN_MS = 52000;
const LENS_MS = 1500;
const GUARANTEE_MS = 1100;
/** Fraction of a lens change by which the deepest declarations lead the shallowest. */
const WAVE = 0.24;

const ease = (t: number) => (t <= 0 ? 0 : t >= 1 ? 1 : t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2);
const f1 = (x: number) => Math.round(x * 10) / 10;

export class LensEngine {
  private n: number;
  private k: number;
  private oNode = 0;
  private oKer: number;
  private oRing: number;
  private oOrb: number;
  private oCore: number;
  private oMisc: number;
  private len: number;
  private cur: Float32Array;
  private from: Float32Array;
  private tgt: Float32Array;
  private delay: Float32Array;
  /** Per guarantee: for each node, its level in the bell (or -1) and its index on that level's ring. */
  private level: Int16Array[];
  private slot: Int16Array[];
  private lens: LensIndex = 0;
  private g = 0;
  private theta = 0.35;
  private t0 = 0;
  private dur = 0;
  private raf = 0;
  private last = 0;
  private visible = true;
  private focus: Set<number> | null = null;
  private edgeShown: Uint8Array;

  constructor(
    private spec: EngineSpec,
    private els: EngineEls,
    private reduced: boolean,
  ) {
    this.n = spec.ids.length;
    this.k = spec.kernelsRadial.length;
    this.oKer = this.n * 4;
    this.oRing = this.oKer + this.k * 4;
    this.oOrb = this.oRing + RING_POOL * 5;
    this.oCore = this.oOrb + 6;
    this.oMisc = this.oCore + 4;
    this.len = this.oMisc + 2;
    this.cur = new Float32Array(this.len);
    this.from = new Float32Array(this.len);
    this.tgt = new Float32Array(this.len);
    this.edgeShown = new Uint8Array(spec.edges.length).fill(1);
    const maxDepth = Math.max(1, ...spec.depth);
    this.delay = Float32Array.from(spec.depth, (d) => WAVE * (1 - d / maxDepth));
    const index = new Map(spec.ids.map((id, i) => [id, i]));
    this.level = spec.bells.map(() => new Int16Array(this.n).fill(-1));
    this.slot = spec.bells.map(() => new Int16Array(this.n).fill(-1));
    spec.bells.forEach((b, gi) =>
      b.levels.forEach((l) =>
        l.ids.forEach((id, j) => {
          const i = index.get(id)!;
          this.level[gi]![i] = l.level;
          this.slot[gi]![i] = j;
        }),
      ),
    );
    this.target(this.cur);
    this.apply();
  }

  /** Move to a lens and guarantee; `instant` skips the transition. */
  set(lens: LensIndex, g: number, instant = false) {
    if (lens === this.lens && g === this.g) return;
    const lensChanged = lens !== this.lens;
    this.from.set(this.cur);
    this.lens = lens;
    this.g = g;
    this.dur = instant || this.reduced ? 0 : lensChanged ? LENS_MS : GUARANTEE_MS;
    this.t0 = performance.now();
    this.kick();
  }

  /** Highlight the cone of a declaration (node indices), or clear it. */
  setFocus(cone: Set<number> | null) {
    this.focus = cone;
    this.els.edges.forEach((el, e) => {
      if (!el) return;
      const [a, b] = this.spec.edges[e]!;
      el.classList.toggle("is-cone", !!cone && cone.has(a) && cone.has(b));
    });
    this.kick();
  }

  /** Pause the turning while the stage is off screen. */
  setVisible(v: boolean) {
    this.visible = v;
    if (v) this.kick();
  }

  destroy() {
    cancelAnimationFrame(this.raf);
    this.raf = 0;
  }

  private kick() {
    if (this.raf) return;
    this.last = performance.now();
    this.raf = requestAnimationFrame(this.tick);
  }

  private turning() {
    return this.lens === 2 && !this.reduced && this.visible;
  }

  private tick = (now: number) => {
    this.raf = 0;
    const dt = Math.min(50, Math.max(0, now - this.last));
    this.last = now;
    if (this.turning()) this.theta += (dt / TURN_MS) * Math.PI * 2;
    const p = this.dur ? (now - this.t0) / this.dur : 1;
    this.target(this.tgt);
    if (p < 1) {
      const eAll = ease(p);
      const span = 1 - WAVE;
      for (let i = 0; i < this.n; i++) {
        const e = ease((p - this.delay[i]!) / span);
        for (let j = i * 4; j < i * 4 + 4; j++) this.cur[j] = this.from[j]! + (this.tgt[j]! - this.from[j]!) * e;
      }
      for (let j = this.oKer; j < this.len; j++) this.cur[j] = this.from[j]! + (this.tgt[j]! - this.from[j]!) * eAll;
    } else {
      this.cur.set(this.tgt);
    }
    this.apply();
    if (p < 1 || this.turning()) this.raf = requestAnimationFrame(this.tick);
  };

  /** The vector the stage is heading to at the current turn. */
  private target(out: Float32Array) {
    const { spec, lens, from } = this;
    // Nodes.
    if (lens === 2) {
      const bell = spec.bells[this.g]!;
      const lv = this.level[this.g]!;
      const sl = this.slot[this.g]!;
      for (let i = 0; i < this.n; i++) {
        const j = i * 4;
        const l = lv[i]!;
        if (l < 0) {
          out[j] = from[j]!;
          out[j + 1] = from[j + 1]!;
          out[j + 2] = 0;
          out[j + 3] = from[j + 3]!;
          continue;
        }
        const p = bellPoint(bell.levels[l]!, sl[i]!, this.theta);
        const b = (p.z + 1) / 2;
        out[j] = p.x;
        out[j + 1] = p.y;
        out[j + 2] = l === 0 ? 1 : 0.34 + 0.66 * b;
        out[j + 3] = l === 0 ? 1 : 0.74 + 0.46 * b;
      }
    } else {
      const pos = lens === 0 ? spec.radial : spec.layers;
      for (let i = 0; i < this.n; i++) {
        const j = i * 4;
        out[j] = pos[i]!.x;
        out[j + 1] = pos[i]!.y;
        out[j + 2] = 1;
        out[j + 3] = 1;
      }
    }
    // Kernels.
    for (let q = 0; q < this.k; q++) {
      const j = this.oKer + q * 4;
      if (lens === 0) {
        out[j] = spec.kernelsRadial[q]!.x;
        out[j + 1] = spec.kernelsRadial[q]!.y;
        out[j + 2] = 1;
        out[j + 3] = 1;
      } else {
        const p = lens === 2 ? onEllipse(orbitFor(spec.bells[this.g]!), KERNEL_PHASES[q]! - this.theta * 0.6) : onEllipse(ORBIT_LAYERS, KERNEL_PHASES[q]!);
        const b = (p.z + 1) / 2;
        out[j] = p.x;
        out[j + 1] = p.y;
        out[j + 2] = lens === 2 ? 0.42 + 0.58 * b : 1;
        out[j + 3] = lens === 2 ? 0.8 + 0.3 * b : 1;
      }
    }
    // Rings: the depth circles of the radial lens, the levels of the bell.
    const bell = lens === 2 ? spec.bells[this.g]! : null;
    for (let r = 0; r < RING_POOL; r++) {
      const j = this.oRing + r * 5;
      if (lens === 0 && r < spec.rings.length) {
        out.set([C, C, spec.rings[r]!, spec.rings[r]!, 1], j);
      } else if (bell && r + 1 < bell.levels.length) {
        const l = bell.levels[r + 1]!;
        out.set([C, l.y, l.rx, l.ry, 1], j);
      } else {
        out.set([from[j]!, from[j + 1]!, from[j + 2]!, from[j + 3]!, 0], j);
      }
    }
    // The orbit: a circle in the radial lens, the tilted ellipse in the others.
    if (lens === 0) out.set([C, C, spec.orbitRadius, spec.orbitRadius, 0, 1], this.oOrb);
    else {
      const o = lens === 1 ? ORBIT_LAYERS : orbitFor(spec.bells[this.g]!);
      out.set([o.cx, o.cy, o.rx, o.ry, o.rot, 1], this.oOrb);
    }
    // The block: the conclusion at the centre, then the guarantee at the top of its bell.
    if (lens === 0) out.set([C, C, 1, 30], this.oCore);
    else if (lens === 1) out.set([C, 18, 0, 20], this.oCore);
    else out.set([C, bell!.levels[0]!.y, 1, 26], this.oCore);
    // Misc: how far edges bend vertically (0 radial, 1 vertical), and the edges' base opacity.
    out[this.oMisc] = lens === 0 ? 0 : 1;
    out[this.oMisc + 1] = lens === 0 ? 0.15 : lens === 1 ? 0.3 : 0.44;
  }

  private apply() {
    const { cur, els, spec } = this;
    for (let i = 0; i < this.n; i++) {
      const el = els.nodes[i];
      if (!el) continue;
      const j = i * 4;
      const o = cur[j + 2]!;
      if (o < 0.01) {
        if (el.style.display !== "none") el.style.display = "none";
        continue;
      }
      if (el.style.display === "none") el.style.display = "";
      el.setAttribute("transform", `translate(${f1(cur[j]!)} ${f1(cur[j + 1]!)}) scale(${cur[j + 3]!.toFixed(3)})`);
      el.style.opacity = o.toFixed(3);
    }
    const w = cur[this.oMisc]!;
    const base = cur[this.oMisc + 1]!;
    const focus = this.focus;
    for (let e = 0; e < spec.edges.length; e++) {
      const el = els.edges[e];
      if (!el) continue;
      const [ub, ua] = spec.edges[e]!;
      const ja = ua * 4;
      const jb = ub * 4;
      let alpha = base * Math.min(cur[ja + 2]!, cur[jb + 2]!);
      if (focus) alpha = focus.has(ua) && focus.has(ub) ? Math.min(1, alpha * 5) : alpha * 0.4;
      if (alpha < 0.006) {
        if (this.edgeShown[e]) (el.style.display = "none"), (this.edgeShown[e] = 0);
        continue;
      }
      if (!this.edgeShown[e]) (el.style.display = ""), (this.edgeShown[e] = 1);
      const ax = cur[ja]!;
      const ay = cur[ja + 1]!;
      const bx = cur[jb]!;
      const by = cur[jb + 1]!;
      // Radial: the quadratic bent toward the centre, as a cubic. Vertical: an S from one row to the next.
      const mx = (ax + bx) / 2;
      const my = (ay + by) / 2;
      const qx = mx + (C - mx) * 0.22;
      const qy = my + (C - my) * 0.22;
      const r1x = ax + ((qx - ax) * 2) / 3;
      const r1y = ay + ((qy - ay) * 2) / 3;
      const r2x = bx + ((qx - bx) * 2) / 3;
      const r2y = by + ((qy - by) * 2) / 3;
      const c1x = r1x + (ax - r1x) * w;
      const c1y = r1y + (my - r1y) * w;
      const c2x = r2x + (bx - r2x) * w;
      const c2y = r2y + (my - r2y) * w;
      el.setAttribute("d", `M${f1(ax)} ${f1(ay)}C${f1(c1x)} ${f1(c1y)} ${f1(c2x)} ${f1(c2y)} ${f1(bx)} ${f1(by)}`);
      el.setAttribute("stroke-opacity", alpha.toFixed(3));
    }
    for (let q = 0; q < this.k; q++) {
      const j = this.oKer + q * 4;
      const x = f1(cur[j]!);
      const y = f1(cur[j + 1]!);
      els.kernels[q]?.setAttribute("transform", `translate(${x} ${y}) scale(${cur[j + 3]!.toFixed(3)})`);
      if (els.kernels[q]) els.kernels[q]!.style.opacity = cur[j + 2]!.toFixed(3);
      const s = els.spokes[q];
      if (s) {
        s.setAttribute("x2", String(x));
        s.setAttribute("y2", String(y));
      }
    }
    for (let r = 0; r < RING_POOL; r++) {
      const el = els.rings[r];
      if (!el) continue;
      const j = this.oRing + r * 5;
      const o = cur[j + 4]!;
      if (o < 0.01) {
        el.style.display = "none";
        continue;
      }
      el.style.display = "";
      el.setAttribute("cx", String(f1(cur[j]!)));
      el.setAttribute("cy", String(f1(cur[j + 1]!)));
      el.setAttribute("rx", String(f1(Math.max(0, cur[j + 2]!))));
      el.setAttribute("ry", String(f1(Math.max(0, cur[j + 3]!))));
      el.style.opacity = o.toFixed(3);
    }
    const ob = this.oOrb;
    if (els.orbit) {
      els.orbit.setAttribute("cx", String(f1(cur[ob]!)));
      els.orbit.setAttribute("cy", String(f1(cur[ob + 1]!)));
      els.orbit.setAttribute("rx", String(f1(cur[ob + 2]!)));
      els.orbit.setAttribute("ry", String(f1(cur[ob + 3]!)));
      els.orbit.setAttribute("transform", `rotate(${cur[ob + 4]!.toFixed(2)} ${f1(cur[ob]!)} ${f1(cur[ob + 1]!)})`);
    }
    const oc = this.oCore;
    if (els.core) {
      els.core.setAttribute("transform", `translate(${f1(cur[oc]!)} ${f1(cur[oc + 1]!)}) scale(${(cur[oc + 3]! / 30).toFixed(3)})`);
      els.core.style.opacity = cur[oc + 2]!.toFixed(3);
    }
  }
}
