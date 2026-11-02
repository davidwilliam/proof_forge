"use client";

import { useCallback, useEffect, useMemo, useRef, useState, type CSSProperties, type KeyboardEvent, type ReactNode } from "react";
import type { GraphLayout, PlacedNode } from "@/lib/proofgraph";
import { bellPoint, displayQuote, type Bell, type Guarantee, type LayersLayout } from "@/lib/lenses";
import type { HoleRun } from "@/lib/hole";
import { LensEngine, type LensIndex } from "@/components/lens-engine";

export interface Readings {
  passport: string;
  status: string;
  requirements: number;
  verified: number;
  kernels: string[];
  propertyCases: number;
  axioms: string[];
  declarations: number;
}

export interface HeroLensesProps {
  radial: GraphLayout;
  layers: LayersLayout;
  guarantees: Guarantee[];
  bells: Bell[];
  /** Every direct use [user, used], for the dependency cone shown on hover. */
  uses: [string, string][];
  readings: Readings;
  passportHref: string;
  text: { headline: string; summary: string; layersTitle: string; layersText: string; guaranteeTitle: string; task: string };
  /** The phone-only figures, placed between the headline and the stage. */
  figures: ReactNode;
  actions: ReactNode;
  /** Index of the guarantee shown first. */
  initial: number;
  /** "A guarantee with a hole": the guarantees of a run that did not verify. */
  hole: HoleRun;
}

const LENSES = ["The whole proof", "The layers", "One guarantee"] as const;
/** Time on "The layers" during the first-visit tour; "The whole proof" stays until its check has run. */
const LAYERS_MS = 4200;
const TOUR_KEY = "pf-lenses";

const KIND_LABEL: Record<PlacedNode["kind"], string> = { requirement: "requirement", lemma: "lemma", definition: "definition", type: "type" };
const fmt = (n: number) => n.toLocaleString("en-US");
const fileName = (f: string) => f.split("/").pop() ?? f;

/** One node, drawn around the origin (the engine places it): a square for requirements and the locked specification, a dot for lemmas. */
function NodeMark({ n }: { n: PlacedNode }) {
  if (n.kind === "requirement") return <rect x={-6} y={-6} width={12} height={12} rx={1.5} />;
  if (n.origin === "specification") return <rect x={-3.6} y={-3.6} width={7.2} height={7.2} rx={1} />;
  if (n.kind === "definition") return <rect x={-3.2} y={-3.2} width={6.4} height={6.4} rx={3.2} />;
  return <circle r={2.9} />;
}

/** The radial lens's edge, for the server render; the engine writes the same path. */
function radialPath(a: { x: number; y: number }, b: { x: number; y: number }, c: number) {
  const mx = (a.x + b.x) / 2;
  const my = (a.y + b.y) / 2;
  const qx = mx + (c - mx) * 0.22;
  const qy = my + (c - my) * 0.22;
  return `M${a.x} ${a.y}Q${qx.toFixed(1)} ${qy.toFixed(1)} ${b.x} ${b.y}`;
}

/** A quoted statement: first letter capitalized, the rest verbatim, `code` spans set as code. */
function Quote({ text: t }: { text: string }) {
  const parts = displayQuote(t).split("`");
  return <>{parts.map((x, i) => (i % 2 ? <code key={i}>{x}</code> : x))}</>;
}
const words = ["no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"];
const count = (n: number) => words[n] ?? String(n);

/** A node of the run with a hole: the hole is a dark gap, the declarations that use it red. */
function HoleMark({ n }: { n: HoleRun["nodes"][number] }) {
  if (n.role === "hole")
    return (
      <>
        <circle className="hl-gap" r={19} />
        <rect className="hl-gap-mark" x={-5} y={-5} width={10} height={10} rx={1} />
      </>
    );
  if (n.kind === "requirement") return <rect x={-6} y={-6} width={12} height={12} rx={1.5} />;
  if (n.origin === "specification") return <rect x={-3.6} y={-3.6} width={7.2} height={7.2} rx={1} />;
  if (n.kind === "definition") return <rect x={-3.2} y={-3.2} width={6.4} height={6.4} rx={3.2} />;
  return <circle r={2.9} />;
}

export function HeroLenses(props: HeroLensesProps) {
  const { radial, layers, guarantees, bells, uses, readings, passportHref, text, figures, actions, hole } = props;
  const { size, center: c, nodes, edges, kernels, rings, orbit, done } = radial;
  const end = kernels.length ? kernels[kernels.length - 1]!.at + 0.5 : done + 1;
  const index = useMemo(() => new Map(nodes.map((n, i) => [n.id, i])), [nodes]);

  const [lens, setLens] = useState<LensIndex>(0);
  const [g, setG] = useState(props.initial);
  const [active, setActive] = useState<string | null>(null);
  const [holeOn, setHoleOn] = useState(false);
  const [hg, setHg] = useState(hole.initial);

  // Dependency cones for hover.
  const usedBy = useMemo(() => {
    const out = new Map<string, string[]>();
    for (const [a, b] of uses) out.set(a, [...(out.get(a) ?? []), b]);
    return out;
  }, [uses]);
  const coneOf = useCallback(
    (id: string) => {
      const seen = new Set<string>([id]);
      const stack = [id];
      while (stack.length) for (const m of usedBy.get(stack.pop()!) ?? []) if (!seen.has(m)) (seen.add(m), stack.push(m));
      return seen;
    },
    [usedBy],
  );
  const cone = useMemo(() => (active ? coneOf(active) : null), [active, coneOf]);

  // The engine and the elements it moves.
  const nodeEls = useRef<(SVGGElement | null)[]>([]);
  const edgeEls = useRef<(SVGPathElement | null)[]>([]);
  const kernelEls = useRef<(SVGGElement | null)[]>([]);
  const spokeEls = useRef<(SVGLineElement | null)[]>([]);
  const ringEls = useRef<(SVGEllipseElement | null)[]>([]);
  const orbitEl = useRef<SVGEllipseElement | null>(null);
  const coreEl = useRef<SVGGElement | null>(null);
  const stageEl = useRef<HTMLDivElement | null>(null);
  const engine = useRef<LensEngine | null>(null);
  const holeNodeEls = useRef<(SVGGElement | null)[]>([]);
  const holeEdgeEls = useRef<(SVGPathElement | null)[]>([]);
  const holeRingEls = useRef<(SVGEllipseElement | null)[]>([]);
  const holeCoreEl = useRef<SVGGElement | null>(null);
  const holeEngine = useRef<LensEngine | null>(null);
  const inView = useRef(true);
  const holeOnRef = useRef(false);
  const holeIndex = useMemo(() => new Map(hole.nodes.map((n, i) => [n.id, i])), [hole]);
  // Where each node of the run with a hole sits before it turns: on the first bell, or at its axis.
  const holeStart = useMemo(() => {
    const at = new Map<string, { x: number; y: number }>();
    for (const l of hole.bells[hole.initial]!.levels) l.ids.forEach((id, i) => at.set(id, bellPoint(l, i, 0.35)));
    return hole.nodes.map((n) => at.get(n.id) ?? { x: c, y: 320 });
  }, [hole, c]);

  useEffect(() => {
    const reduced = matchMedia("(prefers-reduced-motion: reduce)").matches;
    const e = new LensEngine(
      {
        ids: nodes.map((n) => n.id),
        depth: nodes.map((n) => n.depth),
        radial: nodes.map((n) => ({ x: n.x, y: n.y })),
        layers: nodes.map((n) => layers.nodes[n.id]!),
        edges: edges.map((x) => [index.get(x.from)!, index.get(x.to)!] as [number, number]),
        kernelsRadial: kernels.map((k) => ({ x: k.x, y: k.y })),
        rings,
        orbitRadius: orbit,
        bells,
      },
      {
        nodes: nodeEls.current,
        edges: edgeEls.current,
        kernels: kernelEls.current,
        spokes: spokeEls.current,
        rings: ringEls.current,
        orbit: orbitEl.current,
        core: coreEl.current,
      },
      reduced,
    );
    engine.current = e;
    const h = new LensEngine(
      {
        ids: hole.nodes.map((n) => n.id),
        depth: hole.nodes.map((n) => n.depth),
        radial: holeStart,
        layers: holeStart,
        edges: hole.edges.map((x) => [holeIndex.get(x.from)!, holeIndex.get(x.to)!] as [number, number]),
        kernelsRadial: [],
        rings: [],
        orbitRadius: 0,
        bells: hole.bells,
      },
      { nodes: holeNodeEls.current, edges: holeEdgeEls.current, kernels: [], spokes: [], rings: holeRingEls.current, orbit: null, core: holeCoreEl.current },
      reduced,
    );
    h.set(2, hole.initial, true);
    h.setVisible(false);
    holeEngine.current = h;
    const io = new IntersectionObserver(([x]) => {
      inView.current = !!x?.isIntersecting;
      e.setVisible(inView.current && !holeOnRef.current);
      h.setVisible(inView.current && holeOnRef.current);
    });
    if (stageEl.current) io.observe(stageEl.current);
    return () => {
      io.disconnect();
      e.destroy();
      h.destroy();
      engine.current = null;
      holeEngine.current = null;
    };
  }, [nodes, edges, kernels, rings, orbit, layers, bells, index, hole, holeIndex, holeStart]);

  useEffect(() => holeEngine.current?.set(2, hg), [hg]);
  useEffect(() => {
    holeOnRef.current = holeOn;
    engine.current?.setVisible(inView.current && !holeOn);
    holeEngine.current?.setVisible(inView.current && holeOn);
  }, [holeOn]);

  useEffect(() => engine.current?.set(lens, g), [lens, g]);
  useEffect(() => {
    engine.current?.setFocus(cone && lens !== 2 ? new Set([...cone].map((id) => index.get(id)!)) : null);
  }, [cone, lens, index]);

  // The check of the radial lens, and the first-visit tour through the lenses. Both start when the
  // splash ends. Reduced motion: the guarantee lens at once, no tour.
  const [phase, setPhase] = useState<number | null>(null);
  const tour = useRef<{ timer: number; due: number; left: number; next: (() => void) | null; paused: boolean; stopped: boolean }>({
    timer: 0,
    due: 0,
    left: 0,
    next: null,
    paused: false,
    stopped: false,
  });
  const schedule = useCallback((ms: number, next: () => void) => {
    const t = tour.current;
    if (t.stopped) return;
    t.next = next;
    t.left = ms;
    if (t.paused) return;
    t.due = performance.now() + ms;
    t.timer = window.setTimeout(() => {
      t.next = null;
      next();
    }, ms);
  }, []);
  const pause = useCallback((on: boolean) => {
    const t = tour.current;
    if (t.stopped || t.paused === on) return;
    t.paused = on;
    if (on) {
      window.clearTimeout(t.timer);
      t.left = Math.max(0, t.due - performance.now());
    } else if (t.next) schedule(Math.max(600, t.left), t.next);
  }, [schedule]);
  const stopTour = useCallback(() => {
    const t = tour.current;
    t.stopped = true;
    t.next = null;
    window.clearTimeout(t.timer);
  }, []);

  useEffect(() => {
    const root = document.documentElement;
    if (matchMedia("(prefers-reduced-motion: reduce)").matches) {
      setLens(2);
      return;
    }
    let seen = false;
    try {
      seen = sessionStorage.getItem(TOUR_KEY) === "1";
      sessionStorage.setItem(TOUR_KEY, "1");
    } catch {}
    const splash = root.getAttribute("data-splash") === "on";
    const asked = /[?&](tour|splash)\b/.test(location.search);
    const runTour = splash || asked || (!seen && !navigator.webdriver);
    let raf = 0;
    let t0 = 0;
    let last = -1;
    const tick = (now: number) => {
      const t = (now - t0) / 1000;
      if (t >= end + 0.2) {
        setPhase(null);
        return;
      }
      const key = nodes.filter((n) => n.at <= t).length * 10 + kernels.filter((k) => k.at <= t).length;
      if (key !== last) {
        last = key;
        setPhase(t);
      }
      raf = requestAnimationFrame(tick);
    };
    const start = () => {
      t0 = performance.now();
      raf = requestAnimationFrame(tick);
      if (runTour)
        schedule((end + 0.4) * 1000, () => {
          setLens(1);
          schedule(LAYERS_MS, () => {
            setLens(2);
            stopTour();
          });
        });
    };
    let mo: MutationObserver | null = null;
    if (splash) {
      mo = new MutationObserver(() => {
        if (root.getAttribute("data-splash") !== "on") {
          mo?.disconnect();
          start();
        }
      });
      mo.observe(root, { attributes: true, attributeFilter: ["data-splash"] });
    } else start();
    const t = tour.current;
    return () => {
      mo?.disconnect();
      cancelAnimationFrame(raf);
      window.clearTimeout(t.timer);
    };
  }, [end, nodes, kernels, schedule, stopTour]);

  const choose = (i: LensIndex) => {
    stopTour();
    setActive(null);
    setLens(i);
    if (i !== 2) setHoleOn(false);
  };
  const tabKeys = (e: KeyboardEvent<HTMLButtonElement>) => {
    const k = e.key;
    const to = k === "ArrowRight" ? (lens + 1) % 3 : k === "ArrowLeft" ? (lens + 2) % 3 : k === "Home" ? 0 : k === "End" ? 2 : -1;
    if (to < 0) return;
    e.preventDefault();
    choose(to as LensIndex);
    document.getElementById(`hl-tab-${to}`)?.focus();
  };
  const pick = (i: number) => {
    stopTour();
    setHoleOn(false);
    setG(i);
  };
  const barKeys = (n: number, at: number, select: (i: number) => void, prefix: string) => (e: KeyboardEvent<HTMLButtonElement>) => {
    const k = e.key;
    const to = k === "ArrowRight" || k === "ArrowDown" ? (at + 1) % n : k === "ArrowLeft" || k === "ArrowUp" ? (at + n - 1) % n : k === "Home" ? 0 : k === "End" ? n - 1 : -1;
    if (to < 0) return;
    e.preventDefault();
    select(to);
    document.getElementById(`${prefix}-${to}`)?.focus();
  };
  const pickHole = (i: number) => {
    stopTour();
    setHg(i);
  };

  // Readout of the radial lens's check.
  const running = phase !== null;
  const reqDone = running ? nodes.filter((n) => n.kind === "requirement" && n.at <= phase).length : readings.verified;
  const kernelsDone = running ? kernels.filter((k) => k.at <= phase).length : readings.kernels.length;

  const describe = useCallback(
    (n: PlacedNode, coneSize: number) =>
      `${n.id}: ${n.requirement ?? KIND_LABEL[n.kind]}, ${n.origin === "candidate" ? "the repair" : "the locked specification"}, ${fileName(n.file)}${n.lines ? ` lines ${n.lines[0]} to ${n.lines[1]}` : ""}; uses ${coneSize - 1} declarations`,
    [],
  );
  const longest = useMemo(
    () => nodes.map((n) => describe(n, coneOf(n.id).size)).reduce((a, b) => (b.length > a.length ? b : a), ""),
    [nodes, describe, coneOf],
  );
  const shown = active ? nodes[index.get(active)!] : undefined;
  const maxSize = Math.max(...guarantees.map((x) => x.size));
  const holeMax = Math.max(...hole.guarantees.map((x) => x.size));
  const cur = guarantees[g]!;
  const hcur = hole.guarantees[hg]!;

  const label = [
    `Dependency graph of the verified Balancer V2 repair: ${readings.requirements} requirement theorems in the centre, the lemmas and definitions they use around them, checked by ${readings.kernels.length} kernels on the outer orbit.`,
    `The same graph in layers: the ${readings.requirements} requirement theorems on top, the lemmas in the middle, the definitions and types at the bottom, the ${readings.kernels.length} kernels on an orbit.`,
    holeOn
      ? `The declarations ${hcur.id} of the ${hole.task.name} run ${hole.run.name} rests on, stacked by depth: ${hcur.size} declarations on ${hcur.levels} levels, ${hcur.holes.length ? `with ${count(hcur.holes.length)} left as sorry (${hcur.holes.map((x) => x.id).join(", ")}); the guarantee does not hold.` : "all proved."}`
      : `The declarations ${cur.id} rests on, stacked by depth: ${cur.size} declarations on ${cur.levels} levels, from the top ${cur.widths.join(", ")}.`,
  ][lens];

  return (
    <div className="hero-top" data-lens={lens + 1} data-hole={(lens === 2 && holeOn) || undefined}>
      <div className="hero-copy" id="hl-text">
        <div className="hl-stack hl-heads">
          <div className="hl-layer" data-on={lens === 0 || undefined}>
            <h1 id="home-title">{text.headline}</h1>
          </div>
          <div className="hl-layer" data-on={lens === 1 || undefined} aria-hidden={lens !== 1}>
            <h2 className="hl-title">{text.layersTitle}</h2>
          </div>
          <div className="hl-layer" data-on={lens === 2 || undefined} aria-hidden={lens !== 2}>
            <h2 className="hl-title">{text.guaranteeTitle}</h2>
          </div>
        </div>
        <div className="hl-stack hl-bodies">
          <div className="hl-layer" data-on={lens === 0 || undefined} aria-hidden={lens !== 0}>
            <p className="hero-sub">{text.summary}</p>
          </div>
          <div className="hl-layer" data-on={lens === 1 || undefined} aria-hidden={lens !== 1}>
            <p className="hero-sub">{text.layersText}</p>
          </div>
          <div className="hl-layer" data-on={lens === 2 || undefined} aria-hidden={lens !== 2}>
            <div className="hl-stack">
              {guarantees.map((x, i) => (
                <div key={x.id} className="hl-layer hl-guarantee" data-on={(!holeOn && i === g) || undefined} aria-hidden={holeOn || i !== g}>
                  <blockquote className="hl-quote">
                    <p>
                      &ldquo;<Quote text={x.statement} />&rdquo;
                    </p>
                  </blockquote>
                  <p className="hl-cite">
                    <code>{x.id}</code>, locked in the {text.task} task (from its README).
                  </p>
                  <dl className="hl-readings">
                    <div>
                      <dt>Declarations</dt>
                      <dd>{x.size}</dd>
                    </div>
                    <div>
                      <dt>Levels</dt>
                      <dd>{x.levels}</dd>
                    </div>
                    <div>
                      <dt>Kernels</dt>
                      <dd>
                        {readings.kernels.length} of {readings.kernels.length}
                      </dd>
                    </div>
                    <div>
                      <dt>Passport</dt>
                      <dd>
                        <a href={passportHref} tabIndex={lens === 2 && !holeOn && i === g ? undefined : -1}>
                          {readings.passport.slice(0, 8)}
                        </a>
                      </dd>
                    </div>
                  </dl>
                </div>
              ))}
              {hole.guarantees.map((x, i) => {
                const lemmas = x.holes.every((h) => h.kind === "lemma");
                const n = x.holes.length;
                return (
                  <div key={x.id} className="hl-layer hl-guarantee hl-holetext" data-on={(holeOn && i === hg) || undefined} aria-hidden={!holeOn || i !== hg}>
                    <blockquote className={`hl-quote${x.quote.length > 160 ? " hl-quote-long" : ""}`}>
                      <p>
                        &ldquo;<Quote text={x.quote} />&rdquo;
                      </p>
                    </blockquote>
                    <p className="hl-cite">
                      <code>{x.id}</code>, locked in the {hole.task.name} task (
                      {x.quoteFrom.kind === "readme" ? "from its README" : "the doc comment in its locked specification"}). In run {hole.run.name},{" "}
                      {n
                        ? `Muse left ${count(n)} ${lemmas ? (n === 1 ? "lemma" : "lemmas") : n === 1 ? "declaration" : "declarations"} of its proof as`
                        : "Muse proved every declaration of its shape"}
                      {n ? (
                        <>
                          {" "}
                          <code>sorry</code>
                        </>
                      ) : null}
                      {x.openInEveryRun ? `; it is open in all ${count(hole.runsMeasured)} ${hole.task.name} runs of that series` : ""}
                      {hole.laterVerified
                        ? `. Muse Code with ProofForge later proved it, with every other requirement, in ${hole.laterVerified.verified} of ${hole.laterVerified.runs} ${hole.laterVerified.experiment} runs`
                        : ""}
                      .
                    </p>
                    <dl className="hl-readings">
                      <div>
                        <dt>Declarations</dt>
                        <dd>{x.size}</dd>
                      </div>
                      <div>
                        <dt>Levels</dt>
                        <dd>{x.levels}</dd>
                      </div>
                      <div>
                        <dt>Holes</dt>
                        <dd className={n ? "hl-bad" : undefined}>{n}</dd>
                      </div>
                      <div>
                        <dt>Passport</dt>
                        <dd className="hl-none">none</dd>
                      </div>
                    </dl>
                  </div>
                );
              })}
            </div>
            <button
              type="button"
              role="switch"
              className="hl-switch"
              aria-checked={holeOn}
              tabIndex={lens === 2 ? undefined : -1}
              onClick={() => {
                stopTour();
                setHoleOn((x) => !x);
              }}
            >
              <span className="hl-switch-track" aria-hidden="true">
                <span className="hl-switch-thumb" />
              </span>
              A guarantee with a hole
            </button>
          </div>
        </div>
        {actions}
      </div>
      {figures}
      <div className="hl-stage-col" ref={stageEl} onPointerEnter={() => pause(true)} onPointerLeave={() => pause(false)} onFocus={() => pause(true)} onBlur={() => pause(false)}>
        <div className="hl-tabs" role="tablist" aria-label="Ways to look at the proof">
          {LENSES.map((name, i) => (
            <button
              key={name}
              type="button"
              role="tab"
              id={`hl-tab-${i}`}
              aria-selected={lens === i}
              aria-controls="hl-panel hl-text"
              tabIndex={lens === i ? 0 : -1}
              onClick={() => choose(i as LensIndex)}
              onKeyDown={tabKeys}
            >
              {name}
            </button>
          ))}
        </div>
        <figure className="pg" id="hl-panel" role="tabpanel" aria-labelledby={`hl-tab-${lens}`} data-running={running || undefined} aria-describedby="pg-caption">
          <div className="pg-stage">
            <svg className={`pg-svg${cone && lens !== 2 ? " pg-has-focus" : ""}`} viewBox={`-80 22 ${size + 160} ${size - 40}`} role="img" aria-label={label} onMouseLeave={() => setActive(null)}>
              <defs>
                <filter id="pg-soft" x="-1" y="-1" width="3" height="3">
                  <feGaussianBlur stdDeviation="5" />
                </filter>
              </defs>
              <g className="hl-main">
              <g className="pg-rings" aria-hidden="true">
                {Array.from({ length: 10 }, (_, r) => (
                  <ellipse
                    key={r}
                    ref={(el) => {
                      ringEls.current[r] = el;
                    }}
                    cx={c}
                    cy={c}
                    rx={rings[r] ?? 0}
                    ry={rings[r] ?? 0}
                    style={r < rings.length ? undefined : { display: "none" }}
                  />
                ))}
              </g>
              <g className="hl-only-1" aria-hidden="true">
                <path
                  className="pg-sweep"
                  d={`M${c} ${c - orbit}A${orbit} ${orbit} 0 0 1 ${(c + orbit * Math.sin(Math.PI / 4.5)).toFixed(1)} ${(c - orbit * Math.cos(Math.PI / 4.5)).toFixed(1)}`}
                  style={{ "--at": end } as CSSProperties}
                />
              </g>
              </g>
              <ellipse ref={orbitEl} className="pg-orbit" cx={c} cy={c} rx={orbit} ry={orbit} aria-hidden="true" />
              <g className="hl-main">
              <g className="pg-edges" aria-hidden="true">
                {edges.map((e, i) => {
                  const a = nodes[index.get(e.to)!]!;
                  const b = nodes[index.get(e.from)!]!;
                  return (
                    <path
                      key={`${e.from}>${e.to}`}
                      ref={(el) => {
                        edgeEls.current[i] = el;
                      }}
                      d={radialPath(a, b, c)}
                      pathLength={1}
                      strokeOpacity={0.15}
                      style={{ "--at": Math.max(0, e.at - 0.28) } as CSSProperties}
                    />
                  );
                })}
              </g>
              <g className="pg-spokes hl-only-1" aria-hidden="true">
                {kernels.map((k, i) => (
                  <line
                    key={k.name}
                    ref={(el) => {
                      spokeEls.current[i] = el;
                    }}
                    className="pg-spoke"
                    x1={c}
                    y1={c}
                    x2={k.x}
                    y2={k.y}
                    pathLength={1}
                    style={{ "--at": k.at } as CSSProperties}
                  />
                ))}
              </g>
              </g>
              <g className="hl-only-1" aria-hidden="true">
                <path
                  className="pg-hexring"
                  d={kernels.map((k, i) => `${i ? "L" : "M"}${k.x} ${k.y}`).join("") + "Z"}
                  pathLength={1}
                  style={{ "--at": kernels.length ? kernels[kernels.length - 1]!.at : 0 } as CSSProperties}
                />
              </g>
              <g className="pg-kernels" aria-hidden="true">
                {kernels.map((k, i) => {
                  const right = k.x > c + 1;
                  const left = k.x < c - 1;
                  const below = k.y > c;
                  return (
                    <g
                      key={k.name}
                      ref={(el) => {
                        kernelEls.current[i] = el;
                      }}
                      className="pg-kernel"
                      transform={`translate(${k.x} ${k.y})`}
                      style={{ "--at": k.at } as CSSProperties}
                    >
                      <rect className="pg-kernel-mark" x={-7} y={-7} width={14} height={14} rx={1.4} />
                      <g className="hl-only-1">
                        <text
                          className="pg-kernel-label"
                          x={right ? 16 : left ? -16 : 0}
                          y={!right && !left ? (below ? 26 : -15) : 5}
                          textAnchor={right ? "start" : left ? "end" : "middle"}
                        >
                          {k.name}
                        </text>
                      </g>
                    </g>
                  );
                })}
              </g>
              <g className="hl-main">
              <g className="pg-nodes">
                {nodes.map((n, i) => (
                  <g
                    key={n.id}
                    ref={(el) => {
                      nodeEls.current[i] = el;
                    }}
                    transform={`translate(${n.x} ${n.y})`}
                    className={`pg-node pg-${n.kind} pg-${n.origin}${cone?.has(n.id) ? " is-cone" : ""}${active === n.id ? " is-active" : ""}`}
                    style={{ "--at": n.at } as CSSProperties}
                    onMouseEnter={() => setActive(n.id)}
                  >
                    <circle className="pg-hit" r={9} />
                    <NodeMark n={n} />
                    {n.kind === "requirement" ? <rect className="pg-halo" x={-6} y={-6} width={12} height={12} rx={1.5} /> : null}
                  </g>
                ))}
              </g>
              <g className="hl-reqlabels" aria-hidden="true">
                {layers.labels.map((l) => (
                  <text key={l.id} x={l.x} y={layers.labelY - (l.lines.length - 1) * 18} textAnchor="middle">
                    {l.lines.map((line, j) => (
                      <tspan key={j} x={l.x} dy={j ? 18 : 0}>
                        {line}
                      </tspan>
                    ))}
                  </text>
                ))}
              </g>
              <g ref={coreEl} transform={`translate(${c} ${c})`} aria-hidden="true">
                <g className="pg-core" style={{ "--at": done + 0.25 } as CSSProperties}>
                  <rect className="pg-core-glow" x={-15} y={-15} width={30} height={30} rx={2} filter="url(#pg-soft)" />
                  <rect className="pg-core-block" x={-15} y={-15} width={30} height={30} rx={2} />
                </g>
              </g>
              </g>
              <g className="hl-holebell" aria-hidden="true">
                <g className="pg-rings">
                  {Array.from({ length: 10 }, (_, r) => (
                    <ellipse
                      key={r}
                      ref={(el) => {
                        holeRingEls.current[r] = el;
                      }}
                      style={{ display: "none" }}
                    />
                  ))}
                </g>
                <g className="hl-hole-edges">
                  {hole.edges.map((e, i) => (
                    <path
                      key={`${e.from}>${e.to}`}
                      ref={(el) => {
                        holeEdgeEls.current[i] = el;
                      }}
                      className={e.chain ? "hl-chain" : undefined}
                    />
                  ))}
                </g>
                <g className="hl-hole-nodes">
                  {hole.nodes.map((n, i) => (
                    <g
                      key={n.id}
                      ref={(el) => {
                        holeNodeEls.current[i] = el;
                      }}
                      className={`pg-${n.kind} pg-${n.origin} hl-role-${n.role}`}
                      transform={`translate(${holeStart[i]!.x} ${holeStart[i]!.y})`}
                    >
                      <HoleMark n={n} />
                    </g>
                  ))}
                </g>
                <g ref={holeCoreEl} transform={`translate(${c} ${hole.bells[hole.initial]!.levels[0]!.y})`}>
                  <rect className="hl-crown-empty" x={-15} y={-15} width={30} height={30} rx={2} />
                </g>
              </g>
            </svg>
          </div>
          <div className="hl-stack hl-foot">
            <div className="hl-layer pg-panel" data-on={lens !== 2 || undefined} aria-hidden={lens === 2}>
              <div className="hl-stack">
                <dl className="hl-layer pg-readings" data-on={!shown || undefined}>
                  <div>
                    <dt>Passport</dt>
                    <dd className="pg-mono" title={readings.passport}>
                      <a href={passportHref} tabIndex={lens === 2 ? -1 : undefined}>
                        {readings.passport.slice(0, 8)} {readings.passport.slice(8, 16)}
                      </a>
                    </dd>
                  </div>
                  <div>
                    <dt>Status</dt>
                    <dd>{running ? <span className="status status-working">CHECKING</span> : <span className="status status-verified">{readings.status}</span>}</dd>
                  </div>
                  <div>
                    <dt>Requirements</dt>
                    <dd className="pg-mono">
                      {reqDone} of {readings.requirements}
                    </dd>
                  </div>
                  <div>
                    <dt>Kernels</dt>
                    <dd className="pg-mono">
                      {kernelsDone} of {readings.kernels.length}
                    </dd>
                  </div>
                  <div>
                    <dt>Property cases</dt>
                    <dd className="pg-mono">{fmt(readings.propertyCases)}</dd>
                  </div>
                  <div>
                    <dt>Axioms</dt>
                    <dd className="pg-mono">{readings.axioms.join(", ")}</dd>
                  </div>
                </dl>
                <p className="hl-layer hl-hover pg-mono" data-on={shown ? true : undefined} aria-hidden="true">
                  {shown ? describe(shown, cone ? cone.size : 1) : ""}
                </p>
                <p className="hl-layer hl-hover pg-mono" aria-hidden="true">
                  {longest}
                </p>
              </div>
            </div>
            <div className="hl-layer hl-bars" data-on={(lens === 2 && !holeOn) || undefined} role="radiogroup" aria-label="Guarantee of the verified Balancer V2 repair" aria-hidden={lens !== 2 || holeOn}>
              {guarantees.map((x, i) => (
                <button
                  key={x.id}
                  id={`hl-bar-${i}`}
                  type="button"
                  role="radio"
                  aria-checked={i === g}
                  aria-label={`${x.short}, ${x.id}: ${x.size} declarations, proved`}
                  tabIndex={lens === 2 && !holeOn && i === g ? 0 : -1}
                  onClick={() => pick(i)}
                  onKeyDown={barKeys(guarantees.length, g, pick, "hl-bar")}
                >
                  <span className="hl-bar-n">{x.size}</span>
                  <span className="hl-bar-track">
                    <span className="hl-bar" style={{ height: `${((x.size / maxSize) * 100).toFixed(1)}%` }} />
                  </span>
                  <span className="hl-bar-name">
                    {x.lines.map((line, j) => (
                      <span key={j}>{line}</span>
                    ))}
                  </span>
                </button>
              ))}
            </div>
            <div className="hl-layer hl-bars hl-bars-hole" data-on={(lens === 2 && holeOn) || undefined} role="radiogroup" aria-label={`Guarantee of the ${hole.task.name} run ${hole.run.name}`} aria-hidden={lens !== 2 || !holeOn}>
              {hole.guarantees.map((x, i) => (
                <button
                  key={x.id}
                  id={`hl-hbar-${i}`}
                  type="button"
                  role="radio"
                  data-state={x.complete ? "complete" : "open"}
                  aria-checked={i === hg}
                  aria-label={`${x.short}, ${x.id}: ${x.size} declarations, ${x.complete ? "proved" : `hangs from ${x.holes.length} ${x.holes.length === 1 ? "hole" : "holes"}`}`}
                  tabIndex={lens === 2 && holeOn && i === hg ? 0 : -1}
                  onClick={() => pickHole(i)}
                  onKeyDown={barKeys(hole.guarantees.length, hg, pickHole, "hl-hbar")}
                >
                  <span className="hl-bar-n">{x.size}</span>
                  <span className="hl-bar-track">
                    <span className="hl-bar" style={{ height: `${((x.size / holeMax) * 100).toFixed(1)}%` }} />
                  </span>
                  <span className="hl-bar-name">
                    {x.lines.map((line, j) => (
                      <span key={j}>{line}</span>
                    ))}
                  </span>
                </button>
              ))}
            </div>
          </div>
        </figure>
      </div>
    </div>
  );
}
