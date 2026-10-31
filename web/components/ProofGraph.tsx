"use client";

import { useEffect, useMemo, useRef, useState, type CSSProperties } from "react";
import type { GraphLayout, PlacedNode } from "@/lib/proofgraph";

export interface ProofGraphProps {
  layout: GraphLayout;
  /** Every direct use [user, used], for the dependency cone shown on hover. */
  uses: [string, string][];
  readings: {
    passport: string;
    status: string;
    requirements: number;
    verified: number;
    kernels: string[];
    propertyCases: number;
    axioms: string[];
    declarations: number;
  };
  passportHref: string;
}

const KIND_LABEL: Record<PlacedNode["kind"], string> = {
  requirement: "requirement",
  lemma: "lemma",
  definition: "definition",
  type: "type",
};

const fmt = (n: number) => n.toLocaleString("en-US");
const fileName = (f: string) => f.split("/").pop() ?? f;

/** One node: a square for the requirements and the locked specification, a dot for the repair's lemmas. */
function NodeMark({ n }: { n: PlacedNode }) {
  if (n.kind === "requirement") return <rect x={n.x - 6} y={n.y - 6} width={12} height={12} rx={1.5} />;
  if (n.origin === "specification") return <rect x={n.x - 3.6} y={n.y - 3.6} width={7.2} height={7.2} rx={1} />;
  if (n.kind === "definition") return <rect x={n.x - 3.2} y={n.y - 3.2} width={6.4} height={6.4} rx={3.2} />;
  return <circle cx={n.x} cy={n.y} r={2.9} />;
}

/** A gentle curve from the declaration used to its user, bent toward the centre. */
function edgePath(a: { x: number; y: number }, b: { x: number; y: number }, c: number) {
  const mx = (a.x + b.x) / 2;
  const my = (a.y + b.y) / 2;
  const qx = mx + (c - mx) * 0.22;
  const qy = my + (c - my) * 0.22;
  return `M${a.x} ${a.y}Q${qx.toFixed(1)} ${qy.toFixed(1)} ${b.x} ${b.y}`;
}

export function ProofGraph({ layout, uses, readings, passportHref }: ProofGraphProps) {
  const { size, center: c, nodes, edges, kernels, rings, orbit, done } = layout;
  const byId = useMemo(() => new Map(nodes.map((n) => [n.id, n])), [nodes]);
  const end = kernels.length ? kernels[kernels.length - 1]!.at + 0.5 : done + 1;

  // Hover: the declaration and everything it uses.
  const [active, setActive] = useState<string | null>(null);
  const usedBy = useMemo(() => {
    const out = new Map<string, string[]>();
    for (const [a, b] of uses) out.set(a, [...(out.get(a) ?? []), b]);
    return out;
  }, [uses]);
  const coneOf = (id: string) => {
    const seen = new Set<string>([id]);
    const stack = [id];
    while (stack.length) for (const m of usedBy.get(stack.pop()!) ?? []) if (!seen.has(m)) (seen.add(m), stack.push(m));
    return seen;
  };
  const cone = useMemo(() => (active ? coneOf(active) : null), [active, usedBy]); // eslint-disable-line react-hooks/exhaustive-deps

  // The readout follows the check: which declaration it reaches, how many requirements and kernels are done.
  // Server render and reduced motion show the end state; state changes only when the readout does.
  const order = useMemo(() => nodes.slice().sort((a, b) => a.at - b.at), [nodes]);
  const [phase, setPhase] = useState<{ t: number; key: string } | null>(null);
  const raf = useRef(0);
  useEffect(() => {
    if (matchMedia("(prefers-reduced-motion: reduce)").matches) return;
    const root = document.documentElement;
    let t0 = 0;
    let last = "";
    const tick = (now: number) => {
      const t = (now - t0) / 1000;
      if (t >= end + 0.2) {
        setPhase(null);
        return;
      }
      const reached = order.filter((n) => n.at <= t).length;
      const k = kernels.filter((x) => x.at <= t).length;
      const key = `${reached}/${k}`;
      if (key !== last) {
        last = key;
        setPhase({ t, key });
      }
      raf.current = requestAnimationFrame(tick);
    };
    const start = () => {
      t0 = performance.now();
      raf.current = requestAnimationFrame(tick);
    };
    let mo: MutationObserver | null = null;
    if (root.getAttribute("data-splash") === "on") {
      // The graph animation is paused under the splash and starts when it ends.
      mo = new MutationObserver(() => {
        if (root.getAttribute("data-splash") !== "on") {
          mo?.disconnect();
          start();
        }
      });
      mo.observe(root, { attributes: true, attributeFilter: ["data-splash"] });
    } else start();
    return () => {
      mo?.disconnect();
      cancelAnimationFrame(raf.current);
    };
  }, [end, order, kernels]);

  const clock = phase?.t ?? null;
  const running = clock !== null;
  const reqDone = running ? nodes.filter((n) => n.kind === "requirement" && n.at <= clock).length : readings.verified;
  const kernelsDone = running ? kernels.filter((k) => k.at <= clock).length : readings.kernels.length;
  const current = running ? [...order].reverse().find((n) => n.at <= clock) : undefined;
  const verified = !running;

  const describe = (n: (typeof nodes)[number], coneSize: number) =>
    `${n.id}: ${n.requirement ?? KIND_LABEL[n.kind]}, ${n.origin === "candidate" ? "the repair" : "the locked specification"}, ${fileName(n.file)}${n.lines ? ` lines ${n.lines[0]} to ${n.lines[1]}` : ""}; uses ${coneSize - 1} declarations`;
  // The readout reserves the height of its longest text (monospace, so the most characters), so hovering never moves the page.
  const longest = useMemo(() => {
    const texts = nodes.map((n) => describe(n, coneOf(n.id).size));
    texts.push(...kernels.map((k) => `kernel check: ${k.name}`), ...nodes.map((n) => `checking ${n.id}`));
    texts.push(`${fmt(readings.declarations)} declarations, ${fmt(uses.length)} uses, all checked`);
    return texts.reduce((a, b) => (b.length > a.length ? b : a), "");
  }, [nodes, kernels, readings, uses, usedBy]); // eslint-disable-line react-hooks/exhaustive-deps

  const shown = active ? byId.get(active) : undefined;
  const status = shown
    ? describe(shown, cone ? cone.size : 1)
    : running
      ? clock! > done
        ? `kernel check: ${kernels.filter((k) => k.at <= clock!).map((k) => k.name).pop() ?? "starting"}`
        : `checking ${current?.id ?? "definitions"}`
      : `${fmt(readings.declarations)} declarations, ${fmt(uses.length)} uses, all checked`;

  const label = `Dependency graph of the verified Balancer V2 repair: ${readings.requirements} requirement theorems in the centre, the lemmas and definitions they use around them, checked by ${readings.kernels.length} kernels on the outer orbit.`;

  return (
    <figure className="pg" data-running={running || undefined} aria-describedby="pg-caption">
      <div className="pg-stage">
        <svg
          className={`pg-svg${cone ? " pg-has-focus" : ""}`}
          viewBox={`-70 -14 ${size + 140} ${size + 28}`}
          role="img"
          aria-label={label}
          onMouseLeave={() => setActive(null)}
        >
          <defs>
            <filter id="pg-soft" x="-1" y="-1" width="3" height="3">
              <feGaussianBlur stdDeviation="5" />
            </filter>
          </defs>
          <g className="pg-rings" aria-hidden="true">
            {rings.map((r) => (
              <circle key={r} cx={c} cy={c} r={r} />
            ))}
          </g>
          <circle className="pg-orbit" cx={c} cy={c} r={orbit} aria-hidden="true" />
          <path
            className="pg-sweep"
            d={`M${c} ${c - orbit}A${orbit} ${orbit} 0 0 1 ${(c + orbit * Math.sin(Math.PI / 4.5)).toFixed(1)} ${(c - orbit * Math.cos(Math.PI / 4.5)).toFixed(1)}`}
            style={{ "--at": end } as CSSProperties}
            aria-hidden="true"
          />
          <g className="pg-edges" aria-hidden="true">
            {edges.map((e) => {
              const a = byId.get(e.to)!;
              const b = byId.get(e.from)!;
              const lit = cone ? cone.has(e.from) && cone.has(e.to) : false;
              return (
                <path
                  key={`${e.from}>${e.to}`}
                  d={edgePath(a, b, c)}
                  pathLength={1}
                  className={lit ? "is-cone" : undefined}
                  style={{ "--at": Math.max(0, e.at - 0.28) } as CSSProperties}
                />
              );
            })}
          </g>
          <g className="pg-kernels" aria-hidden="true">
            {kernels.map((k) => {
              const right = k.x > c + 1;
              const left = k.x < c - 1;
              const below = k.y > c;
              return (
                <g key={k.name} className="pg-kernel" style={{ "--at": k.at } as CSSProperties}>
                  <line className="pg-spoke" x1={c} y1={c} x2={k.x} y2={k.y} pathLength={1} />
                  <rect className="pg-kernel-mark" x={k.x - 7} y={k.y - 7} width={14} height={14} rx={2} />
                  <text
                    className="pg-kernel-label"
                    x={right ? k.x + 16 : left ? k.x - 16 : k.x}
                    y={!right && !left ? (below ? k.y + 26 : k.y - 15) : k.y + 5}
                    textAnchor={right ? "start" : left ? "end" : "middle"}
                  >
                    {k.name}
                  </text>
                </g>
              );
            })}
          </g>
          <g className="pg-nodes">
            {nodes.map((n) => (
              <g
                key={n.id}
                className={`pg-node pg-${n.kind} pg-${n.origin}${cone?.has(n.id) ? " is-cone" : ""}${active === n.id ? " is-active" : ""}`}
                style={{ "--at": n.at } as CSSProperties}
                onMouseEnter={() => setActive(n.id)}
              >
                <circle className="pg-hit" cx={n.x} cy={n.y} r={9} />
                <NodeMark n={n} />
                {n.kind === "requirement" ? <rect className="pg-halo" x={n.x - 6} y={n.y - 6} width={12} height={12} rx={1.5} /> : null}
              </g>
            ))}
          </g>
          <g className="pg-core" style={{ "--at": done + 0.25 } as CSSProperties} aria-hidden="true">
            <rect className="pg-core-glow" x={c - 15} y={c - 15} width={30} height={30} rx={2} filter="url(#pg-soft)" />
            <rect className="pg-core-block" x={c - 15} y={c - 15} width={30} height={30} rx={2} />
          </g>
        </svg>
      </div>
      <div className="pg-panel">
        <dl className="pg-readings">
          <div>
            <dt>Passport</dt>
            <dd className="pg-mono" title={readings.passport}>
              <a href={passportHref}>{readings.passport.slice(0, 8)} {readings.passport.slice(8, 16)}</a>
            </dd>
          </div>
          <div>
            <dt>Status</dt>
            <dd>
              {verified ? (
                <span className="status status-verified">{readings.status}</span>
              ) : (
                <span className="status status-working">CHECKING</span>
              )}
            </dd>
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
        <p className="pg-status pg-mono" aria-live="off">
          <span className="pg-status-reserve" aria-hidden="true">
            {longest}
          </span>
          <span>{status}</span>
        </p>
      </div>
    </figure>
  );
}
