// "The shape of a guarantee": the declarations each requirement theorem of a flagship task uses, in
// the verified Muse repairs, and the holes of runs that did not verify (generated/shapes/*.json,
// written by scripts/proof-shapes.mjs and checked by tests/shapes.test.ts). Definitions are in the
// data (`definitions`) and in docs/SHAPES.md.

import summary from "@/generated/shapes/summary.json";
import balancer from "@/generated/shapes/verified-balancer.json";
import cetus from "@/generated/shapes/verified-cetus.json";
import euler from "@/generated/shapes/verified-euler.json";
import hundred from "@/generated/shapes/verified-hundred.json";
import knight from "@/generated/shapes/verified-knight.json";
import compoundA01 from "@/generated/shapes/holes-compound-A0-1.json";
import compoundA22 from "@/generated/shapes/holes-compound-A2-2.json";
import compoundTopdown3 from "@/generated/shapes/holes-compound-A2-topdown-3.json";
import balancerA01 from "@/generated/shapes/holes-balancer-A0-1.json";

export type ShapeNodeKind = "requirement" | "lemma" | "definition" | "type";
export type HoleKind = "sorry" | "error";

export interface ShapeNode {
  id: string;
  kind: ShapeNodeKind;
  origin: "candidate" | "specification";
  file: string;
  lines: [number, number] | null;
  depth: number;
  requirement?: string;
  hole: HoleKind | null;
  /** ProofForgeFin declarations the node mentions (not nodes). */
  library?: string[];
}

export interface Guarantee {
  /** Requirement id, e.g. REQ-SWAP-KEEPS-VALUE. */
  id: string;
  theorem: string;
  property: string;
  /** Node id of the requirement theorem. */
  node: string;
  /** Doc comment of the property in the locked specification. */
  statement: { text: string; file: string; lines: [number, number] };
  /** The task README's requirement table row, when one names it. */
  readme: { text: string; file: string; line: number } | null;
  size: number;
  depth: number;
  width: number[];
  composition: { requirements: number; lemmas: number; definitions: number; types: number; candidate: number; specification: number };
  hangsFrom: string[];
  proved: number;
  complete: boolean;
  missing?: boolean;
}

export interface Shape {
  title: string;
  slug: string;
  role: "verified" | "attempt";
  definitions: Record<string, string>;
  rule: string;
  task: { id: string; name: string; namespace: string };
  run: { dir: string; arm: string; model: string; planner: string | null; finalStatus: Record<string, string> | null };
  source: { file: string; sha256: string };
  passport: { file: string; sha256: string; status: string; requirements: Record<string, string>; kernels: number } | null;
  counts: Record<"guarantees" | "complete" | "nodes" | "edges" | "holes" | "lemmas" | "definitions" | "types" | "excluded", number>;
  guarantees: Guarantee[];
  loadBearing: {
    every: { id: string; kind: ShapeNodeKind; origin: string; depth: number }[];
    lemmas: { id: string; origin: string; depth: number; guarantees: number }[];
  };
  holes: { id: string; kind: ShapeNodeKind; hole: HoleKind; origin: string; file: string; lines: [number, number]; depth: number; guarantees: string[] }[];
  nodes: ShapeNode[];
  edges: [string, string][];
  excluded: string[];
}

const as = (x: unknown) => x as Shape;

/** Verified Muse repairs with a Passport, one per flagship that has one. */
export const VERIFIED_SHAPES: Shape[] = [balancer, cetus, euler, hundred, knight].map(as);

/** Runs that did not verify: the best Compound attempts and a Muse-alone Balancer run. */
export const ATTEMPT_SHAPES: Shape[] = [compoundA01, compoundA22, compoundTopdown3, balancerA01].map(as);

export const SHAPES_SUMMARY = summary;
