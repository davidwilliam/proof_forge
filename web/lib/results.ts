// Normalizes GET /api/results. Keys are result directories ("e1-<label>", "e2-<label>");
// E1 values are the e1.json summary, E2 values are { generated, rows }.

export interface E1Summary {
  tasks?: string[];
  arms?: Record<string, { completed: number; n: number; usd_list_total?: number }>;
  pairs?: Record<
    string,
    {
      n: number;
      diff: number;
      ci95_cluster?: [number, number];
      discordant?: { hi_only: number; lo_only: number };
      mcnemar_p?: number;
    }
  >;
  families?: Record<string, Record<string, { completed: number; n: number }>>;
  [k: string]: unknown;
}

export interface E2Row {
  task: string;
  family: string;
  case: string;
  label: string;
  note?: string;
  sha256?: string | null;
  ordinary: { accepted: boolean; reason?: string };
  proofforge: { accepted: boolean; judge?: boolean; binary?: string; reason?: string };
}

export interface E2Data {
  generated?: string;
  rows: E2Row[];
}

export interface Rate {
  count: number;
  of: number;
}

export interface E2Aggregate {
  arms: { arm: E2Arm; falseAccept: Rate; falseReject: Rate }[];
  families: { family: string; arms: Record<E2Arm, { falseAccept: Rate; falseReject: Rate }> }[];
}

export type E2Arm = "ordinary" | "binary" | "proofforge";
export const e2ArmLabels: Record<E2Arm, string> = {
  ordinary: "Ordinary checking",
  binary: "Rebuild and property tests only",
  proofforge: "ProofForge",
};

export function isE2(v: unknown): v is E2Data {
  return !!v && typeof v === "object" && Array.isArray((v as E2Data).rows);
}

export function isE1(v: unknown): v is E1Summary {
  return !!v && typeof v === "object" && (typeof (v as E1Summary).arms === "object" || typeof (v as E1Summary).pairs === "object");
}

function rates(rows: E2Row[], arm: E2Arm) {
  // Older records without a binary result are not evidence of rejection.
  if (arm === "binary") rows = rows.filter((r) => r.proofforge.binary !== undefined);
  const bad = rows.filter((r) => r.label === "bad");
  const good = rows.filter((r) => r.label === "good");
  const accepted = (r: E2Row) => arm === "binary" ? r.proofforge.binary === "PASS" : r[arm].accepted;
  return {
    falseAccept: { count: bad.filter(accepted).length, of: bad.length },
    falseReject: { count: good.filter((r) => !accepted(r)).length, of: good.length },
  };
}

export function aggregateE2(data: E2Data): E2Aggregate {
  const arms = (["ordinary", "binary", "proofforge"] as const).map((arm) => ({ arm, ...rates(data.rows, arm) }));
  const fams = [...new Set(data.rows.map((r) => r.family))].sort();
  const families = fams.map((family) => {
    const rows = data.rows.filter((r) => r.family === family);
    return { family, arms: { ordinary: rates(rows, "ordinary"), binary: rates(rows, "binary"), proofforge: rates(rows, "proofforge") } };
  });
  return { arms, families };
}

/** The same sentence the E1 report prints for a paired comparison. */
export function pairText(key: string, p: NonNullable<E1Summary["pairs"]>[string]): string {
  const [hi, lo] = key.split("-");
  const sign = (x: number) => (x >= 0 ? `+${x.toFixed(3)}` : x.toFixed(3));
  const parts = [`${hi} vs ${lo} on ${p.n} paired tasks: difference in completion rate ${sign(p.diff)}`];
  if (p.ci95_cluster) parts.push(`95% interval [${sign(p.ci95_cluster[0])}, ${sign(p.ci95_cluster[1])}] (bootstrap over base specifications)`);
  if (p.discordant) parts.push(`discordant pairs: ${hi} only ${p.discordant.hi_only}, ${lo} only ${p.discordant.lo_only}`);
  if (p.mcnemar_p != null) parts.push(`McNemar exact p = ${p.mcnemar_p.toFixed(4)}`);
  return parts.join("; ") + ".";
}
