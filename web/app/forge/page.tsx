import { createHash } from "node:crypto";
import type { Metadata } from "next";
import { getJson, type TaskDetail } from "@/lib/api";
import { predicateSource, requirementText } from "@/lib/format";
import { ErrorBox } from "@/components/ui";
import { ForgeSession, type ReqView } from "../ForgeSession";

export const dynamic = "force-dynamic";
export const metadata: Metadata = { title: "Forge session, ProofForge" };

const DEFAULT_TASK = "payout-flagship";

export default async function Page({ searchParams }: { searchParams: Promise<Record<string, string | string[] | undefined>> }) {
  const sp = await searchParams;
  const one = (v: string | string[] | undefined) => (Array.isArray(v) ? v[0] : v);
  const taskId = one(sp.task) || DEFAULT_TASK;

  let task: TaskDetail;
  let recordings: string[];
  try {
    [task, recordings] = await Promise.all([getJson<TaskDetail>(`/api/tasks/${encodeURIComponent(taskId)}`), getJson<string[]>("/api/recordings")]);
  } catch (e) {
    return (
      <main id="main" className="page">
        <ErrorBox title="Could not load the task from the ProofForge API." message={(e as Error).message}>
          <p className="small" style={{ margin: "8px 0 0" }}>
            Start the API with <code>.venv/bin/uvicorn server.app:app --port 8765</code> and reload this page.
          </p>
        </ErrorBox>
      </main>
    );
  }

  const spec = Object.entries(task.files).find(([p]) => p.endsWith("/Spec.lean"))?.[1];
  const reqs: ReqView[] = task.requirements.map((r) => ({
    id: r.id,
    theorem: r.theorem,
    statement: r.statement,
    text: requirementText(r.text, r.id),
    predicate: predicateSource(spec, r.statement),
    statementSha: createHash("sha256").update(r.statement ?? "").digest("hex"),
  }));

  const preferred = process.env.NEXT_PUBLIC_DEFAULT_RECORDING || "flagship-a2-run7";
  const requested = one(sp.recording);
  const defaultRecording =
    (requested && recordings.includes(requested) && requested) || (recordings.includes(preferred) ? preferred : recordings[0] ?? "");

  return (
    <ForgeSession
      task={{ id: task.id, issue: task.issue, family: task.family, namespace: task.namespace, definitions: task.definitions, manifestSha: task.manifest_sha256 }}
      requirements={reqs}
      recordings={recordings}
      defaultRecording={defaultRecording}
      initialJob={one(sp.job) ?? null}
    />
  );
}
