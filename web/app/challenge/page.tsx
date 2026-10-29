import type { Metadata } from "next";
import { getJson, type TaskSummary } from "@/lib/api";
import { requirementText } from "@/lib/format";
import { ErrorBox } from "@/components/ui";
import { ChallengeRunner } from "./ChallengeRunner";

export const dynamic = "force-dynamic";
export const metadata: Metadata = { title: "Challenge, ProofForge" };

export default async function ChallengePage() {
  let variants: string[];
  let tasks: TaskSummary[];
  try {
    [variants, tasks] = await Promise.all([getJson<string[]>("/api/challenge/variants"), getJson<TaskSummary[]>("/api/tasks")]);
  } catch (e) {
    return (
      <main className="page">
        <h1>Challenge a hidden variant</h1>
        <ErrorBox title="Could not load challenge variants." message={(e as Error).message} />
      </main>
    );
  }
  const flagship = tasks.find((t) => t.id === "payout-flagship");
  const texts = Object.fromEntries((flagship?.requirements ?? []).map((r) => [r.id, requirementText(r.text, r.id)]));
  return (
    <main className="page">
      <h1>Challenge a hidden variant</h1>
      <p className="lead">
        Each variant is a buggy payout component that has not been shown to anyone. ProofForge builds its executable and runs the
        requirement-derived property tests against it. A violation comes with a concrete witness: the input and the output that breaks a locked
        requirement. The target is a witness within 20 seconds.
      </p>
      <ChallengeRunner variants={variants} requirementTexts={texts} />
    </main>
  );
}
