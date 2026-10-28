import Link from "next/link";
import type { Metadata } from "next";
import type { ReactNode } from "react";
import { ApiError, apiUrl, getJson, type CheckRecord, type Passport } from "@/lib/api";
import { commandText, formatDuration, formatInt, formatMs, formatUsd, innerCommand, prettyJson, requirementText, shortHash } from "@/lib/format";
import { Code, ErrorBox, Hash, Status } from "@/components/ui";
import { Markdown } from "@/components/Markdown";
import { CopyText, DownloadJson } from "@/components/DownloadJson";

export const dynamic = "force-dynamic";

export async function generateMetadata({ params }: { params: Promise<{ sha: string }> }): Promise<Metadata> {
  const { sha } = await params;
  return { title: `Passport ${sha.slice(0, 12)}, ProofForge` };
}

function CheckRow({ name, r, what }: { name: string; r: CheckRecord | null | undefined; what: string }) {
  if (!r) {
    return (
      <tr>
        <td>{name}</td>
        <td colSpan={4} className="muted">
          not run
        </td>
      </tr>
    );
  }
  return (
    <tr>
      <td>
        {name}
        <div className="small muted">{what}</div>
      </td>
      <td>
        <code>{innerCommand(r.command) || "none"}</code>
        {r.command && typeof r.command !== "string" ? (
          <details>
            <summary className="small">Full command</summary>
            <Code text={commandText(r.command)} wrap />
          </details>
        ) : null}
      </td>
      <td className="num">
        <Status value={r.exit_code === 0 ? "PASS" : "FAILED"}>exit {r.exit_code ?? "none"}</Status>
      </td>
      <td className="num">{formatMs(r.elapsed_ms)}</td>
      <td className="small">
        <div>
          stdout <Hash value={r.stdout_sha256} />
        </div>
        <div>
          stderr <Hash value={r.stderr_sha256} />
        </div>
      </td>
    </tr>
  );
}

export default async function PassportPage({ params }: { params: Promise<{ sha: string }> }) {
  const { sha } = await params;
  let p: Passport;
  let comment: string | null = null;
  try {
    p = await getJson<Passport>(`/api/passports/${encodeURIComponent(sha)}`);
    comment = (await getJson<{ markdown: string }>(`/api/passports/${encodeURIComponent(sha)}/comment`).catch(() => null))?.markdown ?? null;
  } catch (e) {
    const notFound = e instanceof ApiError && e.status === 404;
    return (
      <main className="page">
        <ErrorBox title={notFound ? `No Passport with sha256 ${sha}.` : "Could not load the Passport."} message={notFound ? undefined : (e as Error).message} />
      </main>
    );
  }

  const pt = p.checks.property_tests;
  const prov = p.provenance;
  const budget = prov?.budget;

  return (
    <main className="page">
      <h1>Proof Passport for {p.task.id}</h1>
      <p className="muted">
        Passport sha256 <Hash value={p.passport_sha256} full />. Generated {p.generated}. Schema version {p.schema_version}.
      </p>
      <div className="panel" style={{ fontSize: "1.2rem" }}>
        Component status: <Status value={p.status} /> for <code>{p.task.definitions.join(", ")}</code> ({p.requirements.filter((r) => r.status === "VERIFIED").length} of{" "}
        {p.requirements.length} requirements verified).
        {!p.proof_check.accepted ? (
          <div style={{ fontSize: "1rem", marginTop: 8 }}>
            Proof check rejected:
            <ul>
              {p.proof_check.reasons.map((r, i) => (
                <li key={i}>
                  <code>{r}</code>
                </li>
              ))}
            </ul>
          </div>
        ) : null}
      </div>
      <div className="row" style={{ marginTop: 12 }}>
        <DownloadJson data={p} filename={`passport-${p.passport_sha256.slice(0, 12)}.json`} label="Download Passport JSON" />
        <a href={apiUrl(`/api/passports/${p.passport_sha256}`)}>Raw JSON from the API</a>
      </div>

      <section>
        <h2>Requirements</h2>
        <div className="table-scroll">
          <table>
            <thead>
              <tr>
                <th>Requirement</th>
                <th>Statement</th>
                <th>Status</th>
                <th>Axioms used</th>
              </tr>
            </thead>
            <tbody>
              {p.requirements.map((r) => (
                <tr key={r.id}>
                  <td>
                    <div className="mono" style={{ fontWeight: 700 }}>
                      {r.id}
                    </div>
                    <div>{requirementText(r.text, r.id)}</div>
                    {r.witness ? (
                      <details open>
                        <summary>Witness: {r.witness.message}</summary>
                        <div className="small muted">Input</div>
                        <Code text={prettyJson(r.witness.input)} />
                        <div className="small muted">Output of the rebuilt binary</div>
                        <Code text={prettyJson(r.witness.output)} />
                      </details>
                    ) : null}
                  </td>
                  <td>
                    <code>
                      theorem {r.theorem} : {r.statement}
                    </code>
                    <div className="small muted">
                      sha256 <Hash value={r.statement_sha256} />
                    </div>
                  </td>
                  <td>
                    <Status value={r.status} />
                    {r.binary_violations ? <div className="small">{formatInt(r.binary_violations)} binary violations</div> : null}
                  </td>
                  <td className="mono small">{r.axioms_used?.length ? r.axioms_used.join(", ") : r.axioms_used ? "none" : "not audited"}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <p className="small muted">Permitted axioms: {p.permitted_axioms.join(", ")}.</p>
      </section>

      <section>
        <h2>Checks</h2>
        <div className="table-scroll">
          <table>
            <thead>
              <tr>
                <th>Check</th>
                <th>Command</th>
                <th className="num">Exit</th>
                <th className="num">Time</th>
                <th>Output hashes</th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>Tree check</td>
                <td colSpan={4}>
                  <Status value={p.checks.tree.passed ? "PASS" : "FAILED"} /> {p.checks.tree.problems.join("; ")}
                </td>
              </tr>
              <tr>
                <td>Implementation scan</td>
                <td colSpan={4}>
                  <Status value={p.checks.impl_scan.passed ? "PASS" : "FAILED"} /> {p.checks.impl_scan.problems.join("; ")}
                </td>
              </tr>
              <CheckRow name="Comparator" r={p.checks.comparator} what="locked challenge against the solution in a fresh sandbox" />
              <CheckRow name="leanchecker" r={p.checks.leanchecker} what="replays the environment in the kernel" />
              <CheckRow name="Axiom audit" r={p.checks.axiom_audit} what="#print axioms for each requirement" />
              <CheckRow name="Binary build" r={pt.build} what="executable from the same source" />
            </tbody>
          </table>
        </div>
        <h3 style={{ marginTop: 16 }}>Comparator kernels</h3>
        {p.checks.comparator_kernels.length ? (
          <p>
            Accepted by {p.checks.comparator_kernels.length} kernels: {p.checks.comparator_kernels.join(", ")}.
          </p>
        ) : (
          <p className="muted">No kernel acceptance recorded.</p>
        )}
        <h3>Property tests on the executable</h3>
        <p>
          {formatInt(pt.cases)} cases and {formatInt(pt.followup_cases)} follow-up cases, seed {pt.seed ?? "none"}:{" "}
          {pt.violations && Object.keys(pt.violations).length
            ? Object.entries(pt.violations)
                .map(([k, v]) => `${k} ${v}`)
                .join(", ")
            : "no violations"}
          .
        </p>
      </section>

      <section>
        <h2>Executable</h2>
        <dl className="kv">
          <dt>Target</dt>
          <dd className="mono">{p.executable.target}</dd>
          <dt>sha256</dt>
          <dd>
            <Hash value={p.executable.sha256} full />
          </dd>
          <dt>Property tests</dt>
          <dd>
            <Status value={p.executable.status} />
          </dd>
          <dt>JSON wrapper</dt>
          <dd>
            <Status value={p.executable.wrapper} /> The wrapper (app/Main.lean) parses and serializes JSON; it is tested, not proved.
          </dd>
        </dl>
      </section>

      <section>
        <h2>Solution and locked files</h2>
        <dl className="kv">
          {Object.entries(p.solution.files).map(([f, h]) => (
            <FragmentKV key={f} k={`Solution ${f}`} v={<Hash value={h} full />} />
          ))}
          <dt>Solution tree</dt>
          <dd>
            <Hash value={p.solution.solution_tree_sha256} full />
          </dd>
          <dt>Locked manifest</dt>
          <dd>
            <Hash value={p.locked.manifest_sha256} full />
          </dd>
          <dt>Lean toolchain</dt>
          <dd className="mono">{p.toolchain.lean}</dd>
          <dt>Judge image</dt>
          <dd>
            <Hash value={p.toolchain.judge_image} full />
          </dd>
        </dl>
        <div className="table-scroll">
          <table style={{ marginTop: 12 }}>
            <thead>
              <tr>
                <th>Locked file</th>
                <th>sha256</th>
              </tr>
            </thead>
            <tbody>
              {Object.entries(p.locked.files).map(([f, h]) => (
                <tr key={f}>
                  <td className="mono">{f}</td>
                  <td>
                    <Hash value={h} full />
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </section>

      <section>
        <h2>Trust assumptions</h2>
        <ul>
          {p.trust_assumptions.map((t) => (
            <li key={t}>{t}</li>
          ))}
        </ul>
        <h2>Scope</h2>
        <p>{p.scope}</p>
      </section>

      <section>
        <h2>Provenance</h2>
        {prov ? (
          <dl className="kv">
            {prov.model ? <FragmentKV k="Model" v={<span className="mono">{prov.model}</span>} /> : null}
            {prov.planner ? <FragmentKV k="Planner" v={<span className="mono">{prov.planner}</span>} /> : null}
            {prov.arm ? <FragmentKV k="Arm" v={prov.arm} /> : null}
            {prov.mode ? <FragmentKV k="Mode" v={`${prov.mode}${prov.effort ? `, ${prov.effort} effort` : ""}`} /> : null}
            {prov.versions != null ? <FragmentKV k="Candidate versions" v={formatInt(prov.versions)} /> : null}
            {(budget?.elapsed_s ?? prov.elapsed_s) != null ? <FragmentKV k="Session time" v={formatDuration(budget?.elapsed_s ?? prov.elapsed_s)} /> : null}
            {budget?.usd_list != null ? <FragmentKV k="Cost at list prices" v={formatUsd(budget.usd_list)} /> : null}
            {budget?.usd_actual != null ? <FragmentKV k="Cost billed" v={formatUsd(budget.usd_actual)} /> : null}
            {prov.usage ? (
              <FragmentKV
                k="Tokens"
                v={Object.entries(prov.usage)
                  .map(([k, v]) => `${k} ${formatInt(v)}`)
                  .join(", ")}
              />
            ) : null}
          </dl>
        ) : (
          <p className="muted">No provenance: this candidate was submitted directly for verification.</p>
        )}
        {prov ? (
          <details>
            <summary>Full provenance record</summary>
            <Code text={prettyJson(prov)} />
          </details>
        ) : null}
      </section>

      <section>
        <h2>Reproduce</h2>
        <Code text={p.reproduce} wrap />
        <CopyText text={p.reproduce} label="Copy command" />
      </section>

      {comment ? (
        <section>
          <h2>PR comment</h2>
          <div className="card">
            <Markdown source={comment} />
          </div>
          <details style={{ marginTop: 8 }}>
            <summary>Markdown source</summary>
            <Code text={comment} />
          </details>
        </section>
      ) : null}

      <p style={{ marginTop: 32 }}>
        <Link href="/">Back to the forge session</Link>. Passport {shortHash(p.passport_sha256)}.
      </p>
    </main>
  );
}

function FragmentKV({ k, v }: { k: string; v: ReactNode }) {
  return (
    <>
      <dt>{k}</dt>
      <dd>{v}</dd>
    </>
  );
}
