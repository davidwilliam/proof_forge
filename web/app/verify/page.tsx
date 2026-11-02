import type { Metadata } from "next";
import { CopyButton } from "@/components/DownloadJson";
import { inlineCode } from "@/components/InlineCode";
import { githubFile } from "@/lib/flagships";
import guide from "@/generated/verify-guide.json";
import "./verify.css";

const description =
  "Reproduce a ProofForge Passport on your own machine: clone the repository, build the pinned Lean image and run bin/proofforge verify, which reruns every check and compares each hash and status with the Passport.";

export const metadata: Metadata = {
  title: "Verify a Passport yourself, ProofForge",
  description,
  openGraph: { title: "Verify a Passport yourself, ProofForge", description },
};

interface Block {
  source: string;
  heading: string;
  before: string;
  code: string;
  after: string;
}

const G = guide as {
  usage: string;
  quickstart: Block;
  reproduce: Block;
  running: Block;
  agentSteps: string[];
  compared: { name: string; text: string }[];
  comparedSource: string[];
  samples: { title: string; source: string; passport: string | null; command: string | null; sha256: string | null; status: string | null; text: string; result: string }[];
};

const anchor = (h: string) => `${githubFile("README.md")}#${h.toLowerCase().replace(/[^a-z0-9 -]/g, "").replace(/ /g, "-")}`;

function CodeBlock({ b, label }: { b: { code: string }; label: string }) {
  return (
    <div className="vf-code">
      <div className="vf-code-bar">
        <span>{label}</span>
        <CopyButton text={b.code} label={`Copy: ${label}`} />
      </div>
      <pre>
        <code>
          {b.code.split("\n").map((l, i, a) => (
            <span key={i} className={l.startsWith("#") ? "vf-comment" : undefined}>
              {l}
              {i < a.length - 1 ? "\n" : ""}
            </span>
          ))}
        </code>
      </pre>
    </div>
  );
}

/** A verify transcript as rows: what was compared, and whether it was the same. */
function Readout({ text }: { text: string }) {
  const lines = text.split("\n");
  return (
    <ol className="vf-readout" aria-label="verify output, line by line">
      {lines.map((l, i) => {
        const same = /^(same|DIFFERENT|note)\s+(.+?): (.*)$/.exec(l);
        if (same) {
          return (
            <li key={i} className={`vf-row vf-row-${same[1]!.toLowerCase()}`}>
              <span className="vf-mark" aria-hidden="true" />
              <span className="vf-word">{same[1]}</span>
              <span className="vf-name">{same[2]}</span>
              <span className="vf-val">{same[3]}</span>
            </li>
          );
        }
        const nc = /^not compared\s+(.+?): (.*)$/.exec(l);
        if (nc) {
          return (
            <li key={i} className="vf-row vf-row-nc">
              <span className="vf-mark" aria-hidden="true" />
              <span className="vf-word">not compared</span>
              <span className="vf-name">{nc[1]}</span>
              <span className="vf-val vf-val-wrap">{nc[2]}</span>
            </li>
          );
        }
        if (/^(reproduced|NOT reproduced)/.test(l)) {
          return (
            <li key={i} className="vf-result">
              {l}
            </li>
          );
        }
        return (
          <li key={i} className="vf-plain">
            {l}
          </li>
        );
      })}
    </ol>
  );
}

export default function VerifyPage() {
  const [local, cross] = G.samples;
  const repLines = G.reproduce.code.split("\n");
  const clone = repLines.find((l) => l.startsWith("git clone"))!;
  const image = repLines.find((l) => l.startsWith("docker build"))!;
  const steps = [
    { title: "Clone the repository", code: clone },
    { title: "Build the pinned Lean image", code: image },
    { title: "Reproduce a Passport", code: local!.command! },
  ];
  return (
    <main id="main" className="page verify-page">
      <h1>Verify a Passport yourself</h1>
      <p className="lead">
        Every ProofForge verdict is a Passport, bound by hash to the specification, the source, the executable and the judge image. You do not have
        to trust this site: {inlineCode(G.reproduce.after)}
      </p>

      <section className="vf-hero" aria-labelledby="vf-steps">
        <div className="vf-steps-col">
          <h2 id="vf-steps">Three commands</h2>
          <p className="muted small">{G.reproduce.before}</p>
          <ol className="vf-steps">
            {steps.map((s, i) => (
              <li key={s.title}>
                <span className="vf-n" aria-hidden="true">
                  {i + 1}
                </span>
                <div className="vf-step-body">
                  <p className="vf-step-title">{s.title}</p>
                  <div className="vf-cmd">
                    <code>{s.code}</code>
                    <CopyButton text={s.code} label={`Copy: ${s.title}`} />
                  </div>
                </div>
              </li>
            ))}
          </ol>
          <p className="muted small">
            Usage, from <code>bin/proofforge</code>: <code>{G.usage}</code>
          </p>
        </div>
        <figure className="vf-terminal">
          <figcaption>
            <span className="vf-term-title">{local!.title}</span>
            <span className="vf-term-meta">
              Passport <span className="hash">{local!.sha256!.slice(0, 16)}</span>, {local!.status}; output committed as{" "}
              <a href={githubFile(local!.source)}>{local!.source}</a>
            </span>
          </figcaption>
          <p className="vf-prompt">
            <span aria-hidden="true">$ </span>
            {local!.command}
          </p>
          <Readout text={local!.text} />
        </figure>
      </section>

      <section className="vf-section" aria-labelledby="vf-compared">
        <h2 id="vf-compared">What verify compares</h2>
        <p className="vf-lead">
          Each line of the output is one comparison between the Passport and a fresh run of the same pipeline on the same candidate. Any
          difference makes the result &ldquo;NOT reproduced&rdquo; and the exit code 1. Sources: <a href={githubFile(G.comparedSource[0]!)}>{G.comparedSource[0]}</a>{" "}
          and <a href={githubFile(G.comparedSource[1]!)}>{G.comparedSource[1]}</a>.
        </p>
        <ul className="vf-compared">
          {G.compared.map((c) => (
            <li key={c.name}>
              <span className="vf-c-name">{c.name}</span>
              <span className="vf-c-text">{c.text}</span>
            </li>
          ))}
        </ul>
      </section>

      <section className="vf-section" aria-labelledby="vf-cross">
        <h2 id="vf-cross">On another CPU architecture</h2>
        <p className="vf-lead">
          An executable built for another CPU architecture has a different hash, so verify compares that hash only on the Passport&apos;s platform.
          Elsewhere it rebuilds the executable from the same source and re-tests it, and says so.
        </p>
        <figure className="vf-terminal vf-terminal-wide">
          <figcaption>
            <span className="vf-term-title">{cross!.title}</span>
            <span className="vf-term-meta">
              Committed as <a href={githubFile(cross!.source)}>{cross!.source}</a>
            </span>
          </figcaption>
          <Readout text={cross!.text} />
        </figure>
      </section>

      <section className="vf-section" aria-labelledby="vf-all">
        <h2 id="vf-all">Every Passport on the home page</h2>
        <p className="vf-lead">
          From the README, <a href={anchor(G.reproduce.heading)}>{G.reproduce.heading}</a>. {G.reproduce.before}
        </p>
        <CodeBlock b={G.reproduce} label={`README.md, ${G.reproduce.heading}`} />
      </section>

      <section className="vf-section vf-two" aria-labelledby="vf-nodocker">
        <div>
          <h2 id="vf-nodocker">Without Docker</h2>
          <p className="vf-lead">{inlineCode(G.quickstart.before)}</p>
          <CodeBlock b={G.quickstart} label={`README.md, ${G.quickstart.heading}`} />
          <p className="muted small">{inlineCode(G.quickstart.after)}</p>
        </div>
        <div>
          <h2 id="vf-own">Check your own candidate</h2>
          <p className="vf-lead">{inlineCode(G.running.before)}</p>
          <CodeBlock b={G.running} label={`README.md, ${G.running.heading}`} />
          <p className="muted small">From AGENTS.md, the last two steps of fixing a task:</p>
          <ol className="vf-agent-steps">
            {G.agentSteps.map((s) => (
              <li key={s}>{inlineCode(s.replace(/^\d+\.\s*/, ""))}</li>
            ))}
          </ol>
        </div>
      </section>
    </main>
  );
}
