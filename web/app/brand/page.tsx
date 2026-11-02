import fs from "node:fs";
import path from "node:path";
import type { Metadata } from "next";
import { CopyButton } from "@/components/DownloadJson";
import { Lockup } from "@/components/SiteHeader";
import { githubFile } from "@/lib/flagships";
import {
  ASSETS,
  KIT,
  KIT_DOWNLOADS,
  LOCKUP,
  MIN_SIZES,
  MISUSE,
  PALETTE,
  PALETTE_GROUPS,
  REFERENCE_SHEETS,
  SYMBOL,
  TYPE,
  WORDMARK,
  type KitFile,
} from "@/lib/brand";
import "./brand.css";

const description = `The ProofForge identity kit, version ${KIT.version}: the inference mark, its lockups, the palette with hex values, typography, clear space, minimum sizes and misuse rules, with the kit, the guide and every SVG to download.`;

export const metadata: Metadata = {
  title: "Brand kit, ProofForge",
  description,
  openGraph: { title: "Brand kit, ProofForge", description },
};

/** File size from public/, in the units a download button shows. */
function size(rel: string): string {
  try {
    const b = fs.statSync(path.join(process.cwd(), "public", rel)).size;
    if (b >= 1e6) return `${(b / 1e6).toFixed(1)} MB`;
    return `${Math.max(1, Math.round(b / 1e3))} KB`;
  } catch {
    return "";
  }
}

const ext = (p: string) => p.split(".").pop()!.toUpperCase();
const fileName = (p: string) => p.split("/").pop()!;
type Rect = readonly [number, number, number, number, number];
const R = ({ r, className }: { r: Rect; className?: string }) => <rect x={r[0]} y={r[1]} width={r[2]} height={r[3]} rx={r[4] || undefined} className={className} />;

/** The symbol on its 100 unit grid, drawn from the kit's geometry, with its parts named. */
function Anatomy() {
  const [p1, p2] = SYMBOL.premises;
  const gridLines = Array.from({ length: 11 }, (_, i) => i * 10);
  return (
    <svg className="bk-anatomy" viewBox="-6 12 196 80" role="img" aria-labelledby="bk-anatomy-title">
      <title id="bk-anatomy-title">
        The symbol on its 100 unit grid: two premises above the inference line, and the conclusion block below it.
      </title>
      <g className="bk-grid" aria-hidden="true">
        {gridLines.map((v) => (
          <line key={`v${v}`} x1={v} y1={14} x2={v} y2={90} />
        ))}
        {gridLines
          .filter((v) => v >= 20 && v <= 90)
          .map((v) => (
            <line key={`h${v}`} x1={0} y1={v} x2={100} y2={v} />
          ))}
      </g>
      <rect className="bk-inkbox" x={8} y={22} width={84} height={60} />
      <R r={p1 as Rect} className="bk-ink" />
      <R r={p2 as Rect} className="bk-ink" />
      <R r={SYMBOL.line as Rect} className="bk-ink" />
      <R r={SYMBOL.block as Rect} className="bk-block" />
      <g className="bk-leader" aria-hidden="true">
        <polyline points="88,28 104,28" />
        <polyline points="94,46.5 104,46.5" />
        <polyline points="63,71 104,71" />
      </g>
      <g className="bk-label">
        <text x={107} y={30}>
          premises
        </text>
        <text x={107} y={48.5}>
          inference line
        </text>
        <text x={107} y={73}>
          conclusion: proved
        </text>
        <text x={107} y={86} className="bk-label-muted">
          ink box 84 by 60
        </text>
      </g>
    </svg>
  );
}

/** The horizontal lockup with the alignment rule drawn over it, in the artboard's units (font size 100). */
function Alignment() {
  const [aw, ah] = LOCKUP.artboard;
  const base = LOCKUP.pad - LOCKUP.wordInk[1]; // the baseline: 8 + 70
  const centre = base - LOCKUP.inkCentreEm * 100;
  const mk = LOCKUP.markInk;
  const wd = LOCKUP.wordInk;
  const x = (v: number) => v + LOCKUP.pad;
  const y = (v: number) => v + base;
  return (
    <figure className="bk-figure">
      <svg className="bk-align" viewBox={`0 0 ${aw} ${ah + 22}`} role="img" aria-labelledby="bk-align-title">
        <title id="bk-align-title">
          The horizontal lockup: the centre of the mark ink is level with the centre of the wordmark ink, 0.25 em above the baseline.
        </title>
        <image className="lockup-primary" href="/brand/proofforge-horizontal-primary.svg" x={0} y={0} width={aw} height={ah} />
        <image className="lockup-reversed" href="/brand/proofforge-horizontal-reversed.svg" x={0} y={0} width={aw} height={ah} />
        <line className="bk-al-top" x1={0} y1={y(wd[1])} x2={aw} y2={y(wd[1])} />
        <line className="bk-al-top" x1={0} y1={y(wd[3])} x2={aw} y2={y(wd[3])} />
        <line className="bk-al-base" x1={0} y1={base} x2={aw} y2={base} />
        <line className="bk-al-centre" x1={0} y1={centre} x2={aw} y2={centre} />
        <rect className="bk-al-box" x={x(mk[0])} y={y(mk[1])} width={mk[2] - mk[0]} height={mk[3] - mk[1]} />
        <g className="bk-al-gap">
          <line x1={x(mk[2])} y1={ah + 12} x2={x(wd[0])} y2={ah + 12} />
          <line x1={x(mk[2])} y1={ah + 6} x2={x(mk[2])} y2={ah + 18} />
          <line x1={x(wd[0])} y1={ah + 6} x2={x(wd[0])} y2={ah + 18} />
        </g>
      </svg>
      <figcaption>
        <ul className="bk-legend">
          <li>
            <span className="bk-key bk-key-centre" aria-hidden="true" />
            Ink centre of both parts, {LOCKUP.inkCentreEm} em above the baseline
          </li>
          <li>
            <span className="bk-key bk-key-base" aria-hidden="true" />
            Baseline
          </li>
          <li>
            <span className="bk-key bk-key-top" aria-hidden="true" />
            Top of the f and bottom of the p and g
          </li>
          <li>
            <span className="bk-key bk-key-box" aria-hidden="true" />
            Mark ink, {LOCKUP.markHeightEm} em high
          </li>
          <li>
            <span className="bk-key bk-key-gap" aria-hidden="true" />
            Gap from mark ink to wordmark ink, {LOCKUP.gapEm} em
          </li>
        </ul>
      </figcaption>
    </figure>
  );
}

/** Clear space: half the symbol height on every side of the lockup's ink. */
function ClearSpace() {
  const [aw, ah] = LOCKUP.artboard;
  const half = (LOCKUP.markInk[3] - LOCKUP.markInk[1]) / 2;
  const top = LOCKUP.pad;
  const bottom = LOCKUP.pad + LOCKUP.wordInk[3] - LOCKUP.wordInk[1];
  const left = LOCKUP.pad;
  const right = LOCKUP.pad + LOCKUP.wordInk[2];
  const m = half + 6;
  return (
    <svg className="bk-clear" viewBox={`${left - m} ${top - m} ${right - left + 2 * m} ${bottom - top + 2 * m}`} role="img" aria-labelledby="bk-clear-title">
      <title id="bk-clear-title">The lockup inside its clear space: half the symbol height on every side.</title>
      <rect className="bk-clear-zone" x={left - half} y={top - half} width={right - left + 2 * half} height={bottom - top + 2 * half} />
      <rect className="bk-clear-ink" x={left} y={top} width={right - left} height={bottom - top} />
      <image className="lockup-primary" href="/brand/proofforge-horizontal-primary.svg" x={0} y={0} width={aw} height={ah} />
      <image className="lockup-reversed" href="/brand/proofforge-horizontal-reversed.svg" x={0} y={0} width={aw} height={ah} />
    </svg>
  );
}

/** One way not to use the mark, drawn from the same geometry. */
function Misuse({ kind }: { kind: "colour" | "rotate" | "glow" | "accent" }) {
  const [p1, p2] = SYMBOL.premises;
  return (
    <svg className={`bk-misuse-mark bk-misuse-${kind}`} viewBox="0 0 100 100" aria-hidden="true">
      {kind === "glow" ? (
        <defs>
          <filter id="bk-glow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="5" />
          </filter>
        </defs>
      ) : null}
      <g transform={kind === "rotate" ? "rotate(-14 50 52)" : undefined}>
        <R r={p1 as Rect} className={kind === "accent" ? "bk-block" : "bk-ink"} />
        <R r={p2 as Rect} className="bk-ink" />
        <R r={SYMBOL.line as Rect} className="bk-ink" />
        {kind === "glow" ? <R r={SYMBOL.block as Rect} className="bk-block bk-glow" /> : null}
        <R r={SYMBOL.block as Rect} className={kind === "colour" ? "bk-wrong-verified" : "bk-block"} />
      </g>
    </svg>
  );
}

const MISUSE_SHOWN = [
  { kind: "colour", text: "Verified in the block: verdict colours never enter the mark." },
  { kind: "accent", text: "A second Forge accent beside the block." },
  { kind: "rotate", text: "The mark rotated." },
  { kind: "glow", text: "A glow behind the static block." },
] as const;

function FileLink({ f, primary = false }: { f: KitFile; primary?: boolean }) {
  return (
    <a className={`bk-dl${primary ? " bk-dl-primary" : ""}`} href={`/${f.path}`} download={fileName(f.path)}>
      <span className="bk-dl-label">{f.label}</span>
      <span className="bk-dl-meta">
        {ext(f.path)}, {size(f.path)}
      </span>
    </a>
  );
}

export default function BrandPage() {
  const zip = KIT_DOWNLOADS[0]!;
  const guide = KIT_DOWNLOADS[1]!;
  return (
    <main id="main" className="page brand-page">
      <h1>Brand kit</h1>
      <p className="lead">
        The ProofForge identity, version {KIT.version}, accepted on {KIT.accepted}: {KIT.proposal}. Production vector artwork with an outlined
        wordmark, so no font or raster dependency remains in the masters.
      </p>
      <div className="bk-actions">
        <FileLink f={zip} primary />
        <FileLink f={guide} />
        <a className="bk-dl" href="#bk-downloads">
          <span className="bk-dl-label">Every file</span>
          <span className="bk-dl-meta">SVG, PDF, JSON, CSS</span>
        </a>
      </div>
      <figure className="bk-overview">
        <img
          src="/brand/kit/ProofForge-Kit-Overview.svg"
          alt="The ProofForge identity on one sheet: the primary and reversed lockups, the symbol with its parts named, the palette and the four type families."
          width={1600}
          height={1120}
        />
        <figcaption className="muted small">The kit overview sheet, as delivered in the kit.</figcaption>
      </figure>

      <section className="bk-section bk-mark" aria-labelledby="bk-mark">
        <div className="bk-mark-text">
          <h2 id="bk-mark">The mark: an inference</h2>
          <p>
            The symbol is an inference rule as logicians write it: two premises above the line, the conclusion below. The conclusion is the
            block, the end-of-proof mark: proved. It also reads as a fraction, the arithmetic that financial code gets wrong.
          </p>
          <p className="muted">
            It sits on a 100 unit grid with an ink box of 84 by 60 units. At {SYMBOL.smallUpToPx} px and below the small cut thickens the
            inference line to 10 units, leaving gaps of 8, with every edge on a whole pixel, so at 16 px the premises, the line and the block
            stay separate.
          </p>
          <details className="bk-details">
            <summary>Construction, in grid units</summary>
            <div className="table-scroll">
              <table>
                <thead>
                  <tr>
                    <th scope="col">Part</th>
                    <th scope="col">x, y</th>
                    <th scope="col">Width by height</th>
                    <th scope="col">Corner radius</th>
                  </tr>
                </thead>
                <tbody>
                  {(
                    [
                      ["Premise, left", SYMBOL.premises[0]],
                      ["Premise, right", SYMBOL.premises[1]],
                      ["Inference line", SYMBOL.line],
                      ["Conclusion block", SYMBOL.block],
                      [`Small cut line, ${SYMBOL.smallUpToPx} px and below`, SYMBOL.smallLine],
                    ] as const
                  ).map(([name, r]) => (
                    <tr key={name}>
                      <td>{name}</td>
                      <td className="num">
                        {r[0]}, {r[1]}
                      </td>
                      <td className="num">
                        {r[2]} by {r[3]}
                      </td>
                      <td className="num">{r[4]}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
            <p className="muted small">
              Set aside during selection: {KIT.setAside.join(" and ")}.
            </p>
          </details>
        </div>
        <div className="bk-mark-art">
          <Anatomy />
        </div>
      </section>

      <section className="bk-section" aria-labelledby="bk-lockups">
        <h2 id="bk-lockups">Lockups</h2>
        <p className="bk-lead">
          Horizontal is the default, for headers, documents and app bars. Primary has Ink bars, line and lettering with a Forge deep block, for
          light grounds; reversed has #F2F5F8 bars, line and lettering with a Forge block, for Void and Graphite. Mono ink and mono white put
          everything in one colour.
        </p>
        <ul className="bk-assets">
          {ASSETS.map((a) => (
            <li key={a.path} className={`bk-asset${a.wide ? " bk-asset-wide" : ""}`}>
              <div className={`bk-tile bk-ground-${a.ground}`}>
                <img src={`/${a.path}`} alt={a.label} className={a.wide ? "bk-img-wide" : "bk-img-square"} />
              </div>
              <div className="bk-asset-text">
                <p className="bk-asset-name">{a.label}</p>
                <p className="bk-asset-use">{a.use}</p>
                <a href={`/${a.path}`} download={fileName(a.path)} className="bk-asset-dl">
                  SVG, {size(a.path)}
                </a>
              </div>
            </li>
          ))}
        </ul>
      </section>

      <section className="bk-section" aria-labelledby="bk-align">
        <h2 id="bk-align">The alignment rule</h2>
        <p className="bk-lead">
          In the horizontal lockup the mark is {LOCKUP.markHeightEm} of the wordmark font size high, and its vertical centre is level with the
          wordmark ink centre: the midpoint between the top of the f and the bottom of the p and g, {LOCKUP.inkCentreEm} em above the baseline.
          The gap from mark ink to wordmark ink is {LOCKUP.gapEm} em. At font size 100 the mark runs from {LOCKUP.markInk[1]} to{" "}
          {LOCKUP.markInk[3]} and the wordmark ink from {LOCKUP.wordInk[1]} to {LOCKUP.wordInk[3]}; both centres are -25. Positions come from
          the outlined glyph bounds, not set by eye.
        </p>
        <Alignment />
        <p className="muted small">
          The stacked lockup centres the mark, {LOCKUP.stackedMarkHeightEm} em high, above the wordmark ink, {LOCKUP.stackedGapEm} em above the
          top of the f.
        </p>
      </section>

      <section className="bk-section bk-two" aria-labelledby="bk-space">
        <div>
          <h2 id="bk-space">Clear space and minimum sizes</h2>
          <p className="bk-lead">Keep clear space of half the symbol height on every side of any lockup.</p>
          <ClearSpace />
        </div>
        <div>
          <ul className="bk-min" aria-label="Minimum sizes, shown at that size">
            {MIN_SIZES.map((m, i) => (
              <li key={m.what}>
                <span className="bk-min-art">
                  {i === 0 ? (
                    <>
                      <img className="lockup-primary" src="/brand/proofforge-icon-primary.svg" alt="" width={16} height={16} />
                      <img className="lockup-reversed" src="/brand/proofforge-icon-reversed.svg" alt="" width={16} height={16} />
                    </>
                  ) : i === 1 ? (
                    <Lockup className="bk-min-lockup" />
                  ) : (
                    <>
                      <img className="lockup-primary bk-min-word" src="/brand/kit/proofforge-wordmark-primary.svg" alt="" />
                      <img className="lockup-reversed bk-min-word" src="/brand/kit/proofforge-wordmark-reversed.svg" alt="" />
                    </>
                  )}
                </span>
                <span className="bk-min-what">{m.what}</span>
                <span className="bk-min-size">{m.size}</span>
              </li>
            ))}
          </ul>
        </div>
      </section>

      <section className="bk-section" aria-labelledby="bk-colour">
        <h2 id="bk-colour">Colour</h2>
        <p className="bk-lead">
          Exact sRGB values; PNGs carry sRGB, and PDFs are RGB with no press CMYK or Pantone match claimed. Light is the default; dark follows the
          system or <code>data-theme=&quot;dark&quot;</code>.
        </p>
        {PALETTE_GROUPS.map((g) => (
          <div key={g.group} className="bk-pgroup">
            <h3>{g.group}</h3>
            <p className="muted small">{g.text}</p>
            <ul className="bk-swatches">
              {PALETTE.filter((s) => s.group === g.group).map((s) => (
                <li key={s.key} className="bk-swatch">
                  <span className="bk-chip" style={{ background: s.hex }} aria-hidden="true" />
                  <span className="bk-sw-name">{s.name}</span>
                  <span className="bk-sw-hex">
                    <code>{s.hex}</code>
                    <CopyButton text={s.hex} label={`Copy ${s.name} ${s.hex}`} />
                  </span>
                  <span className="bk-sw-use">{s.use.charAt(0).toUpperCase() + s.use.slice(1)}.</span>
                  {s.contrast ? <span className="bk-sw-contrast">{s.contrast}</span> : null}
                </li>
              ))}
            </ul>
          </div>
        ))}
      </section>

      <section className="bk-section" aria-labelledby="bk-type">
        <h2 id="bk-type">Typography</h2>
        <p className="bk-lead">
          The wordmark is {WORDMARK.face}, lowercase &ldquo;{WORDMARK.text}&rdquo;, tracked at {WORDMARK.trackingEm} em, kerned and frozen into
          outlines: use the artwork, never a live font. All four families are under the SIL Open Font License. Labels are sentence case, with no
          uppercase labels above headings.
        </p>
        <ul className="bk-types">
          {TYPE.map((t) => (
            <li key={t.family}>
              <p className={`bk-type-sample ${t.cls}`}>{t.sample}</p>
              <p className="bk-type-meta">
                <strong>{t.family}</strong>, {t.weights}. {t.use}
              </p>
            </li>
          ))}
        </ul>
      </section>

      <section className="bk-section" aria-labelledby="bk-misuse">
        <h2 id="bk-misuse">Misuse</h2>
        <ul className="bk-misuse" aria-label="Examples of misuse">
          {MISUSE_SHOWN.map((m) => (
            <li key={m.kind}>
              <div className="bk-misuse-tile">
                <Misuse kind={m.kind} />
                <svg className="bk-no" viewBox="0 0 20 20" aria-hidden="true">
                  <circle cx="10" cy="10" r="9" />
                  <path d="M6.5 6.5l7 7M13.5 6.5l-7 7" />
                </svg>
              </div>
              <p>
                <strong>Do not:</strong> {m.text}
              </p>
            </li>
          ))}
        </ul>
        <h3 className="bk-h3">Do not</h3>
        <ul className="bk-rules">
          {MISUSE.map((r) => (
            <li key={r}>{r}</li>
          ))}
        </ul>
      </section>

      <section className="bk-section" id="bk-downloads" aria-labelledby="bk-dl-title">
        <h2 id="bk-dl-title">Downloads</h2>
        <ul className="bk-files">
          {[...KIT_DOWNLOADS, ...REFERENCE_SHEETS].map((f) => (
            <li key={f.path}>
              <a href={`/${f.path}`} download={fileName(f.path)}>
                {f.label}
              </a>
              <span className="bk-file-meta">
                {ext(f.path)}, {size(f.path)}
              </span>
              <span className="bk-file-text">{f.text}</span>
            </li>
          ))}
          {ASSETS.map((a) => (
            <li key={a.path}>
              <a href={`/${a.path}`} download={fileName(a.path)}>
                {a.label}
              </a>
              <span className="bk-file-meta">SVG, {size(a.path)}</span>
              <span className="bk-file-text">{fileName(a.path)}</span>
            </li>
          ))}
        </ul>
        <p className="muted small">
          The ProofForge name and logo are not covered by the code&apos;s Apache License 2.0. Use the kit to refer to ProofForge, as its guide
          describes; <a href={githubFile("NOTICE")}>NOTICE</a> gives the terms and the licenses of the fonts.
        </p>
        <p className="muted small bk-zip-note">
          The zip also holds PNG exports up to 4096 px wide, vector PDFs, favicons and installable icons, app icons with ICO and ICNS, reference
          sheets, the build sources with their fonts, and the splash animation as HTML, MP4 and GIF.
        </p>
      </section>
    </main>
  );
}
