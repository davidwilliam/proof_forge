import { ImageResponse } from "next/og";
import { CETUS_HOTFIX, COUNTEREXAMPLES } from "@/lib/contribution";
import { E2 } from "@/lib/evidence";
import { FEATURED, HEADLINE } from "@/lib/flagships";

// The card shown when a link to the site is shared (Open Graph and, through twitter-image.tsx, X).
// Every figure comes from the same data modules as the home page.

export const alt = HEADLINE;
export const size = { width: 1200, height: 630 };
export const contentType = "image/png";

const ink = "#0d1117";
const muted = "#566070";
const bad = "#b3261e";
const badBg = "#fdeceb";
const ok = "#0c7339";
const okBg = "#e8f5ee";

export default function OpenGraphImage() {
  const versions = FEATURED.timeline;
  const ordinary = E2.arms.find((a) => a.key === "ordinary")!;
  const pf = E2.arms.find((a) => a.key === "proofforge")!;
  return new ImageResponse(
    (
      <div style={{ width: "100%", height: "100%", display: "flex", flexDirection: "column", background: "#f6f7f9", padding: "52px 60px", fontFamily: "sans-serif", color: ink }}>
        <div style={{ display: "flex", alignItems: "center", gap: 14, fontSize: 30, fontWeight: 700 }}>
          <svg width="40" height="40" viewBox="0 0 32 32">
            <rect width="32" height="32" rx="8" fill={ink} />
            <path d="M9 16.5l4.5 4.5L23 11.5" fill="none" stroke="#fff" strokeWidth="3.2" strokeLinecap="round" strokeLinejoin="round" />
          </svg>
          ProofForge
        </div>
        <div style={{ display: "flex", fontSize: 64, lineHeight: 1.08, letterSpacing: -1.5, marginTop: 26, maxWidth: 1080 }}>
          {HEADLINE.replace(/\.$/, "")}
        </div>
        <div style={{ display: "flex", fontSize: 28, color: muted, marginTop: 24 }}>
          {`${FEATURED.incident}, ${FEATURED.loss.amount} ${FEATURED.loss.short}: one locked specification, four versions of the code`}
        </div>
        <div style={{ display: "flex", gap: 14, marginTop: 20 }}>
          {versions.map((v) => (
            <div
              key={v.key}
              style={{
                display: "flex",
                flexDirection: "column",
                flex: 1,
                padding: "14px 16px",
                borderRadius: 12,
                background: v.verdict === "REFUTED" ? badBg : okBg,
                borderLeft: `6px solid ${v.verdict === "REFUTED" ? bad : ok}`,
              }}
            >
              <div style={{ display: "flex", fontSize: 26 }}>{v.title}</div>
              <div style={{ display: "flex", fontSize: 24, color: v.verdict === "REFUTED" ? bad : ok, marginTop: 8 }}>{v.verdict}</div>
            </div>
          ))}
        </div>
        <div style={{ display: "flex", flexDirection: "column", gap: 10, fontSize: 26, color: ink, marginTop: 30 }}>
          <div style={{ display: "flex" }}>
            {`Hotfix counterexample: checkedShlw(2^192) = (0, false), a Lean theorem accepted by ${CETUS_HOTFIX.kernels} kernels.`}
          </div>
          <div style={{ display: "flex", color: muted }}>
            {`Seeded bad repairs accepted: ordinary checking ${ordinary.badAccepted} of ${E2.bad}, ProofForge ${pf.badAccepted}. ${COUNTEREXAMPLES.kernelChecked} of ${COUNTEREXAMPLES.refuted} refutations kernel-checked.`}
          </div>
        </div>
      </div>
    ),
    size,
  );
}
