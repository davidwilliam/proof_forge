import { readFile } from "node:fs/promises";
import path from "node:path";
import { ImageResponse } from "next/og";
import { CETUS_HOTFIX } from "@/lib/contribution";
import { E2 } from "@/lib/evidence";
import { FEATURED, HEADLINE } from "@/lib/flagships";
import { SEAL_KERNELS, SEAL_RING } from "@/components/Seal";

// The card shown when a link to the site is shared (Open Graph and, through twitter-image.tsx, X), in the
// identity kit: Void ground, the reversed lockup, the headline in Instrument Serif. Every figure comes from
// the same data modules as the home page.

export const alt = HEADLINE;
export const size = { width: 1200, height: 630 };
export const contentType = "image/png";

const VOID = "#05070B";
const GRAPHITE = "#0E131B";
const STEEL = "#1C2532";
const MIST = "#A9B4C2";
const FROST = "#F2F5F8";
const INK = "#0B0F15";
const VERIFIED = "#3DDC97";
const REFUTED = "#FF5D5D";


export default async function OpenGraphImage() {
  const [serif, display, sans, sansSemi, mono, lockup] = await Promise.all([
    readFile(path.join(process.cwd(), "assets", "og-fonts", "InstrumentSerif-Regular.ttf")),
    readFile(path.join(process.cwd(), "assets", "og-fonts", "SpaceGrotesk-SemiBold.ttf")),
    readFile(path.join(process.cwd(), "assets", "og-fonts", "Inter-Regular.ttf")),
    readFile(path.join(process.cwd(), "assets", "og-fonts", "Inter-SemiBold.ttf")),
    readFile(path.join(process.cwd(), "assets", "og-fonts", "JetBrainsMono-Regular.ttf")),
    readFile(path.join(process.cwd(), "public", "brand", "proofforge-horizontal-reversed.svg")),
  ]);
  const lockupSrc = `data:image/svg+xml;base64,${lockup.toString("base64")}`;
  const versions = FEATURED.timeline;
  const ordinary = E2.arms.find((a) => a.key === "ordinary")!;
  const pf = E2.arms.find((a) => a.key === "proofforge")!;
  return new ImageResponse(
    (
      <div style={{ width: "100%", height: "100%", display: "flex", flexDirection: "column", background: VOID, padding: "48px 60px", fontFamily: "Inter", color: FROST }}>
        {/* The kit's lockup artboard is 624 by 106 with an 8 unit margin. */}
        <img src={lockupSrc} width={236} height={40} alt="" style={{ marginLeft: -3 }} />
        <div style={{ display: "flex", fontFamily: "Instrument Serif", fontSize: 78, lineHeight: 1.02, marginTop: 36, width: 1060, color: FROST }}>
          {HEADLINE}
        </div>
        <div style={{ display: "flex", fontSize: 25, color: MIST, marginTop: 22 }}>
          {`${FEATURED.incident}, ${FEATURED.loss.amount} ${FEATURED.loss.short}: one specification, four versions of the code`}
        </div>
        <div style={{ display: "flex", gap: 14, marginTop: 30 }}>
          {versions.map((v) => (
            <div
              key={v.key}
              style={{ display: "flex", flexDirection: "column", flex: 1, padding: "14px 16px", borderRadius: 12, background: GRAPHITE, border: `1px solid ${STEEL}` }}
            >
              <div style={{ display: "flex", fontFamily: "Space Grotesk", fontSize: 24, color: FROST }}>{v.title}</div>
              <div style={{ display: "flex", marginTop: 10 }}>
                <div
                  style={{
                    display: "flex",
                    alignItems: "center",
                    gap: 8,
                    fontFamily: "JetBrains Mono",
                    fontSize: 18,
                    color: INK,
                    background: v.verdict === "REFUTED" ? REFUTED : VERIFIED,
                    padding: "2px 10px",
                    borderRadius: 4,
                  }}
                >
                  {v.verdict === "VERIFIED" ? (
                    // The Passport seal in ink on the verdict colour: the proof inside the six kernels.
                    <svg width={20} height={20} viewBox="0 0 100 100">
                      <path d={SEAL_RING} fill="none" stroke={INK} strokeOpacity={0.55} strokeWidth={5} strokeLinejoin="round" />
                      {SEAL_KERNELS.map((k, i) => (
                        <rect key={i} x={k.x - 8} y={k.y - 8} width={16} height={16} rx={1.6} fill={INK} />
                      ))}
                      <rect x={37} y={37} width={26} height={26} rx={1.8} fill={INK} />
                    </svg>
                  ) : (
                    <div style={{ width: 8, height: 8, background: INK, borderRadius: 1 }} />
                  )}
                  {v.verdict}
                </div>
              </div>
            </div>
          ))}
        </div>
        <div style={{ display: "flex", flexDirection: "column", gap: 8, fontSize: 21, marginTop: 30 }}>
          <div style={{ display: "flex", fontFamily: "JetBrains Mono", color: FROST, fontSize: 19 }}>
            {`Hotfix counterexample: checkedShlw(2^192) = (0, false), checked by ${CETUS_HOTFIX.kernels} kernels.`}
          </div>
          <div style={{ display: "flex", color: MIST }}>
            {`Seeded bad repairs accepted: by ordinary checking ${ordinary.badAccepted} of ${E2.bad}, by ProofForge ${pf.badAccepted} of ${E2.bad}.`}
          </div>
        </div>
      </div>
    ),
    {
      ...size,
      fonts: [
        { name: "Instrument Serif", data: serif, weight: 400, style: "normal" },
        { name: "Space Grotesk", data: display, weight: 600, style: "normal" },
        { name: "Inter", data: sans, weight: 400, style: "normal" },
        { name: "Inter", data: sansSemi, weight: 600, style: "normal" },
        { name: "JetBrains Mono", data: mono, weight: 400, style: "normal" },
      ],
    },
  );
}
