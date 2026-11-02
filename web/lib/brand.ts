// The identity kit as the /brand page shows it. Every value is copied from the kit, version 1.0:
// colours, their uses and the symbol geometry from 06-brand-tokens/proofforge-tokens.json (copied to
// public/brand/kit/), the rules from README.txt and ProofForge-Logo-Guide.pdf. tests/brand.test.ts
// pins the colours and the geometry to the tokens file.

export const KIT = {
  version: "1.0",
  accepted: "2026-10-31",
  proposal: 'proposal 02, "the inference"',
  setAside: ['01 "the verdict" (turnstile with end-of-proof block)', '03 "six kernels"'],
} as const;

export type PaletteGroup = "Grounds and surfaces" | "Text and mark" | "Accent" | "Verdicts only";

export interface Swatch {
  key: string;
  name: string;
  hex: string;
  use: string;
  group: PaletteGroup;
  /** Contrast as the kit states it, where it does. */
  contrast?: string;
}

export const PALETTE: Swatch[] = [
  { key: "void", name: "Void", hex: "#05070B", use: "page ground in dark", group: "Grounds and surfaces" },
  { key: "graphite", name: "Graphite", hex: "#0E131B", use: "cards and panels on dark", group: "Grounds and surfaces" },
  { key: "steel", name: "Steel", hex: "#1C2532", use: "card edges on dark", group: "Grounds and surfaces" },
  { key: "paper", name: "Paper", hex: "#F6F7F9", use: "page ground in light", group: "Grounds and surfaces" },
  { key: "white", name: "White", hex: "#FFFFFF", use: "cards on light; the mono white mark", group: "Grounds and surfaces" },
  { key: "hairline", name: "Hairline", hex: "#E1E5EB", use: "card edges on light", group: "Grounds and surfaces" },
  { key: "ink", name: "Ink", hex: "#0B0F15", use: "text and mark on light", group: "Text and mark" },
  { key: "slate", name: "Slate", hex: "#4A5462", use: "body text on light", group: "Text and mark", contrast: "7.2:1 on Paper" },
  { key: "frost", name: "Frost", hex: "#F2F5F8", use: "the mark and headings on dark", group: "Text and mark" },
  { key: "mist", name: "Mist", hex: "#A9B4C2", use: "body text on dark", group: "Text and mark", contrast: "9.6:1 on Void" },
  { key: "forge", name: "Forge", hex: "#FF9A3C", use: "the block on dark; one accent per view", group: "Accent", contrast: "9.5:1 on Void" },
  {
    key: "forge-deep",
    name: "Forge deep",
    hex: "#D45F00",
    use: "the block on light; large accents on light",
    group: "Accent",
    contrast: "3.9:1 on white: the block and large type only, never small text",
  },
  { key: "ion", name: "Ion", hex: "#5BE4F0", use: "proof graphs and Lean code on dark", group: "Accent" },
  { key: "verified", name: "Verified", hex: "#3DDC97", use: "the verified verdict only", group: "Verdicts only" },
  { key: "refuted", name: "Refuted", hex: "#FF5D5D", use: "the refuted verdict only", group: "Verdicts only" },
];

export const PALETTE_GROUPS: { group: PaletteGroup; text: string }[] = [
  { group: "Grounds and surfaces", text: "Paper and white carry light pages, Void and Graphite dark ones." },
  { group: "Text and mark", text: "Ink and Slate on light grounds; Frost and Mist on dark ones." },
  { group: "Accent", text: "The Forge block is the one accent in any view. Ion is for proof graphs and Lean code on dark." },
  {
    group: "Verdicts only",
    text: "Verified and Refuted belong to verdicts and never enter the mark. On light grounds they are fills behind Ink text.",
  },
];

/** Symbol rectangles on the 100 unit grid: x, y, width, height, corner radius. */
export const SYMBOL = {
  grid: 100,
  premises: [
    [14, 22, 30, 12, 1.5],
    [56, 22, 30, 12, 1.5],
  ],
  line: [8, 43, 84, 7, 0],
  block: [39, 60, 22, 22, 1.5],
  smallLine: [8, 42, 84, 10, 0],
  smallUpToPx: 48,
} as const;

/** The horizontal lockup at font size 100: the artboard and the ink boxes, y down from the baseline. */
export const LOCKUP = {
  markHeightEm: 0.78,
  gapEm: 0.33,
  inkCentreEm: 0.25,
  markInk: [0, -64, 109.2, 14],
  wordInk: [142.2, -70, 608, 20],
  artboard: [624, 106],
  pad: 8,
  stackedMarkHeightEm: 1.25,
  stackedGapEm: 0.36,
} as const;

export const WORDMARK = { text: "proofforge", face: "Space Grotesk 700", trackingEm: -0.045 } as const;

export const MIN_SIZES = [
  { what: "Symbol", size: "16 px on screen, 5 mm in print" },
  { what: "Horizontal lockup", size: "120 px wide" },
  { what: "Wordmark alone", size: "90 px wide" },
] as const;

/** "Do not", as the guide lists it. */
export const MISUSE = [
  "Change the grid, the gaps or the order of the parts.",
  "Set the wordmark in a live font, or restyle it.",
  "Align the mark to the baseline or the x-height; use the ink centre rule.",
  "Use Verified, Refuted or Ion in the mark.",
  "Add a second accent next to the Forge block.",
  "Rotate, outline, add gradients, glows or shadows to the static mark.",
  "Crowd the lockup inside its clear space, or set the primary lockup on photographs or busy grounds.",
] as const;

export const TYPE = [
  {
    family: "Instrument Serif",
    cls: "bk-type-head",
    sample: "Every fix carries its proof.",
    use: "Page headlines only.",
    weights: "400",
  },
  {
    family: "Space Grotesk",
    cls: "bk-type-disp",
    sample: "0 of 247, $3.06",
    use: "The wordmark, figures and section titles.",
    weights: "500, 600, 700",
  },
  {
    family: "Inter",
    cls: "bk-type-sans",
    sample: "Six independent kernels check the proof.",
    use: "Interface and body.",
    weights: "400, 500, 600",
  },
  {
    family: "JetBrains Mono",
    cls: "bk-type-mono",
    sample: "theorem req_batch_keeps_value : ...",
    use: "Lean, hashes and Passport readings; Ion on dark grounds.",
    weights: "400, 500",
  },
] as const;

export interface KitFile {
  label: string;
  /** Path under public/. */
  path: string;
  text: string;
}

export const KIT_DOWNLOADS: KitFile[] = [
  { label: "The whole kit", path: "brand/kit/ProofForge-Logo-Kit-v1.0.zip", text: "SVG, PNG and PDF masters, web and app icons, tokens, reference sheets, build sources and the splash renders." },
  { label: "Logo guide", path: "brand/kit/ProofForge-Logo-Guide.pdf", text: "Construction, lockups, colour, type and the rules, on three pages." },
  { label: "Kit overview", path: "brand/kit/ProofForge-Kit-Overview.svg", text: "The identity on one sheet." },
  { label: "Brand tokens, JSON", path: "brand/kit/proofforge-tokens.json", text: "Colours, light and dark roles, type, symbol geometry and lockup ratios." },
  { label: "Brand tokens, CSS", path: "brand/kit/proofforge-tokens.css", text: "The same as custom properties, light by default and dark by system or data-theme." },
];

export interface Asset {
  label: string;
  path: string;
  /** The ground the asset is shown on. */
  ground: "paper" | "void" | "graphite" | "white" | "slate" | "hairline";
  use: string;
  wide: boolean;
}

export const ASSETS: Asset[] = [
  { label: "Horizontal, primary", path: "brand/proofforge-horizontal-primary.svg", ground: "paper", use: "The default lockup, for light grounds.", wide: true },
  { label: "Horizontal, reversed", path: "brand/proofforge-horizontal-reversed.svg", ground: "void", use: "For Void and Graphite grounds.", wide: true },
  { label: "Horizontal, mono ink", path: "brand/kit/proofforge-horizontal-mono-ink.svg", ground: "hairline", use: "One colour, for one-colour print and embossing.", wide: true },
  { label: "Horizontal, mono white", path: "brand/kit/proofforge-horizontal-mono-white.svg", ground: "slate", use: "One colour, for photographs and mid-tone grounds.", wide: true },
  { label: "Stacked, primary", path: "brand/kit/proofforge-stacked-primary.svg", ground: "white", use: "For square placements.", wide: false },
  { label: "Stacked, reversed", path: "brand/kit/proofforge-stacked-reversed.svg", ground: "graphite", use: "For square placements on dark.", wide: false },
  { label: "Symbol, primary", path: "brand/proofforge-icon-primary.svg", ground: "paper", use: "For avatars, favicons and app icons.", wide: false },
  { label: "Symbol, reversed", path: "brand/proofforge-icon-reversed.svg", ground: "void", use: "The favicon is this symbol on a Void tile.", wide: false },
  { label: "Wordmark, primary", path: "brand/kit/proofforge-wordmark-primary.svg", ground: "paper", use: "Where the symbol already shows nearby.", wide: true },
  { label: "Wordmark, reversed", path: "brand/kit/proofforge-wordmark-reversed.svg", ground: "void", use: "The same on dark grounds.", wide: true },
];

export const REFERENCE_SHEETS: KitFile[] = [
  { label: "Alignment rule sheet", path: "brand/kit/alignment-rule.svg", text: "The ink centre rule with its measurements." },
  { label: "Clear space sheet", path: "brand/kit/clear-space.svg", text: "Half the symbol height on every side." },
];
