import { existsSync, readFileSync, readdirSync } from "node:fs";
import path from "node:path";
import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, it } from "vitest";
import BrandPage from "../app/brand/page";
import { ASSETS, KIT_DOWNLOADS, LOCKUP, MISUSE, PALETTE, REFERENCE_SHEETS, SYMBOL, WORDMARK } from "../lib/brand";

const WEB = path.resolve(import.meta.dirname, "..");
const pub = (rel: string) => path.join(WEB, "public", rel);
const tokens = JSON.parse(readFileSync(pub("brand/kit/proofforge-tokens.json"), "utf8"));

describe("the /brand page against the kit's tokens (public/brand/kit/proofforge-tokens.json)", () => {
  it("shows every token colour with the kit's hex value and use", () => {
    expect(PALETTE.map((s) => s.key).sort()).toEqual(Object.keys(tokens.colors).sort());
    for (const s of PALETTE) {
      expect(s.hex, s.key).toBe(tokens.colors[s.key]);
      expect(s.use, s.key).toBe(tokens.colorUse[s.key]);
    }
  });

  it("names the brief's colours with their values", () => {
    const hex = Object.fromEntries(PALETTE.map((s) => [s.name, s.hex]));
    expect(hex).toMatchObject({ Void: "#05070B", Forge: "#FF9A3C", "Forge deep": "#D45F00", Ion: "#5BE4F0", Verified: "#3DDC97", Refuted: "#FF5D5D" });
  });

  it("uses the same colours as the site's tokens", () => {
    const css = readFileSync(path.join(WEB, "app/globals.css"), "utf8").toLowerCase();
    for (const s of PALETTE.filter((x) => x.key !== "white")) expect(css, s.key).toContain(`--${s.key}: ${s.hex.toLowerCase()};`);
  });

  it("draws the symbol and the alignment rule from the kit's geometry", () => {
    expect(SYMBOL.premises).toEqual(tokens.symbol.premises);
    expect(SYMBOL.line).toEqual(tokens.symbol.line);
    expect(SYMBOL.block).toEqual(tokens.symbol.block);
    expect(SYMBOL.smallLine).toEqual(tokens.symbol.small.line);
    expect(SYMBOL.smallUpToPx).toBe(tokens.symbol.small.upToPx);
    const h = tokens.lockups.horizontal;
    expect([LOCKUP.markHeightEm, LOCKUP.gapEm]).toEqual([h.markHeightEm, h.gapEm]);
    expect(LOCKUP.markInk).toEqual(h.markInk);
    expect(LOCKUP.wordInk).toEqual(h.wordInk);
    expect(LOCKUP.artboard).toEqual(h.artboard);
    expect(LOCKUP.pad).toBe(tokens.lockups.artboardPad);
    expect([LOCKUP.stackedMarkHeightEm, LOCKUP.stackedGapEm]).toEqual([tokens.lockups.stacked.markHeightEm, tokens.lockups.stacked.gapEm]);
    // Both ink centres at -25 (0.25 em above the baseline).
    expect((h.markInk[1] + h.markInk[3]) / 2).toBe(-LOCKUP.inkCentreEm * 100);
    expect((h.wordInk[1] + h.wordInk[3]) / 2).toBe(-LOCKUP.inkCentreEm * 100);
    expect([WORDMARK.text, WORDMARK.face, WORDMARK.trackingEm]).toEqual([tokens.wordmark.text, tokens.wordmark.face, tokens.wordmark.trackingEm]);
  });

  it("links only files that ship in public/", () => {
    for (const f of [...KIT_DOWNLOADS, ...REFERENCE_SHEETS, ...ASSETS]) expect(existsSync(pub(f.path)), f.path).toBe(true);
  });

  it("ships no private names or local paths in the copied kit files", () => {
    const dir = pub("brand/kit");
    // The names are stored reversed so that this file does not contain them either.
    const names = ["edualc", "ciporhtna", "xedoc", "zbuhatad", "avlisd"].map((s) => s.split("").reverse().join(""));
    const banned = new RegExp(`${names.join("|")}|/Users/|/home/`, "i");
    for (const f of readdirSync(dir).filter((n) => /\.(svg|json|css)$/.test(n))) {
      expect(readFileSync(path.join(dir, f), "utf8"), f).not.toMatch(banned);
    }
  });

  it("renders the palette, the rules and the downloads on the server", () => {
    const html = renderToStaticMarkup(createElement(BrandPage));
    for (const s of PALETTE) expect(html).toContain(s.hex);
    for (const r of MISUSE) expect(html).toContain(r.replace(/'/g, "&#x27;"));
    expect(html).toContain('href="/brand/kit/ProofForge-Logo-Kit-v1.0.zip"');
    expect(html).toContain('href="/brand/kit/ProofForge-Logo-Guide.pdf"');
  });
});
