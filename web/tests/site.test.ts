import { existsSync, readdirSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import robots from "../app/robots";
import sitemap from "../app/sitemap";
import { SITE_PATHS, SITE_URL } from "../lib/site";
import { ROOT } from "../scripts/lib/results.mjs";

const app = path.join(ROOT, "web/app");

/** Static routes: directories under app/ with a page.tsx, without route groups, private folders or dynamic segments. */
function routes(dir: string): string[] {
  return readdirSync(dir, { withFileTypes: true }).flatMap((e) => {
    if (!e.isDirectory()) return e.name === "page.tsx" ? ["/" + path.relative(app, dir)] : [];
    if (e.name.startsWith("_") || e.name.startsWith("[")) return [];
    return routes(path.join(dir, e.name));
  });
}

describe("robots.txt and sitemap.xml", () => {
  it("list every static page and the machine-readable summaries", () => {
    for (const r of routes(app)) expect(SITE_PATHS, r).toContain(r);
    for (const f of ["llms.txt", "evidence.json"]) {
      expect(SITE_PATHS).toContain(`/${f}`);
      expect(existsSync(path.join(ROOT, "web/public", f))).toBe(true);
    }
    const urls = sitemap().map((u) => u.url);
    expect(urls).toHaveLength(SITE_PATHS.length);
    expect(urls[0]).toBe(SITE_URL);
    expect(urls).toContain(`${SITE_URL}/llms.txt`);
  });

  it("allow every crawler and point to the sitemap", () => {
    const r = robots();
    expect(r.rules).toEqual({ userAgent: "*", allow: "/" });
    expect(r.sitemap).toBe(`${SITE_URL}/sitemap.xml`);
  });
});
