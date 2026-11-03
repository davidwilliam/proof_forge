// The site's origin and its public paths, for app/robots.ts and app/sitemap.ts. tests/site.test.ts
// checks that every static page under app/ is listed.

export const SITE_URL = process.env.NEXT_PUBLIC_SITE_URL || "https://proofforge.dev";

/** Every static page, then the machine-readable summaries that scripts/evidence.mjs writes to public/. */
export const SITE_PATHS = [
  "/",
  "/frontier",
  "/app",
  "/app/payout",
  "/challenge",
  "/forge",
  "/results",
  "/methods",
  "/verify",
  "/about",
  "/brand",
  "/llms.txt",
  "/evidence.json",
] as const;
