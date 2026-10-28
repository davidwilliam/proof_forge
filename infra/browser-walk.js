// Browser walk-through of the deployed demo: drives the replay, challenge and payout flows
// in Chromium, then renders every page at desktop and phone widths in light and dark and
// records console errors, failed requests and horizontal overflow.
//
// Usage: node infra/browser-walk.js [WEB_URL] [OUT_DIR] [PASSPORT_SHA]
// Needs the playwright package (npm i playwright) and a Chromium; PF_CHROME overrides the
// browser executable. With PASSPORT_SHA only the pages are rendered (no judge work).
const { chromium } = require("playwright");
const fs = require("fs");
const path = require("path");

const WEB = process.argv[2] || "https://proofforge-nu.vercel.app";
const OUT = process.argv[3] || "browser-walk";
const EXE = process.env.PF_CHROME || undefined;
fs.mkdirSync(OUT, { recursive: true });

const VIEWS = [
  { name: "desktop", viewport: { width: 1440, height: 900 } },
  { name: "phone", viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true, deviceScaleFactor: 3 },
];
const SCHEMES = ["light", "dark"];
const report = { web: WEB, started: new Date().toISOString(), pages: [], flows: [] };

function watch(page, log) {
  page.on("console", (m) => m.type() === "error" && log.console.push(`${m.text().slice(0, 300)} at ${m.location()?.url}`));
  page.on("pageerror", (e) => log.console.push(`pageerror: ${String(e).slice(0, 300)}`));
  page.on("requestfailed", (r) => !((r.url().includes("_rsc=") || r.url().endsWith("/events")) && r.failure()?.errorText === "net::ERR_ABORTED") && log.failed.push(`${r.failure()?.errorText} ${r.url()}`));
  page.on("response", (r) => r.status() >= 400 && log.failed.push(`HTTP ${r.status()} ${r.url()}`));
}

async function overflow(page) {
  return page.evaluate(() => {
    const w = document.documentElement.clientWidth;
    const wide = [...document.querySelectorAll("body *")]
      .filter((el) => {
        const r = el.getBoundingClientRect();
        if (r.right <= w + 1 || r.width === 0) return false;
        for (let p = el.parentElement; p; p = p.parentElement) {
          const s = getComputedStyle(p);
          if (/(auto|scroll|hidden|clip)/.test(s.overflowX)) return false;
        }
        return true;
      })
      .slice(0, 5)
      .map((el) => `${el.tagName.toLowerCase()}.${el.className || ""} right=${Math.round(el.getBoundingClientRect().right)}`);
    return { scrollWidth: document.documentElement.scrollWidth, clientWidth: w, wide };
  });
}

async function newPage(browser, view, scheme) {
  const ctx = await browser.newContext({ ...view, colorScheme: scheme });
  const page = await ctx.newPage();
  const log = { console: [], failed: [] };
  watch(page, log);
  return { ctx, page, log };
}

async function pages(browser, passportSha) {
  const paths = ["/", "/results", "/app", "/challenge"];
  if (passportSha) paths.push(`/passport/${passportSha}`);
  for (const view of VIEWS) {
    for (const scheme of SCHEMES) {
      for (const p of paths) {
        const { ctx, page, log } = await newPage(browser, view, scheme);
        const t0 = Date.now();
        const resp = await page.goto(WEB + p, { waitUntil: "networkidle", timeout: 60000 }).catch((e) => ({ status: () => 0, e }));
        const ms = Date.now() - t0;
        const ov = await overflow(page);
        const h1 = await page.locator("h1").first().textContent().catch(() => null);
        const bg = await page.evaluate(() => getComputedStyle(document.body).backgroundColor);
        const file = `${view.name}-${scheme}-${p === "/" ? "home" : p.split("/")[1]}.png`;
        await page.screenshot({ path: path.join(OUT, file), fullPage: true });
        report.pages.push({ view: view.name, scheme, path: p, http: resp.status(), load_ms: ms, h1: h1?.trim().slice(0, 120),
          body_bg: bg, horizontal_overflow: ov.scrollWidth > ov.clientWidth, overflow: ov, ...log, screenshot: file });
        await ctx.close();
      }
    }
  }
}

async function replayFlow(browser) {
  const { ctx, page, log } = await newPage(browser, VIEWS[0], "light");
  const t0 = Date.now();
  await page.goto(WEB + "/", { waitUntil: "networkidle" });
  await page.getByLabel("Recording").selectOption("flagship-a2-run7");
  await page.getByLabel("Speed").selectOption("80");
  await page.getByRole("button", { name: "Start replay" }).click();
  const link = page.getByRole("link", { name: /Open Passport/ }).first();
  let ok = true, err = null;
  try {
    await link.waitFor({ timeout: 300000 });
  } catch (e) { ok = false; err = String(e).slice(0, 200); }
  const secs = (Date.now() - t0) / 1000;
  const jobState = await page.locator(".segment-bar").textContent();
  const claims = await page.locator("ul.claims li").allTextContents();
  await page.screenshot({ path: path.join(OUT, "flow-replay-done.png"), fullPage: false });
  let sha = null, passportText = null;
  if (ok) {
    const href = await link.getAttribute("href");
    sha = href.split("/").pop();
    await link.click();
    await page.waitForURL(/\/passport\//);
    await page.waitForLoadState("networkidle");
    passportText = (await page.locator("main").textContent()).slice(0, 400);
    await page.screenshot({ path: path.join(OUT, "flow-passport.png"), fullPage: true });
  }
  report.flows.push({ flow: "replay to Passport", passed: ok && claims.every((c) => c.includes("VERIFIED")), seconds: secs,
    segment_bar: jobState?.trim(), claims, passport_sha: sha, passport_text: passportText, error: err, ...log });
  await ctx.close();
  return sha;
}

async function challengeFlow(browser) {
  const { ctx, page, log } = await newPage(browser, VIEWS[1], "dark");
  await page.goto(WEB + "/challenge", { waitUntil: "networkidle" });
  const t0 = Date.now();
  await page.getByRole("button", { name: "Run check" }).click();
  let ok = true, err = null;
  try { await page.getByText(/is\s+(REFUTED|UNRESOLVED|VERIFIED)/).first().waitFor({ timeout: 90000 }); }
  catch (e) { ok = false; err = String(e).slice(0, 200); }
  const card = ok ? (await page.locator(".card").first().textContent()) : null;
  await page.screenshot({ path: path.join(OUT, "flow-challenge.png"), fullPage: true });
  report.flows.push({ flow: "hidden challenge (phone, dark)", passed: ok && /REFUTED/.test(card || ""), seconds: (Date.now() - t0) / 1000,
    result: card?.slice(0, 300), error: err, ...log });
  await ctx.close();
}

async function payoutFlow(browser) {
  const { ctx, page, log } = await newPage(browser, VIEWS[0], "dark");
  await page.goto(WEB + "/app", { waitUntil: "networkidle" });
  const out = {};
  for (const [b, label] of [["buggy", "Run on buggy build"], ["repaired", "Run on repaired build"]]) {
    const t0 = Date.now();
    await page.getByRole("button", { name: label }).click();
    await page.getByRole("button", { name: label }).waitFor({ state: "visible", timeout: 120000 });
    await page.waitForFunction((l) => [...document.querySelectorAll("button")].some((x) => x.textContent === l && !x.disabled), label, { timeout: 120000 });
    out[b] = { seconds: (Date.now() - t0) / 1000 };
  }
  const totals = await page.locator(".big-total").allTextContents();
  await page.screenshot({ path: path.join(OUT, "flow-payout.png"), fullPage: true });
  report.flows.push({ flow: "payout buggy and repaired (desktop, dark)", passed: totals.length === 2 && totals[0] !== totals[1],
    totals, timings: out, ...log });
  await ctx.close();
}

(async () => {
  const browser = await chromium.launch({ executablePath: EXE });
  try {
    if (process.argv[4]) {
      await pages(browser, process.argv[4]);
    } else {
      const sha = await replayFlow(browser);
      await challengeFlow(browser);
      await payoutFlow(browser);
      await pages(browser, sha);
    }
  } finally {
    await browser.close();
  }
  report.finished = new Date().toISOString();
  report.passed = report.flows.every((f) => f.passed) &&
    report.pages.every((p) => p.http === 200 && !p.horizontal_overflow && !p.console.length && !p.failed.length);
  fs.writeFileSync(path.join(OUT, "report.json"), JSON.stringify(report, null, 2) + "\n");
  for (const f of report.flows) console.log(`${f.passed ? "PASS" : "FAIL"}  ${f.flow}  ${f.seconds?.toFixed?.(1) ?? ""}`);
  for (const p of report.pages) {
    const bad = [p.http !== 200 && `http ${p.http}`, p.horizontal_overflow && "overflow", p.console.length && `${p.console.length} console`, p.failed.length && `${p.failed.length} failed`].filter(Boolean);
    console.log(`${bad.length ? "FAIL" : "PASS"}  ${p.view} ${p.scheme} ${p.path}  ${p.load_ms} ms  ${bad.join(", ")}`);
  }
  process.exit(report.passed ? 0 : 1);
})();
