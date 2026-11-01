"use client";

import { useEffect, useRef } from "react";
import { SPLASH_SVG } from "./splash-svg";

/**
 * The identity splash: the kit's sequence (premises, inference line, conclusion with its labels, the six kernels, then
 * the lockup) over the page, on the first view of the home page in a browser session.
 *
 * The page renders underneath; the splash is an overlay. The head script in splash-script.ts decides before first paint
 * whether to show it (html[data-splash]); without that attribute the overlay is display: none, so
 * crawlers, browsers without scripts, automated browsers and reduced motion never see it. CSS alone
 * fades it out at 5.85 s; a click, key or scroll ends it at once. `?splash` shows it again.
 */
const DURATION_MS = 6250;

export function Splash() {
  const ref = useRef<HTMLDivElement>(null);
  useEffect(() => {
    const root = document.documentElement;
    if (root.getAttribute("data-splash") !== "on") return;
    try {
      sessionStorage.setItem("pf-splash", "seen");
    } catch {
      // storage unavailable: the splash may show again on the next view
    }
    let done = false;
    const end = () => {
      if (done) return;
      done = true;
      root.removeAttribute("data-splash");
      off();
    };
    const skip = () => {
      if (done) return;
      ref.current?.classList.add("pf-splash-skip");
      window.setTimeout(end, 220);
    };
    const timer = window.setTimeout(end, DURATION_MS);
    const events = ["pointerdown", "keydown", "wheel", "touchmove", "scroll"] as const;
    events.forEach((e) => window.addEventListener(e, skip, { passive: true }));
    function off() {
      window.clearTimeout(timer);
      events.forEach((e) => window.removeEventListener(e, skip));
    }
    return off;
  }, []);
  return <div ref={ref} className="pf-splash" aria-hidden="true" dangerouslySetInnerHTML={{ __html: SPLASH_SVG }} />;
}
