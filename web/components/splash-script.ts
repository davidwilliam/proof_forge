// Runs in <head> before first paint (app/layout.tsx); kept out of the client module so the server can inline it.
/**
 * The identity splash: the kit's sequence (premises, inference line, conclusion with its labels, then
 * the lockup) over the page, on the first view of the home page in a browser session.
 *
 * The page renders underneath; the splash is an overlay. This script decides before first paint
 * whether to show it (html[data-splash]); without that attribute the overlay is display: none, so
 * crawlers, browsers without scripts, automated browsers and reduced motion never see it. CSS alone
 * fades it out at 4.3 s; a click, key or scroll ends it at once. `?splash` shows it again.
 */
export const splashScript = `try{var d=document.documentElement,q=/[?&]splash\\b/.test(location.search),s=null;try{s=sessionStorage.getItem("pf-splash")}catch(e){}if(location.pathname==="/"&&!matchMedia("(prefers-reduced-motion: reduce)").matches&&(q||(!s&&!navigator.webdriver)))d.setAttribute("data-splash","on")}catch(e){}`;
