"use client";

import { useEffect, useState } from "react";

// The contact address is assembled in the browser from reversed parts, so it never appears in
// the server HTML or the page data as plain text. Before scripts run, and without them, the
// reader sees it written out in words.
const PARTS = ["tcatnoc", "avliswdivad", "moc"] as const;
const rev = (s: string) => s.split("").reverse().join("");
export const EMAIL_FALLBACK = "contact at davidwsilva dot com";

export function Email({ className, label }: { className?: string; label?: string }) {
  const [addr, setAddr] = useState<string | null>(null);
  useEffect(() => {
    setAddr(`${rev(PARTS[0])}${String.fromCharCode(64)}${rev(PARTS[1])}.${rev(PARTS[2])}`);
  }, []);
  if (!addr) return <span className={className}>{EMAIL_FALLBACK}</span>;
  return (
    <a className={className} href={`mailto:${addr}`}>
      {label ?? addr}
    </a>
  );
}
