"use client";

import { useState } from "react";

export function DownloadJson({ data, filename, label }: { data: unknown; filename: string; label: string }) {
  return <DownloadText text={JSON.stringify(data, null, 2) + "\n"} type="application/json" filename={filename} label={label} />;
}

export function DownloadText({ text, type, filename, label }: { text: string; type: string; filename: string; label: string }) {
  const download = () => {
    const blob = new Blob([text], { type });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = filename;
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  };
  return <button onClick={download}>{label}</button>;
}

export function CopyText({ text, label }: { text: string; label: string }) {
  const [copied, copy] = useCopy(text);
  return <button onClick={copy}>{copied ? "Copied" : label}</button>;
}

/** A small copy control placed next to a hash. */
export function CopyButton({ text, label }: { text: string; label: string }) {
  const [copied, copy] = useCopy(text);
  return (
    <button type="button" className="copy-btn" onClick={copy} aria-label={label} title={label}>
      <svg viewBox="0 0 16 16" aria-hidden="true" fill="none" stroke="currentColor" strokeWidth="1.5">
        <rect x="5.5" y="5.5" width="8" height="8" rx="1.5" />
        <path d="M10.5 5.5v-2a1 1 0 0 0-1-1h-6a1 1 0 0 0-1 1v6a1 1 0 0 0 1 1h2" />
      </svg>
      {copied ? "Copied" : "Copy"}
    </button>
  );
}

function useCopy(text: string): [boolean, () => void] {
  const [copied, setCopied] = useState(false);
  const copy = () => {
    void navigator.clipboard?.writeText(text).then(() => {
      setCopied(true);
      setTimeout(() => setCopied(false), 1500);
    });
  };
  return [copied, copy];
}
