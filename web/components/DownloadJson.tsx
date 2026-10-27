"use client";

export function DownloadJson({ data, filename, label }: { data: unknown; filename: string; label: string }) {
  const download = () => {
    const blob = new Blob([JSON.stringify(data, null, 2) + "\n"], { type: "application/json" });
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
  return (
    <button
      onClick={() => {
        void navigator.clipboard?.writeText(text);
      }}
    >
      {label}
    </button>
  );
}
