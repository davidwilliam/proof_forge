"use client";

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
