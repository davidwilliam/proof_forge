import type { ReactNode } from "react";

// Renders the small Markdown subset the Passport comment uses: paragraphs, bold,
// inline code, fenced code blocks and "- " lists. Text is never injected as HTML.

function inline(text: string, key: string): ReactNode[] {
  const out: ReactNode[] = [];
  const re = /(\*\*[^*]+\*\*|`[^`]+`)/g;
  let last = 0;
  let m: RegExpExecArray | null;
  let i = 0;
  while ((m = re.exec(text))) {
    if (m.index > last) out.push(text.slice(last, m.index));
    const tok = m[0];
    if (tok.startsWith("**")) out.push(<strong key={`${key}-${i++}`}>{tok.slice(2, -2)}</strong>);
    else out.push(<code key={`${key}-${i++}`}>{tok.slice(1, -1)}</code>);
    last = m.index + tok.length;
  }
  if (last < text.length) out.push(text.slice(last));
  return out;
}

export function Markdown({ source }: { source: string }) {
  const lines = source.split("\n");
  const blocks: ReactNode[] = [];
  let i = 0;
  let k = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith("```")) {
      const body: string[] = [];
      i++;
      while (i < lines.length && !lines[i]!.startsWith("```")) body.push(lines[i++]!);
      i++;
      blocks.push(
        <pre key={k++}>
          <code>{body.join("\n")}</code>
        </pre>,
      );
    } else if (line.startsWith("- ")) {
      const items: string[] = [];
      while (i < lines.length && lines[i]!.startsWith("- ")) items.push(lines[i++]!.slice(2));
      blocks.push(
        <ul key={k++}>
          {items.map((t, j) => (
            <li key={j}>{inline(t, `l${k}-${j}`)}</li>
          ))}
        </ul>,
      );
    } else if (line.trim() === "") {
      i++;
    } else {
      const para: string[] = [];
      while (i < lines.length && lines[i]!.trim() !== "" && !lines[i]!.startsWith("```") && !lines[i]!.startsWith("- ")) para.push(lines[i++]!);
      blocks.push(<p key={k++}>{inline(para.join(" "), `p${k}`)}</p>);
    }
  }
  return <div className="md">{blocks}</div>;
}
