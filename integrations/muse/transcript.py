#!/usr/bin/env python3
"""A readable rendering of a Muse Code JSONL transcript (`muse exec --json`, events.jsonl).

In event order: each prompt (`turn.input.user`), Muse Code's text between tool calls (the
`run.output.delta` pieces joined), every tool result abridged to its opening lines, and how each
session part ended (`run.terminal.*`). The JSONL file stays the record; this is for reading.

Usage: transcript.py RUN_DIR [--lines 12] > transcript.txt
"""
import argparse, gzip, json, pathlib


def events(run):
    p = pathlib.Path(run) / "events.jsonl"
    text = p.read_text() if p.is_file() else gzip.open(p.with_suffix(".jsonl.gz"), "rt").read()
    for line in text.splitlines():
        try:
            yield json.loads(line)
        except ValueError:
            continue


def render(run, lines=12):
    out, said = [], []

    def flush():
        if said:
            out.append("MUSE CODE: " + "".join(said).strip() + "\n")
            said.clear()
    for e in events(run):
        t, p = e.get("payload_type", ""), e.get("payload") or {}
        if t == "turn.input.user":
            flush()
            out.append("PROMPT:\n" + (p.get("prompt") or "").strip() + "\n")
        elif t == "run.output.delta":
            said.append(p.get("text") or "")
        elif t == "tool.result":
            flush()
            text = (p.get("text") or "").strip().splitlines()
            more = f"\n    [... {len(text) - lines} more lines]" if len(text) > lines else ""
            out.append("TOOL RESULT:\n    " + "\n    ".join(text[:lines]) + more + "\n")
        elif t.startswith("run.terminal"):
            flush()
            out.append(f"SESSION PART ENDED: {p.get('terminal')}" + (f" ({p.get('reason')})" if p.get("reason") else "") + "\n")
    flush()
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--lines", type=int, default=12)
    a = ap.parse_args()
    print(render(a.run, a.lines))


if __name__ == "__main__":
    main()
