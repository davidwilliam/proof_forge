#!/usr/bin/env python3
"""Audit a Muse Code run for access outside its workspace.

Muse Code's shell sandbox lets the agent read outside the workspace, so every run's transcript
(events.jsonl, or events.jsonl.gz) is checked: each shell command (from its tool result) and each file read is listed
when it names an absolute path outside the workspace, a parent directory (`..`), the home
directory, or anything that names the ProofForge checkout, reference solutions, attacks,
witnesses or results. The runner already writes the workspace as `<workspace>`.

Commands that use only named files in /tmp (the sandbox's writable temp directory, where the agent
keeps backup copies of its own candidate) are counted separately; a listing of /tmp itself, or any
other path, is reported as outside the workspace.

Usage: audit.py RUN_DIR...   (prints flagged accesses per run; exit 0)
"""
import gzip, json, pathlib, re, sys

SUSPECT = re.compile(r"(?<![\w<])(\.\./|~/|\$HOME|/Users/|/home/|/private/|/var/|/tmp\b|/etc/|/opt/|"
                     r"proof_?forge|<proofforge>|reference/|attacks/|witnesses/|results/|SolutionA|SolutionB)")
ALLOWED = re.compile(r"<workspace>/?|/work\b|/dev/null|/usr/bin/env|/bin/(ba)?sh|\.lake/packages/proofforge-fin/?|"
                     r"proofforge-fin|\.agents/skills/proofforge/?|\.proofforge/")
TEMP_FILE = re.compile(r"/tmp/[\w.\-]+")   # a file in the sandbox's temp directory, e.g. a backup copy


def accesses(events):
    """(kind, text) for every shell command and file read in a transcript."""
    text = (gzip.open(events, "rt", errors="replace").read() if events.suffix == ".gz"
            else events.read_text(errors="replace"))
    for line in text.splitlines():
        try:
            e = json.loads(line)
        except ValueError:
            continue
        if e.get("payload_type") != "tool.result":
            continue
        text = e["payload"].get("text") or ""
        if text.startswith("{"):
            try:
                cmd = json.loads(text).get("command")
            except ValueError:
                cmd = None
            if cmd:
                yield "shell", cmd
                continue
        m = re.match(r"Read text file `([^`]+)`", text)
        if m:
            yield "read", m.group(1)


def transcript(run):
    """events.jsonl, or events.jsonl.gz as committed for measured runs."""
    p = pathlib.Path(run) / "events.jsonl"
    return p if p.is_file() else p.with_suffix(".jsonl.gz")


def audit(run):
    """(outside, temp): accesses outside the workspace, and uses of named files in /tmp (the
    sandbox's writable temp directory, where the agent keeps its own scratch copies)."""
    outside, temp = [], []
    for kind, text in accesses(transcript(run)):
        stripped = ALLOWED.sub("", text)
        if kind == "read" and text.startswith("/") and not text.startswith("<workspace>"):
            outside.append((kind, text))
        elif SUSPECT.search(TEMP_FILE.sub("", stripped)):
            outside.append((kind, text))
        elif TEMP_FILE.search(stripped):
            temp.append((kind, text))
    return outside, temp


def main():
    for run in sys.argv[1:]:
        ev = transcript(run)
        if not ev.is_file():
            continue
        n = sum(1 for _ in accesses(ev))
        outside, temp = audit(run)
        print(f"{run}: {n} shell commands and reads, {len(outside)} outside the workspace, "
              f"{len(temp)} using named files in /tmp")
        for kind, text in outside:
            print(f"  {kind}: {text[:300]}")


if __name__ == "__main__":
    main()
