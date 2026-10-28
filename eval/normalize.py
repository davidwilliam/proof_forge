#!/usr/bin/env python3
"""Normalize recorded run artifacts before committing them: em dashes become semicolons
and en dashes become hyphens, in plain text and in JSON-escaped form, and absolute paths
into a ProofForge checkout (this one or a sibling such as an isolated experiment checkout)
become paths relative to the repository root. Nothing else changes; results/README.md
records that this was applied.

Usage: normalize.py PATH...   (files or directories, recursively)
"""
import pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
CHECKOUT = re.escape(str(ROOT.parent)) + r"/" + re.escape(ROOT.name) + r"[\w.-]*"

PATTERNS = [(re.compile(r"\s*(—|\\u2014)\s*"), "; "), (re.compile(r"–|\\u2013"), "-"),
            (re.compile(CHECKOUT + r"/"), ""), (re.compile(CHECKOUT + r"(?![\w.-])"), ".")]


def normalize(path):
    text = path.read_text(errors="strict")
    new = text
    for pat, rep in PATTERNS:
        new = pat.sub(rep, new)
    if new != text:
        path.write_text(new)
        return True
    return False


if __name__ == "__main__":
    changed = 0
    for arg in sys.argv[1:]:
        p = pathlib.Path(arg)
        files = [p] if p.is_file() else [f for f in p.rglob("*") if f.is_file() and f.suffix in (".jsonl", ".json", ".log", ".md", ".lean", ".txt")]
        for f in files:
            changed += normalize(f)
    print(f"normalized {changed} files")
