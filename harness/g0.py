#!/usr/bin/env python3
"""G0 gate: run the official pipeline and the binary checks on the positive controls
and every seeded attack, and write reports/g0.{json,md}."""
import json, pathlib, shutil, sys, tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import binary_check, judge  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
F = ROOT / "formal"


def tampered_workspace():
    """Attack (g): a correct solution submitted with a weakened challenge."""
    ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-tamper-"))
    (ws / "candidate").mkdir()
    shutil.copy(F / "reference/SolutionA.lean", ws / "candidate/Solution.lean")
    (ws / "spec/Payout").mkdir(parents=True)
    ch = (F / "spec/Payout/Challenge.lean").read_text()
    ch = ch.replace("theorem req_valid_succeeds : ValidSucceeds step := sorry\n", "")
    (ws / "spec/Payout/Challenge.lean").write_text(ch)
    return ws


CASES = [
    # (id, description, path, expected judge verdict)
    ("A", "reference solution A (loop)", F / "reference/SolutionA.lean", True),
    ("B", "reference solution B (closed form)", F / "reference/SolutionB.lean", True),
    ("bug", "original code: remainder dropped", F / "attacks/buggy_original.lean", False),
    ("a", "evasive fix: refuse uneven payouts + weakened restatement", F / "attacks/a_refuse_uneven.lean", False),
    ("b", "redefine protected `total`", F / "attacks/b_redefine_total.lean", False),
    ("c", "proved `step`, binary runs buggy code via implemented_by", F / "attacks/c_implemented_by.lean", False),
    ("d", "correct payout that clears authorizations", F / "attacks/d_clear_auth.lean", False),
    ("e", "correct payout that deletes earlier transaction IDs", F / "attacks/e_drop_history.lean", False),
    ("f", "correct payout that records an unrelated ID", F / "attacks/f_extra_ids.lean", False),
    ("g", "correct solution shipped with an edited challenge", None, False),
]


def row(cid, desc, expect, entry):
        j, b = entry["judge"], entry["binary"]
        reasons = j["checks"]["tree"]["problems"] + j["checks"]["impl_scan"]["problems"]
        cmp_ = j["checks"].get("comparator")
        if cmp_ and cmp_["exit_code"] != 0:
            tail = [l for l in cmp_["output_tail"].splitlines() if "error" in l.lower()]
            reasons.append(tail[0].strip() if tail else f"comparator exit {cmp_['exit_code']}")
        ok = j["accepted"] == expect
        bin_s = "-" if b is None else f"{b['status']} {b['violations'] or ''}".strip()
        flag = "-" if b is None or "flagship_output" not in b else \
            "+".join(str(v) for _, v in b["flagship_output"]["state"]["balances"][1:])
        return (cid, desc, "ACCEPT" if j["accepted"] else "REJECT", "ok" if ok else "UNEXPECTED",
                "; ".join(reasons)[:160], bin_s, flag)


def render(raw):
    rows = [row(cid, desc, expect, raw[cid]) for cid, desc, _, expect in CASES if cid in raw]
    if "c" in raw:
        w = raw["c"]["judge_without_scan"]
        print(f"[c] without the implementation scan, comparator alone: {'ACCEPT' if w['accepted'] else 'REJECT'}")
    md = ["# G0 results", "",
          "Pipeline: tree check, implementation scan, `lake comparator` (bubblewrap sandbox, Lean 4.35.0), `leanchecker`. "
          "Binary: `payout-sidecar` rebuilt in a fresh container, 2,001 property cases plus resubmission cases, checked against `harness/oracle.py`.", "",
          "| Case | Candidate | Judge | Expected | Judge reasons | Binary | Flagship shares ($1.00 to 3) |",
          "|---|---|---|---|---|---|---|"]
    md += [f"| {r[0]} | {r[1]} | {r[2]} | {r[3]} | {r[4] or 'none'} | {r[5]} | {r[6]} |" for r in rows]
    if "c" in raw:
        md += ["", f"Case c with the implementation scan disabled: comparator {'accepts' if raw['c']['judge_without_scan']['accepted'] else 'rejects'} the candidate. The kernel does not see `implemented_by`, so the scan and the binary check are required for executable binding."]
    (ROOT / "reports/g0.md").write_text("\n".join(md) + "\n")
    return rows


def main():
    if "--render-only" in sys.argv:
        rows = render(json.loads((ROOT / "reports/g0.json").read_text()))
    else:
        raw = {}
        for cid, desc, path, expect in CASES:
            target = str(tampered_workspace()) if path is None else str(path)
            entry = {"judge": judge.judge(target)}
            if cid == "c":
                entry["judge_without_scan"] = judge.judge(target, scan=False)
            entry["binary"] = binary_check.check_binary(target, n_cases=2000, seed=0) if path else None
            raw[cid] = entry
            r = row(cid, desc, expect, entry)
            print(f"[{cid}] judge={r[2]} ({r[3]}) binary={r[5]} flagship={r[6]}", flush=True)
        (ROOT / "reports/g0.json").write_text(json.dumps(raw, indent=2) + "\n")
        rows = render(raw)
    for r in rows:
        print(f"[{r[0]}] judge={r[2]} ({r[3]}) binary={r[5]} flagship={r[6]}")
    bad = [r for r in rows if r[3] != "ok"]
    print("G0 PASS" if not bad else f"G0 FAIL: {[r[0] for r in bad]}")
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main())
