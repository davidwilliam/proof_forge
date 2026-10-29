#!/usr/bin/env python3
"""Compound Proposal 62: the deployed Comptroller code against the proved reward component.

For realworld/tasks/rw-compound-comp this script:
  1. port       kernel-checks the refutations of the Lean port of the Proposal 62 distribution
                (witnesses/cSUSHI_claim.lean: the cSUSHI claim of 2021-09-29;
                witnesses/compound_regression.lean: the test Compound added after the
                incident) and the Compound-style unit tests (tests/PortUnitTests.lean) on the
                port and on the proved component, and Compound's regression test on the proved
                component (tests/RegressionOnFix.lean);
  2. sources    fetches compound-finance/compound-protocol at the commits of Proposals 62, 64
                and 65, checks every Solidity file the Comptroller and the Unitroller import
                against recorded SHA-256 hashes, compiles them with solc 0.5.16 (optimizer 200
                runs, istanbul, as deployed) and compares each compiled Comptroller with the
                runtime code of the deployed implementation, metadata hash excluded;
  3. real code  runs the documented sequences and generated ones on the three compiled
                Comptrollers (realworld/adapters/compound, forge): a Unitroller with the
                pre-upgrade state, the Proposal 62 upgrade, then the Proposal 64 or Proposal 65
                implementation where selected, then every operation;
  4. Lean       runs the same sequences on the executables of the port of Proposal 62, the
                port of Proposal 64 (attacks/p64_claim_lock.lean) and the proved component (an
                accepted Muse repair when one exists, otherwise the build-team reference);
  5. compare    checks every real output against the task's requirements (the oracle mirrors
                Spec.lean), compares each Comptroller with its Lean counterpart operation by
                operation, and states the real-code violations of the reward bounds as `decide`
                goals over the Lean definitions, checked in the kernel;
  6. fork       replays the cSUSHI claim on a fork of mainnet at block 13322936 with the
                deployed Proposal 62 code and with the compiled Proposal 64 and 65 code
                (needs an archive RPC endpoint, PF_ETH_RPC, default https://eth.drpc.org);
  7. chain      with --scan, lists every DistributedSupplierComp and DistributedBorrowerComp
                event between the upgrade and Proposal 64 that credits a positive amount at an
                index of exactly 1e36, the pattern of the bug.

What is proved: the Lean component accepted by the judge meets every requirement for every
reachable state. What is tested: the compiled Comptrollers, sequence by sequence. The Solidity
code is not proved.

Compound's sources are fetched at run time into PF_REALWORLD_CACHE (default
~/.cache/proofforge-realworld) and never copied into this repository. Needs network access,
Docker (the pinned Lean image), Foundry (forge, which downloads solc 0.5.16 on first use) and
cast.

Usage: realworld_compound.py [--cases 500] [--seed 0] [--out results/compound-1] [--scan]
"""
import argparse, hashlib, io, json, os, pathlib, random, re, shutil, subprocess, sys, tarfile, time, urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "eval")]
import binary_check, judge, task as taskmod  # noqa: E402
from realworld import lean_check  # noqa: E402

TASK = ROOT / "realworld" / "tasks" / "rw-compound-comp"
ADAPTER = ROOT / "realworld" / "adapters" / "compound"
CACHE = pathlib.Path(os.environ.get("PF_REALWORLD_CACHE", pathlib.Path.home() / ".cache" / "proofforge-realworld"))
RPC = os.environ.get("PF_ETH_RPC", "https://eth.drpc.org")
REPO = "https://codeload.github.com/compound-finance/compound-protocol/tar.gz/"

VARIANTS = {
    "p62": {"commit": "f73b29373eb65cedf24896d7be46eed38435fc91", "pr": 161, "proposal": 62,
            "implementation": "0x374ABb8cE19A73f2c4EFAd642bda76c797f19233", "active_from": 13322798,
            "active_to": 13382884},
    "p64": {"commit": "32f765957e05560cbbd977d7a49c86a09a81282b", "pr": 165, "proposal": 64,
            "implementation": "0x234b619b4f4e405665f7d94f2ce60c24256032b5", "active_from": 13382885,
            "active_to": 13449597},
    "p65": {"commit": "c05d7e09e57ff69582ddb621984e46099f1b4d4b", "pr": 166, "proposal": 65,
            "implementation": "0xbafe01ff935c7305907c33bf824352ee5979b526", "active_from": 13449598,
            "active_to": None},
}
# SHA-256 of every file the Comptroller (and, at the Proposal 62 commit, the Unitroller) imports,
# as fetched at each commit. contracts/Comptroller.sol is byte-identical to the Sourcify-verified
# source of the deployed implementation.
SHA256 = json.loads((ADAPTER / "sources.json").read_text())

UNITROLLER = "0x3d9819210A31b4961b30EF54bE2aeD79B9c9Cd3B"
KINDS = {"mint": 0, "redeem": 1, "transfer": 2, "borrow": 3, "repay": 4, "claim": 5, "setSpeeds": 6,
         "advance": 7, "drip": 8}
SLOT_NAMES = ["markets", "allMarkets", "compSpeeds", "compSupplyState", "compBorrowState",
              "compSupplierIndex", "compBorrowerIndex", "compAccrued"]
PAIRS = {"p62": "port", "p64": "p64_port", "p65": "proved"}
TOPICS = {"0x1fc3ecc087d8d2d15e23d0032af5a47059c3892d003d8e139fdcb6bb327c99a6": "borrow",
          "0x2caecd17d02f56fa897705dcc740da2d237c373f70686f4e0d9bd3bf0400ea7a": "supply"}


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def sha256(b):
    return hashlib.sha256(b).hexdigest()


# 2. Sources.

def source(v):
    """compound-protocol at the variant's commit, extracted into the cache, every file checked."""
    commit = VARIANTS[v]["commit"]
    dest = CACHE / "compound" / f"src-{commit[:12]}"
    if not dest.exists():
        data = urllib.request.urlopen(urllib.request.Request(REPO + commit, headers={"User-Agent": "proofforge"}),
                                      timeout=300).read()
        tmp = CACHE / "compound" / f"tmp-{os.getpid()}"
        shutil.rmtree(tmp, ignore_errors=True)
        tmp.mkdir(parents=True)
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tf:
            tf.extractall(tmp, filter="data")
        (top,) = list(tmp.iterdir())
        if top.name != f"compound-protocol-{commit}":
            raise RuntimeError(f"unexpected archive root {top.name}")
        top.rename(dest)
        shutil.rmtree(tmp, ignore_errors=True)
    for rel, want in SHA256[v].items():
        got = sha256((dest / rel).read_bytes())
        if got != want:
            raise RuntimeError(f"{v} {rel}: sha256 {got}, expected {want}")
    return dest


def workdir():
    """A Foundry project: each variant's Comptroller sources in src/<variant>, the drivers in test/."""
    d = CACHE / "compound" / "work"
    for v in VARIANTS:
        src = source(v)
        for rel in SHA256[v]:
            dst = d / "src" / v / pathlib.Path(rel).relative_to("contracts")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(src / rel, dst)
    (d / "test").mkdir(parents=True, exist_ok=True)
    (d / "io").mkdir(exist_ok=True)
    for f in ("CompDriver.t.sol", "ForkReplay.t.sol"):
        shutil.copy(ADAPTER / f, d / "test" / f)
    shutil.copy(ADAPTER / "foundry.toml", d / "foundry.toml")
    return d


def build(d):
    r = sh(["forge", "build"], cwd=d, timeout=3600)
    if r.returncode:
        raise RuntimeError((r.stdout + r.stderr)[-4000:])
    lay = sh(["forge", "inspect", "src/p62/Comptroller.sol:Comptroller", "storageLayout", "--json"], cwd=d)
    if lay.returncode:
        raise RuntimeError(lay.stderr[-2000:])
    slots = {s["label"]: int(s["slot"]) for s in json.loads(lay.stdout)["storage"]}
    return [slots[n] for n in SLOT_NAMES], {n: slots[n] for n in SLOT_NAMES}


def strip_metadata(code):
    """Runtime code without the trailing CBOR metadata (its length is in the last two bytes)."""
    b = bytes.fromhex(code[2:] if code.startswith("0x") else code)
    n = int.from_bytes(b[-2:], "big")
    return b[:-(n + 2)]


def compare_bytecode(d):
    out = {}
    for v, info in VARIANTS.items():
        local = sh(["forge", "inspect", f"src/{v}/Comptroller.sol:Comptroller", "deployedBytecode"], cwd=d).stdout.strip()
        chain = sh(["cast", "code", info["implementation"], "--block", str(info["active_from"]), "--rpc-url", RPC])
        if chain.returncode or len(chain.stdout.strip()) < 10:
            out[v] = {"checked": False, "reason": (chain.stderr or "no code")[-300:]}
            continue
        code = chain.stdout.strip()
        a, b = strip_metadata(local), strip_metadata(code)
        out[v] = {"checked": True, "identical_without_metadata": a == b, "bytes": len(bytes.fromhex(code[2:])),
                  "deployed_sha256": sha256(bytes.fromhex(code[2:]))}
    return out


# 3. Real code.

def encode(case):
    L, ops = case["legacy"], case["ops"]
    w = [len(L["accts"]), L["blockNumber"], L["compSpeed"], L["supplyIndex"], L["supplyBlock"],
         L["borrowIndex"], L["borrowBlock"], L["reserve"]]
    for a in L["accts"]:
        w += [a["supply"], a["borrow"], a["supplierIndex"], a["borrowerIndex"], a["accrued"], a["wallet"]]
    w.append(len(ops))
    for op in ops:
        k = op["op"]
        if k == "transfer":
            w += [KINDS[k], op["src"], op["dst"], op["amount"]]
        elif k == "setSpeeds":
            w += [KINDS[k], op["supply"], op["borrow"], 0]
        elif k == "advance":
            w += [KINDS[k], op["blocks"], 0, 0]
        elif k == "drip":
            w += [KINDS[k], op["amount"], 0, 0]
        elif k == "claim":
            w += [KINDS[k], op["who"], 0, 0]
        else:
            w += [KINDS[k], op["who"], op["amount"], 0]
    return words_hex(w)


def words_hex(w):
    b = (32).to_bytes(32, "big") + len(w).to_bytes(32, "big") + b"".join(x.to_bytes(32, "big") for x in w)
    return "0x" + b.hex()


def compact(out):
    """An output with each state as a flat list: blockNumber, supply index, block, speed,
    borrow index, block, speed, reserve, then per account supply, borrow, supplierIndex,
    borrowerIndex, accrued, wallet; each step is [applied (0 or 1), state]."""
    def flat(s):
        v = [s["blockNumber"], s["supplyState"]["index"], s["supplyState"]["block"], s["supplyState"]["speed"],
             s["borrowState"]["index"], s["borrowState"]["block"], s["borrowState"]["speed"], s["reserve"]]
        for a in s["accts"]:
            v += [a["supply"], a["borrow"], a["supplierIndex"], a["borrowerIndex"], a["accrued"], a["wallet"]]
        return v
    return {"start": flat(out["start"]), "steps": [[1 if st["ok"] else 0, flat(st["state"])] for st in out["steps"]]}


def parse_state(f):
    f = [int(x) for x in f]
    n = f[8]
    accts = []
    for i in range(n):
        a = f[9 + 6 * i: 15 + 6 * i]
        accts.append(dict(zip(("supply", "borrow", "supplierIndex", "borrowerIndex", "accrued", "wallet"), a)))
    return {"blockNumber": f[0], "supplyState": {"index": f[1], "block": f[2], "speed": f[3]},
            "borrowState": {"index": f[4], "block": f[5], "speed": f[6]}, "reserve": f[7], "accts": accts}


def run_real(d, slots, cases, variant):
    (d / "io" / "cases.txt").write_text(words_hex(slots + [len(cases)]) + "\n" + "".join(encode(c) + "\n" for c in cases))
    out = d / "io" / f"out-{variant}.txt"
    out.unlink(missing_ok=True)
    env = {**os.environ, "COMP_CASES": "io/cases.txt", "COMP_OUT": f"io/out-{variant}.txt", "COMP_VARIANT": variant}
    r = sh(["forge", "test", "--match-test", "testRunCases", "-q"], cwd=d, env=env, timeout=14400)
    if r.returncode or not out.exists():
        raise RuntimeError((r.stdout + r.stderr)[-4000:])
    outs, cur = [], None
    for line in out.read_text().splitlines():
        f = line.split()
        if f[0] == "s":
            cur = {"start": parse_state(f[1:]), "steps": []}
        elif f[0] == "o":
            cur["steps"].append({"ok": f[1] == "1", "state": parse_state(f[2:])})
        elif f[0] == "e":
            outs.append(cur)
    if len(outs) != len(cases):
        raise RuntimeError(f"{variant}: {len(outs)} outputs for {len(cases)} cases")
    return outs


def fork_replay(d):
    out = d / "io" / "fork.txt"
    out.unlink(missing_ok=True)
    env = {**os.environ, "COMP_OUT": "io/fork.txt", "COMP_RPC": RPC}
    r = sh(["forge", "test", "--match-test", "testReplay", "-q"], cwd=d, env=env, timeout=3600)
    if r.returncode or not out.exists():
        return {"ran": False, "reason": (r.stdout + r.stderr)[-1500:]}
    res = {"ran": True, "fork_block": 13322936, "block": 13322937, "rpc": RPC}
    for line in out.read_text().splitlines():
        f = line.split()
        v = [int(x) for x in f[1:]]
        res[f[0]] = {"before": {"compAccrued": v[0], "comp_balance": v[1], "borrower_index": v[2]},
                     "after": {"compAccrued": v[3], "comp_balance": v[4], "borrower_index": v[5]},
                     "comptroller_comp": [v[6], v[7]], "paid": v[4] - v[1], "credited": v[3] + v[4] - v[0] - v[1]}
    return res


# 7. Chain.

def rpc(method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    err = None
    for i in range(6):
        try:
            r = json.loads(urllib.request.urlopen(urllib.request.Request(
                RPC, data=body, headers={"Content-Type": "application/json", "User-Agent": "proofforge"}), timeout=90).read())
            if "result" in r:
                return r["result"]
            err = r.get("error")
        except Exception as e:  # noqa: BLE001
            err = str(e)
        time.sleep(1 + i)
    raise RuntimeError(err)


def scan(lo=13322798, hi=13382884, step=50):
    ev = []
    for b in range(lo, hi + 1, step):
        for l in rpc("eth_getLogs", [{"address": UNITROLLER, "fromBlock": hex(b), "toBlock": hex(min(hi, b + step - 1)),
                                      "topics": [list(TOPICS)]}]):
            data = l["data"][2:]
            delta, idx = int(data[:64], 16), int(data[64:128], 16)
            if idx == 10 ** 36 and delta > 0:
                ev.append({"side": TOPICS[l["topics"][0]], "block": int(l["blockNumber"], 16), "tx": l["transactionHash"],
                           "ctoken": "0x" + l["topics"][1][-40:], "account": "0x" + l["topics"][2][-40:], "delta": str(delta)})
    return ev


# 4. Lean.

def lean_outputs(t, candidate, cases, need_accept):
    j = judge.judge(str(candidate), task=t) if need_accept else None
    if need_accept and not j["accepted"]:
        raise RuntimeError(f"{candidate} is not accepted by the judge")
    ws = judge.load_workspace(str(candidate))
    project = judge.fresh_project(ws, judge.candidate_files(ws), t)
    b = binary_check.build(project, t)
    if b["exit_code"]:
        raise RuntimeError(b["output_tail"])
    sha = (project / "binary.sha256").read_text().strip()
    outs = binary_check.run_cases(project, t.exe, cases, "compound")
    shutil.rmtree(project, ignore_errors=True)
    return outs, sha, (j or {}).get("solution_tree_sha256")


def verified_candidate(t, out):
    for run in sorted(out.glob("repair-*")):
        p = run / "passport.json"
        if p.exists() and json.loads(p.read_text())["status"] == "VERIFIED":
            return run / "final.lean", f"Muse repair {run.name} (Passport {json.loads(p.read_text())['passport_sha256'][:16]})"
    return t.root / "reference" / "SolutionA.lean", "build-team reference (reference/SolutionA.lean)"


# 5. Lean statements of real-code violations.

def lean_acct(a):
    return "⟨" + ", ".join(str(a[f]) for f in ("supply", "borrow", "supplierIndex", "borrowerIndex", "accrued", "wallet")) + "⟩"


def lean_state(s):
    side = lambda x: f"⟨{x['index']}, {x['block']}, {x['speed']}⟩"
    return (f"({{ blockNumber := {s['blockNumber']}, supplyState := {side(s['supplyState'])}, borrowState := "
            f"{side(s['borrowState'])}, reserve := {s['reserve']}, accts := [{', '.join(lean_acct(a) for a in s['accts'])}] }} : St)")


def lean_legacy(L):
    return (f"({{ blockNumber := {L['blockNumber']}, compSpeed := {L['compSpeed']}, supplyIndex := {L['supplyIndex']}, "
            f"supplyBlock := {L['supplyBlock']}, borrowIndex := {L['borrowIndex']}, borrowBlock := {L['borrowBlock']}, "
            f"supplyStart := {L['supplyStart']}, borrowStart := {L['borrowStart']}, reserve := {L['reserve']}, "
            f"accts := [{', '.join(lean_acct(a) for a in L['accts'])}] }} : Legacy)")


def lean_op(op):
    k = op["op"]
    if k == "transfer":
        return f"Op.transfer {op['src']} {op['dst']} {op['amount']}"
    if k == "setSpeeds":
        return f"Op.setSpeeds {op['supply']} {op['borrow']}"
    if k == "advance":
        return f"Op.advance {op['blocks']}"
    if k == "drip":
        return f"Op.drip {op['amount']}"
    if k == "claim":
        return f"Op.claim {op['who']}"
    return f"Op.{k} {op['who']} {op['amount']}"


def lean_goal(case, real, rid, oracle):
    """A `decide` goal over Spec.lean that holds exactly when the real states break `rid`."""
    L, ops = case["legacy"], case["ops"]
    states = [real["start"]] + [s["state"] for s in real["steps"]]
    cum = oracle.emitted_steps(L, ops)
    if rid == "REQ-REWARDS-BOUNDED":
        for j, s in enumerate(states):
            if oracle.credited(s) > oracle.credited(real["start"]) + oracle.owed(L) + cum[j]:
                return (f"¬ ({lean_state(s)}.credited ≤ (upgrade {lean_legacy(L)}).credited + {lean_legacy(L)}.owed + "
                        f"emitted ({L['compSpeed']}, {L['compSpeed']}) [{', '.join(lean_op(o) for o in ops[:j])}])"), j
    if rid == "REQ-ACCOUNT-BOUNDED":
        for w in range(len(L["accts"])):
            for j, s in enumerate(states):
                if oracle.credited_to(s, w) > oracle.credited_to(real["start"], w) + oracle.owed_to(L, w) + cum[j]:
                    return (f"¬ ({lean_state(s)}.creditedTo {w} ≤ (upgrade {lean_legacy(L)}).creditedTo {w} + "
                            f"{lean_legacy(L)}.owedTo {w} + emitted ({L['compSpeed']}, {L['compSpeed']}) "
                            f"[{', '.join(lean_op(o) for o in ops[:j])}])"), j
    if rid in ("REQ-SUPPLY-HOOK", "REQ-BORROW-HOOK"):
        side = "supply" if rid == "REQ-SUPPLY-HOOK" else "borrow"
        for i, op in enumerate(ops):
            if op["op"] in (("mint", "redeem") if side == "supply" else ("borrow", "repay")) and real["steps"][i]["ok"]:
                p, q = states[i], states[i + 1]
                exp = oracle.distributed(p, op["who"], side)
                if exp is None:
                    continue
                key = "Supply" if side == "supply" else "Borrow"
                # The hook's state is the reported state with the balance change undone.
                h = json.loads(json.dumps(q))
                d = op["amount"] if op["op"] in ("mint", "borrow") else -op["amount"]
                h["accts"][op["who"]][side] -= d
                if h != exp:
                    return f"¬ {key}Distributed {lean_state(p)} {op['who']} {lean_state(h)}", i
    return None, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=500)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default="results/compound-1")
    ap.add_argument("--scan", action="store_true", help="list the incident-pattern credits on mainnet")
    a = ap.parse_args()
    out = (ROOT / a.out).resolve()
    rc = out / "real-code"
    rc.mkdir(parents=True, exist_ok=True)
    t = taskmod.load(TASK)
    oracle = t.oracle
    t0 = time.monotonic()

    # 1. The port and the proved component: kernel refutations and unit tests.
    port = TASK / "attacks" / "p62_port.lean"
    p64 = TASK / "attacks" / "p64_claim_lock.lean"
    candidate, label = verified_candidate(t, out)
    rd = lambda p: (TASK / p).read_text()
    port_res = lean_check(t, port, {"Claim.lean": rd("witnesses/cSUSHI_claim.lean"),
                                    "Regression.lean": rd("witnesses/compound_regression.lean"),
                                    "UnitTests.lean": rd("tests/PortUnitTests.lean")})
    fix_res = lean_check(t, candidate, {"UnitTests.lean": rd("tests/PortUnitTests.lean"),
                                        "RegressionOnFix.lean": rd("tests/RegressionOnFix.lean")})
    print("port: cSUSHI refutation", "checked" if port_res["Claim.lean"][0] else "FAILED",
          "| regression refutation", "checked" if port_res["Regression.lean"][0] else "FAILED",
          "| unit tests", "pass" if port_res["UnitTests.lean"][0] else "FAIL",
          "| on the proved component: unit tests", "pass" if fix_res["UnitTests.lean"][0] else "FAIL",
          ", regression test", "pass" if fix_res["RegressionOnFix.lean"][0] else "FAIL", flush=True)

    # 2. Sources, compilation, bytecode.
    d = workdir()
    slots, slot_map = build(d)
    bytecode = compare_bytecode(d)
    print("compiled Comptrollers vs deployed runtime code (metadata excluded):",
          {v: b.get("identical_without_metadata") for v, b in bytecode.items()}, flush=True)

    # 3 and 4. Cases on the compiled Solidity and on the Lean executables.
    documented = [
        {"name": "cSUSHI claim, mainnet transaction 0xc9244e53...0001", "case": oracle.FLAGSHIP},
        {"name": "Compound's post-incident regression scenario on the upgrade path", "case": {
            "legacy": {"blockNumber": 1000, "compSpeed": 0, "supplyIndex": 0, "supplyBlock": 900, "borrowIndex": 0,
                       "borrowBlock": 900, "supplyStart": 0, "borrowStart": 0, "reserve": 10 ** 24,
                       "accts": [oracle.acct(supply=100 * 10 ** 18), oracle.acct(), oracle.acct(borrow=10 * 10 ** 18),
                                 oracle.acct()]},
            "ops": [{"op": "mint", "who": 1, "amount": 100 * 10 ** 18}, {"op": "borrow", "who": 3, "amount": 10 * 10 ** 18},
                    {"op": "advance", "blocks": 1000}, {"op": "claim", "who": 1}, {"op": "claim", "who": 0},
                    {"op": "claim", "who": 3}, {"op": "claim", "who": 2}]}},
        {"name": "Sanity.lean honest_rewards", "case": {
            "legacy": {"blockNumber": 100, "compSpeed": 0, "supplyIndex": 0, "supplyBlock": 90, "borrowIndex": 0,
                       "borrowBlock": 90, "supplyStart": 0, "borrowStart": 0, "reserve": 1000,
                       "accts": [oracle.acct(supply=50), oracle.acct(borrow=20)]},
            "ops": [{"op": "setSpeeds", "supply": 3, "borrow": 2}, {"op": "advance", "blocks": 10},
                    {"op": "claim", "who": 0}, {"op": "claim", "who": 1}]}},
    ]
    rng = random.Random(a.seed)
    cases = [x["case"] for x in documented] + [oracle.gen_case(rng) for _ in range(a.cases)]
    real = {v: run_real(d, slots, cases, v) for v in VARIANTS}
    print(f"real code: {len(cases)} cases run on each of {list(real)}", flush=True)
    lean = {}
    lean["port"] = lean_outputs(t, port, cases, False)
    lean["p64_port"] = lean_outputs(t, p64, cases, False)
    lean["proved"] = lean_outputs(t, candidate, cases, True)
    (rc / "cases.jsonl").write_text("".join(json.dumps(c, separators=(",", ":")) + "\n" for c in cases))
    for v in real:
        (rc / f"real-{v}-outputs.jsonl").write_text("".join(json.dumps(compact(o), separators=(",", ":")) + "\n"
                                                             for o in real[v]))
    lean_files = {k: {"sha256": sha256("".join(json.dumps(compact(o)) + "\n" for o in lean[k][0]).encode()),
                      "identical_to_real": lean[k][0] == real[[v for v, kk in PAIRS.items() if kk == k][0]]}
                  for k in lean}

    # 5. Compare and check.
    pairs = PAIRS
    comparison = {}
    confirm, confirm_items = [], []
    for v, outs in real.items():
        lo = lean[pairs[v]][0]
        rep = {"lean_counterpart": pairs[v], "identical": 0, "differs": [], "identical_to_proved": 0,
               "violating_cases": 0, "by_requirement": {}, "witnesses": []}
        seen = set()
        for i, (c, r, l, p) in enumerate(zip(cases, outs, lo, lean["proved"][0])):
            if r == l:
                rep["identical"] += 1
            elif len(rep["differs"]) < 10:
                rep["differs"].append({"case": i, "input": c, "real": r, "lean": l})
            if r == p:
                rep["identical_to_proved"] += 1
            viol = oracle.violations(c, r["start"], r["steps"])
            if not viol:
                continue
            rep["violating_cases"] += 1
            for rid, msg in viol:
                rep["by_requirement"][rid] = rep["by_requirement"].get(rid, 0) + 1
                if i < len(documented) or (rid not in seen and len(rep["witnesses"]) < 12):
                    g, step = lean_goal(c, r, rid, oracle)
                    w = {"case": i, "documented": documented[i]["name"] if i < len(documented) else None,
                         "requirement": rid, "message": msg, "step": step, "lean_goal": g}
                    rep["witnesses"].append(w)
                    if g:
                        confirm_items.append((v, w))
                    if i >= len(documented):
                        seen.add(rid)
        rep["proved_violations"] = sum(1 for c, p in zip(cases, lean["proved"][0]) if oracle.check(c, p))
        comparison[v] = rep
    text = ("import CompRewards.Spec\nopen CompRewards\n\n"
            "instance (s : St) (who : Account) (s' : St) : Decidable (SupplyDistributed s who s') := by\n"
            "  unfold SupplyDistributed; infer_instance\n\n"
            "instance (s : St) (who : Account) (s' : St) : Decidable (BorrowDistributed s who s') := by\n"
            "  unfold BorrowDistributed; infer_instance\n\n") + "".join(
        f"-- {v} case {w['case']}, step {w['step']}, {w['requirement']}: {w['message']}\n"
        f"example : {w['lean_goal']} := by decide\n\n" for v, w in confirm_items)
    (rc / "Confirm.lean").write_text(text)
    ok, tail = lean_check(t, candidate, {"Confirm.lean": text})["Confirm.lean"] if confirm_items else (True, "")
    for _, w in confirm_items:
        w["confirmed_in_lean"] = ok
    for v, rep in comparison.items():
        print(f"{v}: {rep['identical']} of {len(cases)} identical to the Lean {rep['lean_counterpart']}; "
              f"{rep['violating_cases']} violate the requirements {rep['by_requirement']}", flush=True)

    # 6. Fork replay of the cSUSHI claim.
    fork = fork_replay(d)
    print("fork replay:", {k: (fork[k]["credited"] if isinstance(fork.get(k), dict) else fork[k])
                           for k in fork if k in ("ran", "p62", "p64", "p65")}, flush=True)

    # 7. Credits with the pattern of the bug on mainnet.
    chain = None
    if a.scan:
        ev = scan()
        (rc / "onchain-credits.jsonl").write_text("".join(json.dumps(e) + "\n" for e in ev))
        chain = {"from_block": 13322798, "to_block": 13382884, "events": len(ev),
                 "accounts": len({e["account"] for e in ev}),
                 "credited_total": str(sum(int(e["delta"]) for e in ev)),
                 "largest": sorted(ev, key=lambda e: -int(e["delta"]))[:5]}
        print(f"mainnet: {len(ev)} credits at index 1e36 to {chain['accounts']} accounts", flush=True)

    forge = sh(["forge", "--version"]).stdout.splitlines()[0]
    report = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "elapsed_s": round(time.monotonic() - t0, 1),
        "task": t.id, "source": t.meta["source"], "variants": VARIANTS, "forge": forge, "rpc": RPC,
        "storage_slots": slot_map, "bytecode": bytecode, "image": judge.IMAGE, "image_id": judge.image_id(),
        "seed": a.seed, "cases": len(cases), "documented": [x["name"] for x in documented],
        "port": {"candidate": "realworld/tasks/rw-compound-comp/attacks/p62_port.lean",
                 "executable_sha256": lean["port"][1],
                 "cSUSHI_refutation_checked": port_res["Claim.lean"][0], "cSUSHI_output_tail": port_res["Claim.lean"][1],
                 "regression_refutation_checked": port_res["Regression.lean"][0],
                 "unit_tests_pass": port_res["UnitTests.lean"][0], "unit_tests_output_tail": port_res["UnitTests.lean"][1]},
        "p64_port": {"candidate": "realworld/tasks/rw-compound-comp/attacks/p64_claim_lock.lean",
                     "executable_sha256": lean["p64_port"][1]},
        "proved": {"candidate": label, "executable_sha256": lean["proved"][1], "solution_tree_sha256": lean["proved"][2],
                   "unit_tests_pass": fix_res["UnitTests.lean"][0],
                   "regression_test_pass": fix_res["RegressionOnFix.lean"][0],
                   "output_tail": fix_res["UnitTests.lean"][1] + fix_res["RegressionOnFix.lean"][1]},
        "comparison": comparison,
        "lean_outputs": lean_files,
        "output_format": compact.__doc__.strip(),
        "lean_confirmation": {"file": "real-code/Confirm.lean", "goals": len(confirm_items),
                              "checked": len(confirm_items) if ok else 0, "output_tail": tail},
        "fork_replay": fork, "chain": chain,
    }
    (rc / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"wrote {rc / 'report.json'}")


if __name__ == "__main__":
    main()
