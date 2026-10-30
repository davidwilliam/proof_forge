"""Counterexample adapter for rw-euler-donate (harness/counterexample.py).

A case is a sequence of operations from `genesis` over accounts 0 to n - 1; the executable
reports the state after each one. The adapter replays the task oracle to find the first step at
which the requirement fails, then:

* for the per-step requirements (REQ-ALLOWED-SUCCEEDS, REQ-EFFECTS, REQ-ACTOR-HEALTHY,
  REQ-STAYS-HEALTHY), which hold for every state, instantiates them at the state before that
  step, written out from the reported balances (accounts n and above are empty, as in every
  state reached from `genesis` by operations on accounts below n). The state after the step is
  left to the kernel;
* for REQ-NO-BAD-DEBT, which is about reachable states, runs the operations that succeeded up to
  that step with `runAll` from `genesis` in the kernel, and proves the result reachable with the
  helper lemma `cex_reachable_of_run`.
"""
from counterexample import lst, nat, struct

PER_STEP = {"REQ-ALLOWED-SUCCEEDS", "REQ-EFFECTS", "REQ-ACTOR-HEALTHY", "REQ-STAYS-HEALTHY"}

REACHABLE_OF_RUN = """theorem cex_reachable_of_run :
    ∀ (ops : List Op) (s s' : St), Reachable step s → runAll step s ops = some s' →
      Reachable step s'
  | [], s, s', h, hr => by
    simp only [runAll, Option.some.injEq] at hr
    exact hr ▸ h
  | op :: ops, s, s', h, hr => by
    simp only [runAll] at hr
    split at hr
    · rename_i s1 h1
      exact cex_reachable_of_run ops s1 s' (Reachable.step op h h1) hr
    · cases hr"""


def op_term(op):
    k = op[0]
    return f"(Op.{k} {' '.join(nat(x) for x in op[1:])})"


def state_term(s):
    accts = lst([f"⟨{nat(e)}, {nat(d)}⟩" for e, d in s["acct"]])
    return struct({"acct": f"(fun u => {accts}.getD u ⟨0, 0⟩)", "cash": nat(s["cash"]),
                   "reserves": nat(s["reserves"])}, "St")


def replay(oracle, case, out):
    """(k, s, op, ok, s2, done) for every step, where `done` lists the ops that succeeded so far."""
    s, done = oracle.genesis(case["n"]), []
    for k, (op, st) in enumerate(zip(case["ops"], out["steps"])):
        op = oracle.resolve(op, s["acct"])
        s2 = {"acct": st["acct"], "cash": st["cash"], "reserves": st["reserves"]}
        if st["ok"]:
            done = done + [op]
        yield k, s, op, st["ok"], s2, done
        s = s2


def instance(task, requirement, case, out):
    o = task.oracle
    if "steps" not in (out or {}):
        return None
    for k, s, op, ok, s2, done in replay(o, case, out):
        if requirement in PER_STEP:
            v = [rid for rid, _ in o.transition_violations(s, op, ok, s2)]
            if requirement not in v:
                continue
            S, OP = state_term(s), op_term(op)
            note = f"step {k} of the case, {op}, from the reported state before it"
            if requirement == "REQ-ALLOWED-SUCCEEDS":
                return {"args": [S, OP, "?"], "hints": ["by unfold Allowed; decide"], "note": note}
            if requirement == "REQ-EFFECTS":
                return {"args": [S, OP, "_", "?"], "note": note}
            if requirement == "REQ-ACTOR-HEALTHY":
                return {"args": [S, OP, "_", nat(o.checked(op)[0]), "?", "?"], "note": note}
            w = next(w for w, ((e, d), (e2, d2)) in enumerate(zip(s["acct"], s2["acct"]))
                     if o.healthy(e, d) and not o.healthy(e2, d2))
            return {"args": [S, OP, "_", nat(w), "?", "?"], "note": note + f", account {w}"}
        if requirement == "REQ-NO-BAD-DEBT":
            bad = [w for w, (e, d) in enumerate(s2["acct"]) if not o.healthy(e, d)]
            if not bad:
                continue
            ops = lst([op_term(x) for x in done], "Op")
            return {"preamble": REACHABLE_OF_RUN,
                    "proof": f"""intro h
have := h _ (cex_reachable_of_run {ops} genesis _ Reachable.genesis
  (Option.some_get (by decide : (runAll step genesis {ops}).isSome = true)).symm) {nat(bad[0])}
revert this
decide""",
                    "note": f"the {len(done)} operations that succeed up to step {k} leave account {bad[0]} unhealthy"}
    if requirement == "REQ-HONEST-FLOW":
        return {"args": [], "note": "the honest session"}
    return None
