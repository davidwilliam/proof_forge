"""Refutation of new sub-lemmas on concrete values, before any model turn is spent on them.

When a planner lemma, a skeleton helper or a helper the model states with `sorry` enters the
candidate, a Lean probe (run like the dependency probe, after `lake build Solution`, never part of
a candidate) evaluates its statement on concrete instances:

  * the statement's binders are opened (definitions unfolded as far as Lean's `whnf` exposes
    more binders); hypotheses (binders whose type is a proposition) stay as hypotheses;
  * every other binder gets values: Nat, Int, Bool, String, Option, List, Array and pairs from
    fixed pools; structures and inductive types (no indices) from their constructors with field
    values drawn recursively; functions as constant functions; type parameters as Nat; instance
    arguments by instance resolution. Values the task's own generator produces come first: the
    JSON cases of the task's oracle (`gen_case`, and `FLAGSHIP`), every object and array inside
    them, are converted to the binder's type by field and constructor names (a structure from an
    object with keys equal to its field names, an inductive constructor from a string or from an
    object with a string naming it). Nothing is specific to a task;
  * for each instance, the instantiated statement (hypotheses included, as implications) must be
    decidable by instance resolution; `decide` of it is reduced with `whnf` under a heartbeat
    limit. A reduction to `false` is a candidate counterexample;
  * a counterexample counts only when Lean's kernel accepts the refutation: a theorem
    `¬ (statement)` whose proof applies the statement to the instance and closes the instance by
    `of_decide_eq_false rfl`, added with the kernel's own `addDecl`. Only then is the lemma refused.

Statements over undecidable propositions (an `∀` left inside, a predicate without a `Decidable`
instance) or over types with no sampleable values are reported as unsupported and left to the
model. No dollars; the Lean time counts against the wall cap (judge.in_container).
"""
import hashlib, json, random, re, time

import judge  # noqa: E402

SAMPLES = 64          # instances per statement
GEN_CASES = 40        # oracle cases whose JSON values seed the pools
GEN_VALUES = 400      # most JSON values passed to the probe
BASE_SECONDS = 40
PER_LEMMA_SECONDS = 15
MAX_SECONDS = 240

PROBE = r'''import Solution
import Lean
open Lean Meta

/-! Harness probe (agents/refute.py): evaluates statements on concrete instances; a falsifying
instance counts only when the kernel accepts the refutation. Never part of a candidate. -/

namespace PFRefute

def natPool : Array Nat := #[0, 1, 2, 3, 5, 10, 100, 1000, 1000000, 1000000000000000000]
def intPool : Array Int := #[0, 1, -1, 2, -3, 10, -100, 1000000]

def nextRand (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

structure St where
  pools : Std.HashMap Expr (Array Expr) := {}
  rand : Nat := 7

abbrev M := StateRefT St MetaM

def rnd (n : Nat) : M Nat := do
  let s ← get
  let r := nextRand s.rand
  set { s with rand := r }
  return if n == 0 then 0 else (r / 65536) % n

def pick (xs : Array Expr) (k : Nat) : M Expr := do
  if k < xs.size then return xs[k]!
  return xs[← rnd xs.size]!

def lower (s : String) : String := s.toLower

/-- A value of type `ty` from a JSON value, by field and constructor names. -/
partial def ofJson (ty : Expr) (j : Json) (fuel : Nat) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let ty ← whnf ty
  let args := ty.getAppArgs
  match ty.getAppFn with
  | .const ``Nat _ => return (j.getNat?.toOption).map mkNatLit
  | .const ``Int _ => return (j.getInt?.toOption).map toExpr
  | .const ``Bool _ => return (j.getBool?.toOption).map toExpr
  | .const ``String _ => return (j.getStr?.toOption).map toExpr
  | .const ``List _ =>
    let some arr := j.getArr?.toOption | return none
    let mut out := #[]
    for x in arr do
      let some v ← ofJson args[0]! x (fuel - 1) | return none
      out := out.push v
    return some (← mkListLit args[0]! out.toList)
  | .const ``Array _ =>
    let some arr := j.getArr?.toOption | return none
    let mut out := #[]
    for x in arr do
      let some v ← ofJson args[0]! x (fuel - 1) | return none
      out := out.push v
    return some (← mkArrayLit args[0]! out.toList)
  | .const ``Option [u] =>
    if j.isNull then return some (mkApp (.const ``Option.none [u]) args[0]!)
    let some v ← ofJson args[0]! j (fuel - 1) | return none
    return some (mkApp2 (.const ``Option.some [u]) args[0]! v)
  | .const c lvls =>
    let some (.inductInfo iv) := (← getEnv).find? c | return none
    if iv.numIndices != 0 || args.size != iv.numParams then return none
    for ctor in iv.ctors do
      let some (.ctorInfo ci) := (← getEnv).find? ctor | continue
      let cty ← instantiateForall ci.type args
      let short := ctor.getString!
      if ci.numFields == 0 then
        if (j.getStr?.toOption).map lower == some (lower short) then
          return some (mkAppN (.const ctor lvls) args)
        continue
      let some obj := j.getObj?.toOption | continue
      if iv.ctors.length > 1 then
        let tagged := obj.toArray.any fun (_, v) => (v.getStr?.toOption).map lower == some (lower short)
        if !tagged then continue
      let r ← forallTelescopeReducing cty fun fs _ => do
        let mut vals := #[]
        for f in fs do
          let fty ← inferType f
          if (← isProp fty) || fty.hasAnyFVar (fun x => fs.contains (.fvar x)) then return none
          let nm := (← f.fvarId!.getUserName).toString
          let some (_, v) := obj.toArray.find? (fun (k, _) => lower k == lower nm) | return none
          let some e ← ofJson fty v (fuel - 1) | return none
          vals := vals.push e
        return some vals
      if let some vals := r then
        return some (mkAppN (mkAppN (.const ctor lvls) args) vals)
    return none
  | _ => return none

def jsonVals (ty : Expr) (js : Array Json) : MetaM (Array Expr) := do
  let mut out := #[]
  for j in js do
    if out.size ≥ 24 then break
    try
      if let some e ← ofJson ty j 6 then
        if !(out.contains e) then out := out.push e
    catch _ => pure ()
  return out

partial def pool (ty : Expr) (js : Array Json) (fuel : Nat) : M (Array Expr) := do
  if let some p := (← get).pools.get? ty then return p
  let res ← go
  modify fun s => { s with pools := s.pools.insert ty res }
  return res
where
  go : M (Array Expr) := do
    if fuel == 0 then return #[]
    let fromGen ← jsonVals ty js
    let ty ← whnf ty
    let args := ty.getAppArgs
    let generic : Array Expr ← match ty.getAppFn with
      | .const ``Nat _ => pure (natPool.map mkNatLit)
      | .const ``Int _ => pure (intPool.map toExpr)
      | .const ``Bool _ => pure #[toExpr false, toExpr true]
      | .const ``String _ => pure #[toExpr "", toExpr "a", toExpr "b"]
      | .const ``Option [u] => do
        let p ← pool args[0]! js (fuel - 1)
        pure (#[mkApp (.const ``Option.none [u]) args[0]!] ++ (p.extract 0 4).map (mkApp2 (.const ``Option.some [u]) args[0]!))
      | .const ``List _ => do
        let p ← pool args[0]! js (fuel - 1)
        let mut out := #[← mkListLit args[0]! []]
        if !p.isEmpty then
          for k in [0:8] do
            let mut xs := #[]
            for i in [0:1 + k % 3] do xs := xs.push (← pick p (if k < 2 then i else 1000))
            out := out.push (← mkListLit args[0]! xs.toList)
        pure out
      | .const ``Array _ => do
        let p ← pool args[0]! js (fuel - 1)
        let mut out := #[← mkArrayLit args[0]! []]
        if !p.isEmpty then
          for k in [0:6] do
            let mut xs := #[]
            for i in [0:1 + k % 3] do xs := xs.push (← pick p (if k < 2 then i else 1000))
            out := out.push (← mkArrayLit args[0]! xs.toList)
        pure out
      | .const ``Prod [u, v] => do
        let a ← pool args[0]! js (fuel - 1)
        let b ← pool args[1]! js (fuel - 1)
        if a.isEmpty || b.isEmpty then pure #[] else
        let mut out := #[]
        for k in [0:16] do
          out := out.push (mkApp4 (.const ``Prod.mk [u, v]) args[0]! args[1]!
            (← pick a (if k < 3 then k else 1000)) (← pick b (if k < 3 then k else 1000)))
        pure out
      | .const c lvls => ofInductive c lvls args
      | _ =>
        if ty.isForall && !ty.bindingBody!.hasLooseBVars then do
          let p ← pool ty.bindingBody! js (fuel - 1)
          pure ((p.extract 0 6).map fun b => Expr.lam `x ty.bindingDomain! b .default)
        else pure #[]
    return fromGen ++ generic.filter (!fromGen.contains ·)
  ofInductive (c : Name) (lvls : List Level) (args : Array Expr) : M (Array Expr) := do
    let some (.inductInfo iv) := (← getEnv).find? c | return #[]
    if iv.numIndices != 0 || args.size != iv.numParams then return #[]
    let mut out := #[]
    for ctor in iv.ctors do
      let some (.ctorInfo ci) := (← getEnv).find? ctor | continue
      let cty ← instantiateForall ci.type args
      let fieldPools? ← forallTelescopeReducing cty fun fs _ => do
        let mut ps := #[]
        for f in fs do
          let fty ← inferType f
          if (← isProp fty) || fty.hasAnyFVar (fun x => fs.contains (.fvar x)) then return none
          let p ← pool fty js (fuel - 1)
          if p.isEmpty then return none
          ps := ps.push p
        return some ps
      let some ps := fieldPools? | continue
      let head := mkAppN (.const ctor lvls) args
      if ps.isEmpty then
        out := out.push head
        continue
      for k in [0:(if iv.ctors.length > 1 then 6 else 24)] do
        let mut vs := #[]
        for p in ps do vs := vs.push (← pick p (if k < 2 then k else 1000))
        out := out.push (mkAppN head vs)
    return out

def describe (names : Array Name) (vals : Array Expr) : MetaM String := do
  let mut parts := #[]
  for (n, v) in names.zip vals do
    parts := parts.push s!"{n} := {← ppExpr v}"
  return String.intercalate ", " parts.toList

def clean (s : String) : String := (s.replace "\n" " ").replace "\t" " "

/-- `n` instances of the statement of `thm`; the first whose `decide` reduces to `false` and
whose refutation the kernel accepts makes the statement false. -/
def refuteOne (thm : Name) (js : Array Json) (n : Nat) : M String := do
  let some ci := (← getEnv).find? thm | return s!"{thm}\tmissing"
  let ty := ci.type
  forallTelescopeReducing ty fun xs body => do
    let mut hyps := #[]
    let mut data := #[]
    for x in xs do
      if ← isProp (← inferType x) then hyps := hyps.push x else data := data.push x
    for x in data do
      if (← inferType x).hasAnyFVar (fun f => hyps.contains (.fvar f)) then
        return s!"{thm}\tunsupported\ta binder depends on a hypothesis"
    let q0 ← mkForallFVars hyps body
    let mut tried := 0
    let mut undecided := 0
    let mut unconfirmed := ""
    for k in [0:n] do
      let mut vals := #[]
      for x in data do
        let t := (← inferType x).replaceFVars (data.extract 0 vals.size) vals
        if t.isSort then
          vals := vals.push (mkConst ``Nat)
          continue
        if (← x.fvarId!.getBinderInfo).isInstImplicit then
          let some i ← synthInstance? t | return s!"{thm}\tunsupported\tno instance {clean (toString (← ppExpr t))}"
          vals := vals.push i
          continue
        let p ← pool t js 4
        if p.isEmpty then return s!"{thm}\tunsupported\tno values of type {clean (toString (← ppExpr t))}"
        vals := vals.push (← pick p k)
      let q := q0.replaceFVars data vals
      if q.hasFVar then return s!"{thm}\tunsupported\topen statement"
      let some inst ← synthInstance? (mkApp (mkConst ``Decidable) q) | return s!"{thm}\tunsupported\tnot decidable"
      tried := tried + 1
      let dec := mkApp2 (mkConst ``Decidable.decide) q inst
      let r ← tryCatchRuntimeEx
          (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := HEARTBEATS * 1000 }) <|
            withTransparency .all <| whnf dec)
          (fun _ => pure (mkConst ``Unit))
      if r.isConstOf ``Bool.true then continue
      if !r.isConstOf ``Bool.false then
        undecided := undecided + 1
        continue
      let names ← data.mapM fun x => x.fvarId!.getUserName
      let desc := clean (← describe names vals)
      let pf ← withLocalDeclD `h ty fun h => do
        let args := xs.map fun x => if hyps.contains x then x else vals[data.idxOf x]!
        let pq := (← mkLambdaFVars hyps (mkAppN h args)).replaceFVars data vals
        let notQ := mkApp3 (mkConst ``of_decide_eq_false) q inst
          (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.false))
        mkLambdaFVars #[h] (mkApp notQ pq)
      let decl := Declaration.thmDecl { name := thm ++ `pf_refuted, levelParams := ci.levelParams,
                                        type := mkNot ty, value := pf }
      match (← getEnv).toKernelEnv.addDecl {} decl with
      | .ok _ => return s!"{thm}\tfalse\t{k}\t{tried}\t{desc}"
      | .error _ => if unconfirmed.isEmpty then unconfirmed := desc
    if !unconfirmed.isEmpty then return s!"{thm}\tunconfirmed\t{tried}\t{undecided}\t{unconfirmed}"
    return s!"{thm}\tsurvived\t{tried}\t{undecided}"

end PFRefute

open PFRefute in
#eval show MetaM Unit from do
  let js : Array Json := match Json.parse (← IO.FS.readFile "pf_gen.json") with
    | .ok (.arr a) => a
    | _ => #[]
  for n in NAMES do
    let r ← tryCatchRuntimeEx ((refuteOne n js SAMPLES).run' {})
      (fun e => do return s!"{n}\terror\t{PFRefute.clean (toString (← e.toMessageData.toString))}")
    IO.println s!"PFREFUTE {r}"
    (← IO.getStdout).flush
'''


def gen_values(task, n_cases=GEN_CASES, seed=0):
    """JSON values from the task's oracle generator: every object and array inside FLAGSHIP and
    `n_cases` generated cases, de-duplicated. [] when the task has no oracle generator."""
    try:
        oracle = task.oracle
        gen = getattr(oracle, "gen_case", None)
    except Exception:
        return []
    if gen is None:
        return []
    rng = random.Random(seed)
    cases = [getattr(oracle, "FLAGSHIP", None)]
    try:
        cases += [gen(rng) for _ in range(n_cases)]
    except Exception:
        pass
    seen, out = set(), []

    def walk(v, depth=0):
        if depth > 6 or len(out) >= GEN_VALUES:
            return
        if isinstance(v, (dict, list)):
            key = json.dumps(v, sort_keys=True)
            if key not in seen and len(key) < 20000:
                seen.add(key)
                out.append(v)
            for x in (v.values() if isinstance(v, dict) else v):
                walk(x, depth + 1)
    for c in cases:
        if c is not None:
            walk(c)
    return out


def probe_text(names, samples=SAMPLES, heartbeats=20000):
    lean_names = ", ".join(f"`{n}" if re.fullmatch(r"[\w.']+", n) else f"`«{n}»" for n in names)
    return (PROBE.replace("NAMES do", f"[{lean_names}] do").replace("SAMPLES).run'", f"{int(samples)}).run'")
            .replace("HEARTBEATS * 1000", f"{int(heartbeats)} * 1000"))


def parse(output):
    """{full name: record} from the probe's PFREFUTE lines."""
    res = {}
    for line in output.splitlines():
        if not line.startswith("PFREFUTE "):
            continue
        parts = line[len("PFREFUTE "):].split("\t")
        name, status = parts[0], parts[1] if len(parts) > 1 else "error"
        rec = {"status": status}
        if status == "false":
            rec.update(instance=int(parts[2]), tried=int(parts[3]), counterexample=parts[4] if len(parts) > 4 else "")
        elif status in ("survived", "unconfirmed"):
            rec.update(tried=int(parts[2]), undecided=int(parts[3]))
            if status == "unconfirmed":
                rec["counterexample"] = parts[4] if len(parts) > 4 else ""
        else:
            rec["reason"] = "\t".join(parts[2:])[:300]
        res[name] = rec
    return res


def run_probe(s, names, samples=None, label=""):
    """Evaluate the statements of theorems `names` (short names in the candidate) on concrete
    instances. Returns ({short name: record}, info). The candidate must compile."""
    samples = samples or getattr(s, "refute_samples", SAMPLES) or SAMPLES
    full = {f"{s.ns}.{n}": n for n in names}
    gen = s.__dict__.get("refute_gen")
    if gen is None:
        gen = s.refute_gen = gen_values(s.task)
    (s.ws / "pf_gen.json").write_text(json.dumps(gen))
    (s.ws / "Refute.lean").write_text(probe_text(list(full), samples))
    out = s.ws / ".refute.txt"
    out.unlink(missing_ok=True)
    timeout = min(MAX_SECONDS, BASE_SECONDS + PER_LEMMA_SECONDS * len(names))
    t0 = time.monotonic()
    r = judge.in_container(s.ws, "lake build Solution >/dev/null 2>&1; lake env lean Refute.lean > .refute.txt 2>&1; "
                                 "tail -c 600 .refute.txt", timeout=timeout)
    ms = int((time.monotonic() - t0) * 1000)
    text = out.read_text(errors="replace") if out.exists() else ""
    parsed = parse(text)
    res = {short: parsed.get(f, {"status": "not run"}) for f, short in full.items()}
    stopped = judge.TIMEOUT_MARK in r["output_tail"]
    info = {"ms": ms, "stopped": stopped, "gen_values": len(gen)}
    if not parsed:
        info["error"] = (r["output_tail"] or text)[-500:]
    return res, info


def enabled(s):
    return bool(getattr(s, "refute_samples", 0))


def _key(s, name, stmt, src):
    defs = re.findall(r"(?ms)^(?:def|abbrev|structure|inductive|instance)\b.*?(?=^\S)", src)
    return hashlib.sha256((name + "\0" + re.sub(r"\s+", " ", stmt) + "\0" + "".join(defs)).encode()).hexdigest()


def check(s, names, where):
    """Sample the open helper theorems among `names` (a statement and its context are sampled
    once). Returns {short name: counterexample text} for the ones Lean shows false. Logs a
    `refute_sample` event."""
    if not enabled(s) or not names or s.budget.past_deadline():
        return {}
    import repair
    src = s._source()
    seen = s.__dict__.setdefault("refute_seen", {})
    todo, false = [], {}
    for n in dict.fromkeys(names):
        if n in s.theorems:
            continue
        text = repair.decl_text(s, n, src)
        if not text or not re.match(rf"^{repair.DECL_PREFIX}(?:theorem|lemma)\s", text):
            continue
        k = _key(s, n, repair.statement_of(text), src)
        if k in seen:
            if seen[k]:
                false[n] = seen[k]
            continue
        todo.append((n, k))
    if todo:
        res, info = run_probe(s, [n for n, _ in todo])
        for n, k in todo:
            r = res.get(n, {})
            seen[k] = r.get("counterexample", "") if r.get("status") == "false" else ""
            if seen[k]:
                false[n] = seen[k]
        st = s.__dict__.setdefault("refute_stats", {"probes": 0, "statements": 0, "false": 0, "survived": 0,
                                                     "unsupported": 0, "unconfirmed": 0, "ms": 0})
        st["probes"] += 1
        st["statements"] += len(todo)
        st["ms"] += info["ms"]
        for n, _ in todo:
            stt = res.get(n, {}).get("status")
            key = {"false": "false", "survived": "survived", "unconfirmed": "unconfirmed"}.get(stt, "unsupported")
            st[key] += 1
        s.log(kind="refute_sample", where=where, ms=info["ms"], stopped=info["stopped"],
              results={n: res.get(n) for n, _ in todo}, **({"error": info["error"]} if "error" in info else {}))
    return false


def summary(s, a=None):
    on = enabled(s) if a is None else getattr(a, "refute", "on") != "off"
    rec = {"enabled": on, "samples": getattr(s, "refute_samples", 0) or (SAMPLES if on else 0)}
    rec.update(s.__dict__.get("refute_stats", {}))
    return rec


def feedback(false, statements=None):
    """Prompt text naming each false statement with its counterexample."""
    lines = []
    for n, cex in false.items():
        stmt = (statements or {}).get(n)
        lines.append(f"- `{n}` is FALSE" + (f" (`{stmt}`)" if stmt else "") + f": counterexample {cex} "
                     "(Lean's kernel checked the refutation).")
    return "\n".join(lines)
