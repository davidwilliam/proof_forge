import Lean
import Solution
/-!
# Dependency graph of a verified candidate (web/scripts/proof-graph.mjs)

Run by `web/scripts/proof-graph.mjs` in the pinned Lean image after `lake build Solution`:
`lake env lean ProofGraph.lean > graph.jsonl`. Starting from the requirement theorems named on
the first line of `roots.txt`, it follows `ConstantInfo.getUsedConstantsAsSet` (the constants
that the type and the value of a declaration mention, as the kernel sees them) and prints one
JSON object per line for every declaration it reaches in the candidate (`Solution`) or the
locked specification (modules under `BalancerSwap`):

* compiler-generated declarations (matchers, equation lemmas, `proof_n` auxiliaries, `_private`
  names) are not nodes: the walk passes through them, so their uses count for the declaration
  that generated them;
* constructors, recursors and projections count as their inductive type or structure;
* constants of Lean's core library are not nodes and are not followed.

Nothing that the requirements do not reach is printed, so a declaration of the candidate that
no requirement uses is left out by construction.
-/

open Lean Meta Elab Command

/-- Modules whose declarations become nodes. -/
def tracked (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  if m == `Solution || m.getRoot == `BalancerSwap then some m else none

/-- Whether `n` is a declaration Lean generated rather than one written in the source. -/
def generated (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || isPrivateName n || isMatcherCore env n || isAuxRecursor env n ||
    isNoConfusion env n ||
    match n.components.getLast? with
    | some last =>
      let s := last.toString
      s.startsWith "eq_" || s.startsWith "proof_" || s.startsWith "match_" || s == "eq_def" ||
        s.startsWith "_" || s == "injEq" || s == "inj" || s == "sizeOf_spec" || s == "ctorIdx"
    | none => false

/-- The node a constant counts as: itself, its inductive type for a constructor or recursor,
its structure for a projection, or `none` for a generated declaration (walked through). -/
def nodeOf (env : Environment) (n : Name) : Option Name :=
  match env.find? n with
  | some (.ctorInfo v) => some v.induct
  | some (.recInfo _) => some n.getPrefix
  | _ =>
    if let some info := env.getProjectionFnInfo? n then
      match env.find? info.ctorName with
      | some (.ctorInfo v) => some v.induct
      | _ => some n
    else if generated env n then none
    else some n

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.thmInfo _) => "theorem"
  | some (.inductInfo _) => if isStructure env n then "structure" else "inductive"
  | some (.defnInfo _) => "def"
  | some (.opaqueInfo _) => "opaque"
  | some (.axiomInfo _) => "axiom"
  | _ => "other"

/-- The nodes `n` uses directly, walking through generated declarations. -/
partial def directDeps (env : Environment) (n : Name) : StateM (NameSet × NameSet) Unit := do
  let some ci := env.find? n | return
  for m in ci.getUsedConstantsAsSet do
    if (tracked env m).isNone then continue
    match nodeOf env m with
    | some k => modify fun (seen, out) => (seen, out.insert k)
    | none =>
      let (seen, _) ← get
      unless seen.contains m do
        modify fun (seen, out) => (seen.insert m, out)
        directDeps env m

def deps (env : Environment) (n : Name) : Array Name :=
  let ((), (_, out)) := (directDeps env n).run ({}, {})
  (out.toList.filter (· != n)).toArray.qsort Name.lt

#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots := ((← IO.FS.readFile "roots.txt").replace "\n" " ").splitOn " " |>.filter (· ≠ "")
  let mut queue : Array Name := roots.toArray.map String.toName
  let mut done : NameSet := {}
  while h : queue.size > 0 do
    let n := queue.back
    queue := queue.pop
    if done.contains n then continue
    done := done.insert n
    let some m := tracked env n | continue
    let ds := deps env n
    let lines := match ← findDeclarationRanges? n with
      | some r => s!"[{r.range.pos.line},{r.range.endPos.line}]"
      | none => "null"
    let depsJson := ", ".intercalate (ds.toList.map fun d => (toJson d.toString).compress)
    IO.println s!"\{\"name\":{(toJson n.toString).compress},\"kind\":\"{kindOf env n}\",\"module\":{(toJson m.toString).compress},\"lines\":{lines},\"deps\":[{depsJson}]}"
    for d in ds do
      unless done.contains d do queue := queue.push d
