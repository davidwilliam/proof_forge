import Lean
import Solution
/-!
# Dependency graph of a candidate (web/scripts/proof-graph.mjs, web/scripts/proof-shapes.mjs)

Run in the pinned Lean image after `lake build Solution`: `lake env lean ProofGraph.lean > graph.jsonl`.
Starting from the requirement theorems named on the first line of `roots.txt`, it follows
`ConstantInfo.getUsedConstantsAsSet` (the constants that the type and the value of a declaration
mention, as the kernel sees them) and prints one JSON object per line for every declaration it
reaches in the candidate (`Solution`) or the locked specification (modules under the root named in
`spec-root.txt`, `BalancerSwap` when that file is absent):

* compiler-generated declarations (matchers, equation lemmas, `proof_n` auxiliaries, `_private`
  names) are not nodes: the walk passes through them, so their uses count for the declaration
  that generated them;
* constructors, recursors and projections count as their inductive type or structure;
* constants of Lean's core library and of ProofForgeFin are not nodes and are not followed; the
  ProofForgeFin declarations a node mentions are listed under `lib`.

`hole` records the `sorryAx` the kernel sees in the type or value of a node (or of a generated
declaration walked through for it): `"sorry"` for an explicit `sorry`, `"error"` for one that Lean
inserted for an elaboration error (`sorryAx _ true`), `null` for none. A requirement theorem that
the environment does not contain is printed as `{"name": ..., "missing": true}`.

Nothing that the requirements do not reach is printed, so a declaration of the candidate that
no requirement uses is left out by construction.
-/

open Lean Meta Elab Command

/-- The module of `n` if its declarations become nodes: the candidate or the locked specification. -/
def tracked (spec : Name) (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  if m == `Solution || m.getRoot == spec then some m else none

/-- Whether `n` is a declaration of ProofForgeFin. -/
def fromLibrary (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!.getRoot == `ProofForgeFin
  | none => false

/-- Whether `n` is a declaration Lean generated rather than one written in the source. -/
def generated (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || isPrivateName n || isMatcherCore env n || isAuxRecursor env n ||
    isNoConfusion env n ||
    match n.components.getLast? with
    | some last =>
      let s := last.toString
      s.startsWith "eq_" || s.startsWith "proof_" || s.startsWith "match_" || s == "eq_def" ||
        s.startsWith "_" || s == "injEq" || s == "inj" || s == "sizeOf_spec" || s == "ctorIdx" ||
        s == "noConfusionType"
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

/-- `sorryAx` in the type or value of a declaration: (explicit `sorry`, inserted for an error). -/
def sorries (ci : ConstantInfo) : Bool × Bool :=
  let es := match ci with
    | .thmInfo v => #[ci.type, v.value]
    | .defnInfo v => #[ci.type, v.value]
    | .opaqueInfo v => #[ci.type, v.value]
    | _ => #[ci.type]
  let isSorry (b : Name) (x : Expr) := x.isAppOfArity ``sorryAx 2 && x.appArg!.isConstOf b
  (es.any (fun e => (e.find? (isSorry ``Bool.false)).isSome),
   es.any (fun e => (e.find? (isSorry ``Bool.true)).isSome))

structure Walk where
  seen : NameSet := {}
  out : NameSet := {}
  lib : NameSet := {}
  explicit : Bool := false
  synthetic : Bool := false

/-- The nodes `n` uses directly, walking through generated declarations. -/
partial def directDeps (spec : Name) (env : Environment) (n : Name) : StateM Walk Unit := do
  let some ci := env.find? n | return
  let (e, s) := sorries ci
  modify fun w => { w with explicit := w.explicit || e, synthetic := w.synthetic || s }
  for m in ci.getUsedConstantsAsSet do
    if fromLibrary env m then
      if let some k := nodeOf env m then modify fun w => { w with lib := w.lib.insert k }
      continue
    if (tracked spec env m).isNone then continue
    match nodeOf env m with
    | some k => modify fun w => { w with out := w.out.insert k }
    | none =>
      unless (← get).seen.contains m do
        modify fun w => { w with seen := w.seen.insert m }
        directDeps spec env m

def sorted (s : NameSet) (n : Name) : Array Name :=
  (s.toList.filter (· != n)).toArray.qsort Name.lt

def strs (ns : Array Name) : String :=
  ", ".intercalate (ns.toList.map fun d => (toJson d.toString).compress)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots := ((← IO.FS.readFile "roots.txt").replace "\n" " ").splitOn " " |>.filter (· ≠ "")
  let spec : Name ← do
    if ← System.FilePath.pathExists "spec-root.txt" then
      pure ((← IO.FS.readFile "spec-root.txt").replace "\n" "" |>.replace " " "").toName
    else pure `BalancerSwap
  let mut queue : Array Name := roots.toArray.map String.toName
  for r in queue do
    unless env.contains r do
      IO.println s!"\{\"name\":{(toJson r.toString).compress},\"missing\":true}"
  let mut done : NameSet := {}
  while h : queue.size > 0 do
    let n := queue.back
    queue := queue.pop
    if done.contains n then continue
    done := done.insert n
    let some m := tracked spec env n | continue
    let ((), w) := (directDeps spec env n).run {}
    let ds := sorted w.out n
    let lines := match ← findDeclarationRanges? n with
      | some r => s!"[{r.range.pos.line},{r.range.endPos.line}]"
      | none => "null"
    let hole := if w.synthetic then "\"error\"" else if w.explicit then "\"sorry\"" else "null"
    IO.println s!"\{\"name\":{(toJson n.toString).compress},\"kind\":\"{kindOf env n}\",\"module\":{(toJson m.toString).compress},\"lines\":{lines},\"deps\":[{strs ds}],\"hole\":{hole},\"lib\":[{strs (sorted w.lib n)}]}"
    for d in ds do
      unless done.contains d do queue := queue.push d
