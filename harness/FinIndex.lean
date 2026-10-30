import Lean
import ProofForgeFin
/-!
# Declaration index of ProofForgeFin (harness/fin_lib.py)

Run by the harness, never by a candidate, after the library is built:
`lake env lean FinIndex.lean > index.jsonl`. Prints one JSON object per line for every module of
`ProofForgeFin` (its module doc) and every declaration it makes (theorems, definitions,
structures, inductive types, instances, tactic and other syntax), with the signature as Lean
prints it and the doc string. Compiler-generated declarations are left out.
-/

open Lean Meta Elab Command

/-- The kind recorded for a declaration, or `none` for a declaration the index leaves out. -/
def indexKind (env : Environment) (n : Name) (ci : ConstantInfo) : MetaM (Option String) := do
  if n.isInternalDetail || isPrivateName n || isAuxRecursor env n || isNoConfusion env n ||
      isMatcherCore env n then
    return none
  if let some last := n.components.getLast? then
    let s := last.toString
    if s.startsWith "eq_" || s.startsWith "proof_" || s.startsWith "match_" || s == "injEq" ||
        s == "inj" || s == "sizeOf_spec" || s.startsWith "_" then
      return none
  match ci with
  | .thmInfo _ => return some "theorem"
  | .inductInfo _ => return some (if isStructure env n then "structure" else "inductive")
  | .defnInfo d =>
    if d.type.isConstOf ``ParserDescr || d.type.isConstOf ``TrailingParserDescr then
      return some "syntax"
    if (← isInstance n) then return some "instance"
    if (env.getProjectionFnInfo? n).isSome then return none
    return some "def"
  | .opaqueInfo _ => return some "opaque"
  | .axiomInfo _ => return some "axiom"
  | _ => return none

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  for m in mods do
    if m.getRoot == `ProofForgeFin then
      let doc := (getModuleDoc? env m).bind (·[0]?) |>.map (·.doc) |>.getD ""
      IO.println (Json.compress (Json.mkObj [("kind", "module"), ("name", toString m),
        ("module", toString m), ("signature", ""), ("doc", doc)]))
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if (mods[idx.toNat]!).getRoot == `ProofForgeFin then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    let some ci := env.find? n | continue
    let some idx := env.getModuleIdxFor? n | continue
    let line ← liftTermElabM do
      let some kind ← indexKind env n ci | return none
      let sig ← try
          pure ((← PrettyPrinter.ppSignature n).fmt.pretty 160)
        catch _ => pure ((← ppExpr ci.type).pretty 160)
      let doc := (← findDocString? env n).getD ""
      return some (Json.compress (Json.mkObj [("kind", kind), ("name", toString n),
        ("module", toString mods[idx.toNat]!), ("signature", sig), ("doc", doc)]))
    if let some l := line then IO.println l
