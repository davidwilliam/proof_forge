import Lean
import ProofForgeFin
/-!
# Declaration index of ProofForgeFin (harness/fin_lib.py)

Run by the harness, never by a candidate, after the library is built:
`lake env lean FinIndex.lean > index.jsonl`. Prints one JSON object per line for every module of
`ProofForgeFin` (its module doc) and every declaration it makes (theorems, definitions,
structures, inductive types, instances, tactic and other syntax), with the signature as Lean
prints it and the doc string. Compiler-generated declarations are left out. Each theorem also
records the shape of its conclusion (`concl`: the relation at its head, the head constants of the
two sides and the constants the conclusion mentions), which the goal-aware ranking of
harness/fin_lib.py compares with a goal.
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

/-- The relations whose two sides the conclusion shape records, with the argument positions of
the sides. -/
def relSides : Name → Option (Nat × Nat)
  | ``Eq => some (1, 2)
  | ``Ne => some (1, 2)
  | ``HEq => some (1, 3)
  | ``LE.le => some (2, 3)
  | ``LT.lt => some (2, 3)
  | ``GE.ge => some (2, 3)
  | ``GT.gt => some (2, 3)
  | ``Iff => some (0, 1)
  | ``Dvd.dvd => some (2, 3)
  | _ => none

/-- The constant at the head of an application, or the empty name. -/
def headConst (e : Expr) : Name :=
  e.consumeMData.getAppFn.constName?.getD .anonymous

/-- The shape of a theorem's conclusion (the type after its binders and hypotheses): the head
relation or constant, the head constants of the two sides of a relation, and the constants the
conclusion mentions other than instances. -/
def conclShape (ty : Expr) : MetaM Json :=
  forallTelescope ty fun _ body => do
    let body := body.consumeMData
    let rel := headConst body
    let args := body.getAppArgs
    let (lhs, rhs) := match relSides rel with
      | some (i, j) => (headConst (args.getD i (.sort .zero)), headConst (args.getD j (.sort .zero)))
      | none => (Name.anonymous, Name.anonymous)
    let mut consts : Array String := #[]
    for c in body.getUsedConstants do
      unless (← isInstance c) || c.isInternalDetail do
        consts := consts.push (toString c)
    let str (n : Name) : String := if n.isAnonymous then "" else toString n
    return Json.mkObj [("rel", str rel), ("lhs", str lhs), ("rhs", str rhs), ("consts", toJson consts)]

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
      let shape ← if kind == "theorem" then
          try conclShape ci.type catch _ => pure Json.null
        else pure Json.null
      return some (Json.compress (Json.mkObj [("kind", kind), ("name", toString n),
        ("module", toString mods[idx.toNat]!), ("signature", sig), ("doc", doc), ("concl", shape)]))
    if let some l := line then IO.println l
