import Lean
/-!
# The goals library lemmas are used on (harness/fin_retrieval.py)

Run by the harness, never by a candidate, compiled as an executable (`fingoals`, a `lean_exe`
target the harness adds; running it with `lean --run` loads a second Lean environment and needs
more memory than the container has): `lake env fingoals FILE` elaborates one Lean file (its
imports must be built; one file per process, since a process imports modules once) with info
trees and prints one JSON object per line
for every use of a ProofForgeFin theorem in a tactic proof: the theorem, the file, and the goal
the tactic that names it was run on (the main goal before the innermost enclosing tactic, as
Lean displays it, hypotheses included). A use outside any tactic (a term-mode proof) is printed
with an empty goal. The retrieval evaluation ranks library theorems for these goals.
-/

open Lean Elab Meta

/-- A use: the theorem and, once the enclosing tactic is known, the goal it was used on. -/
structure Use where
  /-- The library theorem. -/
  lemma : Name
  /-- The goal, as displayed, if a tactic encloses the use. -/
  goal : Option String
  /-- The declaration whose proof uses it. -/
  decl : Name := .anonymous

/-- Whether `n` is a theorem of the library. -/
def isLibTheorem (env : Environment) (n : Name) : Bool :=
  (`ProofForgeFin).isPrefixOf n && !n.isInternalDetail &&
    match env.find? n with
    | some (.thmInfo _) => true
    | _ => false

/-- The uses below a node, the innermost tactic giving each its goal. -/
def usesOf (env : Environment) (ctx : ContextInfo) (i : Info) (children : List Use) : IO (List Use) := do
  match i with
  | .ofTermInfo ti =>
    match ti.expr.consumeMData.getAppFn with
    | .const n _ =>
      if isLibTheorem env n then return { lemma := n, goal := none, decl := ctx.parentDecl?.getD .anonymous } :: children
      else return children
    | _ => return children
  | .ofTacticInfo ti =>
    if children.all (·.goal.isSome) then return children
    let goal ← match ti.goalsBefore with
      | g :: _ =>
        let ctx' := { ctx with mctx := ti.mctxBefore }
        match ti.mctxBefore.findDecl? g with
        | some d =>
          try
            let f ← ctx'.runMetaM d.lctx (Meta.ppGoal g)
            pure (some (toString f))
          catch _ => pure none
        | none => pure none
      | [] => pure none
    return children.map fun u => if u.goal.isSome then u else { u with goal := goal }
  | _ => return children

/-- Elaborate one file and print its uses. -/
def processFile (path : String) : IO Unit := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  for m in messages.toList do
    IO.eprintln s!"header: {← m.toString}"
  let cmdState := Command.mkState env messages {}
  let s ← IO.processCommands inputCtx parserState { cmdState with infoState := { enabled := true } }
  let env := s.commandState.env
  IO.eprintln s!"{path}: {s.commandState.infoState.trees.size} info trees"
  for t in s.commandState.infoState.trees do
    let uses ← t.collectNodesBottomUpM (m := IO) fun ctx i _ cs => usesOf env ctx i cs
    for u in uses do
      IO.println (Json.compress (Json.mkObj [("file", path), ("decl", toString u.decl),
        ("lemma", toString u.lemma), ("goal", u.goal.getD "")]))

/-- Every file given on the command line. -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  -- The library registers simp sets and syntax with initializers, which importing must run.
  unsafe enableInitializersExecution
  for p in args do
    try processFile p
    catch e => IO.eprintln s!"{p}: {e}"
