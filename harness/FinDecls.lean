import Lean
import ProofForgeFin
import ProofForgeFinDemo
/-!
# Declarations of ProofForgeFin and its demonstrations (harness/fin_kernels.py)

Run by the harness, never by a candidate, after the library and its demonstrations are built:
`lake env lean FinDecls.lean > decls.jsonl`. Prints one JSON object per line for every constant
declared in a module of `ProofForgeFin` or `ProofForgeFinDemo`, compiler-generated ones included:
its name, module, kind, whether `leanexport` can be given the name on its command line (the name
reads back from its printed form), the library constants its type and value use, and whether it
is or reaches an `unsafe` or `partial` constant. The kernel checker exports the names that read
back; every other constant is in the export because one of them uses it, or is tactic state that
no proof term can mention.
-/

open Lean Elab Command

/-- The constant kinds as the kernel sees them. -/
def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- The roots of the audited modules. -/
def libRoots : List Name := [`ProofForgeFin, `ProofForgeFinDemo]

/-- Whether `n` or a constant it depends on, transitively, is `unsafe` or `partial` (in this
library, the `_unsafe_rec` definitions Lean generates to compile recursive definitions); no safe
constant, and so no proof term, mentions one. Memoized over the whole environment; the
recursion follows the dependency graph, which is acyclic through safe constants. -/
partial def reachesUnsafe (env : Environment) (n : Name) : StateM (Std.HashMap Name Bool) Bool := do
  if let some b := (← get)[n]? then return b
  -- Marked first, so a cycle through unsafe or partial constants ends.
  modify (·.insert n false)
  let some ci := env.find? n | return false
  let mut bad := ci.isUnsafe || ci.isPartial
  unless bad do
    for m in ci.getUsedConstantsAsSet do
      if ← reachesUnsafe env m then
        bad := true
        break
  modify (·.insert n bad)
  return bad

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let inLib (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => libRoots.contains (mods[idx.toNat]!).getRoot
    | none => false
  let mut memo : Std.HashMap Name Bool := {}
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless libRoots.contains m.getRoot do continue
    let exportable := Syntax.decodeNameLit ("`" ++ n.toString) == some n
    let uses := ci.getUsedConstantsAsSet.toList.filter inLib |>.map toString
    let (reaches, memo') := (reachesUnsafe env n).run memo
    memo := memo'
    IO.println (Json.compress (Json.mkObj [("name", toString n), ("module", toString m),
      ("kind", kindOf ci), ("exportable", exportable), ("internal", n.isInternalDetail),
      ("unsafe", reaches), ("uses", toJson uses)]))
