import Lean
import ProofForgeFin.Sums.Eqns
/-!
# `lib_defs`: restated definitions become the library's

Specifications and candidates restate definitions the library already has: a `sumOver` over an
account list by `List.foldr`, a function update `upd f k v`, a ceiling division
`(a + b - 1) / b`, a fixed-point product `a * b / ONE`. The library's lemmas are stated over its
own definitions, so neither `exact?` nor `simp` finds them for the restated ones, although the
two are definitionally equal.

`lib_defs` finds, for every constant of the goal and of the hypotheses that is defined outside
the library and the Lean core, a ProofForgeFin definition it is definitionally equal to, and
replaces it by that definition, in the goal and in every hypothesis. The replacement is a change
of the goal up to definitional equality (like `change` or `show`), checked by the kernel; it adds
no hypothesis and no axiom. Afterwards library lemmas apply directly (`exact?`, `simp [lemma]`,
`rw [lemma]`).

A restated definition matches a library definition when, after the leading implicit and instance
arguments of both are instantiated (the library's by unification, instances by synthesis) and up
to three leading explicit arguments of the library's are supplied (a scale constant, for
example), the two are definitionally equal as functions. A sum restated by recursion on a list
or a natural number (a sum defined by pattern matching) is not definitionally equal to a fold;
`lib_defs` then rewrites each application into `List.sum` of a mapped list with the lemmas of
`ProofForgeFin.Sums.Eqns`, when the defining equations hold by `rfl` (a `simp only` rewrite,
not a change).

`lib_defs` fails when nothing changes. With `lib_defs?` it also reports the replacements.
-/

namespace ProofForgeFin.Tactic

open Lean Meta Elab Tactic

/-- The number of leading implicit, strict implicit and instance binders of a type. -/
def leadingImplicit : Expr → Nat
  | .forallE _ _ b bi => if bi.isExplicit then 0 else leadingImplicit b + 1
  | .mdata _ e => leadingImplicit e
  | _ => 0

/-- The head constant of a definition's value under its lambdas, or the empty name. -/
def valueHead : Expr → Name
  | .lam _ _ b _ => valueHead b
  | .mdata _ e => valueHead e
  | e => e.getAppFn.constName?.getD .anonymous

/-- Whether a module belongs to the library or to the Lean distribution. -/
def isLibOrCore (m : Name) : Bool :=
  [`ProofForgeFin, `Init, `Std, `Lean, `Lake].contains m.getRoot

/-- A restated definition `c`, the library definition `lib` it equals, the number of leading
arguments of `c` the replacement takes, and the replacement: a function of those arguments, in
`c`'s universe parameters. -/
structure LibBridge where
  /-- The restated definition. -/
  c : Name
  /-- The library definition. -/
  lib : Name
  /-- The leading implicit and instance arguments of `c` that the replacement consumes. -/
  nArgs : Nat
  /-- The universe parameters of `c`. -/
  levels : List Name
  /-- The replacement, `fun xs => lib ...`. -/
  repl : Expr

/-- Whether a constant is a definition of the library that a restated definition may equal: not
an instance, a projection, a compiler-generated declaration or a theorem. -/
def isLibraryDef (env : Environment) (n : Name) : MetaM Bool := do
  let some idx := env.getModuleIdxFor? n | return false
  unless (env.header.moduleNames[idx.toNat]!).getRoot == `ProofForgeFin do return false
  let some (.defnInfo _) := env.find? n | return false
  if n.isInternalDetail || (env.getProjectionFnInfo? n).isSome || isAuxRecursor env n ||
      isMatcherCore env n then return false
  return !(← isInstance n)

/-- The value heads of a library definition: the head of its value, and while that head is
itself a library definition, the head of that one's value (at most three levels). A definition
written through another (`mulDown` through `mulDiv`) is found under the head a restatement
writes out (`HDiv.hDiv`). -/
def valueHeads (env : Environment) (v : Expr) : Array Name := Id.run do
  let mut out := #[]
  let mut h := valueHead v
  for _ in [0:4] do
    if h.isAnonymous then break
    out := out.push h
    match env.find? h with
    | some (.defnInfo d) =>
      if (env.getModuleIdxFor? h).any (fun i => (env.header.moduleNames[i.toNat]!).getRoot == `ProofForgeFin) then
        h := valueHead d.value
      else break
    | _ => break
  return out

/-- The library definitions by value head (`valueHeads`), with the number of library theorems
whose statement mentions each, to try the best-supported definition first. -/
def libraryDefsByHead (env : Environment) : MetaM (Std.HashMap Name (Array Name) × Std.HashMap Name Nat) := do
  let mut libConsts : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if m.getRoot == `ProofForgeFin then libConsts := libConsts ++ d.constNames
  let mut out : Std.HashMap Name (Array Name) := {}
  let mut defs : NameSet := {}
  for n in libConsts do
    let some (.defnInfo d) := env.find? n | continue
    unless ← isLibraryDef env n do continue
    defs := defs.insert n
    for h in valueHeads env d.value do
      out := out.insert h ((out.getD h #[]).push n)
  let mut uses : Std.HashMap Name Nat := {}
  for n in libConsts do
    let some (.thmInfo t) := env.find? n | continue
    if n.isInternalDetail then continue
    for c in t.type.getUsedConstants do
      if defs.contains c then uses := uses.insert c (uses.getD c 0 + 1)
  return (out, uses)

/-- The bridge from `c` to `lib` with `extra` leading explicit arguments of `lib` left to
unification, if the two are definitionally equal. -/
def bridgeWith? (c lib : Name) (extra : Nat) : MetaM (Option LibBridge) := do
  let ci ← getConstInfo c
  let li ← getConstInfo lib
  let n := leadingImplicit ci.type
  withNewMCtxDepth do
    forallBoundedTelescope ci.type n fun xs cRest => do
      let lus ← li.levelParams.mapM fun _ => mkFreshLevelMVar
      let lty := li.type.instantiateLevelParams li.levelParams lus
      let (ms, bis, lRest) ← forallMetaBoundedTelescope lty (leadingImplicit lty + extra)
      unless ms.size == leadingImplicit lty + extra do return none
      unless ← isDefEq cRest lRest do return none
      for mv in ms, bi in bis do
        if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
          match ← trySynthInstance (← inferType mv) with
          | .some inst => unless ← isDefEq mv inst do return none
          | _ => return none
      let lhs := mkAppN (mkConst c (ci.levelParams.map mkLevelParam)) xs
      let rhs := mkAppN (mkConst lib lus) ms
      unless ← withTransparency .default (isDefEq lhs rhs) do return none
      let rhs ← instantiateMVars rhs
      if rhs.hasMVar || rhs.hasLevelMVar then return none
      return some { c, lib, nArgs := n, levels := ci.levelParams, repl := ← mkLambdaFVars xs rhs }

/-- The first library definition among `cands` that `c` equals, trying no, one, two and three
supplied explicit arguments. -/
def bridgeFor? (c : Name) (cands : Array Name) : MetaM (Option LibBridge) := do
  for extra in [0, 1, 2, 3] do
    for l in cands do
      try
        if let some b ← bridgeWith? c l extra then return some b
      catch _ => pure ()
  return none

/-- `e` with every application of a bridged constant, with at least the arguments its
replacement takes, replaced; one pass (the arguments of a replaced application are not
visited). -/
def replaceOnce (bs : Array LibBridge) (e : Expr) : Expr :=
  e.replace fun t =>
    match t.getAppFn with
    | .const n us =>
      match bs.find? (·.c == n) with
      | some b =>
        if t.getAppNumArgs ≥ b.nArgs then
          let args := t.getAppArgs
          let r := (b.repl.instantiateLevelParams b.levels us).beta (args.extract 0 b.nArgs)
          some (mkAppN r (args.extract b.nArgs args.size))
        else none
      | none => none
    | _ => none

/-- `replaceOnce` until nothing changes, at most eight passes. -/
def replaceAll (bs : Array LibBridge) (e : Expr) : Expr := Id.run do
  let mut e := e
  for _ in [0:8] do
    let e' := replaceOnce bs e
    if e' == e then break
    e := e'
  return e

/-- The constants of the goal and the hypotheses that are defined outside the library and the
Lean distribution and are not theorems. -/
def restatedConsts (g : MVarId) : MetaM (Array Name) := g.withContext do
  let env ← getEnv
  let mut es := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    unless d.isImplementationDetail do es := es.push (← instantiateMVars d.type)
  let mut seen : NameSet := {}
  let mut out := #[]
  for e in es do
    for c in e.getUsedConstants do
      if seen.contains c then continue
      seen := seen.insert c
      if let some idx := env.getModuleIdxFor? c then
        if isLibOrCore env.header.moduleNames[idx.toNat]! then continue
      if c.isInternalDetail || (env.getProjectionFnInfo? c).isSome || isAuxRecursor env c ||
          isMatcherCore env c then continue
      if ← isInstance c then continue
      if let some (.defnInfo _) := env.find? c then out := out.push c
  return out

/-- The lemmas of `ProofForgeFin.Sums.Eqns` that identify a recursive sum, by the type of its
recursion argument (`List` or `Nat`) and of its value (`Nat` or `Int`). -/
def sumEqnLemmas : List (Name × Name × Name) :=
  [(``List, ``Nat, ``ProofForgeFin.Sums.eq_sum_map_of_eqns),
   (``List, ``Int, ``ProofForgeFin.Sums.eq_sum_map_of_eqns_int),
   (``Nat, ``Nat, ``ProofForgeFin.Sums.eq_sum_range_of_eqns),
   (``Nat, ``Int, ``ProofForgeFin.Sums.eq_sum_range_of_eqns_int)]

/-- For an application `c args` of a restated definition whose first explicit argument is a list
or a natural number and whose value is a `Nat` or an `Int`: the equation `∀ x, F x = sum` with
`F := fun x => c args` (the first explicit argument abstracted), proved by the matching
`ProofForgeFin.Sums` lemma when `F [] = 0` and `F (a :: l) = f a + F l` (or `F 0 = 0` and
`F (n + 1) = F n + f n`) hold by `rfl` for some `f`. -/
def sumEqnFor? (e : Expr) : TacticM (Option Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .const c _ := fn | return none
  let ci ← getConstInfo c
  let n := leadingImplicit ci.type
  if args.size ≤ n then return none
  let x := args[n]!
  let xTy ← inferType x
  let some argHead := (← whnf xTy).getAppFn.constName? | return none
  let some valHead := (← whnf (← inferType e)).constName? | return none
  let some (_, _, lem) := sumEqnLemmas.find? fun (a, v, _) => a == argHead && v == valHead | return none
  let F ← withLocalDeclD `x xTy fun y => mkLambdaFVars #[y] (mkAppN fn (args.set! n y))
  let FStx ← Term.exprToSyntax F
  let stx ← if argHead == ``List then
      `($(mkIdent lem) (F := $FStx) _ rfl (fun _ _ => rfl))
    else `($(mkIdent lem) (F := $FStx) _ rfl (fun _ => rfl))
  try
    let p ← Term.withoutErrToSorry <| Term.elabTermAndSynthesize stx none
    let p ← instantiateMVars p
    if p.hasMVar then return none
    let ty ← Core.betaReduce (← instantiateMVars (← inferType p))
    return some (← mkExpectedTypeHint p ty)
  catch _ => return none

/-- The equations (`sumEqnFor?`) of every application of a constant of `cs` in the goal and the
hypotheses that mentions no bound variable. -/
def sumEqns (g : MVarId) (cs : NameSet) : TacticM (Array Expr) := g.withContext do
  let mut es := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    unless d.isImplementationDetail do es := es.push (← instantiateMVars d.type)
  let mut apps : Array Expr := #[]
  for e in es do
    let r ← IO.mkRef (#[] : Array Expr)
    e.forEach fun t => do
      if !t.hasLooseBVars && t.isApp && (t.getAppFn.constName?.any cs.contains) then r.modify (·.push t)
    for t in ← r.get do
      unless apps.contains t do apps := apps.push t
  let mut out := #[]
  let mut seenF : Array Expr := #[]
  for t in apps do
    if let some p ← sumEqnFor? t then
      let ty ← inferType p
      unless seenF.contains ty do
        seenF := seenF.push ty
        out := out.push p
  return out

/-- Rewrite the main goal with the bridges of its restated definitions (definitional
replacements, then recursive sums by their equations); returns the definitional bridges and the
constants rewritten by equations. -/
def libDefsCore : TacticM (Array LibBridge × Array Name) := withMainContext do
  let g ← getMainGoal
  let (byHead, uses) ← libraryDefsByHead (← getEnv)
  let mut bs := #[]
  let restated ← restatedConsts g
  for c in restated do
    let some (.defnInfo d) := (← getEnv).find? c | continue
    let cands := (byHead.getD (valueHead d.value) #[]).qsort fun a b =>
      let ua := uses.getD a 0
      let ub := uses.getD b 0
      ua > ub || (ua == ub && a.toString.length < b.toString.length)
    if cands.isEmpty then continue
    if let some b ← bridgeFor? c cands then bs := bs.push b
  let mut g := g
  let t ← instantiateMVars (← g.getType)
  let t' := replaceAll bs t
  if t' != t then g ← g.replaceTargetDefEq t'
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' := replaceAll bs ty
    if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
  replaceMainGoal [g]
  -- Recursive sums: rewritten with their equations.
  let rest := restated.filter fun c => !bs.any (·.c == c)
  let eqns ← sumEqns g (rest.foldl (·.insert ·) {})
  let mut byEqns : Array Name := #[]
  if !eqns.isEmpty then
    let hs ← eqns.mapM fun p => do
      let s ← Term.exprToSyntax p
      `(Lean.Parser.Tactic.simpLemma| $s:term)
    try
      evalTactic (← `(tactic| simp only [$hs,*, List.map_id'] at *))
      for p in eqns do
        if let some c := (← inferType p).getForallBody.eq?.map (·.2.1.getAppFn.constName?) |>.join then
          byEqns := byEqns.push c
    catch _ => pure ()
  if bs.isEmpty && byEqns.isEmpty then
    throwError "lib_defs: no definition of the goal or the hypotheses equals a ProofForgeFin definition \
      or is a sum by recursion"
  return (bs, byEqns)

/-- `lib_defs` replaces every definition of the goal and the hypotheses that is defined outside
the library and is definitionally equal to a ProofForgeFin definition (a restated `sumOver`,
`upd`, `ceilDiv`, `a * b / ONE`...) by the library definition, and rewrites a sum restated by
recursion on a list or a natural number into `List.sum` of a mapped list, so that library
lemmas apply. `lib_defs?` also reports the replacements. -/
syntax (name := libDefs) "lib_defs" : tactic

@[inherit_doc libDefs]
syntax (name := libDefsQ) "lib_defs?" : tactic

elab_rules : tactic
  | `(tactic| lib_defs) => discard libDefsCore
  | `(tactic| lib_defs?) => do
    let (bs, byEqns) ← libDefsCore
    logInfo m!"lib_defs: {bs.toList.map fun b => m!"{b.c} ↦ {b.lib}"}; by equations: {byEqns.toList}"

end ProofForgeFin.Tactic
