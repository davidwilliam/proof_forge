import ProofForgeFin.Tactic.Struct
/-!
# `run_induction`

Requirements over every sequence of operations are proved by an induction over the list of
operations, and the induction step is the same for every requirement: from a state satisfying
the invariant, every operation leads to a state satisfying it. `ProofForgeFin.Seq` proves the
induction principles once; `run_induction` applies the right one to the goal and leaves one goal
per constructor of the operation type, with the step function unfolded, so that what remains is
the per-operation lemmas.

* `run_induction`: for a goal `G (Seq.run step s ops)`, the invariant is `fun x => G x` (every
  occurrence of the run abstracted); `Seq.run_invariant`. Goals: `init : G s`, and for every
  constructor `c` of the operation type a goal `G (step x (c ...))` with `ih : G x`.
* `run_induction using J`: a stronger invariant `J`; `Seq.run_invariant_of_imp`. Goals: `imp`
  (`∀ x, J x → G x`), `init : J s`, and one goal per constructor with `ih : J x`.
* For a goal `P (Seq.run step s ops) ≤ P s + (ops.map f).sum` the accumulated bound
  `Seq.run_le_add_sum` is used instead (with `using J`, `Seq.run_le_add_sum_of_inv`, which adds the
  goals of the invariant). Goals per constructor: `P (step x (c ...)) ≤ P x + f (c ...)`.
* `run_induction total Inv`: for a goal mentioning `Seq.accum next f g ops`, the ghost
  invariant `Inv : γ → Nat → σ → Prop` of `Seq.run_total_invariant` with total `0` at the start.
  The main goal receives `hrun : Inv (Seq.run next g ops) (Seq.accum next f g ops)
  (Seq.run step s ops)`; goals `init : Inv g 0 s` and, per constructor,
  `Inv (next g (c ...)) (e + f g (c ...)) (step x (c ...))` with `ih : Inv g e x`.

The goal may state the run with the task's own definitions: `run_induction [run]` rewrites the
goal with the given lemmas and definitions first, and `List.foldl step s ops` is read as
`Seq.run step s ops`. `run_induction ... with [defs]` simplifies the per-constructor goals, their
`ih` and the `init` goal with `struct_simp [defs]`. The head constant of the step function (and,
in the total form, of `next` and `f`) is unfolded too, unless it is erased as `with [-c]`, which
keeps the step folded so that per-operation lemmas stated about it apply. The operation is split
with `cases` when its type is inductive; otherwise one step goal remains. Goals that `rfl`, an
assumption, a contradiction or `omega` close are dropped. The tactic fails with a message naming
it when the goal has no run.
-/

namespace ProofForgeFin.Tactic

open Lean Elab Tactic Meta Parser.Tactic

/-- The first subterm `Seq.run step s ops` of `e` whose step function is not `avoid`. -/
def findRun? (e : Expr) (avoid : Option Expr := none) : Option Expr :=
  e.find? fun t =>
    t.isAppOfArity ``Seq.run 5 &&
      match avoid with
      | some a => t.getArg! 2 != a
      | none => true

/-- The first subterm `Seq.accum next f g ops` of `e`. -/
def findAccum? (e : Expr) : Option Expr :=
  e.find? fun t => t.isAppOfArity ``Seq.accum 6

/-- A local name based on `n` that is not used in the current context. -/
def freshName (n : Name) : MetaM Name := return (← getLCtx).getUnusedName n

/-- The simp arguments of the per-constructor goals: `post`, and the head constants of the
given functions to unfold, except a head constant `c` erased in `post` as `-c` (the erasure is
then dropped from the arguments, since `c` is not otherwise in the simp set). -/
def headUnfoldArgs (fs : List Expr) (post : Array Syntax) : TacticM (Array Syntax) := do
  let heads : Array Name := (fs.filterMap fun f => f.getAppFn.constName?).toArray
  let mut erased : Array Name := #[]
  let mut out : Array Syntax := #[]
  for a in post do
    if a.getKind == ``simpErase && a[1].isIdent then
      let c? ← try some <$> realizeGlobalConstNoOverload a[1] catch _ => pure none
      if let some c := c? then
        if heads.contains c then
          erased := erased.push c
          continue
    out := out.push a
  for c in heads do
    if c == ``Seq.skip || erased.contains c then continue
    if let some (.defnInfo _) := (← getEnv).find? c then
      let s ← `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident)
      out := out.push s.raw
  return out

/-- Rename the inaccessible locals of `g` that are not in `before` (the fields `cases`
introduced) to accessible names. -/
def nameNewLocals (g : MVarId) (before : LocalContext) : MetaM MVarId := do
  let mut g := g
  let decls := (← g.getDecl).lctx.decls.toArray.filterMap id
  for d in decls do
    if d.isImplementationDetail || before.contains d.fvarId then continue
    unless d.userName.hasMacroScopes do continue
    let n := (← g.getDecl).lctx.getUnusedName d.userName.eraseMacroScopes
    g ← g.rename d.fvarId n
  return g

/-- Close `g` if a cheap closer does; otherwise return it. -/
def keepUnlessCheap (g : MVarId) : TacticM (List MVarId) := do
  setGoals [g]
  if ← tryCloseCheap then return [] else return [g]

/-- Simplify `g` with `struct_simp` and `unfold`, then drop it if a cheap closer closes it. -/
def simpAndKeep (g : MVarId) (unfold : Array Syntax) : TacticM (List MVarId) := do
  setGoals [g]
  let _ ← g.withContext (runStructSimp unfold none)
  let mut out := []
  for g' in (← getGoals) do
    out := out ++ (← keepUnlessCheap g')
  return out

/-- Introduce `names` in `g`, split the operation (the local at position `opIdx` of the
introduced ones) into its constructors, tag each case `pre ++ constructor` and simplify it with
`struct_simp` and `unfold`. -/
def introAndSplit (g : MVarId) (names : List Name) (opIdx : Nat) (pre : String)
    (unfold : Array Syntax) : TacticM (List MVarId) := do
  let names ← g.withContext (names.mapM fun n => (freshName n : MetaM Name))
  let (fvars, g) ← g.introNP names.length
  let g ← (fvars.zip names.toArray).foldlM (fun g (f, n) => g.rename f n) g
  let before := (← g.getDecl).lctx
  let cases ← try
      some <$> g.cases fvars[opIdx]!
    catch _ => pure none
  let goals : Array (Name × MVarId) ← match cases with
    | some cs => cs.mapM fun c => do
        return (c.ctorName.getD .anonymous, ← nameNewLocals c.mvarId before)
    | none => pure #[(Name.anonymous, g)]
  let mut out := []
  for (c, g) in goals do
    let tag := if c.isAnonymous then pre else pre ++ c.getString!
    g.setTag (Name.mkSimple (if tag.isEmpty then "step" else tag))
    setGoals [g]
    let hyps ← g.withContext do
      let mut hs := #[]
      for n in names do
        if let some d := (← getLCtx).findFromUserName? n then
          if ← Meta.isProp d.type then hs := hs.push (mkIdent n)
      pure hs
    let loc ← if hyps.isEmpty then pure none
      else
        let hs : Array Term := hyps.map (⟨·.raw⟩)
        some <$> `(Lean.Parser.Tactic.location| at $hs* ⊢)
    let _ ← g.withContext (runStructSimp unfold loc)
    for g' in (← getGoals) do
      out := out ++ (← keepUnlessCheap g')
  return out

/-- Rewrite the main goal with `args` and `foldl_eq_run` (to expose `Seq.run`); no error when
nothing changes. -/
def exposeRun (args : Array Syntax) : TacticM Unit := do
  let base ← `(Lean.Parser.Tactic.simpLemma| ProofForgeFin.foldl_eq_run)
  let all : Array Syntax := #[base.raw] ++ args
  let lemmas : Syntax.TSepArray [``simpStar, ``simpErase, ``simpLemma] "," :=
    Syntax.TSepArray.ofElems (all.map (⟨·⟩))
  try evalTactic (← `(tactic| simp only [$lemmas,*])) catch _ => pure ()

/-- `∀ x op, H x → C x op`, with binder names `x`, `op`, `ih`; `hyp` and `concl` build the body
from the bound variables. -/
def mkStepType (σ α : Expr) (hyp : Option (Expr → MetaM Expr))
    (concl : Expr → Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `x σ fun x => withLocalDeclD `op α fun a => do
    let c ← concl x a
    match hyp with
    | some h => do
      let hx ← h x
      withLocalDeclD `ih hx fun ih => mkForallFVars #[x, a, ih] c
    | none => mkForallFVars #[x, a] c

/-- `true` when `e` is `a + List.sum (List.map f ops)` for the given `ops`; returns `a` and `f`. -/
def matchSumBound? (e ops : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  let_expr HAdd.hAdd _ _ _ _ a t := e | return none
  let_expr List.sum _ _ _ l := t | return none
  let_expr List.map _ _ f l' := l | return none
  unless ← isDefEq l' ops do return none
  return some (a, f)

/-- The constructor goals of `run_induction`. Error messages name the tactic. -/
def runInductionCore (using? : Option Syntax) (pre : Array Syntax) (post : Array Syntax) :
    TacticM Unit := do
  exposeRun pre
  let g ← getMainGoal
  g.withContext do
  let target ← instantiateMVars (← g.getType)
  let some R := findRun? target
    | throwError "run_induction: no `Seq.run step s ops` (or `List.foldl step s ops`) in the \
        goal; pass the task's definition of the run, or a lemma that rewrites it to `Seq.run`, \
        as `run_induction [run]`"
  let args := R.getAppArgs
  let σ := args[0]!; let α := args[1]!; let step := args[2]!; let s := args[3]!; let ops := args[4]!
  let unfold ← headUnfoldArgs [step] post
  let tgtAbs ← kabstract target R
  let J? ← using?.mapM fun j => do
    let J ← elabTermEnsuringType j (some (← mkArrow σ (mkSort .zero)))
    instantiateMVars J
  -- accumulated bound
  if target.isAppOfArity ``LE.le 4 then
    let lhs := target.getArg! 2
    let rhs := target.getArg! 3
    if (lhs.find? (· == R)).isSome then
      if let some (a, f) ← matchSumBound? rhs ops then
        let lhsAbs ← kabstract lhs R
        let P := mkLambda `x .default σ lhsAbs
        if ← isDefEq a (P.beta #[s]) then
          let hType ← mkStepType σ α (J?.map fun J x => pure (J.beta #[x])) fun x op => do
            mkAppM ``LE.le #[P.beta #[mkApp2 step x op],
              ← mkAppM ``HAdd.hAdd #[P.beta #[x], f.beta #[op]]]
          let h ← mkFreshExprSyntheticOpaqueMVar hType
          match J? with
          | none =>
            let pf ← mkAppOptM ``Seq.run_le_add_sum #[none, none, step, P, f, h, s, ops]
            unless ← isDefEq (← inferType pf) target do
              throwError "run_induction: the accumulated bound does not match the goal"
            g.assign pf
            let gs ← introAndSplit h.mvarId! [`x, `op] 1 "" unfold
            setGoals gs
          | some J =>
            let hsType ← mkStepType σ α (some fun x => pure (J.beta #[x]))
              fun x op => pure (J.beta #[mkApp2 step x op])
            let hs ← mkFreshExprSyntheticOpaqueMVar hsType
            let h0 ← mkFreshExprSyntheticOpaqueMVar (J.beta #[s]) (tag := `init)
            let pf ← mkAppOptM ``Seq.run_le_add_sum_of_inv
              #[none, none, step, J, hs, P, f, h, s, h0, ops]
            unless ← isDefEq (← inferType pf) target do
              throwError "run_induction: the accumulated bound does not match the goal"
            g.assign pf
            let gi ← simpAndKeep h0.mvarId! unfold
            let gs ← introAndSplit hs.mvarId! [`x, `op, `ih] 1 "inv_" unfold
            let gb ← introAndSplit h.mvarId! [`x, `op, `ih] 1 "" unfold
            setGoals (gi ++ gs ++ gb)
          return
  -- invariant
  let I := mkLambda `x .default σ tgtAbs
  match J? with
  | none =>
    let hsType ← mkStepType σ α (some fun x => pure (I.beta #[x]))
      fun x op => pure (I.beta #[mkApp2 step x op])
    let hs ← mkFreshExprSyntheticOpaqueMVar hsType
    let h0 ← mkFreshExprSyntheticOpaqueMVar (I.beta #[s]) (tag := `init)
    let pf ← mkAppOptM ``Seq.run_invariant #[none, none, step, I, hs, s, h0, ops]
    unless ← isDefEq (← inferType pf) target do
      throwError "run_induction: the invariant built from the goal does not match it"
    g.assign pf
    let gi ← simpAndKeep h0.mvarId! unfold
    let gs ← introAndSplit hs.mvarId! [`x, `op, `ih] 1 "" unfold
    setGoals (gi ++ gs)
  | some J =>
    let himpType ← withLocalDeclD `x σ fun x => withLocalDeclD `h (J.beta #[x]) fun h => do
      mkForallFVars #[x, h] (I.beta #[x])
    let himp ← mkFreshExprSyntheticOpaqueMVar himpType (tag := `imp)
    let hsType ← mkStepType σ α (some fun x => pure (J.beta #[x]))
      fun x op => pure (J.beta #[mkApp2 step x op])
    let hs ← mkFreshExprSyntheticOpaqueMVar hsType
    let h0 ← mkFreshExprSyntheticOpaqueMVar (J.beta #[s]) (tag := `init)
    let pf ← mkAppOptM ``Seq.run_invariant_of_imp #[none, none, step, I, J, himp, hs, s, h0, ops]
    unless ← isDefEq (← inferType pf) target do
      throwError "run_induction: the invariant `using` term does not match the goal"
    g.assign pf
    let gimp ← do
      let (_, gi) ← himp.mvarId!.introNP 2
      keepUnlessCheap gi
    let gi ← simpAndKeep h0.mvarId! unfold
    let gs ← introAndSplit hs.mvarId! [`x, `op, `ih] 1 "" unfold
    setGoals (gimp ++ gi ++ gs)

/-- The ghost-total form of `run_induction` (`Seq.run_total_invariant`). -/
def runInductionTotal (inv : Syntax) (pre : Array Syntax) (post : Array Syntax) :
    TacticM Unit := do
  exposeRun pre
  let g ← getMainGoal
  g.withContext do
  let target ← instantiateMVars (← g.getType)
  let some A := findAccum? target
    | throwError "run_induction total: no `Seq.accum next f g ops` in the goal; rewrite the \
        task's total to `Seq.accum` first (pass the lemma as `run_induction total Inv [lemma]`)"
  let aargs := A.getAppArgs
  let α := aargs[0]!; let γ := aargs[1]!; let next := aargs[2]!; let f := aargs[3]!
  let g0 := aargs[4]!; let ops := aargs[5]!
  let some R := findRun? target (avoid := some next)
    | throwError "run_induction total: no `Seq.run step s ops` of the state in the goal"
  let rargs := R.getAppArgs
  let σ := rargs[0]!; let step := rargs[2]!; let s := rargs[3]!
  let invType ← mkArrow γ (← mkArrow (mkConst ``Nat) (← mkArrow σ (mkSort .zero)))
  let Inv ← instantiateMVars (← elabTermEnsuringType inv (some invType))
  let unfold ← headUnfoldArgs [step, next, f] post
  let hType ← withLocalDeclD `g γ fun gv => withLocalDeclD `e (mkConst ``Nat) fun e =>
    withLocalDeclD `x σ fun x => withLocalDeclD `op α fun a => do
      let ih := Inv.beta #[gv, e, x]
      withLocalDeclD `ih ih fun ihv => do
        let c := Inv.beta #[mkApp2 next gv a, ← mkAppM ``HAdd.hAdd #[e, mkApp2 f gv a],
          mkApp2 step x a]
        mkForallFVars #[gv, e, x, a, ihv] c
  let h ← mkFreshExprSyntheticOpaqueMVar hType
  let zero := mkNatLit 0
  let h0 ← mkFreshExprSyntheticOpaqueMVar (Inv.beta #[g0, zero, s]) (tag := `init)
  let pf ← mkAppOptM ``Seq.run_total_invariant
    #[none, none, none, step, next, f, Inv, h, g0, zero, s, h0, ops]
  let pfType ← instantiateMVars (← inferType pf)
  let n ← freshName `hrun
  let gm ← g.assert n pfType pf
  let (_, gm) ← gm.intro n
  setGoals [gm]
  let zl ← `(Lean.Parser.Tactic.simpLemma| Nat.zero_add)
  let _ ← gm.withContext (runStructSimp #[zl.raw] (some (← `(Lean.Parser.Tactic.location| at $(mkIdent n):term))))
  let gmain ← getGoals
  let gi ← simpAndKeep h0.mvarId! unfold
  let gs ← introAndSplit h.mvarId! [`g, `e, `x, `op, `ih] 3 "" unfold
  setGoals (gmain ++ gi ++ gs)

/-- `run_induction` proves a statement about `Seq.run step s ops` by induction over the
operations and leaves one goal per constructor of the operation type, with the step function
unfolded: `run_induction` (the invariant read off the goal), `run_induction using J` (a stronger
invariant), and for `P (Seq.run step s ops) ≤ P s + (ops.map f).sum` the accumulated bound.
`run_induction [lemmas]` first rewrites the goal (for a task's own `run`), and
`with [defs]` unfolds `defs` in the per-constructor goals. -/
syntax (name := runInduction) "run_induction" (" using " term)? (simpArgs)?
  (" with " simpArgs)? : tactic

/-- `run_induction total Inv` proves a ghost-total statement with
`Seq.run_total_invariant`: `Inv g e x` relates the ghost state `g`, the total `e` so far and the
state `x`. The main goal receives `hrun`, the invariant at the end of the run. -/
syntax (name := runInductionTotalStx) "run_induction" &" total " term:max (simpArgs)?
  (" with " simpArgs)? : tactic

elab_rules : tactic
  | `(tactic| run_induction $[using $j]? $[$pre:simpArgs]? $[with $post:simpArgs]?) =>
    runInductionCore (j.map (·.raw)) (simpArgsOf pre) (simpArgsOf post)
  | `(tactic| run_induction total $inv $[$pre:simpArgs]? $[with $post:simpArgs]?) =>
    runInductionTotal inv (simpArgsOf pre) (simpArgsOf post)

end ProofForgeFin.Tactic
