import ProofForgeFin.Tactic.SimpSets
/-!
# `struct_simp` and `step_cases`

Step functions of task models build the next state as a structure instance
(`{ s with parents := upd s.parents id p }`), return pairs and options, and branch on matches
and conditions. Goals about them fill with terms such as `{ st := a, tr := b }.st`,
`(x.st, []).fst`, `upd f k v j`, `match some s' with ...` and `if True ∧ c then ...`, which a
proof has to reduce before any arithmetic applies.

* `struct_simp [h₁, ...] (at loc)?`: `simp only` with the `struct_simp` set and the given
  lemmas, definitions to unfold, hypotheses or `*`. For every hypothesis `h : ¬a = b` given (or
  in the context, with `*`) it also uses `Ne.symm h`, so a condition is decided whichever way
  round the update writes it.
* `step_cases (x)? [defs]`: `cases x` (when given), then in every case `struct_simp [defs]`,
  then repeated case splits: `by_cases` on the first condition of an `if`, `cases` with an
  equation on the first discriminant of a `match` or an `Option` consumer (`getD`, `map`,
  `bind`, `isSome`), found anywhere in the goal, under binders too, as long as it does not
  mention a bound variable; `split` when there is neither. The new hypotheses are named `hc`,
  `hc_1`, ... (conjunctions split into their parts), each branch is simplified with them, and
  goals closed by `rfl`, an assumption, a contradiction or `omega` are dropped. At most 64 splits
  are made and at most 12 nested, so the tactic always terminates.
* `generalize_divs`: every `a / b` and `a % b` on `Nat` with a variable divisor becomes a fresh
  variable, so that `omega` knows it is nonnegative (it reads `a / b` as an integer quotient
  of casts about which it knows nothing).

Both `struct_simp` and `step_cases` fail with a message naming the tactic when they change
nothing.
-/

namespace ProofForgeFin.Tactic

open Lean Elab Tactic Meta Parser.Tactic

/-- `struct_simp` reduces record projections, constructor matches, decided conditions, function
updates and run equations: `simp only` with the `struct_simp` set and the given arguments (lemmas,
definitions to unfold, hypotheses or `*`). For a hypothesis `h : ¬a = b` among the arguments, or
in the context with `*`, `Ne.symm h` is used as well. -/
syntax (name := structSimp) "struct_simp" (simpArgs)? (location)? : tactic

/-- The simp arguments of an optional `simpArgs` node. -/
def simpArgsOf (args : Option (TSyntax ``simpArgs)) : Array Syntax :=
  match args with
  | some a => a.raw[1].getSepArgs
  | none => #[]

/-- `Ne.symm h` for a local hypothesis `h : ¬a = b`, as a simp argument. -/
def symmArgOfFVar (d : LocalDecl) : MetaM (Option Syntax) := do
  if d.isImplementationDetail then return none
  let ty ← instantiateMVars d.type
  let isNegEq := match ty.not? with
    | some p => p.isAppOfArity ``Eq 3
    | none => ty.isAppOfArity ``Ne 3
  unless isNegEq do return none
  if d.userName.hasMacroScopes then return none
  let h := mkIdent d.userName
  let stx ← `(Lean.Parser.Tactic.simpLemma| (Ne.symm $h:ident))
  return some stx.raw

/-- The extra `Ne.symm` arguments for the user's simp arguments: for each identifier that names a
negated equation of the context, and for every such hypothesis when `*` is given. -/
def symmArgs (args : Array Syntax) : TacticM (Array Syntax) := withMainContext do
  let lctx ← getLCtx
  let mut out := #[]
  let star := args.any (·.getKind == ``simpStar)
  if star then
    for d in lctx do
      if let some s ← symmArgOfFVar d then out := out.push s
  else
    for a in args do
      if a.getKind == ``simpLemma && a[0].isNone && a[1].isNone && a[2].isIdent then
        if let some d := lctx.findFromUserName? a[2].getId then
          if let some s ← symmArgOfFVar d then out := out.push s
  return out

/-- The structure projections applied to an `if` (or a dependent `if`) somewhere in `e`. -/
def projsOfIte (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let r ← IO.mkRef (#[] : Array Name)
  e.forEach fun t => do
    let some p := t.getAppFn.constName? | return
    let some info := env.getProjectionFnInfo? p | return
    unless t.getAppNumArgs > info.numParams do return
    let a := t.getArg! info.numParams
    if a.isAppOfArity ``ite 5 || a.isAppOfArity ``dite 5 then
      unless (← r.get).contains p do r.modify (·.push p)
  r.get

/-- `apply_ite p` and `apply_dite p` for a projection `p`, as simp arguments: they move the
projection into both branches of a condition. -/
def projIteArgs (p : Name) : MetaM (Array Syntax) := do
  let a ← `(Lean.Parser.Tactic.simpLemma| (apply_ite $(mkIdent p)))
  let b ← `(Lean.Parser.Tactic.simpLemma| (apply_dite $(mkIdent p)))
  return #[a.raw, b.raw]

/-- One `simp only [args] at loc`. Returns `false` when simp made no progress. -/
def simpOnlyOnce (all : Array Syntax) (loc : Option (TSyntax ``location)) : TacticM Bool := do
  let lemmas : Syntax.TSepArray [``simpStar, ``simpErase, ``simpLemma] "," :=
    Syntax.TSepArray.ofElems (all.map (⟨·⟩))
  let tac ← match loc with
    | some l => `(tactic| simp only [$lemmas,*] $l:location)
    | none => `(tactic| simp only [$lemmas,*])
  try
    evalTactic tac
    return true
  catch e =>
    let msg ← e.toMessageData.toString
    if (msg.splitOn "made no progress").length > 1 then return false
    throw e

/-- The projections applied to a condition in the main goal and its hypotheses. -/
def projsOfIteInGoal : TacticM (Array Name) := do
  let some g ← getMainGoal? | return #[]
  g.withContext do
    let mut ps ← projsOfIte (← instantiateMVars (← g.getType))
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      for p in ← projsOfIte (← instantiateMVars d.type) do
        unless ps.contains p do ps := ps.push p
    return ps
where
  getMainGoal? : TacticM (Option MVarId) := do
    match ← getGoals with
    | g :: _ => return some g
    | [] => return none

/-- Run `simp only [struct_simp, args] at loc`, then again with `apply_ite p` for every
structure projection `p` that the result applies to a condition (at most four rounds), so that
`(if c then a else b).f` becomes `if c then a.f else b.f`. Returns `false` when nothing
changed. -/
def runStructSimp (args : Array Syntax) (loc : Option (TSyntax ``location)) : TacticM Bool := do
  let extra ← symmArgs args
  let base ← `(Lean.Parser.Tactic.simpLemma| struct_simp)
  let ctor ← `(Lean.Parser.Tactic.simpLemma| reduceCtorEq)
  let mut all : Array Syntax := #[base.raw, ctor.raw] ++ args ++ extra
  let mut done : Array Name := #[]
  for p in ← projsOfIteInGoal do
    all := all ++ (← projIteArgs p)
    done := done.push p
  let mut progress ← simpOnlyOnce all loc
  for _ in [0:4] do
    if (← getGoals).isEmpty then break
    let ps := (← projsOfIteInGoal).filter (!done.contains ·)
    if ps.isEmpty then break
    for p in ps do
      all := all ++ (← projIteArgs p)
      done := done.push p
    if ← simpOnlyOnce all loc then progress := true
  return progress

elab_rules : tactic
  | `(tactic| struct_simp $[$args:simpArgs]? $[$loc:location]?) => do
    unless ← runStructSimp (simpArgsOf args) loc do
      throwError "struct_simp: nothing to reduce: no projection of a structure instance, \
        constructor match, decided condition, function update or run equation in the goal \
        (pass definitions to unfold as `struct_simp [f]`)"

/-- The quotients and remainders on `Nat` in `e` whose divisor mentions a local variable (and
that do not depend on a bound variable). -/
def natDivTerms (e : Expr) : MetaM (Array Expr) := do
  let r ← IO.mkRef (#[] : Array Expr)
  e.forEach fun t => do
    if t.hasLooseBVars then return
    if (t.isAppOfArity ``HDiv.hDiv 6 || t.isAppOfArity ``HMod.hMod 6) &&
        (t.getArg! 0).isConstOf ``Nat && (t.getArg! 5).hasFVar then
      unless (← r.get).contains t do r.modify (·.push t)
  r.get

/-- Replace every quotient and remainder by a variable divisor in the target and the
hypotheses of `g` by a fresh natural number. `omega` reads `a / b` as the integer quotient of
the casts, about which it knows nothing (not even that it is nonnegative); a fresh `Nat`
variable it knows to be nonnegative. -/
def generalizeDivs (g : MVarId) : MetaM MVarId := g.withContext do
  let mut terms ← natDivTerms (← instantiateMVars (← g.getType))
  let mut hyps := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless ← Meta.isProp d.type do continue
    let ts ← natDivTerms (← instantiateMVars d.type)
    unless ts.isEmpty do hyps := hyps.push d.fvarId
    for t in ts do
      unless terms.contains t do terms := terms.push t
  if terms.isEmpty then return g
  let (_, _, g') ← g.generalizeHyp (terms.map fun e => { expr := e }) hyps
  return g'

/-- `generalize_divs` replaces every quotient and remainder on `Nat` whose divisor is not a
constant, in the goal and the hypotheses, by a fresh variable, so that `omega` knows it is
nonnegative. -/
syntax (name := generalizeDivsTac) "generalize_divs" : tactic

elab_rules : tactic
  | `(tactic| generalize_divs) => liftMetaTactic fun g => do return [← generalizeDivs g]

/-- Try to close the main goal with a cheap closer (`rfl`, `True`,
an assumption, a contradiction, `omega`, `omega` after `generalize_divs`); `true` when it is
closed. The state is restored when it is not. -/
def tryCloseCheap : TacticM Bool := do
  let tac ← `(tactic| first
    | rfl | exact True.intro | assumption | contradiction | omega
    | (generalize_divs; omega))
  let s ← saveState
  try
    evalTactic tac
    if (← getGoals).isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- Make the inaccessible hypotheses and variables that a case split introduced into `g` accessible,
with fresh names (`hc`, `hc_1`, ... for propositions, the original name for variables); return
the new proposition hypotheses. -/
def nameSplitLocals (g : MVarId) (before : LocalContext) : MetaM (MVarId × Array Name) := do
  let mut g := g
  let mut props := #[]
  let decls := (← g.getDecl).lctx.decls.toArray.filterMap id
  for d in decls do
    if d.isImplementationDetail then continue
    if before.contains d.fvarId then continue
    unless d.userName.hasMacroScopes do continue
    let isProp ← g.withContext (Meta.isProp d.type)
    let lctx := (← g.getDecl).lctx
    let base := if isProp then `hc else d.userName.eraseMacroScopes
    let n := lctx.getUnusedName base
    g ← g.rename d.fvarId n
    if isProp then props := props.push n
  return (g, props)

/-- The first condition of an `if` or discriminant of a `match` in `e` that does not depend on a
bound variable, is not already decided and is not in `avoid`: `(true, c)` for a condition,
`(false, d)` for a discriminant. Conditions are found under binders too (a condition that does
not mention the bound variable can be split outside the binder). -/
def findSplitTarget? (e : Expr) (avoid : Array Expr) : MetaM (Option (Bool × Expr)) := do
  let r ← IO.mkRef (none : Option (Bool × Expr))
  e.forEach' fun t => do
    if (← r.get).isSome then return false
    if t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5 then
      let c := t.getArg! 1
      if !c.hasLooseBVars && !c.isConstOf ``True && !c.isConstOf ``False && !avoid.contains c then
        r.set (some (true, c))
        return false
    if !t.hasLooseBVars then
      -- an option consumed by `getD`, `map`, `bind`, `isSome` or `isNone`: split on it
      let optArg? : Option Expr :=
        if t.isAppOfArity ``Option.getD 3 then some (t.getArg! 1)
        else if t.isAppOfArity ``Option.map 4 then some (t.getArg! 3)
        else if t.isAppOfArity ``Option.bind 4 then some (t.getArg! 2)
        else if t.isAppOfArity ``Option.isSome 2 then some (t.getArg! 1)
        else if t.isAppOfArity ``Option.isNone 2 then some (t.getArg! 1)
        else none
      if let some d := optArg? then
        let isBranch := d.isAppOfArity ``ite 5 || d.isAppOfArity ``dite 5 ||
          (← matchMatcherApp? d).isSome
        if !isBranch && !avoid.contains d && !(← isConstructorApp d) then
          r.set (some (false, d))
          return false
      if let some m ← matchMatcherApp? t then
        for d in m.discrs do
          if d.hasLooseBVars || avoid.contains d then continue
          if (← isConstructorApp d) then continue
          r.set (some (false, d))
          return false
    return true
  r.get

/-- Split the hypotheses named `ns` that are conjunctions into their parts (named `hc`, `hc_1`,
...); return the goal and the names of the parts and of the other hypotheses. -/
def splitAnds (g : MVarId) (ns : Array Name) : MetaM (MVarId × Array Name) := do
  let mut g := g
  let mut todo := ns.toList
  let mut out := #[]
  for _ in [0:16] do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      let some d := (← g.getDecl).lctx.findFromUserName? n | continue
      let ty ← g.withContext (whnfR (← instantiateMVars d.type))
      if ty.isAppOfArity ``And 2 then
        let before := (← g.getDecl).lctx
        let cs ← g.cases d.fvarId
        let some c := cs[0]? | continue
        let (g', ps) ← nameSplitLocals c.mvarId before
        g := g'
        todo := ps.toList ++ todo
      else
        out := out.push n
  return (g, out ++ todo.toArray)

/-- Split the main goal on the conditions and match discriminants of its `if` and `match`
terms (`by_cases` on a condition, `cases` with an equation on a discriminant; `split` when
neither applies), at most `fuel` levels deep and while the number of splits stays below the cap
kept in `budget`. Each branch is simplified with `struct_simp`, `args` and the new hypotheses. -/
def splitLoop (args : Array Syntax) (budget : IO.Ref Nat) (avoid : Array Expr) :
    Nat → MVarId → TacticM (List MVarId)
  | 0, g => return [g]
  | fuel + 1, g => do
    if (← budget.get) == 0 then return [g]
    let before := (← g.getDecl).lctx
    setGoals [g]
    let tgt ← g.withContext do findSplitTarget? (← instantiateMVars (← g.getType)) avoid
    let hn ← g.withContext do return (← getLCtx).getUnusedName `hc
    let h := mkIdent hn
    let saved ← saveState
    let ok ← try
        match tgt with
        | some (true, c) =>
          let cs ← g.withContext (Term.exprToSyntax c)
          evalTactic (← `(tactic| by_cases $h : $cs))
        | some (false, d) =>
          let ds ← g.withContext (Term.exprToSyntax d)
          if d.isFVar then evalTactic (← `(tactic| cases $ds:term))
          else evalTactic (← `(tactic| cases $h:ident : $ds))
        | none => evalTactic (← `(tactic| split))
        pure true
      catch _ =>
        saved.restore
        pure false
    unless ok do return [g]
    let avoid := match tgt with
      | some (_, c) => avoid.push c
      | none => avoid
    let gs ← getGoals
    budget.modify (· - 1)
    let mut out := []
    for g' in gs do
      let (g', props) ← nameSplitLocals g' before
      let hasH := ((← g'.getDecl).lctx.findFromUserName? hn).isSome
      let props := if props.contains hn || !hasH then props else props.push hn
      let (g', props) ← splitAnds g' props
      setGoals [g']
      let hyps ← props.mapM fun n => do
        let s ← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
        pure s.raw
      let _ ← g'.withContext (runStructSimp (args ++ hyps) none)
      for g'' in (← getGoals) do
        setGoals [g'']
        if ← tryCloseCheap then continue
        out := out ++ (← splitLoop args budget avoid fuel g'')
    return out

/-- `step_cases x [defs]` splits a goal about one step of a model: `cases x` when the variable
`x` is given, then in every case `struct_simp [defs]`, then repeated case splits on the first
condition of an `if` (`by_cases`) or discriminant of a `match` or of an `Option` consumer such as
`getD` (`cases` with an equation) that does not depend on a bound variable, naming the new
hypotheses `hc`, `hc_1`, ... and simplifying each branch with them. Goals that `rfl`, an
assumption, a contradiction or `omega` close are dropped. At most 12 nested splits and 64 splits
in all are made. -/
syntax (name := stepCases) "step_cases" (ppSpace colGt ident)? (simpArgs)? : tactic

elab_rules : tactic
  | `(tactic| step_cases $[$x:ident]? $[$args:simpArgs]?) => do
    let args := simpArgsOf args
    let start ← getMainGoal
    let mut progress := false
    if let some x := x then
      let before := (← start.getDecl).lctx
      evalTactic (← `(tactic| cases $x:ident))
      let gs ← (← getGoals).mapM fun g => do pure (← nameSplitLocals g before).1
      setGoals gs
      progress := true
    let budget ← IO.mkRef 64
    let mut out := []
    for g in (← getGoals) do
      setGoals [g]
      if ← g.withContext (runStructSimp args none) then progress := true
      for g' in (← getGoals) do
        setGoals [g']
        if ← tryCloseCheap then
          progress := true
          continue
        let gs ← splitLoop args budget #[] 12 g'
        unless gs == [g'] do progress := true
        out := out ++ gs
    unless progress do
      setGoals [start]
      throwError "step_cases: nothing to split: no `cases` variable given and no `if`, `match` \
        or definition to unfold in the goal (pass the step function as `step_cases op [step]`)"
    setGoals out

end ProofForgeFin.Tactic
