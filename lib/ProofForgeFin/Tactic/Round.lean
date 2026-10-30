import ProofForgeFin.Tactic.Struct
/-!
# `fin_simp`, `div_norm` and `round_bound`

Rounding goals are nonlinear: `x / d * d ≤ x` multiplies a quotient by a variable divisor, and
`omega` treats `x / d * d` as an opaque atom. They close by combining the floor and ceiling
facts of each quotient with linear arithmetic, after the goal is put in a form where those
facts apply.

* `fin_simp [h₁, ...] (at loc)?`: `simp only` with the `fin_simp` set: every fixed-point
  operation and share conversion as floor division and `ceilDiv`, units and zeros removed,
  exact cancellations (`a * b / b = a` for `0 < b`) applied.
* `div_norm [defs] (at loc)?`: the preprocessing for `omega`: `fin_simp`, `ceilDiv a b` as
  `(a + b - 1) / b`, the given definitions unfolded (named constants such as `WAD` or
  `doubleScale`), literal arithmetic evaluated (`10 ^ 18`). `omega` handles division and
  remainder by literals, so after `div_norm` a goal whose divisors are literals is linear.
* `round_bound [facts]`: closes rounding bounds. In order: (1) one library lemma (floor and
  ceiling bounds, `mulDown ≤ mulUp`, sums of floors, round trips, monotonicity) applied to the
  goal with side conditions closed by an assumption or `omega`; (2) `div_norm` and `omega`;
  (3) cross-multiplication: a top-level quotient `a / b` on either side of `≤` or `<` is
  replaced by the equivalent product comparison (a positive divisor is proved by `omega`, a
  divisor that may be zero is split on), products are distributed and put in a canonical order,
  and for every quotient `a / b` with a variable divisor the facts `a / b * b ≤ a` and
  `a < a / b * b + b` (and their multiples by the other factors of each product of the goal that
  contains `a / b * b`) are added before `omega`. The given facts are added as hypotheses first.
  The tactic either closes the goal or fails with a message and leaves the goal unchanged.
-/

namespace ProofForgeFin

/-- A floor quotient times a factor is at most the product divided: `a / c * b ≤ a * b / c`. -/
theorem div_mul_le_mul_div (a b c : Nat) : a / c * b ≤ a * b / c := by
  rw [Nat.mul_comm (a / c) b, Nat.mul_comm a b]
  exact Nat.mul_div_le_mul_div_assoc b a c

end ProofForgeFin

namespace ProofForgeFin.Tactic

open Lean Elab Tactic Meta Parser.Tactic

/-- `fin_simp` puts rounding and fixed-point terms in normal form: `simp only` with the
`fin_simp` set (fixed-point operations and share conversions as `a / b` and `ceilDiv a b`, units,
zeros and exact cancellations removed) and the given arguments. -/
syntax (name := finSimp) "fin_simp" (simpArgs)? (location)? : tactic

/-- `simp only [base, args] at loc`; `false` when nothing changed. -/
def simpWithBase (base : Array Syntax) (args : Array Syntax) (loc : Option (TSyntax ``location)) :
    TacticM Bool :=
  simpOnlyOnce (base ++ args) loc

/-- The `fin_simp` set as a simp argument. -/
def finSimpArg : MetaM Syntax := do
  return (← `(Lean.Parser.Tactic.simpLemma| fin_simp)).raw

elab_rules : tactic
  | `(tactic| fin_simp $[$args:simpArgs]? $[$loc:location]?) => do
    unless ← simpWithBase #[← finSimpArg] (simpArgsOf args) loc do
      throwError "fin_simp: no fixed-point operation, share conversion, unit, zero or exact \
        cancellation to normalize in the goal"

/-- `div_norm` prepares a goal with division for `omega`: `fin_simp`, `ceilDiv a b` as
`(a + b - 1) / b`, the given definitions unfolded, literal arithmetic evaluated. -/
syntax (name := divNorm) "div_norm" (simpArgs)? (location)? : tactic

/-- The simp arguments of `div_norm`. -/
def divNormArgs : MetaM (Array Syntax) := do
  return #[← finSimpArg, (← `(Lean.Parser.Tactic.simpLemma| ProofForgeFin.ceilDiv)).raw,
    (← `(Lean.Parser.Tactic.simpLemma| ge_iff_le)).raw,
    (← `(Lean.Parser.Tactic.simpLemma| gt_iff_lt)).raw]

elab_rules : tactic
  | `(tactic| div_norm $[$args:simpArgs]? $[$loc:location]?) => do
    unless ← simpWithBase (← divNormArgs) (simpArgsOf args) loc do
      throwError "div_norm: nothing to normalize: no fixed-point operation, `ceilDiv`, named \
        constant given or literal arithmetic in the goal"

/-! ## `round_bound` -/

/-- The library lemmas `round_bound` tries first, by `apply`. -/
def roundLemmas : List Name :=
  [``Nat.div_mul_le_self, ``Nat.mul_div_le, ``Nat.div_le_self, ``Nat.lt_div_mul_add,
   ``lt_div_add_one_mul, ``le_ceilDiv_mul, ``ceilDiv_mul_lt, ``div_le_ceilDiv,
   ``ceilDiv_le_div_add_one, ``mulDiv_le_mulDivUp, ``mulDivUp_le_mulDiv_add_one,
   ``mulDown_le_mulUp, ``mulUp_le_mulDown_add_one, ``divDown_le_divUp, ``divUp_le_divDown_add_one,
   ``mulDown_mul_le, ``le_mulUp_mul, ``div_add_div_le, ``div_add_le_div_add_div_add_one,
   ``Nat.mul_div_le_mul_div_assoc, ``div_mul_le_mul_div, ``mul_div_le_of_le, ``mulDiv_le_of_le,
   ``mulDivUp_le_of_le, ``divDown_mulDown_le, ``mulDown_divDown_le, ``le_divUp_mulUp,
   ``le_mulUp_divUp, ``mulDown_mulDown_le, ``le_mulUp_mulUp, ``sum_div_mul_le,
   ``sum_div_le_div_sum, ``Shares.previewRedeem_le_assets, ``Shares.previewWithdraw_le_supply,
   ``Shares.previewDeposit_le_previewWithdraw, ``Shares.previewRedeem_le_previewMint,
   ``Shares.deposit_redeem_le, ``Shares.mint_redeem_le, ``Shares.redeem_deposit_le,
   ``Nat.div_le_div_right, ``div_anti_right, ``ceilDiv_mono_left, ``ceilDiv_anti_right,
   ``mulDiv_mono, ``mulDivUp_mono, ``mulDown_mono, ``mulUp_mono, ``divDown_mono_left,
   ``divUp_mono_left, ``divDown_anti_right, ``divUp_anti_right, ``div_le_div_of_mul_le,
   ``ceilDiv_le_ceilDiv_of_mul_le]

/-- Run `tac` on `g` alone; `true` when it closes `g`. The state is restored when it does
not. -/
def closesWith (g : MVarId) (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try
    setGoals [g]
    tac
    if (← getGoals).isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- Stage 1: one library lemma, with side goals closed by an assumption or `omega`. -/
def tryRoundLemmas (g : MVarId) : TacticM Bool := do
  for n in roundLemmas do
    unless (← getEnv).contains n do continue
    let tac : TacticM Unit := do
      evalTactic (← `(tactic| apply $(mkIdent n) <;> first | assumption | omega))
    if ← closesWith g tac then return true
  return false

/-- `e` is `a / b` on `Nat`. -/
def natDiv? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HDiv.hDiv 6 && (e.getArg! 0).isConstOf ``Nat then
    some (e.getArg! 4, e.getArg! 5)
  else none

/-- `e` is `a % b` on `Nat`. -/
def natMod? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HMod.hMod 6 && (e.getArg! 0).isConstOf ``Nat then
    some (e.getArg! 4, e.getArg! 5)
  else none

/-- The factors of a product `x * y * ...` on `Nat` (a non-product is its own factor), up to
`fuel` levels of nesting. -/
def natFactors : Nat → Expr → Array Expr
  | 0, e => #[e]
  | fuel + 1, e =>
    if e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 0).isConstOf ``Nat then
      natFactors fuel (e.getArg! 4) ++ natFactors fuel (e.getArg! 5)
    else #[e]

/-- Prove `0 < b` by `omega` in the context of `g`. -/
def provePos? (g : MVarId) (b : Expr) : TacticM (Option Expr) := g.withContext do
  let ty ← mkAppM ``LT.lt #[mkNatLit 0, b]
  let m ← mkFreshExprMVar ty
  let s ← saveState
  try
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| omega)))
    if gs.isEmpty then return some (← instantiateMVars m)
    s.restore
    return none
  catch _ =>
    s.restore
    return none

/-- The quotients and remainders with a divisor that is not a literal, in `e`. -/
def divAtoms (e : Expr) : MetaM (Array (Bool × Expr × Expr)) := do
  let r ← IO.mkRef (#[] : Array (Bool × Expr × Expr))
  e.forEach fun t => do
    if t.hasLooseBVars then return
    let add (isDiv : Bool) (a b : Expr) : MetaM Unit := do
      if b.nat?.isSome then return
      unless (← r.get).any (fun (d, a', b') => d == isDiv && a' == a && b' == b) do
        r.modify (·.push (isDiv, a, b))
    if let some (a, b) := natDiv? t then add true a b
    if let some (a, b) := natMod? t then add false a b
  r.get

/-- Simp arguments: distribution of products over sums and differences, and units. -/
def distribArgs : MetaM (Array Syntax) := do
  let ns := [``Nat.add_mul, ``Nat.mul_add, ``Nat.sub_mul, ``Nat.mul_sub, ``Nat.mul_one,
    ``Nat.one_mul, ``Nat.mul_zero, ``Nat.zero_mul, ``Nat.add_zero, ``Nat.zero_add]
  ns.toArray.mapM fun n => do return (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)).raw

/-- Simp arguments: the canonical order of products. -/
def acArgs : MetaM (Array Syntax) := do
  let ns := [``Nat.mul_comm, ``Nat.mul_assoc, ``Nat.mul_left_comm]
  ns.toArray.mapM fun n => do return (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)).raw

/-- Cross-multiply the top-level quotient of the main goal, once. Returns `false` when the
goal has no top-level quotient with a variable divisor. Splits on a divisor that may be zero. -/
def crossMultiplyOnce : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let rel? : Option (Name × Expr × Expr) :=
    if tgt.isAppOfArity ``LE.le 4 then some (``LE.le, tgt.getArg! 2, tgt.getArg! 3)
    else if tgt.isAppOfArity ``LT.lt 4 then some (``LT.lt, tgt.getArg! 2, tgt.getArg! 3)
    else none
  let some (rel, lhs, rhs) := rel? | return false
  unless (tgt.getArg! 0).isConstOf ``Nat do return false
  let varDiv (e : Expr) : Option Expr :=
    (natDiv? e).bind fun (_, b) => if b.nat?.isNone then some b else none
  let pick : Option (Bool × Expr) :=
    match varDiv rhs with
    | some b => some (false, b)
    | none => (varDiv lhs).map fun b => (true, b)
  let some (onLeft, b) := pick | return false
  let rewrite (hb : TSyntax `term) : TacticM Unit := do
    match rel, onLeft with
    | ``LE.le, false => evalTactic (← `(tactic| rw [Nat.le_div_iff_mul_le $hb]))
    | ``LE.le, true => evalTactic (← `(tactic| rw [Nat.div_le_iff_le_mul_add_pred $hb]))
    | ``LT.lt, true => evalTactic (← `(tactic| rw [Nat.div_lt_iff_lt_mul $hb]))
    | _, _ => evalTactic (← `(tactic| rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le $hb]))
  let bs ← Term.exprToSyntax b
  match ← provePos? g b with
  | some _ =>
    let hn := (← getLCtx).getUnusedName `hdiv
    evalTactic (← `(tactic| have $(mkIdent hn) : 0 < $bs := by omega))
    withMainContext (rewrite (mkIdent hn))
    return true
  | none =>
    let h := mkIdent ((← getLCtx).getUnusedName `hdiv)
    evalTactic (← `(tactic| by_cases $h:ident : $bs = 0))
    match ← getGoals with
    | [g0, g1] =>
      -- divisor zero: the quotients are zero
      setGoals [g0]
      let zs : Array Syntax := #[(← `(Lean.Parser.Tactic.simpLemma| $h:ident)).raw,
        (← `(Lean.Parser.Tactic.simpLemma| Nat.div_zero)).raw,
        (← `(Lean.Parser.Tactic.simpLemma| Nat.mod_zero)).raw]
      let _ ← simpOnlyOnce (zs ++ (← distribArgs)) none
      let rest0 ← getGoals
      setGoals [g1]
      let hp := mkIdent ((← g1.withContext getLCtx).getUnusedName `hdiv)
      evalTactic (← `(tactic| have $hp:ident : 0 < $bs := Nat.pos_of_ne_zero $h))
      withMainContext (rewrite hp)
      setGoals (rest0 ++ (← getGoals))
      return true
    | _ => return true

/-- Add the floor facts of every quotient with a variable divisor in the main goal and its
hypotheses (and their multiples by the other factors of the products of the goal), put them
in the canonical form, and run `omega`. -/
def atomFactsOmega : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  -- canonical form of the goal and the hypotheses
  let _ ← simpOnlyOnce ((← distribArgs) ++ (← acArgs)) (some (← `(Lean.Parser.Tactic.location| at *)))
  if (← getGoals).isEmpty then return
  let g ← getMainGoal
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut atoms ← divAtoms tgt
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← Meta.isProp d.type then
      for a in ← divAtoms (← instantiateMVars d.type) do
        unless atoms.contains a do atoms := atoms.push a
  -- the products of the goal
  let prods ← do
    let r ← IO.mkRef (#[] : Array (Array Expr))
    tgt.forEach fun t => do
      if t.hasLooseBVars then return
      if t.isAppOfArity ``HMul.hMul 6 && (t.getArg! 0).isConstOf ``Nat then
        r.modify (·.push (natFactors 64 t))
    r.get
  let mut facts : Array Expr := #[]
  for (isDiv, a, b) in atoms do
    let pos ← provePos? g b
    if isDiv then
      let q ← mkAppM ``HDiv.hDiv #[a, b]
      let f1 ← mkAppM ``Nat.div_mul_le_self #[a, b]
      facts := facts.push f1
      let f2? ← pos.mapM fun hb => mkAppOptM ``Nat.lt_div_mul_add #[a, b, hb]
      if let some f2 := f2? then facts := facts.push f2
      for fs in prods do
        unless fs.contains q && fs.contains b do continue
        let mut rest := #[]
        let mut dropQ := false
        let mut dropB := false
        for f in fs do
          if !dropQ && f == q then dropQ := true
          else if !dropB && f == b then dropB := true
          else rest := rest.push f
        let some m0 := rest[0]? | continue
        let m ← rest[1:].foldlM (fun acc f => mkAppM ``HMul.hMul #[acc, f]) m0
        facts := facts.push (← mkAppM ``Nat.mul_le_mul_right #[m, f1])
        if let some f2 := f2? then
          facts := facts.push (← mkAppM ``Nat.mul_le_mul_right #[m, ← mkAppM ``Nat.le_of_lt #[f2]])
    else
      facts := facts.push (← mkAppM ``Nat.div_add_mod #[a, b])
      if let some hb := pos then facts := facts.push (← mkAppM ``Nat.mod_lt #[a, hb])
  -- assert the facts
  let mut g := g
  let mut names := #[]
  for f in facts do
    let n := (← g.getDecl).lctx.getUnusedName `hround
    g ← g.assert n (← inferType f) f
    let (_, g') ← g.intro n
    g := g'
    names := names.push n
  setGoals [g]
  unless names.isEmpty do
    let hs : Array Term := names.map fun n => ⟨(mkIdent n).raw⟩
    let loc ← `(Lean.Parser.Tactic.location| at $hs*)
    let _ ← g.withContext (simpOnlyOnce ((← distribArgs) ++ (← acArgs)) (some loc))
  withMainContext (evalTactic (← `(tactic| first | omega | (generalize_divs; omega))))

/-- The stages of `round_bound` on the main goal; throws when they fail. -/
def roundBoundCore (extraFacts : Array Syntax) (defs : Array Syntax) : TacticM Unit := do
  let _ ← (try evalTactic (← `(tactic| intros)) catch _ => pure ())
  let g ← getMainGoal
  -- conjunctions: each part separately
  if (← whnfR (← instantiateMVars (← g.getType))).isAppOfArity ``And 2 then
    evalTactic (← `(tactic| constructor))
    return
  for t in extraFacts do
    evalTactic (← `(tactic| have := $(⟨t⟩)))
  let g ← getMainGoal
  -- stage 1: library lemmas
  if ← tryRoundLemmas g then return
  -- stage 2: normalization and omega
  let s ← saveState
  let everywhere ← `(Lean.Parser.Tactic.location| at *)
  try
    let _ ← simpOnlyOnce ((← divNormArgs) ++ defs) (some everywhere)
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| first | omega | (generalize_divs; omega)))
    return
  catch _ => s.restore
  -- stage 3: cross-multiplication and the floor facts of every quotient
  let _ ← simpOnlyOnce ((← divNormArgs) ++ defs) (some everywhere)
  if (← getGoals).isEmpty then return
  -- equations: both inequalities
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.isAppOfArity ``Eq 3 && (tgt.getArg! 0).isConstOf ``Nat then
    evalTactic (← `(tactic| apply Nat.le_antisymm))
  let goals ← getGoals
  let mut rest := []
  for g in goals do
    setGoals [g]
    let _ ← crossMultiplyOnce
    let mut gs := []
    for g' in ← getGoals do
      setGoals [g']
      let _ ← crossMultiplyOnce
      gs := gs ++ (← getGoals)
    for g' in gs do
      setGoals [g']
      atomFactsOmega
      rest := rest ++ (← getGoals)
  setGoals rest

/-- `round_bound` closes rounding bounds on `Nat`: floor and ceiling bounds (`x / d * d ≤ x`,
`x ≤ ceilDiv x d * d`), the order of the two rounding directions (`mulDown a b ≤ mulUp a b`),
sums of rounded parts, round trips, and goals that follow from the floor facts of their
quotients by linear arithmetic after cross-multiplication. `round_bound [h₁, ...]` adds the
given facts first; `round_bound with [defs]` also unfolds `defs` (named scales such as
`WAD`). It either closes the goal or fails, leaving the goal unchanged. -/
syntax (name := roundBound) "round_bound" (" [" term,* "]")? (" with " simpArgs)? : tactic

/-- The core loop of `round_bound`: conjunctions are split and each part is proved. -/
def roundBoundAll (extraFacts : Array Syntax) (defs : Array Syntax) : Nat → TacticM Unit
  | 0 => throwError "round_bound: too many conjunctions"
  | fuel + 1 => do
    let goals ← getGoals
    let mut rest := []
    for g in goals do
      setGoals [g]
      let isAnd ← g.withContext do
        return (← whnfR (← instantiateMVars (← g.getType))).isAppOfArity ``And 2
      roundBoundCore extraFacts defs
      if isAnd then
        roundBoundAll extraFacts defs fuel
      rest := rest ++ (← getGoals)
    setGoals rest

elab_rules : tactic
  | `(tactic| round_bound $[[$facts,*]]? $[with $defs:simpArgs]?) => do
    let facts := (facts.map (·.getElems.map (·.raw))).getD #[]
    let defs := simpArgsOf defs
    let g ← getMainGoal
    let s ← saveState
    try
      roundBoundAll facts defs 8
      unless (← getGoals).isEmpty do throwError "round_bound: goals remain"
    catch _ =>
      s.restore
      let tgt ← g.withContext do ppExpr (← instantiateMVars (← g.getType))
      throwError "round_bound: could not prove{indentD tgt}\ntried the library rounding lemmas, \
        `div_norm` with `omega`, and cross-multiplication with the floor facts of every quotient \
        with a variable divisor. Give the missing facts as `round_bound [h₁, h₂]` (for example a \
        positive divisor or a bound on a product), or unfold named scales with \
        `round_bound with [WAD]`."

end ProofForgeFin.Tactic
