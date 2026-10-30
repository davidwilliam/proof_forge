import ProofForgeFin.Tactic.Attr
import ProofForgeFin.Rounding
import ProofForgeFin.FixedPoint
import ProofForgeFin.Shares
import ProofForgeFin.Seq
import ProofForgeFin.Ledger
/-!
# The lemmas of `fin_simp` and `struct_simp`

The lemmas of both simp sets, and the few lemmas they need that the other modules do not state
(`ceilDiv` by zero and by one, function updates applied to an argument, `List.foldl` as
`Seq.run`). One simplification procedure, `ctorEq`, turns an equation between two applications of
the same constructor into the equations of their fields, for every inductive type (the
`injEq` theorems that `simp only` does not use unless they are named).
-/

namespace ProofForgeFin

universe u v

/-! ## Lemmas the simp sets need -/

/-- Division rounded up by zero is zero, as `Nat` division by zero is. -/
theorem ceilDiv_zero_right (a : Nat) : ceilDiv a 0 = 0 := by simp [ceilDiv]

/-- Division rounded up by one is the identity. -/
theorem ceilDiv_one_right (a : Nat) : ceilDiv a 1 = a := by simp [ceilDiv]

/-- The ceiling of an exact multiple, with the multiplier on the right. -/
theorem ceilDiv_mul_cancel_left (a : Nat) {b : Nat} (hb : 0 < b) : ceilDiv (b * a) b = a := by
  rw [Nat.mul_comm]; exact ceilDiv_mul_cancel a hb

/-- A left fold is a run (the converse of `Seq.run_eq_foldl`). -/
theorem foldl_eq_run {σ : Type u} {α : Type v} (step : σ → α → σ) (s : σ) (as : List α) :
    as.foldl step s = Seq.run step s as := (Seq.run_eq_foldl step s as).symm

namespace Ledger

/-- An updated function read at any position. -/
theorem upd_apply {κ : Type u} {β : Type v} [DecidableEq κ] (f : κ → β) (k : κ) (v : β) (j : κ) :
    upd f k v j = if j = k then v else f j := rfl

/-- An adjusted balance read at any account. -/
theorem adjust_apply {κ : Type u} [DecidableEq κ] (bal : κ → Int) (k : κ) (d : Int) (j : κ) :
    adjust bal k d j = if j = k then bal j + d else bal j := rfl

/-- A balance after a transfer, read at any account. -/
theorem transfer_apply {κ : Type u} [DecidableEq κ] (bal : κ → Int) (src dst : κ) (x : Int)
    (j : κ) :
    transfer bal src dst x j = bal j - (if j = src then x else 0) + (if j = dst then x else 0) :=
  rfl

end Ledger

/-- A condition between two functions, applied: the condition between the two values. -/
theorem ite_apply_fun {α : Sort u} {β : α → Sort v} (c : Prop) [Decidable c]
    (f g : (a : α) → β a) (a : α) : (if c then f else g) a = if c then f a else g a := by
  by_cases h : c <;> simp [h]

/-- A condition `a = b` whose branches differ only by `b` in place of `a` is its else branch:
an update read at the updated position, when the new value is the old one. -/
theorem ite_eq_subst_left {α : Sort u} {β : Sort v} {a b : α} {inst : Decidable (a = b)}
    (f : α → β) : @ite β (a = b) inst (f b) (f a) = f a := by
  by_cases h : a = b <;> simp [h]

/-- The same with `a` in the then branch and `b` in the else branch. -/
theorem ite_eq_subst_right {α : Sort u} {β : Sort v} {a b : α} {inst : Decidable (a = b)}
    (f : α → β) : @ite β (a = b) inst (f a) (f b) = f b := by
  by_cases h : a = b <;> simp [h]

namespace Seq

/-- An atomic run of `a :: as`: the first operation, then the rest from the state it leaves. -/
theorem runAll_cons {σ : Type u} {α : Type v} (step : σ → α → Option σ) (s : σ) (a : α)
    (as : List α) :
    runAll step s (a :: as) = match step s a with
      | some s' => runAll step s' as
      | none => none := rfl

/-- `skip` applied: the successor state, or the state itself when the operation is refused. -/
theorem skip_apply {σ : Type u} {α : Type v} (step : σ → α → Option σ) (s : σ) (a : α) :
    skip step s a = (step s a).getD s := rfl

end Seq

/-! ## `fin_simp` -/

attribute [fin_simp] mulDiv mulDivUp mulDown mulUp divDown divUp scaleDown scaleUp unscaleDown
  unscaleUp convertDecimalsDown convertDecimalsUp Shares.previewDeposit Shares.previewMint
  Shares.previewRedeem Shares.previewWithdraw
attribute [fin_simp] ceilDiv_zero_left ceilDiv_zero_right ceilDiv_one_right ceilDiv_mul_cancel
  ceilDiv_mul_cancel_left
attribute [fin_simp] Nat.div_one Nat.div_zero Nat.zero_div Nat.mul_one Nat.one_mul Nat.mul_zero
  Nat.zero_mul Nat.add_zero Nat.zero_add Nat.sub_zero Nat.mul_div_cancel Nat.mul_div_cancel_left
  Nat.div_div_eq_div_mul Nat.pow_zero Nat.pow_one

/-! ## `struct_simp` -/

attribute [struct_simp] Option.getD_some Option.getD_none Option.map_some Option.map_none
  Option.isSome_some Option.isSome_none Option.some.injEq Prod.mk.injEq
attribute [struct_simp] and_true true_and and_false false_and or_true true_or or_false false_or
  not_true_eq_false not_false_eq_true eq_self_iff_true ne_eq Nat.lt_irrefl Nat.le_refl
  Nat.zero_le Nat.add_zero Nat.zero_add Nat.sub_zero Nat.sub_self Nat.add_sub_cancel
  Int.add_zero Int.zero_add Int.sub_zero Nat.not_lt_zero List.not_mem_nil false_implies implies_true ite_self forall_eq forall_eq'
  ite_apply_fun ite_true ite_false dite_true dite_false
attribute [struct_simp] List.map_nil List.map_cons List.nil_append List.cons_append
  List.append_nil List.length_nil List.length_cons List.length_append List.length_map
  List.length_modify Ledger.getD_modify List.getElem?_modify List.getElem_modify List.modify_nil
  List.modify_zero_cons List.modify_succ_cons List.length_set List.getElem?_set List.getElem_set
  List.getElem?_nil List.getElem?_cons_zero List.getElem?_cons_succ
attribute [struct_simp] Ledger.upd_apply Ledger.adjust_apply Ledger.transfer_apply Ledger.upd_self
  Shares.Pool.add Shares.Pool.sub
attribute [struct_simp] Seq.run_nil Seq.run_cons Seq.trace_nil Seq.trace_cons Seq.accum_nil
  Seq.accum_cons Seq.runAll_nil Seq.runAll_cons Seq.skip_apply

open Lean Meta Simp in
/-- An equation between two applications of the same constructor is the conjunction of the
equations of their fields (the constructor's `injEq` theorem), for every inductive type. -/
simproc [struct_simp] ctorEq (@Eq _ _ _) := fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  let some c := lhs.getAppFn.constName? | return .continue
  unless rhs.getAppFn.constName? == some c do return .continue
  let some (.ctorInfo ci) := (← getEnv).find? c | return .continue
  unless ci.numFields > 0 do return .continue
  unless lhs.getAppNumArgs == ci.numParams + ci.numFields do return .continue
  unless rhs.getAppNumArgs == ci.numParams + ci.numFields do return .continue
  let thmName := c ++ `injEq
  unless (← getEnv).contains thmName do return .continue
  let thm ← mkConstWithFreshMVarLevels thmName
  let (mvars, _, ty) ← forallMetaTelescopeReducing (← inferType thm)
  let some (_, l, r) := ty.eq? | return .continue
  unless ← isDefEq l e do return .continue
  let proof ← instantiateMVars (mkAppN thm mvars)
  let r ← instantiateMVars r
  if r.hasExprMVar || proof.hasExprMVar then return .continue
  return .visit { expr := r, proof? := some proof }

open Lean Meta Simp in
/-- `if a = b then t else e` is `e` when `t` with `a` in place of `b` (or `e` with `b` in place of
`a`) is `e`: the condition does not matter (`ite_eq_subst_left`, `ite_eq_subst_right`). -/
simproc [struct_simp] iteEqSubst (@ite _ (_ = _) _ _ _) := fun e => do
  let_expr ite β c inst t el := e | return .continue
  let_expr Eq α a b := c | return .continue
  let tb ← kabstract t b
  if tb.hasLooseBVars then
    let F := mkLambda `x .default α tb
    if (F.beta #[a]) == el then
      let proof ← mkAppOptM ``ite_eq_subst_left #[α, β, a, b, inst, F]
      return .visit { expr := el, proof? := some proof }
  let ta ← kabstract t a
  if ta.hasLooseBVars then
    let F := mkLambda `x .default α ta
    if (F.beta #[b]) == el then
      let proof ← mkAppOptM ``ite_eq_subst_right #[α, β, a, b, inst, F]
      return .visit { expr := el, proof? := some proof }
  return .continue

end ProofForgeFin
