import ProofForgeFin.DeFi.Rewards
/-!
# MasterChef's `rewardDebt` accounting and its bound

SushiSwap's `MasterChef` (and its many forks) does not record a checkpoint index per account. It
records `rewardDebt = amount * accSushiPerShare / 1e12`, rounded down, at the account's last
interaction, and pays `amount * accSushiPerShare / 1e12 - rewardDebt` on the next one. Both
divisions round down, so a payment can exceed the exact rewards accrued since by up to one unit;
the contract's `safeSushiTransfer` ("just in case if rounding error causes pool to not have
enough SUSHIs") caps a payment at the balance held.

This module is a one-pool model (`State`, `step`: emit, update, deposit, withdraw, harvest) and
quantifies that rounding: over any sequence of operations the rewards paid never exceed those paid
at the start, plus those owed at the start, plus those emitted, plus one unit per deposit or
withdrawal (`run_paid_le`); the same holds for each account (`run_paidTo_le`). A harvest that does
not change the stake adds nothing (`term_harvest_le`); a stake change adds less than one unit
(`term_restake_le`).

The potential term of an account is `paid * one + units * index - rewardDebt * one`, with the
invariant `rewardDebt ≤ units * index / one` (`Inv`), from `Rewards.harvest_term_eq` and
`Rewards.restake_term_lt`.
-/

namespace ProofForgeFin.DeFi.Chef

open ProofForgeFin ProofForgeFin.DeFi.Rewards

/-- One account (`UserInfo`): its stake, its reward debt, and the rewards paid to it. -/
structure Acct where
  /-- `amount`: units staked. -/
  units : Nat
  /-- `rewardDebt`: `units * index / one` at the last interaction. -/
  debt : Nat
  /-- Rewards paid out. -/
  paid : Nat
  deriving DecidableEq, Repr

/-- The record of an account beyond the list. -/
def Acct.empty : Acct := ⟨0, 0, 0⟩

/-- The pool (`PoolInfo`): the index `accSushiPerShare`, rewards emitted and not yet in the index,
and the accounts. -/
structure State where
  /-- `accSushiPerShare`, at scale `one`. -/
  index : Nat
  /-- Rewards emitted since the last `updatePool`. -/
  unindexed : Nat
  /-- Accounts, numbered by position. -/
  accts : List Acct
  deriving DecidableEq, Repr

/-- The record of account `w`. -/
def State.acct (s : State) (w : Nat) : Acct := s.accts.getD w Acct.empty

/-- `lpSupply`: units staked by all accounts. -/
def State.total (s : State) : Nat := (s.accts.map Acct.units).sum

/-- Rewards paid to all accounts. -/
def State.paid (s : State) : Nat := (s.accts.map Acct.paid).sum

/-- Rewards paid to account `w`. -/
def State.paidTo (s : State) (w : Nat) : Nat := (s.acct w).paid

section Model

variable (one : Nat)

/-- `updatePool`: the unindexed rewards spread over the units staked (discarded over none). -/
def State.update (s : State) : State :=
  { s with index := s.index + indexDelta one s.unindexed s.total, unindexed := 0 }

/-- An account paid its pending rewards at `index` and left with `units'` staked and the reward
debt recomputed for them. -/
def settleTo (index : Nat) (a : Acct) (units' : Nat) : Acct :=
  ⟨units', debtOf one units' index, a.paid + harvest one a.units index a.debt⟩

/-- Operations on the pool. -/
inductive Op where
  /-- `x` rewards are emitted (`sushiPerBlock` times the blocks passed). -/
  | emit (x : Nat)
  /-- `updatePool`. -/
  | update
  /-- `deposit(pid, x)` by account `w`. -/
  | deposit (w x : Nat)
  /-- `withdraw(pid, x)` by account `w`; refused above its stake. -/
  | withdraw (w x : Nat)
  /-- `deposit(pid, 0)` (a harvest) by account `w`. -/
  | harvest (w : Nat)
  deriving DecidableEq, Repr

/-- One operation: every interaction updates the pool, pays the account and recomputes its debt. -/
def step (s : State) : Op → State
  | .emit x => { s with unindexed := s.unindexed + x }
  | .update => s.update one
  | .deposit w x =>
    { s.update one with
      accts := s.accts.modify w (fun a => settleTo one (s.update one).index a (a.units + x)) }
  | .withdraw w x =>
    if x ≤ (s.acct w).units then
      { s.update one with
        accts := s.accts.modify w (fun a => settleTo one (s.update one).index a (a.units - x)) }
    else s
  | .harvest w =>
    { s.update one with
      accts := s.accts.modify w (fun a => settleTo one (s.update one).index a a.units) }

/-- What an operation may add to the rewards paid beyond what was owed: the emission, and one
unit of rounding for a deposit or a withdrawal. -/
def allowance : Op → Nat
  | .emit x => x
  | .deposit _ _ => 1
  | .withdraw _ _ => 1
  | _ => 0

/-- The allowance of a sequence: the emission plus the number of deposits and withdrawals. -/
def allowed (ops : List Op) : Nat := (ops.map allowance).sum

/-- The potential term of an account at index `i`: `paid * one + units * i - debt * one`. -/
def term (i : Nat) (a : Acct) : Nat := a.paid * one + a.units * i - a.debt * one

/-- The potential: every account's term plus the scaled unindexed emission. -/
def pot (s : State) : Nat := (s.accts.map (term one s.index)).sum + s.unindexed * one

/-- The potential of account `w`. -/
def potTo (s : State) (w : Nat) : Nat :=
  term one s.index (s.acct w) + (if 0 < (s.acct w).units then s.unindexed * one else 0)

/-- The invariant: no account's debt exceeds `units * index / one`. -/
def Inv (s : State) : Prop := ∀ a ∈ s.accts, a.debt ≤ debtOf one a.units s.index

/-- Rewards owed at a state: every account's pending rewards, at scale `one`, summed and rounded
down once, plus the unindexed emission. -/
def State.owed (s : State) : Nat :=
  (s.accts.map fun a => a.units * s.index - a.debt * one).sum / one + s.unindexed

/-- Rewards owed to account `w`. -/
def State.owedTo (s : State) (w : Nat) : Nat :=
  ((s.acct w).units * s.index - (s.acct w).debt * one) / one +
    (if 0 < (s.acct w).units then s.unindexed else 0)

end Model

/-- The update does not touch the accounts. -/
@[simp] theorem update_accts (one : Nat) (s : State) : (s.update one).accts = s.accts := rfl

/-- The update does not touch the accounts. -/
@[simp] theorem update_acct (one : Nat) (s : State) (w : Nat) : (s.update one).acct w = s.acct w :=
  rfl

/-- After the update nothing is unindexed. -/
@[simp] theorem update_unindexed (one : Nat) (s : State) : (s.update one).unindexed = 0 := rfl

/-- An account holds at most the total. -/
theorem units_le_total (s : State) (w : Nat) : (s.acct w).units ≤ s.total :=
  Ledger.getD_le_sum_map _ _ _ _ rfl

section Proofs

variable {one : Nat}

/-- A settlement with the stake unchanged keeps the term exactly. -/
theorem term_harvest_le (i : Nat) (a : Acct) (h : a.debt ≤ debtOf one a.units i) :
    term one i (settleTo one i a a.units) ≤ term one i a := by
  unfold term settleTo
  exact Nat.le_of_eq (harvest_term_eq one a.units i a.debt a.paid h)

/-- A settlement with any new stake raises the term by less than one reward unit. -/
theorem term_restake_le (hone : 0 < one) (i : Nat) (a : Acct) (u : Nat)
    (h : a.debt ≤ debtOf one a.units i) :
    term one i (settleTo one i a u) ≤ term one i a + 1 * one := by
  have h1 := harvest_term_eq one a.units i a.debt a.paid h
  have h2 := restake_term_lt one u i (a.paid + harvest one a.units i a.debt) hone
  have h3 := debtOf_mul_le one a.units i
  have h4 : a.debt * one ≤ debtOf one a.units i * one := Nat.mul_le_mul_right _ h
  unfold term settleTo
  dsimp only
  omega

/-- Each term grows with the update by at most the account's units times the increment. -/
theorem term_update_le (s : State) (a : Acct) :
    term one (s.update one).index a ≤ term one s.index a + a.units * indexDelta one s.unindexed s.total := by
  unfold term State.update
  dsimp only
  rw [Nat.mul_add]
  omega

/-- The update keeps the invariant. -/
theorem inv_update {s : State} (h : Inv one s) : Inv one (s.update one) := fun a ha =>
  Nat.le_trans (h a ha) (debtOf_mono_index one a.units (Nat.le_add_right _ _))

/-- The update does not raise the potential. -/
theorem pot_update (s : State) : pot one (s.update one) ≤ pot one s := by
  have h := sum_le_of_index_le s.accts (term one s.index) (term one (s.update one).index) Acct.units
    (fun a _ => term_update_le s a) (total_mul_indexDelta_le one s.unindexed s.total)
  unfold pot
  simp only [State.update, Nat.zero_mul, Nat.add_zero] at h ⊢
  exact h

/-- The update does not raise an account's potential. -/
theorem potTo_update (s : State) (w : Nat) : potTo one (s.update one) w ≤ potTo one s w := by
  have h1 := term_update_le (one := one) s (s.acct w)
  have h2 := units_mul_le_ite (units_le_total s w) (total_mul_indexDelta_le one s.unindexed s.total)
  unfold potTo
  simp only [update_acct, update_unindexed, Nat.zero_mul, ite_self, Nat.add_zero]
  omega

/-- Every operation keeps the invariant. -/
theorem inv_step (s : State) (op : Op) (h : Inv one s) : Inv one (step one s op) := by
  have hu := inv_update h
  have hs : ∀ (i : Nat) (f : Acct → Acct),
      (∀ a, (f a).debt ≤ debtOf one (f a).units (s.update one).index) →
      Inv one { s.update one with accts := s.accts.modify i f } := fun i f hf a ha =>
    forall_mem_modify (P := fun a => a.debt ≤ debtOf one a.units (s.update one).index)
      (fun b hb => hu b hb) (fun b _ => hf b) a ha
  cases op with
  | emit x => exact h
  | update => exact hu
  | deposit w x => exact hs w _ fun a => Nat.le_refl _
  | withdraw w x =>
    simp only [step]; split
    · exact hs w _ fun a => Nat.le_refl _
    · exact h
  | harvest w => exact hs w _ fun a => Nat.le_refl _

/-- A change of one account that raises its term by at most `c` raises the potential by at most
`c`. -/
theorem pot_modify (s : State) (i : Nat) (f : Acct → Acct) (c : Nat)
    (hf : ∀ a ∈ s.accts, term one s.index (f a) ≤ term one s.index a + c) :
    pot one { s with accts := s.accts.modify i f } ≤ pot one s + c := by
  unfold pot
  dsimp only
  by_cases hi : i < s.accts.length
  · have e := Ledger.sum_map_modify s.accts f (term one s.index) Acct.empty hi
    have hm : s.accts.getD i Acct.empty ∈ s.accts := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    have := hf _ hm
    omega
  · rw [Ledger.modify_of_length_le s.accts f (by omega)]; omega

/-- The per-account form of `pot_modify`, after an update (nothing unindexed). -/
theorem potTo_modify (s : State) (i w : Nat) (f : Acct → Acct) (c : Nat) (h0 : s.unindexed = 0)
    (hf : ∀ a ∈ s.accts, term one s.index (f a) ≤ term one s.index a + c) :
    potTo one { s with accts := s.accts.modify i f } w ≤ potTo one s w + c := by
  unfold potTo
  have e := Ledger.getD_modify s.accts i w f Acct.empty
  simp only [State.acct, e, h0, Nat.zero_mul, ite_self, Nat.add_zero]
  split
  · rename_i hc
    have hm : s.accts.getD w Acct.empty ∈ s.accts := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc.2, Option.getD_some]
      exact List.getElem_mem hc.2
    exact hf _ hm
  · omega

/-- The terms of a deposit, a withdrawal and a harvest, for the accounts of a state with the
invariant. -/
theorem settle_terms (hone : 0 < one) {s : State} (h : Inv one s) (g : Nat → Nat) :
    ∀ a ∈ s.accts, term one s.index (settleTo one s.index a (g a.units)) ≤ term one s.index a + 1 * one :=
  fun a ha => term_restake_le hone _ a _ (h a ha)

/-- One operation raises the potential by at most its allowance, scaled. -/
theorem pot_step (hone : 0 < one) (s : State) (op : Op) (h : Inv one s) :
    pot one (step one s op) ≤ pot one s + allowance op * one := by
  have hu := inv_update h
  cases op with
  | emit x => simp only [step, allowance, pot, Nat.add_mul]; omega
  | update => simp only [step, allowance, Nat.zero_mul, Nat.add_zero]; exact pot_update s
  | deposit w x =>
    simp only [step, allowance]
    exact Nat.le_trans (pot_modify (s.update one) w _ _ (settle_terms hone hu (· + x)))
      (Nat.add_le_add_right (pot_update s) _)
  | withdraw w x =>
    simp only [step, allowance]
    split
    · exact Nat.le_trans (pot_modify (s.update one) w _ _ (settle_terms hone hu (· - x)))
        (Nat.add_le_add_right (pot_update s) _)
    · omega
  | harvest w =>
    simp only [step, allowance, Nat.zero_mul, Nat.add_zero]
    have := pot_modify (s.update one) w _ 0 (fun a ha => by
      simpa using term_harvest_le (one := one) (s.update one).index a (hu a ha))
    exact Nat.le_trans (by simpa using this) (pot_update s)

/-- One operation raises an account's potential by at most its allowance, scaled. -/
theorem potTo_step (hone : 0 < one) (s : State) (w : Nat) (op : Op) (h : Inv one s) :
    potTo one (step one s op) w ≤ potTo one s w + allowance op * one := by
  have hu := inv_update h
  cases op with
  | emit x =>
    have e : ({ s with unindexed := s.unindexed + x } : State).acct w = s.acct w := rfl
    simp only [step, allowance, potTo, term, e]
    split <;> (try simp only [Nat.add_mul]) <;> omega
  | update => simp only [step, allowance, Nat.zero_mul, Nat.add_zero]; exact potTo_update s w
  | deposit v x =>
    simp only [step, allowance]
    exact Nat.le_trans (potTo_modify (s.update one) v w _ _ rfl (settle_terms hone hu (· + x)))
      (Nat.add_le_add_right (potTo_update s w) _)
  | withdraw v x =>
    simp only [step, allowance]
    split
    · exact Nat.le_trans (potTo_modify (s.update one) v w _ _ rfl (settle_terms hone hu (· - x)))
        (Nat.add_le_add_right (potTo_update s w) _)
    · omega
  | harvest v =>
    simp only [step, allowance, Nat.zero_mul, Nat.add_zero]
    have := potTo_modify (s.update one) v w _ 0 rfl (fun a ha => by
      simpa using term_harvest_le (one := one) (s.update one).index a (hu a ha))
    exact Nat.le_trans (by simpa using this) (potTo_update s w)

/-- Rewards paid, scaled, are covered by the potential. -/
theorem paid_mul_le_pot (s : State) (h : Inv one s) : s.paid * one ≤ pot one s := by
  have := sum_mul_le_of_le s.accts Acct.paid (term one s.index) one (fun a ha => by
    have h1 := debtOf_mul_le one a.units s.index
    have h2 : a.debt * one ≤ debtOf one a.units s.index * one := Nat.mul_le_mul_right _ (h a ha)
    unfold term; omega)
  unfold pot State.paid
  omega

/-- Rewards paid to one account, scaled, are covered by its potential. -/
theorem paidTo_mul_le_potTo (s : State) (w : Nat) (h : Inv one s) :
    s.paidTo w * one ≤ potTo one s w := by
  have hd : (s.acct w).debt ≤ debtOf one (s.acct w).units s.index := by
    rcases Ledger.getD_mem_or s.accts w Acct.empty with hm | hm
    · exact h _ hm
    · unfold State.acct; rw [hm]; exact Nat.zero_le _
  have h1 := debtOf_mul_le one (s.acct w).units s.index
  have h2 : (s.acct w).debt * one ≤ debtOf one (s.acct w).units s.index * one :=
    Nat.mul_le_mul_right _ hd
  unfold potTo term State.paidTo
  omega

/-- The allowance of a run as a ghost accumulator without ghost state. -/
theorem allowed_eq_accum (ops : List Op) :
    allowed ops = Seq.accum (fun (_ : Unit) _ => ()) (fun _ op => allowance op) () ops :=
  (Seq.accum_const allowance () ops).symm

/-! ## The bounds -/

/-- Over any sequence of operations from a state with the invariant, the rewards paid never exceed
those paid at the start, plus those owed at the start, plus those emitted, plus one unit per deposit
or withdrawal. -/
theorem run_paid_le (hone : 0 < one) (s : State) (h : Inv one s) (ops : List Op) :
    (Seq.run (step one) s ops).paid ≤ s.paid + s.owed one + allowed ops := by
  have hs : pot one s ≤ (s.paid + s.unindexed) * one +
      (s.accts.map fun a => a.units * s.index - a.debt * one).sum := by
    have e := Ledger.sum_map_le_add s.accts (fun a => a.paid * one) (term one s.index)
      (fun a => a.units * s.index - a.debt * one) (fun a _ => by unfold term; omega)
    rw [Ledger.sum_map_mul_right] at e
    unfold pot State.paid
    rw [Nat.add_mul]
    omega
  have := Seq.run_bound_via_potential (fun (_ : Unit) t => Inv one t) (pot one) State.paid hone
    (next := fun _ _ => ()) (f := fun _ op => allowance op)
    (fun _ t op ht => inv_step t op ht) (fun _ t op ht => by rw [Nat.mul_comm one]; exact pot_step hone t op ht)
    (fun _ t ht => paid_mul_le_pot t ht) (g := ()) h hs ops
  rw [allowed_eq_accum]
  unfold State.owed
  omega

/-- The same bound for each account. -/
theorem run_paidTo_le (hone : 0 < one) (s : State) (h : Inv one s) (w : Nat) (ops : List Op) :
    (Seq.run (step one) s ops).paidTo w ≤ s.paidTo w + s.owedTo one w + allowed ops := by
  have hs : potTo one s w ≤ (s.paidTo w + (if 0 < (s.acct w).units then s.unindexed else 0)) * one +
      ((s.acct w).units * s.index - (s.acct w).debt * one) := by
    unfold potTo term State.paidTo
    split <;> simp only [Nat.add_mul, Nat.zero_mul] <;> omega
  have := Seq.run_bound_via_potential (fun (_ : Unit) t => Inv one t) (fun t => potTo one t w)
    (fun t => t.paidTo w) hone (next := fun _ _ => ()) (f := fun _ op => allowance op)
    (fun _ t op ht => inv_step t op ht)
    (fun _ t op ht => by rw [Nat.mul_comm one]; exact potTo_step hone t w op ht)
    (fun _ t ht => paidTo_mul_le_potTo t w ht) (g := ()) h hs ops
  rw [allowed_eq_accum]
  unfold State.owedTo
  omega

end Proofs

end ProofForgeFin.DeFi.Chef
