import ProofForgeFin.DeFi.Rewards
/-!
# A reward distributor and its bounds

A single-index reward distributor in the pattern of Synthetix's `StakingRewards`, Compound's
Comptroller (one side of one market) and MasterChef (one pool), with every interaction accruing
the index and settling the account before its stake changes. It is a reference model: a
protocol whose accounting is shown to follow it inherits its bounds, and its proofs show how the
lemmas of `ProofForgeFin.DeFi.Rewards` combine.

* The index (`State.index`, at scale `one`) grows by `indexDelta one unindexed total` when the
  distributor is brought up to date; rewards emitted over zero units are discarded, as Synthetix
  and Compound discard them.
* An account records its checkpoint; 0 means none is recorded, and such an account is owed from
  `init`, the value the index started from (`effStart`). An account that held a stake before
  rewards started is therefore owed nothing for the time before.
* Rewards credited to an account are `accrued` (not yet paid) plus `paid`.

The theorems, for every start state and every sequence of emissions, updates, stakes, unstakes
and claims:

* `run_credited_le`: rewards credited to all accounts never exceed those credited at the start
  plus those owed at the start (`State.owed`: pending rewards rounded down plus emission not yet
  indexed) plus those emitted since;
* `run_creditedTo_le`: the same for each account, with what it was owed at the start;
* `run_creditedTo_le_of_units_eq_zero`: an account without a stake gains at most what is emitted
  from then on (no backdated rewards);
* `owed_of_fresh`: when rewards have just started (index at `init`, every account settled or
  without a checkpoint), nothing but the unindexed emission is owed.
-/

namespace ProofForgeFin.DeFi.Distributor

open ProofForgeFin ProofForgeFin.DeFi.Rewards

/-- One account: its stake, its recorded checkpoint (0 for none), rewards accrued and not yet
paid, and rewards paid out. -/
structure Acct where
  /-- Units staked. -/
  units : Nat
  /-- The index recorded at the last settlement; 0 when none is recorded. -/
  checkpoint : Nat
  /-- Rewards credited and not yet paid. -/
  accrued : Nat
  /-- Rewards paid out. -/
  paid : Nat
  deriving DecidableEq, Repr

/-- The record of an account number beyond the list. -/
def Acct.empty : Acct := ⟨0, 0, 0, 0⟩

/-- Rewards credited to an account: accrued plus paid. -/
def Acct.credited (a : Acct) : Nat := a.accrued + a.paid

/-- The distributor: the index, rewards emitted and not yet in the index, and the accounts. -/
structure State where
  /-- The reward index, at scale `one`. -/
  index : Nat
  /-- Rewards emitted since the index was last brought up to date. -/
  unindexed : Nat
  /-- Accounts, numbered by position. -/
  accts : List Acct
  deriving DecidableEq, Repr

/-- The record of account `w`. -/
def State.acct (s : State) (w : Nat) : Acct := s.accts.getD w Acct.empty

/-- Units staked by all accounts. -/
def State.total (s : State) : Nat := (s.accts.map Acct.units).sum

/-- Rewards credited to all accounts. -/
def State.credited (s : State) : Nat := (s.accts.map Acct.credited).sum

/-- Rewards credited to account `w`. -/
def State.creditedTo (s : State) (w : Nat) : Nat := (s.acct w).credited

section Model

variable (one init : Nat)

/-- The index brought up to date: the unindexed emission is spread over the units staked. -/
def State.update (s : State) : State :=
  { s with index := s.index + indexDelta one s.unindexed s.total, unindexed := 0 }

/-- An account settled at `index`: credited from its effective start, rounded down, with the
index recorded. -/
def settle (index : Nat) (a : Acct) : Acct :=
  { a with accrued := a.accrued + credit one a.units (effStart init a.checkpoint) index,
           checkpoint := index }

/-- Operations on the distributor.
* `emit x`: `x` rewards are emitted (time passes at the reward rate).
* `update`: the index is brought up to date (`updatePool`, `updateReward(address(0))`).
* `stake w x`, `unstake w x`: account `w` stakes or unstakes `x` units, after the update and its
  settlement.
* `claim w`: account `w` is settled and paid everything it has accrued. -/
inductive Op where
  /-- `x` rewards are emitted. -/
  | emit (x : Nat)
  /-- The index is brought up to date. -/
  | update
  /-- Account `w` stakes `x` units. -/
  | stake (w x : Nat)
  /-- Account `w` unstakes `x` units; refused above its stake. -/
  | unstake (w x : Nat)
  /-- Account `w` claims. -/
  | claim (w : Nat)
  deriving DecidableEq, Repr

/-- One operation. An unstake above the stake is refused and changes nothing. Operations naming
an account beyond the list change only the index. -/
def step (s : State) : Op → State
  | .emit x => { s with unindexed := s.unindexed + x }
  | .update => s.update one
  | .stake w x =>
    { s.update one with accts := (s.update one).accts.modify w fun a =>
        { settle one init (s.update one).index a with units := a.units + x } }
  | .unstake w x =>
    if x ≤ (s.acct w).units then
      { s.update one with accts := (s.update one).accts.modify w fun a =>
          { settle one init (s.update one).index a with units := a.units - x } }
    else s
  | .claim w =>
    { s.update one with accts := (s.update one).accts.modify w fun a =>
        { settle one init (s.update one).index a with
            accrued := 0,
            paid := (settle one init (s.update one).index a).paid +
              (settle one init (s.update one).index a).accrued } }

/-- Rewards emitted by an operation. -/
def emittedBy : Op → Nat
  | .emit x => x
  | _ => 0

/-- Rewards emitted by a sequence of operations. -/
def emitted (ops : List Op) : Nat := (ops.map emittedBy).sum

/-- Rewards owed at a state: every account's pending rewards, rounded down once, plus the
emission not yet in the index. -/
def State.owed (s : State) : Nat :=
  (s.accts.map fun a => pending a.units (effStart init a.checkpoint) s.index).sum / one +
    s.unindexed

/-- Rewards owed to account `w`: its pending rewards, rounded down, plus the emission not yet in
the index while it holds a stake. -/
def State.owedTo (s : State) (w : Nat) : Nat :=
  pending (s.acct w).units (effStart init (s.acct w).checkpoint) s.index / one +
    (if 0 < (s.acct w).units then s.unindexed else 0)

/-! ## The potentials -/

/-- The potential term of an account at the index of `s`: rewards credited, scaled, plus rewards
pending. -/
def term (s : State) (a : Acct) : Nat :=
  a.credited * one + pending a.units (effStart init a.checkpoint) s.index

/-- The potential: every account's term plus the scaled unindexed emission. -/
def pot (s : State) : Nat := (s.accts.map (term one init s)).sum + s.unindexed * one

/-- The potential of account `w`: its term plus the scaled unindexed emission while it holds a
stake. -/
def potTo (s : State) (w : Nat) : Nat :=
  term one init s (s.acct w) + (if 0 < (s.acct w).units then s.unindexed * one else 0)

end Model

/-! ## Facts about the records -/

/-- Reading an account after modifying one. -/
theorem acct_modify (s : State) (i w : Nat) (f : Acct → Acct) :
    ({ s with accts := s.accts.modify i f } : State).acct w =
      if i = w ∧ w < s.accts.length then f (s.acct w) else s.acct w :=
  Ledger.getD_modify _ _ _ _ _

/-- The update does not touch the accounts. -/
@[simp] theorem update_accts (one : Nat) (s : State) : (s.update one).accts = s.accts := rfl

/-- The update does not touch the accounts. -/
@[simp] theorem update_acct (one : Nat) (s : State) (w : Nat) : (s.update one).acct w = s.acct w :=
  rfl

/-- After the update nothing is unindexed. -/
@[simp] theorem update_unindexed (one : Nat) (s : State) : (s.update one).unindexed = 0 := rfl

/-- The empty record holds nothing. -/
theorem acct_mem_or (s : State) (w : Nat) : s.acct w ∈ s.accts ∨ s.acct w = Acct.empty :=
  Ledger.getD_mem_or _ _ _

/-- An account holds at most the total. -/
theorem units_le_total (s : State) (w : Nat) : (s.acct w).units ≤ s.total :=
  Ledger.getD_le_sum_map _ _ _ _ rfl

section Proofs

variable {one init : Nat}

/-- Each term grows with the update by at most the account's units times the increment. -/
theorem term_update_le (s : State) (a : Acct) :
    term one init (s.update one) a ≤
      term one init s a + a.units * indexDelta one s.unindexed s.total := by
  have := pending_le_add a.units (effStart init a.checkpoint)
    (Nat.le_add_right s.index (indexDelta one s.unindexed s.total))
  unfold term State.update
  simp only [Nat.add_sub_cancel_left] at this ⊢
  omega

/-- The update does not raise the potential. -/
theorem pot_update (s : State) : pot one init (s.update one) ≤ pot one init s := by
  have h := sum_le_of_index_le s.accts (term one init s) (term one init (s.update one)) Acct.units
    (fun a _ => term_update_le s a) (total_mul_indexDelta_le one s.unindexed s.total)
  unfold pot
  simp only [update_accts, update_unindexed, Nat.zero_mul, Nat.add_zero]
  exact h

/-- The update does not raise an account's potential. -/
theorem potTo_update (s : State) (w : Nat) : potTo one init (s.update one) w ≤ potTo one init s w := by
  have h1 := term_update_le (one := one) (init := init) s (s.acct w)
  have h2 := units_mul_le_ite (units_le_total s w)
    (total_mul_indexDelta_le one s.unindexed s.total)
  unfold potTo
  simp only [update_acct, update_unindexed, Nat.zero_mul, ite_self, Nat.add_zero]
  omega

/-- A settlement at the index does not raise the term: `b` is `a` credited from its effective
start and checkpointed at the index, with any stake. -/
theorem term_le_of_settled (s : State) {a b : Acct}
    (hc : b.credited = a.credited + credit one a.units (effStart init a.checkpoint) s.index)
    (hk : b.checkpoint = s.index) : term one init s b ≤ term one init s a := by
  unfold term
  rw [hk, pending_effStart_self, Nat.add_zero]
  exact settle_le_self hc (Nat.le_refl _)

/-- Changing one account by a change that does not raise its term does not raise the potential;
an account's own potential is not raised when the change does not raise its term and when nothing
is unindexed. -/
theorem pot_modify (s : State) (i : Nat) (f : Acct → Acct)
    (hf : ∀ a, term one init s (f a) ≤ term one init s a) :
    pot one init { s with accts := s.accts.modify i f } ≤ pot one init s := by
  unfold pot
  have := Ledger.sum_map_modify_le s.accts i f (term one init s) Acct.empty (fun _ => hf _)
  exact Nat.add_le_add_right this _

/-- The per-account form of `pot_modify`, after an update (nothing unindexed). -/
theorem potTo_modify (s : State) (i w : Nat) (f : Acct → Acct) (h0 : s.unindexed = 0)
    (hf : ∀ a, term one init s (f a) ≤ term one init s a) :
    potTo one init { s with accts := s.accts.modify i f } w ≤ potTo one init s w := by
  unfold potTo
  rw [acct_modify, h0]
  simp only [Nat.zero_mul, ite_self, Nat.add_zero]
  split
  · exact hf _
  · exact Nat.le_refl _

/-- One operation raises the potential by at most the scaled emission. -/
theorem pot_step (s : State) (op : Op) :
    pot one init (step one init s op) ≤ pot one init s + emittedBy op * one := by
  cases op with
  | emit x =>
    simp only [step, emittedBy, pot, Nat.add_mul]
    exact Nat.le_of_eq (by rw [Nat.add_assoc]; rfl)
  | update => simp only [step, emittedBy, Nat.zero_mul, Nat.add_zero]; exact pot_update s
  | stake w x =>
    simp only [step, emittedBy, Nat.zero_mul, Nat.add_zero]
    exact Nat.le_trans (pot_modify _ _ _ fun _ => term_le_of_settled _ (by simp only [settle, Acct.credited]; omega) rfl) (pot_update s)
  | unstake w x =>
    simp only [step, emittedBy, Nat.zero_mul, Nat.add_zero]
    split
    · exact Nat.le_trans (pot_modify _ _ _ fun _ => term_le_of_settled _ (by simp only [settle, Acct.credited]; omega) rfl) (pot_update s)
    · exact Nat.le_refl _
  | claim w =>
    simp only [step, emittedBy, Nat.zero_mul, Nat.add_zero]
    exact Nat.le_trans (pot_modify _ _ _ fun _ => term_le_of_settled _ (by simp only [settle, Acct.credited]; omega) rfl) (pot_update s)

/-- One operation raises an account's potential by at most the scaled emission. -/
theorem potTo_step (s : State) (w : Nat) (op : Op) :
    potTo one init (step one init s op) w ≤ potTo one init s w + emittedBy op * one := by
  cases op with
  | emit x =>
    have e : ({ s with unindexed := s.unindexed + x } : State).acct w = s.acct w := rfl
    simp only [step, emittedBy, potTo, term, e]
    split <;> (try simp only [Nat.add_mul]) <;> omega
  | update => simp only [step, emittedBy, Nat.zero_mul, Nat.add_zero]; exact potTo_update s w
  | stake v x =>
    simp only [step, emittedBy, Nat.zero_mul, Nat.add_zero]
    exact Nat.le_trans (potTo_modify _ _ _ _ rfl fun _ => term_le_of_settled _ (by simp only [settle, Acct.credited]; omega) rfl) (potTo_update s w)
  | unstake v x =>
    simp only [step, emittedBy, Nat.zero_mul, Nat.add_zero]
    split
    · exact Nat.le_trans (potTo_modify _ _ _ _ rfl fun _ => term_le_of_settled _ (by simp only [settle, Acct.credited]; omega) rfl)
        (potTo_update s w)
    · exact Nat.le_refl _
  | claim v =>
    simp only [step, emittedBy, Nat.zero_mul, Nat.add_zero]
    exact Nat.le_trans (potTo_modify _ _ _ _ rfl fun _ => term_le_of_settled _ (by simp only [settle, Acct.credited]; omega) rfl) (potTo_update s w)

/-- Rewards credited, scaled, are covered by the potential. -/
theorem credited_mul_le_pot (s : State) : s.credited * one ≤ pot one init s := by
  have := sum_mul_le_of_le s.accts Acct.credited (term one init s) one (fun a _ => by
    unfold term; omega)
  unfold pot State.credited
  omega

/-- An account's rewards credited, scaled, are covered by its potential. -/
theorem creditedTo_mul_le_potTo (s : State) (w : Nat) : s.creditedTo w * one ≤ potTo one init s w := by
  unfold potTo term State.creditedTo
  omega

/-- The emission of a run as a ghost accumulator without ghost state. -/
theorem emitted_eq_accum (ops : List Op) :
    emitted ops = Seq.accum (fun (_ : Unit) _ => ()) (fun _ op => emittedBy op) () ops :=
  (Seq.accum_const emittedBy () ops).symm

/-- The sequence bound for any potential that one operation raises by at most the scaled
emission and that covers the quantity `Q` at scale `one`. -/
theorem run_le_of_pot (hone : 0 < one) (P Q : State → Nat)
    (hP : ∀ s op, P (step one init s op) ≤ P s + emittedBy op * one)
    (hQ : ∀ s, Q s * one ≤ P s) (s : State) {B R : Nat} (hstart : P s ≤ B * one + R)
    (ops : List Op) : Q (Seq.run (step one init) s ops) ≤ B + emitted ops + R / one := by
  rw [emitted_eq_accum]
  exact Seq.run_bound_via_potential (fun (_ : Unit) _ => True) P Q hone (fun _ _ _ _ => trivial)
    (fun _ s op _ => by rw [Nat.mul_comm one]; exact hP s op) (fun _ s _ => hQ s) trivial hstart ops

/-! ## The bounds -/

/-- Rewards credited to all accounts, after any sequence of operations, never exceed those
credited at the start plus those owed at the start plus those emitted since. -/
theorem run_credited_le (hone : 0 < one) (s : State) (ops : List Op) :
    (Seq.run (step one init) s ops).credited ≤ s.credited + s.owed one init + emitted ops := by
  have h := run_le_of_pot hone (pot one init) State.credited pot_step credited_mul_le_pot s
    (B := s.credited + s.unindexed)
    (R := (s.accts.map fun a => pending a.units (effStart init a.checkpoint) s.index).sum)
    (by
      have := Ledger.sum_map_le_add s.accts (fun a => a.credited * one)
        (term one init s) (fun a => pending a.units (effStart init a.checkpoint) s.index)
        (fun a _ => Nat.le_refl _)
      rw [Ledger.sum_map_mul_right] at this
      unfold pot State.credited
      rw [Nat.add_mul]
      omega) ops
  unfold State.owed
  omega

/-- Rewards credited to one account, after any sequence of operations, never exceed those
credited to it at the start plus those owed to it at the start plus those emitted since. -/
theorem run_creditedTo_le (hone : 0 < one) (s : State) (w : Nat) (ops : List Op) :
    (Seq.run (step one init) s ops).creditedTo w ≤
      s.creditedTo w + s.owedTo one init w + emitted ops := by
  have h := run_le_of_pot hone (fun t => potTo one init t w) (fun t => t.creditedTo w)
    (fun t op => potTo_step t w op) (fun t => creditedTo_mul_le_potTo t w) s
    (B := s.creditedTo w + (if 0 < (s.acct w).units then s.unindexed else 0))
    (R := pending (s.acct w).units (effStart init (s.acct w).checkpoint) s.index)
    (by
      unfold potTo term State.creditedTo
      split <;> simp only [Nat.add_mul, Nat.zero_mul] <;> omega) ops
  unfold State.owedTo
  omega

/-- No backdated rewards: an account without a stake gains, over any sequence of operations, at
most the rewards emitted during it. -/
theorem run_creditedTo_le_of_units_eq_zero (hone : 0 < one) (s : State) (w : Nat)
    (h0 : (s.acct w).units = 0) (ops : List Op) :
    (Seq.run (step one init) s ops).creditedTo w ≤ s.creditedTo w + emitted ops := by
  have := run_creditedTo_le (init := init) hone s w ops
  unfold State.owedTo at this
  rw [h0] at this
  simpa using this

/-- When rewards have just started (the index at `init`, every account settled at it or without
a checkpoint), nothing is owed but the unindexed emission: accounts that held a stake before
rewards started are owed nothing for the time before. -/
theorem owed_of_fresh (s : State) (hi : s.index = init)
    (ha : ∀ a ∈ s.accts, a.checkpoint = 0 ∨ a.checkpoint = s.index) :
    s.owed one init = s.unindexed := by
  have : (s.accts.map fun a => pending a.units (effStart init a.checkpoint) s.index).sum = 0 := by
    rw [Ledger.sum_map_congr s.accts (g := fun _ => 0) (fun a hm => by
      rcases ha a hm with h | h
      · rw [h, effStart_zero, ← hi, pending_self]
      · rw [h, pending_effStart_self])]
    generalize s.accts = l
    induction l <;> simp_all
  unfold State.owed
  rw [this, Nat.zero_div, Nat.zero_add]

end Proofs

end ProofForgeFin.DeFi.Distributor
