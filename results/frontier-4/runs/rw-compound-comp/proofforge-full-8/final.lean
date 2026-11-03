import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
/-!
Fixed COMP distribution of Compound's Comptroller (Proposal 62, corrected by Proposal 64).

The deployed Proposal 62 code credited an account with no recorded index from 0 whenever the
market index was strictly above `compInitialIndex`
(`supplierIndex == 0 && supplyIndex > compInitialIndex`). When the upgrade initialized an index
that was still 0 to exactly `compInitialIndex`, such an account was credited `units` of COMP
that were never emitted. The fix uses the Proposal 64 condition (`>=`): an account with no
recorded index starts accruing from `compInitialIndex` once the market index has reached it,
which is exactly `accrualStart` of the specification.

Each call is written in the specification's closed form (`accrueSide`, `accrualStart`,
`creditFor`, `grant`), so the effect requirements hold by case analysis on the preconditions.
-/
namespace CompRewards

/-- Next state of a supply hook, in the specification's closed form. -/
def supplyNext (s : St) (who : Account) : St :=
  { s with
    supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
    accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }

/-- Next state of a borrow hook, in the specification's closed form. -/
def borrowNext (s : St) (who : Account) : St :=
  { s with
    borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
    accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }

/-- Next state of a speed change, in the specification's closed form. -/
def speedsNext (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }

/-- Preconditions of a supply hook (the two `sub_` underflow guards). -/
def supplyPre (s : St) (who : Account) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index

/-- Preconditions of a borrow hook. -/
def borrowPre (s : St) (who : Account) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index

instance supplyPreDec (s : St) (who : Account) : Decidable (supplyPre s who) := by
  unfold supplyPre; infer_instance

instance borrowPreDec (s : St) (who : Account) : Decidable (borrowPre s who) := by
  unfold borrowPre; infer_instance

/-- Fixed Comptroller: each call in the specification's closed form. -/
def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who =>
    if supplyPre s who then some (supplyNext s who) else none
  | .borrowHook who =>
    if borrowPre s who then some (borrowNext s who) else none
  | .claim who =>
    if borrowPre s who ∧ supplyPre (borrowNext s who) who then
      some (grant (supplyNext (borrowNext s who) who) who)
    else none
  | .setSpeeds a b =>
    if (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
       (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber)
    then some (speedsNext s a b) else none

theorem supplyHook_eq (s : St) (who : Account) :
    comptroller s (.supplyHook who) =
      if supplyPre s who then some (supplyNext s who) else none := rfl

theorem borrowHook_eq (s : St) (who : Account) :
    comptroller s (.borrowHook who) =
      if borrowPre s who then some (borrowNext s who) else none := rfl

theorem claim_eq (s : St) (who : Account) :
    comptroller s (.claim who) =
      if borrowPre s who ∧ supplyPre (borrowNext s who) who then
        some (grant (supplyNext (borrowNext s who) who) who)
      else none := rfl

theorem setSpeeds_eq (s : St) (a b : Nat) :
    comptroller s (.setSpeeds a b) =
      if (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
         (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber)
      then some (speedsNext s a b) else none := rfl

/-- The index update of the specification is the library's `catchUp`. -/
theorem accrue_index (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

/-- The index update never lowers the index. -/
theorem accrue_index_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  rw [accrue_index]
  exact ProofForgeFin.Accumulator.le_catchUp _ _ _ _ _ _

/-- An account's accrual start never lies above the index once its recorded index does not lie
above the index the market had. -/
theorem accrualStart_le (recorded index oldIndex : Nat) (hrec : recorded ≤ oldIndex)
    (hidx : oldIndex ≤ index) : accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp only [hr, ite_true]
    split <;> omega
  · simp only [hr, ite_false]
    omega

/-- A borrow hook keeps every supply field: totals, sides, blocks and recorded supply indices. -/
theorem totalSupply_borrowNext (s : St) (who : Account) :
    totalSupply (borrowNext s who) = totalSupply s := by
  unfold borrowNext totalSupply
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (fun _ => rfl)

theorem borrowNext_supplyState (s : St) (who : Account) :
    (borrowNext s who).supplyState = s.supplyState := rfl

theorem borrowNext_blockNumber (s : St) (who : Account) :
    (borrowNext s who).blockNumber = s.blockNumber := rfl

theorem borrowNext_supplierIndex (s : St) (who : Account) :
    ((borrowNext s who).acct who).supplierIndex = ((s.acct who)).supplierIndex :=
  ProofForgeFin.Ledger.getD_modify_of_keeps s.accts who who noAcct
    (fun a : Acct => a.supplierIndex) (fun _ => rfl)

/-- A supply hook keeps every borrow field. -/
theorem totalBorrows_supplyNext (s : St) (who : Account) :
    totalBorrows (supplyNext s who) = totalBorrows s := by
  unfold supplyNext totalBorrows
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (fun _ => rfl)

/-- A supply hook succeeds from the block bound and a recorded index at or below the market's. -/
theorem supplyPre_of (s : St) (who : Account) (hblock : s.supplyState.block ≤ s.blockNumber)
    (hrec : (s.acct who).supplierIndex ≤ s.supplyState.index) : supplyPre s who := by
  refine ⟨hblock, ?_⟩
  exact accrualStart_le _ _ _ hrec
    (accrue_index_le s.supplyState s.blockNumber (totalSupply s))

/-- A borrow hook succeeds from the block bound and a recorded index at or below the market's. -/
theorem borrowPre_of (s : St) (who : Account) (hblock : s.borrowState.block ≤ s.blockNumber)
    (hrec : (s.acct who).borrowerIndex ≤ s.borrowState.index) : borrowPre s who := by
  refine ⟨hblock, ?_⟩
  exact accrualStart_le _ _ _ hrec
    (accrue_index_le s.borrowState s.blockNumber (totalBorrows s))

/-- A recorded index read at any position lies at or below the market index in a consistent
state. -/
theorem rec_le_of_Consistent (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
    (s.acct who).borrowerIndex ≤ s.borrowState.index :=
  ProofForgeFin.Ledger.getD_of_forall s.accts who hc.2.2 ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem supplyPre_of_Consistent (s : St) (who : Account) (hc : Consistent s) :
    supplyPre s who :=
  supplyPre_of s who hc.1 (rec_le_of_Consistent s who hc).1

theorem borrowPre_of_Consistent (s : St) (who : Account) (hc : Consistent s) :
    borrowPre s who :=
  borrowPre_of s who hc.2.1 (rec_le_of_Consistent s who hc).2

/-- The supply preconditions also hold after the borrow half of a claim. -/
theorem supplyPre_borrowNext (s : St) (who : Account) (hc : Consistent s) :
    supplyPre (borrowNext s who) who := by
  unfold supplyPre
  rw [borrowNext_supplyState, borrowNext_blockNumber]
  refine ⟨hc.1, ?_⟩
  rw [borrowNext_supplierIndex, totalSupply_borrowNext]
  exact (supplyPre_of_Consistent s who hc).2

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    rw [supplyHook_eq]
    simp [supplyPre_of_Consistent s who hc]
  | borrowHook who =>
    rw [borrowHook_eq]
    simp [borrowPre_of_Consistent s who hc]
  | claim who =>
    rw [claim_eq]
    simp [borrowPre_of_Consistent s who hc, supplyPre_borrowNext s who hc]
  | setSpeeds a b =>
    have hpre : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
        (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) :=
      ⟨fun _ => hc.1, fun _ => hc.2.1⟩
    rw [setSpeeds_eq, if_pos hpre, Option.isSome_some]

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  rw [supplyHook_eq] at h
  by_cases hc : supplyPre s who
  · rw [if_pos hc] at h
    injection h with h'
    subst h'
    exact ⟨hc.1, hc.2, rfl⟩
  · rw [if_neg hc] at h
    injection h

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  rw [borrowHook_eq] at h
  by_cases hc : borrowPre s who
  · rw [if_pos hc] at h
    injection h with h'
    subst h'
    exact ⟨hc.1, hc.2, rfl⟩
  · rw [if_neg hc] at h
    injection h

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  rw [claim_eq] at h
  by_cases hc : borrowPre s who ∧ supplyPre (borrowNext s who) who
  · rw [if_pos hc] at h
    injection h with h'
    subst h'
    exact ⟨borrowNext s who, supplyNext (borrowNext s who) who,
      ⟨hc.1.1, hc.1.2, rfl⟩, ⟨hc.2.1, hc.2.2, rfl⟩, rfl⟩
  · rw [if_neg hc] at h
    injection h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  rw [setSpeeds_eq] at h
  by_cases hc : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
      (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber)
  · rw [if_pos hc] at h
    injection h with h'
    subst h'
    exact ⟨hc.1, hc.2, rfl⟩
  · rw [if_neg hc] at h
    injection h

/-! ## Reading the state as a two-sided reward market -/

/-- The market reading: supply side 1, borrow side 2, at index scale `doubleScale`. -/
def M : ProofForgeFin.Accumulator.Market St Acct where
  one := doubleScale
  init := compInitialIndex
  clock s := ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed,
    s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩
  accts s := s.accts
  dflt := noAcct
  units₁ a := a.supply
  units₂ a := a.borrow
  rec₁ a := a.supplierIndex
  rec₂ a := a.borrowerIndex
  credited a := a.accrued + a.wallet
  dflt_units₁ := rfl
  dflt_units₂ := rfl

/-- The legacy clock before the upgrade. -/
def cL (L : Legacy) : ProofForgeFin.Accumulator.Clock :=
  ⟨L.blockNumber, L.supplyIndex, L.supplyBlock, L.compSpeed,
    L.borrowIndex, L.borrowBlock, L.compSpeed⟩

theorem one_eq : M.one = doubleScale := rfl
theorem total₁_eq (s : St) : M.total₁ s = totalSupply s := rfl
theorem total₂_eq (s : St) : M.total₂ s = totalBorrows s := rfl
theorem creditSum_eq (s : St) : M.creditSum s = s.credited := rfl
theorem acct_eq (s : St) (w : Nat) : M.acct s w = s.acct w := rfl
theorem creditedTo_eq (s : St) (w : Nat) :
    M.credited (M.acct s w) = s.creditedTo w := rfl

/-- What an account is owed in the market reading is the legacy pending amount. -/
theorem owed_eq (L : Legacy) (a : Acct) :
    M.owed L.supplyStart L.borrowStart (cL L) a = L.pendingScaled a := rfl

theorem un₁_eq (L : Legacy) : (cL L).un₁ = L.unindexedSupply := rfl
theorem un₂_eq (L : Legacy) : (cL L).un₂ = L.unindexedBorrow := rfl

theorem accrue_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide; split <;> rfl

theorem accrue_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide; split <;> rfl

theorem totalSupply_supplyNext (s : St) (who : Account) :
    totalSupply (supplyNext s who) = totalSupply s := by
  unfold supplyNext totalSupply
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (fun _ => rfl)

theorem totalBorrows_borrowNext (s : St) (who : Account) :
    totalBorrows (borrowNext s who) = totalBorrows s := by
  unfold borrowNext totalBorrows
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (fun _ => rfl)

/-- Accruing twice at the same block accrues once: the second update moves nothing. -/
theorem accrue_accrue_index (sd : Side) (now total total' : Nat) :
    (accrueSide (accrueSide sd now total) now total').index =
      (accrueSide sd now total).index := by
  generalize hy : accrueSide sd now total = Y
  have hY : Y.block = now := by rw [← hy]; exact accrue_block _ _ _
  unfold accrueSide
  rw [hY]
  simp

/-- The market invariant gives consistency. -/
theorem Consistent_of_Inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St}
    (hI : M.Inv g₁ g₂ sp s) : Consistent s := by
  obtain ⟨hl1, hl2, hrec, -, -, -, -⟩ := hI
  exact ⟨hl1, hl2, hrec⟩

/-- A supply hook settles the account on side 1. -/
theorem settle₁ (s : St) (who : Account) : M.Settle₁ who s (supplyNext s who) :=
  ⟨by
    have h1 : M.clock (supplyNext s who) =
        ProofForgeFin.Accumulator.Clock.mk s.blockNumber
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).block
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed
          s.borrowState.index s.borrowState.block s.borrowState.speed := rfl
    have h2 : (M.clock s).catchUp₁ M.one (M.total₁ s) =
        ProofForgeFin.Accumulator.Clock.mk s.blockNumber
          (ProofForgeFin.Accumulator.catchUp M.one s.supplyState.index s.supplyState.block
            s.supplyState.speed s.blockNumber (M.total₁ s))
          s.blockNumber s.supplyState.speed
          s.borrowState.index s.borrowState.block s.borrowState.speed := by
      show (ProofForgeFin.Accumulator.Clock.mk s.blockNumber s.supplyState.index
        s.supplyState.block s.supplyState.speed s.borrowState.index s.borrowState.block
        s.borrowState.speed).catchUp₁ M.one (M.total₁ s) = _
      rw [ProofForgeFin.Accumulator.Clock.catchUp₁_mk]
    rw [h1, h2, accrue_index, accrue_block, accrue_speed, one_eq, total₁_eq],
  (fun a =>
    { a with
      supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
      accrued := a.accrued + creditFor a.supply
        (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }),
  rfl,
  fun a => ⟨rfl, rfl, rfl, rfl, Nat.le_of_eq (Nat.add_right_comm _ _ _)⟩⟩

/-- A borrow hook settles the account on side 2. -/
theorem settle₂ (s : St) (who : Account) : M.Settle₂ who s (borrowNext s who) :=
  ⟨by
    have h1 : M.clock (borrowNext s who) =
        ProofForgeFin.Accumulator.Clock.mk s.blockNumber
          s.supplyState.index s.supplyState.block s.supplyState.speed
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed := rfl
    have h2 : (M.clock s).catchUp₂ M.one (M.total₂ s) =
        ProofForgeFin.Accumulator.Clock.mk s.blockNumber
          s.supplyState.index s.supplyState.block s.supplyState.speed
          (ProofForgeFin.Accumulator.catchUp M.one s.borrowState.index s.borrowState.block
            s.borrowState.speed s.blockNumber (M.total₂ s))
          s.blockNumber s.borrowState.speed := by
      show (ProofForgeFin.Accumulator.Clock.mk s.blockNumber s.supplyState.index
        s.supplyState.block s.supplyState.speed s.borrowState.index s.borrowState.block
        s.borrowState.speed).catchUp₂ M.one (M.total₂ s) = _
      rw [ProofForgeFin.Accumulator.Clock.catchUp₂_mk]
    rw [h1, h2, accrue_index, accrue_block, accrue_speed, one_eq, total₂_eq],
  (fun a =>
    { a with
      borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
      accrued := a.accrued + creditFor a.borrow
        (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }),
  rfl,
  fun a => ⟨rfl, rfl, rfl, rfl, Nat.le_of_eq (Nat.add_right_comm _ _ _)⟩⟩

/-! ## Every operation is a market action -/

open ProofForgeFin.Accumulator

theorem supplyHook_some (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who : Account)
    (hI : M.Inv g₁ g₂ sp s) :
    comptroller s (.supplyHook who) = some (supplyNext s who) := by
  rw [supplyHook_eq, if_pos (supplyPre_of_Consistent s who (Consistent_of_Inv hI))]

theorem borrowHook_some (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who : Account)
    (hI : M.Inv g₁ g₂ sp s) :
    comptroller s (.borrowHook who) = some (borrowNext s who) := by
  rw [borrowHook_eq, if_pos (borrowPre_of_Consistent s who (Consistent_of_Inv hI))]

theorem rec_le_of_Inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St}
    (hI : M.Inv g₁ g₂ sp s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
    (s.acct who).borrowerIndex ≤ s.borrowState.index :=
  ProofForgeFin.Ledger.getD_of_forall s.accts who hI.recs ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- The supply preconditions also hold after another account's supply settlement. -/
theorem supplyPre_supplyNext_of_ne (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St)
    (src dst : Account) (hne : src ≠ dst) (hI : M.Inv g₁ g₂ sp s) :
    supplyPre (supplyNext s src) dst := by
  have hT : totalSupply (supplyNext s src) = totalSupply s := totalSupply_supplyNext _ _
  have hacct : ((supplyNext s src).acct dst).supplierIndex =
      ((s.acct dst)).supplierIndex := by
    show (((s.accts.modify src (fun a => { a with
      supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
      accrued := a.accrued + creditFor a.supply
        (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index })).getD dst
      noAcct)).supplierIndex = _
    rw [ProofForgeFin.Ledger.getD_modify_ne _ _ _ hne]
    rfl
  have hidx : (accrueSide (supplyNext s src).supplyState (supplyNext s src).blockNumber
      (totalSupply (supplyNext s src))).index =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    have hY : (supplyNext s src).supplyState =
        accrueSide s.supplyState s.blockNumber (totalSupply s) := rfl
    have hN : (supplyNext s src).blockNumber = s.blockNumber := rfl
    rw [hY, hN, hT]
    exact accrue_accrue_index _ _ _ _
  have hblock : (supplyNext s src).supplyState.block ≤ (supplyNext s src).blockNumber := by
    have hb : ((supplyNext s src).supplyState).block = s.blockNumber := accrue_block _ _ _
    have hn : (supplyNext s src).blockNumber = s.blockNumber := rfl
    rw [hb, hn]
    exact Nat.le_refl _
  unfold supplyPre
  rw [hidx]
  refine ⟨hblock, ?_⟩
  rw [hacct]
  exact accrualStart_le _ _ _ (rec_le_of_Inv hI dst).1
    (accrue_index_le s.supplyState s.blockNumber (totalSupply s))

theorem speedsNext_rate₁ (s : St) (a b : Nat) :
    (M.clock (speedsNext s a b)).rate₁ = a := by
  show (speedsNext s a b).supplyState.speed = a
  unfold speedsNext
  by_cases hsup : s.supplyState.speed = a <;> simp [hsup]

theorem speedsNext_rate₂ (s : St) (a b : Nat) :
    (M.clock (speedsNext s a b)).rate₂ = b := by
  show (speedsNext s a b).borrowState.speed = b
  unfold speedsNext
  by_cases hbor : s.borrowState.speed = b <;> simp [hbor]

/-- A speed change retunes the market. -/
theorem retune_speeds (s : St) (a b : Nat) : M.Retune s (speedsNext s a b) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · by_cases hsup : s.supplyState.speed = a
    · have e : (speedsNext s a b).supplyState = s.supplyState := by
        unfold speedsNext; simp [hsup]
      exact Or.inl ⟨by show (speedsNext s a b).supplyState.index = _; rw [e]; rfl,
        by show (speedsNext s a b).supplyState.block = _; rw [e]; rfl,
        by show (speedsNext s a b).supplyState.speed = _; rw [e]; rfl⟩
    · have e : (speedsNext s a b).supplyState =
          { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } := by
        unfold speedsNext; simp [hsup]
      refine Or.inr ⟨?_, ?_⟩
      · show (speedsNext s a b).supplyState.index = _
        rw [e]
        show (accrueSide s.supplyState s.blockNumber (totalSupply s)).index = _
        rw [accrue_index, one_eq, total₁_eq]
        rfl
      · show (speedsNext s a b).supplyState.block = _
        rw [e]
        show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = _
        rw [accrue_block]
        rfl
  · by_cases hbor : s.borrowState.speed = b
    · have e : (speedsNext s a b).borrowState = s.borrowState := by
        unfold speedsNext; simp [hbor]
      exact Or.inl ⟨by show (speedsNext s a b).borrowState.index = _; rw [e]; rfl,
        by show (speedsNext s a b).borrowState.block = _; rw [e]; rfl,
        by show (speedsNext s a b).borrowState.speed = _; rw [e]; rfl⟩
    · have e : (speedsNext s a b).borrowState =
          { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } := by
        unfold speedsNext; simp [hbor]
      refine Or.inr ⟨?_, ?_⟩
      · show (speedsNext s a b).borrowState.index = _
        rw [e]
        show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index = _
        rw [accrue_index, one_eq, total₂_eq]
        rfl
      · show (speedsNext s a b).borrowState.block = _
        rw [e]
        show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = _
        rw [accrue_block]
        rfl

/-- A payment is an adjustment: it moves accrued COMP to the wallet, keeping every total. -/
theorem grant_adjust (s : St) (who : Account)
    (hg : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    M.Adjust who s (grant s who) := by
  unfold grant
  rw [if_pos hg]
  refine ⟨rfl, (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }), rfl,
    ?_, .inl (fun _ => rfl), .inl (fun _ => rfl)⟩
  intro a
  exact ⟨by show (0 : Nat) + (a.wallet + a.accrued) ≤ a.accrued + a.wallet; omega,
    rfl, rfl⟩

/-- A payment that pays nothing is a silent step. -/
theorem grant_same (s : St) (who : Account)
    (hg : ¬ (0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve)) :
    M.Step s (grant s who) := by
  have hgrant : grant s who = s := by unfold grant; rw [if_neg hg]
  rw [hgrant]
  exact .same rfl rfl

theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (op : Op)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  cases op with
  | mint who x =>
    by_cases hwho : who < s.accts.length
    · have hhook := supplyHook_some g₁ g₂ sp s who hI
      have hexec : exec comptroller s (.mint who x) =
          (supplyNext s who).withAcct who fun a => { a with supply := a.supply + x } := by
        simp only [exec]
        rw [if_pos hwho, hhook]
      rw [hexec]
      exact .moves (Market.Settle₁.then_adjust (settle₁ s who) rfl rfl
        (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
    · have hexec : exec comptroller s (.mint who x) = s := by
        simp only [exec]
        rw [if_neg hwho]
      rw [hexec]
      exact .moves (Market.Reach.refl s)
  | redeem who x =>
    by_cases hwho : who < s.accts.length
    · have hhook := supplyHook_some g₁ g₂ sp s who hI
      by_cases hbal : x ≤ ((supplyNext s who).acct who).supply
      · have hexec : exec comptroller s (.redeem who x) =
            (supplyNext s who).withAcct who fun a => { a with supply := a.supply - x } := by
          simp only [exec]
          rw [if_pos hwho, hhook]
          dsimp only
          rw [if_pos hbal]
        rw [hexec]
        exact .moves (Market.Settle₁.then_adjust (settle₁ s who) rfl rfl
          (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
      · have hexec : exec comptroller s (.redeem who x) = s := by
          simp only [exec]
          rw [if_pos hwho, hhook]
          dsimp only
          rw [if_neg hbal]
        rw [hexec]
        exact .moves (Market.Reach.refl s)
    · have hexec : exec comptroller s (.redeem who x) = s := by
        simp only [exec]
        rw [if_neg hwho]
      rw [hexec]
      exact .moves (Market.Reach.refl s)
  | transfer src dst x =>
    by_cases h : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · have hne : src ≠ dst := h.2.2
      have h1 : comptroller s (.supplyHook src) = some (supplyNext s src) :=
        supplyHook_some g₁ g₂ sp s src hI
      have h2 : comptroller (supplyNext s src) (.supplyHook dst) =
          some (supplyNext (supplyNext s src) dst) := by
        rw [supplyHook_eq, if_pos (supplyPre_supplyNext_of_ne g₁ g₂ sp s src dst hne hI)]
      by_cases hbal : x ≤ ((supplyNext (supplyNext s src) dst).acct src).supply
      · have hexec : exec comptroller s (.transfer src dst x) =
            ((supplyNext (supplyNext s src) dst).withAcct src
              fun a => { a with supply := a.supply - x }).withAcct dst
              fun a => { a with supply := a.supply + x } := by
          simp only [exec]
          rw [if_pos h, h1]
          dsimp only
          rw [h2]
          dsimp only
          rw [if_pos hbal]
        rw [hexec]
        exact .moves (Market.Settle₁.transfer (settle₁ s src)
          (settle₁ (supplyNext s src) dst) rfl rfl
          (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
          (fun _ => rfl) (fun _ => rfl))
      · have hexec : exec comptroller s (.transfer src dst x) = s := by
          simp only [exec]
          rw [if_pos h, h1]
          dsimp only
          rw [h2]
          dsimp only
          rw [if_neg hbal]
        rw [hexec]
        exact .moves (Market.Reach.refl s)
    · have hexec : exec comptroller s (.transfer src dst x) = s := by
        simp only [exec]
        rw [if_neg h]
      rw [hexec]
      exact .moves (Market.Reach.refl s)
  | borrow who x =>
    by_cases hwho : who < s.accts.length
    · have hhook := borrowHook_some g₁ g₂ sp s who hI
      have hexec : exec comptroller s (.borrow who x) =
          (borrowNext s who).withAcct who fun a => { a with borrow := a.borrow + x } := by
        simp only [exec]
        rw [if_pos hwho, hhook]
      rw [hexec]
      exact .moves (Market.Settle₂.then_adjust (settle₂ s who) rfl rfl
        (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
    · have hexec : exec comptroller s (.borrow who x) = s := by
        simp only [exec]
        rw [if_neg hwho]
      rw [hexec]
      exact .moves (Market.Reach.refl s)
  | repay who x =>
    by_cases hwho : who < s.accts.length
    · have hhook := borrowHook_some g₁ g₂ sp s who hI
      by_cases hbal : x ≤ ((borrowNext s who).acct who).borrow
      · have hexec : exec comptroller s (.repay who x) =
            (borrowNext s who).withAcct who fun a => { a with borrow := a.borrow - x } := by
          simp only [exec]
          rw [if_pos hwho, hhook]
          dsimp only
          rw [if_pos hbal]
        rw [hexec]
        exact .moves (Market.Settle₂.then_adjust (settle₂ s who) rfl rfl
          (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
      · have hexec : exec comptroller s (.repay who x) = s := by
          simp only [exec]
          rw [if_pos hwho, hhook]
          dsimp only
          rw [if_neg hbal]
        rw [hexec]
        exact .moves (Market.Reach.refl s)
    · have hexec : exec comptroller s (.repay who x) = s := by
        simp only [exec]
        rw [if_neg hwho]
      rw [hexec]
      exact .moves (Market.Reach.refl s)
  | claim who =>
    have hI' := Consistent_of_Inv hI
    have hb : borrowPre s who := borrowPre_of_Consistent s who hI'
    have hs : supplyPre (borrowNext s who) who := supplyPre_borrowNext s who hI'
    have hclaim : comptroller s (.claim who) =
        some (grant (supplyNext (borrowNext s who) who) who) := by
      rw [claim_eq, if_pos ⟨hb, hs⟩]
    have hexec : exec comptroller s (.claim who) =
        grant (supplyNext (borrowNext s who) who) who := by
      simp only [exec]
      rw [hclaim]
      rfl
    have h₂ : M.Settle₂ who s (borrowNext s who) := settle₂ s who
    have h₁ : M.Settle₁ who (borrowNext s who) (supplyNext (borrowNext s who) who) :=
      settle₁ (borrowNext s who) who
    by_cases hg : 0 < ((supplyNext (borrowNext s who) who).acct who).accrued ∧
        ((supplyNext (borrowNext s who) who).acct who).accrued ≤
          (supplyNext (borrowNext s who) who).reserve
    · rw [hexec]
      exact .moves (((Market.Reach.single (.settle₂ h₂)).tail (.settle₁ h₁)).tail
        (.adjust (grant_adjust _ _ hg)))
    · rw [hexec]
      exact .moves (((Market.Reach.single (.settle₂ h₂)).tail (.settle₁ h₁)).tail
        (grant_same _ _ hg))
  | setSpeeds a b =>
    have hcond : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
        (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) :=
      ⟨fun _ => hI.1, fun _ => hI.2⟩
    have hset : comptroller s (.setSpeeds a b) = some (speedsNext s a b) := by
      rw [setSpeeds_eq, if_pos hcond]
    have hexec : exec comptroller s (.setSpeeds a b) = speedsNext s a b := by
      simp only [exec]
      rw [hset]
      rfl
    rw [hexec]
    exact .retune (retune_speeds s a b) (speedsNext_rate₁ s a b) (speedsNext_rate₂ s a b)
  | advance k =>
    have hexec : exec comptroller s (.advance k) = { s with blockNumber := s.blockNumber + k } := by
      simp only [exec]
    rw [hexec]
    exact .advance k ⟨rfl, rfl⟩
  | drip x =>
    have hexec : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := by
      simp only [exec]
    rw [hexec]
    exact .moves (Market.Reach.single (.same rfl rfl))

/-! ## The upgrade and the bounds over runs -/

theorem clock_upgrade (L : Legacy) : M.clock (upgrade L) = (cL L).reinit M.init := by
  show ProofForgeFin.Accumulator.Clock.mk _ _ _ _ _ _ _ = _
  simp only [M, cL, upgrade, initSide, ProofForgeFin.Accumulator.Clock.reinit]
  by_cases h1 : L.supplyIndex = 0 <;> by_cases h2 : L.borrowIndex = 0 <;>
    simp [h1, h2]

theorem owed_sum_eq (L : Legacy) :
    ((M.accts (upgrade L)).map (M.owed L.supplyStart L.borrowStart (cL L))).sum =
      (L.accts.map L.pendingScaled).sum := by
  have hmod : M.accts (upgrade L) = L.accts := rfl
  rw [hmod]
  exact ProofForgeFin.Ledger.sum_map_congr L.accts (fun a _ => owed_eq L a)

theorem inv_start_hr (L : Legacy) (hL : L.WellFormed) :
    ∀ a ∈ M.accts (upgrade L),
      M.rec₁ a ≤ (cL L).index₁ ∧ M.rec₂ a ≤ (cL L).index₂ :=
  fun a ha => hL.2.2.2.2.2.2 a ha

theorem inv_start (L : Legacy) (hL : L.WellFormed) :
    M.Inv (reinitStart M.init (cL L).index₁ L.supplyStart)
      (reinitStart M.init (cL L).index₂ L.borrowStart)
      ((cL L).rate₁, (cL L).rate₂) (upgrade L) :=
  M.inv_reinit (clock_upgrade L) hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1 hL.2.2.2.2.1
    hL.2.2.2.2.2.1 (inv_start_hr L hL)

theorem inv_start_hr_acct (L : Legacy) (hL : L.WellFormed) (who : Account) :
    M.rec₁ (M.acct (upgrade L) who) ≤ (cL L).index₁ ∧
    M.rec₂ (M.acct (upgrade L) who) ≤ (cL L).index₂ :=
  ProofForgeFin.Ledger.getD_of_forall (M.accts (upgrade L)) who
    (inv_start_hr L hL) ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem acct_upgrade (L : Legacy) (who : Account) :
    M.acct (upgrade L) who = L.accts.getD who noAcct := rfl

theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hL
  have hI := inv_start L hL
  have hs := M.pot_reinit_le L.supplyStart L.borrowStart (clock_upgrade L)
    (inv_start_hr L hL)
  have hone : 0 < M.one := by decide
  have h := M.rewards_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone hI hs ops
  rw [creditSum_eq, owed_sum_eq, un₁_eq, un₂_eq, one_eq] at h
  exact h

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hL
  have hI := inv_start L hL
  have hs := M.potOf_reinit_le L.supplyStart L.borrowStart who (clock_upgrade L)
    (inv_start_hr_acct L hL who)
  have hone : 0 < M.one := by decide
  have h := M.account_rewards_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone hI who hs ops
  rw [creditedTo_eq, creditedTo_eq, owed_eq, acct_upgrade, un₁_eq, un₂_eq, one_eq] at h
  exact h

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hL hpos
  have hI := inv_start L hL
  have hone : 0 < M.one := by decide
  have hu₁ : M.units₁ (M.acct (run comptroller (upgrade L) history) who) = 0 := hpos.1
  have hu₂ : M.units₂ (M.acct (run comptroller (upgrade L) history) who) = 0 := hpos.2
  have h := M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone hI history ops who hu₁ hu₂
  rw [creditedTo_eq, creditedTo_eq] at h
  exact h

end CompRewards
