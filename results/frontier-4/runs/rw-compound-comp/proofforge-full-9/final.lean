import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
import ProofForgeFin.DeFi.Rewards

namespace CompRewards

open ProofForgeFin.Accumulator (Market Clock catchUp unindexed reinitStart)
open ProofForgeFin.DeFi.Rewards (firstStart effStart credit pending)

/-- The market reading for the accumulator library: supply is side 1, borrow is side 2. -/
def M : Market St Acct where
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

/-- Closed forms of each call, written with the specification's own definitions. -/
def supplyTop (s : St) (who : Account) : St :=
  let idx := accrueSide s.supplyState s.blockNumber (totalSupply s)
  { s with
    supplyState := idx,
    accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := idx.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex idx.index) idx.index } }

def borrowTop (s : St) (who : Account) : St :=
  let idx := accrueSide s.borrowState s.blockNumber (totalBorrows s)
  { s with
    borrowState := idx,
    accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := idx.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex idx.index) idx.index } }

def claimMid (s : St) (who : Account) : St := borrowTop s who

def claimTop (s : St) (who : Account) : St :=
  let m₁ := claimMid s who
  let sIdx := accrueSide m₁.supplyState m₁.blockNumber (totalSupply m₁)
  { m₁ with
    supplyState := sIdx,
    accts := m₁.accts.modify who fun a =>
      { a with
        supplierIndex := sIdx.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex sIdx.index) sIdx.index } }

def speedsTop (s : St) (a b : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
    borrowState := if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }

def supplyOk (s : St) (who : Account) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧
    accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index

def borrowOk (s : St) (who : Account) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
    accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index

def claimOk (s : St) (who : Account) : Prop :=
  borrowOk s who ∧
    supplyOk (claimMid s who) who

def speedsOk (s : St) (a b : Nat) : Prop :=
  (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber)

instance (s : St) (who : Account) : Decidable (supplyOk s who) := by
  unfold supplyOk; infer_instance
instance (s : St) (who : Account) : Decidable (borrowOk s who) := by
  unfold borrowOk; infer_instance
instance (s : St) (who : Account) : Decidable (claimOk s who) := by
  unfold claimOk supplyOk borrowOk claimMid borrowTop; infer_instance
instance (s : St) (a b : Nat) : Decidable (speedsOk s a b) := by
  unfold speedsOk; infer_instance

/-- Fixed comptroller: each call is `if` its specification preconditions `then some`
its closed form `else none`. The start is `accrualStart` (`firstStart`), so an index
exactly at `compInitialIndex` credits nothing (the deployed `>` is fixed to `≥`). -/
def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => if supplyOk s who then some (supplyTop s who) else none
  | .borrowHook who => if borrowOk s who then some (borrowTop s who) else none
  | .claim who => if claimOk s who then some (grant (claimTop s who) who) else none
  | .setSpeeds a b => if speedsOk s a b then some (speedsTop s a b) else none

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  by_cases hc : supplyOk s who
  · simp only [comptroller, if_pos hc] at h
    cases h
    obtain ⟨h1, h2⟩ := hc
    exact ⟨h1, h2, rfl⟩
  · simp only [comptroller, if_neg hc] at h
    cases h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  by_cases hc : borrowOk s who
  · simp only [comptroller, if_pos hc] at h
    cases h
    obtain ⟨h1, h2⟩ := hc
    exact ⟨h1, h2, rfl⟩
  · simp only [comptroller, if_neg hc] at h
    cases h

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  by_cases hc : claimOk s who
  · simp only [comptroller, if_pos hc] at h
    cases h
    obtain ⟨⟨hb1, hb2⟩, ⟨hs1, hs2⟩⟩ := hc
    exact ⟨claimMid s who, claimTop s who, ⟨hb1, hb2, rfl⟩, ⟨hs1, hs2, rfl⟩, rfl⟩
  · simp only [comptroller, if_neg hc] at h
    cases h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  by_cases hc : speedsOk s a b
  · simp only [comptroller, if_pos hc] at h
    cases h
    obtain ⟨h1, h2⟩ := hc
    exact ⟨h1, h2, rfl⟩
  · simp only [comptroller, if_neg hc] at h
    cases h

theorem accrueSide_index_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrualStart_le {recorded oldIdx newIdx : Nat}
    (h1 : recorded ≤ oldIdx) (h2 : oldIdx ≤ newIdx) :
    accrualStart recorded newIdx ≤ newIdx := by
  have heq : accrualStart recorded newIdx =
      firstStart compInitialIndex recorded newIdx := rfl
  rw [heq]
  exact ProofForgeFin.DeFi.Rewards.firstStart_le_index compInitialIndex (by omega)

theorem acct_supplier_le {s : St} (hc : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hc.2.2 _ hm).1
  · rw [hm]; exact Nat.zero_le _

theorem acct_borrower_le {s : St} (hc : Consistent s) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hc.2.2 _ hm).2
  · rw [hm]; exact Nat.zero_le _

theorem supplyOk_of_consistent {s : St} (hc : Consistent s) (who : Account) :
    supplyOk s who := by
  unfold supplyOk
  exact ⟨hc.1, accrualStart_le (acct_supplier_le hc who)
    (accrueSide_index_le s.supplyState s.blockNumber (totalSupply s))⟩

theorem borrowOk_of_consistent {s : St} (hc : Consistent s) (who : Account) :
    borrowOk s who := by
  unfold borrowOk
  exact ⟨hc.2.1, accrualStart_le (acct_borrower_le hc who)
    (accrueSide_index_le s.borrowState s.blockNumber (totalBorrows s))⟩

theorem claimMid_supplier (s : St) (who : Account) :
    ((claimMid s who).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold claimMid borrowTop St.acct
  simp only
  exact ProofForgeFin.Ledger.getD_modify_of_keeps s.accts who who noAcct
    (·.supplierIndex) (fun a => rfl)

theorem claimOk_of_consistent {s : St} (hc : Consistent s) (who : Account) :
    claimOk s who := by
  have hss : (claimMid s who).supplyState = s.supplyState := rfl
  have hbn : (claimMid s who).blockNumber = s.blockNumber := rfl
  have hsup : ((claimMid s who).acct who).supplierIndex =
      (s.acct who).supplierIndex := claimMid_supplier s who
  refine ⟨borrowOk_of_consistent hc who, ?_, ?_⟩
  · show (claimMid s who).supplyState.block ≤ (claimMid s who).blockNumber
    rw [hss, hbn]
    exact hc.1
  · rw [hss, hbn, hsup]
    exact accrualStart_le (acct_supplier_le hc who) (accrueSide_index_le _ _ _)

theorem speedsOk_of_consistent {s : St} (hc : Consistent s) (a b : Nat) :
    speedsOk s a b :=
  ⟨fun _ => hc.1, fun _ => hc.2.1⟩

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    simp only [comptroller, if_pos (supplyOk_of_consistent hc who)]
    rfl
  | borrowHook who =>
    simp only [comptroller, if_pos (borrowOk_of_consistent hc who)]
    rfl
  | claim who =>
    simp only [comptroller, if_pos (claimOk_of_consistent hc who)]
    rfl
  | setSpeeds a b =>
    simp only [comptroller, if_pos (speedsOk_of_consistent hc a b)]
    rfl
theorem accrueSide_speed_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem accrueSide_block_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem accrueSide_catchUp (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      catchUp M.one sd.index sd.block sd.speed now total := by
  have h1 : M.one = doubleScale := rfl
  rw [h1]
  unfold accrueSide catchUp
  split
  · rfl
  · rfl

/-- The account change of a supply settlement, as a separate function. -/
def supplySF (s : St) (_who : Account) (a : Acct) : Acct :=
  { a with
    supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
    accrued := a.accrued + creditFor a.supply
      (accrualStart a.supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }

/-- The account change of a borrow settlement, as a separate function. -/
def borrowSF (s : St) (_who : Account) (a : Acct) : Acct :=
  { a with
    borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
    accrued := a.accrued + creditFor a.borrow
      (accrualStart a.borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }

theorem supplyClock : ∀ (s : St) (who : Account),
    M.clock (supplyTop s who) = (M.clock s).catchUp₁ M.one (M.total₁ s) := by
  intro s who
  have hT : M.total₁ s = totalSupply s := rfl
  have h4 : M.clock (supplyTop s who) =
      Clock.mk (supplyTop s who).blockNumber (supplyTop s who).supplyState.index
        (supplyTop s who).supplyState.block (supplyTop s who).supplyState.speed
        (supplyTop s who).borrowState.index (supplyTop s who).borrowState.block
        (supplyTop s who).borrowState.speed := rfl
  have h1 : (supplyTop s who).supplyState =
      accrueSide s.supplyState s.blockNumber (totalSupply s) := rfl
  have h2 : (supplyTop s who).blockNumber = s.blockNumber := rfl
  have h3 : (supplyTop s who).borrowState = s.borrowState := rfl
  have h5 : M.clock s = Clock.mk s.blockNumber s.supplyState.index s.supplyState.block
      s.supplyState.speed s.borrowState.index s.borrowState.block s.borrowState.speed := rfl
  have h6 : (Clock.mk s.blockNumber s.supplyState.index s.supplyState.block
      s.supplyState.speed s.borrowState.index s.borrowState.block
      s.borrowState.speed).catchUp₁ M.one (totalSupply s) =
    Clock.mk s.blockNumber (catchUp M.one s.supplyState.index s.supplyState.block
      s.supplyState.speed s.blockNumber (totalSupply s)) s.blockNumber
      s.supplyState.speed s.borrowState.index s.borrowState.block s.borrowState.speed := rfl
  have h7 : (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed =
      s.supplyState.speed := accrueSide_speed_eq _ _ _
  have h8 : (accrueSide s.supplyState s.blockNumber (totalSupply s)).index =
      catchUp M.one s.supplyState.index s.supplyState.block s.supplyState.speed
        s.blockNumber (totalSupply s) := accrueSide_catchUp _ _ _
  have h9 : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block =
      s.blockNumber := accrueSide_block_eq _ _ _
  rw [h4, h1, h2, h3, hT, h5, h6, h7, h8, h9]

theorem borrowClock : ∀ (s : St) (who : Account),
    M.clock (borrowTop s who) = (M.clock s).catchUp₂ M.one (M.total₂ s) := by
  intro s who
  have hT : M.total₂ s = totalBorrows s := rfl
  have h4 : M.clock (borrowTop s who) =
      Clock.mk (borrowTop s who).blockNumber (borrowTop s who).supplyState.index
        (borrowTop s who).supplyState.block (borrowTop s who).supplyState.speed
        (borrowTop s who).borrowState.index (borrowTop s who).borrowState.block
        (borrowTop s who).borrowState.speed := rfl
  have h1 : (borrowTop s who).borrowState =
      accrueSide s.borrowState s.blockNumber (totalBorrows s) := rfl
  have h2 : (borrowTop s who).blockNumber = s.blockNumber := rfl
  have h3 : (borrowTop s who).supplyState = s.supplyState := rfl
  have h5 : M.clock s = Clock.mk s.blockNumber s.supplyState.index s.supplyState.block
      s.supplyState.speed s.borrowState.index s.borrowState.block s.borrowState.speed := rfl
  have h6 : (Clock.mk s.blockNumber s.supplyState.index s.supplyState.block
      s.supplyState.speed s.borrowState.index s.borrowState.block
      s.borrowState.speed).catchUp₂ M.one (totalBorrows s) =
    Clock.mk s.blockNumber s.supplyState.index s.supplyState.block s.supplyState.speed
      (catchUp M.one s.borrowState.index s.borrowState.block s.borrowState.speed
        s.blockNumber (totalBorrows s)) s.blockNumber s.borrowState.speed := rfl
  have h7 : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed =
      s.borrowState.speed := accrueSide_speed_eq _ _ _
  have h8 : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index =
      catchUp M.one s.borrowState.index s.borrowState.block s.borrowState.speed
        s.blockNumber (totalBorrows s) := accrueSide_catchUp _ _ _
  have h9 : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block =
      s.blockNumber := accrueSide_block_eq _ _ _
  rw [h4, h1, h2, h3, hT, h5, h6, h7, h8, h9]

theorem supplyAccts (s : St) (who : Account) : M.accts (supplyTop s who) =
    (M.accts s).modify who (supplySF s who) := rfl

theorem borrowAccts (s : St) (who : Account) : M.accts (borrowTop s who) =
    (M.accts s).modify who (borrowSF s who) := rfl

theorem supplySettles (s : St) (who : Account) :
    M.SettlesAt₁ (M.clock (supplyTop s who)).index₁ (supplySF s who) := by
  intro a
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

theorem borrowSettles (s : St) (who : Account) :
    M.SettlesAt₂ (M.clock (borrowTop s who)).index₂ (borrowSF s who) := by
  intro a
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

theorem settleSupply (s : St) (who : Account) :
    M.Settle₁ who s (supplyTop s who) :=
  ⟨supplyClock s who, supplySF s who, supplyAccts s who, supplySettles s who⟩

theorem settleBorrow (s : St) (who : Account) :
    M.Settle₂ who s (borrowTop s who) :=
  ⟨borrowClock s who, borrowSF s who, borrowAccts s who, borrowSettles s who⟩

theorem creditSum_eq (s : St) : M.creditSum s = St.credited s := rfl

theorem creditedTo_eq (s : St) (who : Account) :
    M.credited (M.acct s who) = St.creditedTo s who := rfl

theorem owed_eq (L : Legacy) (a : Acct) :
    M.owed L.supplyStart L.borrowStart (Clock.mk L.blockNumber L.supplyIndex
      L.supplyBlock L.compSpeed L.borrowIndex L.borrowBlock L.compSpeed) a =
      L.pendingScaled a := rfl

theorem un1_eq (L : Legacy) : (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock
    L.compSpeed L.borrowIndex L.borrowBlock L.compSpeed).un₁ =
    L.unindexedSupply := rfl

theorem un2_eq (L : Legacy) : (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock
    L.compSpeed L.borrowIndex L.borrowBlock L.compSpeed).un₂ =
    L.unindexedBorrow := rfl

theorem upgrade_clock (L : Legacy) :
    M.clock (upgrade L) = (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock
      L.compSpeed L.borrowIndex L.borrowBlock L.compSpeed).reinit M.init := by
  have hI : M.init = compInitialIndex := rfl
  rw [hI]
  unfold M upgrade initSide Clock.reinit
  by_cases hs : L.supplyIndex = 0 <;> by_cases hb : L.borrowIndex = 0 <;> simp [hs, hb]

theorem upgrade_inv (L : Legacy) (hW : L.WellFormed) :
    M.Inv (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart)
      (L.compSpeed, L.compSpeed) (upgrade L) := by
  have hc := upgrade_clock L
  have hI : M.init = compInitialIndex := rfl
  have hac : M.accts (upgrade L) = L.accts := rfl
  unfold Legacy.WellFormed at hW
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, hrec⟩ := hW
  refine M.inv_reinit hc ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hI]; exact hs0
  · exact hsle
  · rw [hI]; exact hb0
  · exact hble
  · exact hsb
  · exact hbb
  · intro a ha
    rw [hac] at ha
    exact hrec _ ha

theorem upgrade_pot (L : Legacy) (hW : L.WellFormed) :
    M.pot (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart) (upgrade L) ≤
      M.creditSum (upgrade L) * M.one + (L.accts.map fun a => L.pendingScaled a).sum +
        M.one * (L.unindexedSupply + L.unindexedBorrow) := by
  have hc := upgrade_clock L
  have hac : M.accts (upgrade L) = L.accts := rfl
  unfold Legacy.WellFormed at hW
  obtain ⟨_, _, _, _, _, _, hrec⟩ := hW
  have hr : ∀ a ∈ M.accts (upgrade L),
      M.rec₁ a ≤ (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
        L.borrowIndex L.borrowBlock L.compSpeed).index₁ ∧
      M.rec₂ a ≤ (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
        L.borrowIndex L.borrowBlock L.compSpeed).index₂ := by
    intro a ha
    rw [hac] at ha
    exact hrec _ ha
  have h := M.pot_reinit_le L.supplyStart L.borrowStart hc hr
  simp only [owed_eq, un1_eq, un2_eq] at h
  exact h

theorem upgrade_potOf (L : Legacy) (hW : L.WellFormed) (who : Account) :
    M.potOf (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart) who (upgrade L) ≤
      M.credited (M.acct (upgrade L) who) * M.one + L.pendingScaled (M.acct (upgrade L) who) +
        M.one * ((if 0 < (M.acct (upgrade L) who).supply then L.unindexedSupply else 0) +
          (if 0 < (M.acct (upgrade L) who).borrow then L.unindexedBorrow else 0)) := by
  have hc := upgrade_clock L
  have hac : M.accts (upgrade L) = L.accts := rfl
  unfold Legacy.WellFormed at hW
  obtain ⟨_, _, _, _, _, _, hrec⟩ := hW
  have hr : M.rec₁ (M.acct (upgrade L) who) ≤
        (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
          L.borrowIndex L.borrowBlock L.compSpeed).index₁ ∧
      M.rec₂ (M.acct (upgrade L) who) ≤
        (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
          L.borrowIndex L.borrowBlock L.compSpeed).index₂ := by
    have e : M.acct (upgrade L) who = L.accts.getD who noAcct := rfl
    rw [e]
    rcases ProofForgeFin.Ledger.getD_mem_or L.accts who noAcct with hm | hm
    · exact hrec _ hm
    · rw [hm]
      constructor <;> (show (0 : Nat) ≤ _; exact Nat.zero_le _)
  have h := M.potOf_reinit_le L.supplyStart L.borrowStart who hc hr
  simp only [owed_eq, un1_eq, un2_eq] at h
  exact h

theorem hone : 0 < M.one := by
  show 0 < 10 ^ 36
  decide

theorem supplyOk_of_Inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St}
    (hI : M.Inv g₁ g₂ sp s) (who : Account) : supplyOk s who := by
  refine ⟨hI.last₁, ?_⟩
  have hr : (s.acct who).supplierIndex ≤ s.supplyState.index := by
    unfold St.acct
    rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
    · exact (hI.recs _ hm).1
    · rw [hm]; exact Nat.zero_le _
  exact accrualStart_le hr (accrueSide_index_le _ _ _)

theorem borrowOk_of_Inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St}
    (hI : M.Inv g₁ g₂ sp s) (who : Account) : borrowOk s who := by
  refine ⟨hI.last₂, ?_⟩
  have hr : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
    unfold St.acct
    rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
    · exact (hI.recs _ hm).2
    · rw [hm]; exact Nat.zero_le _
  exact accrualStart_le hr (accrueSide_index_le _ _ _)

theorem claimMid_supplyState (s : St) (who : Account) :
    (claimMid s who).supplyState = s.supplyState := rfl

theorem claimMid_blockNumber (s : St) (who : Account) :
    (claimMid s who).blockNumber = s.blockNumber := rfl

theorem claimOk_of_Inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St}
    (hI : M.Inv g₁ g₂ sp s) (who : Account) : claimOk s who := by
  have hss := claimMid_supplyState s who
  have hbn := claimMid_blockNumber s who
  refine ⟨borrowOk_of_Inv hI who, ?_, ?_⟩
  · show (claimMid s who).supplyState.block ≤ (claimMid s who).blockNumber
    rw [hss, hbn]
    exact hI.last₁
  · rw [claimMid_supplier]
    have hr : (s.acct who).supplierIndex ≤ (claimMid s who).supplyState.index := by
      rw [hss]
      unfold St.acct
      rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
      · exact (hI.recs _ hm).1
      · rw [hm]; exact Nat.zero_le _
    exact accrualStart_le hr (accrueSide_index_le _ _ _)

theorem speedsOk_of_Inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St}
    (hI : M.Inv g₁ g₂ sp s) (a b : Nat) : speedsOk s a b :=
  ⟨fun _ => hI.last₁, fun _ => hI.last₂⟩

/-- `grantCompInternal` moves accrued COMP to the wallet: credited is unchanged. -/
def grantF (a : Acct) : Acct :=
  { a with accrued := 0, wallet := a.wallet + a.accrued }

theorem grantAdjusts : M.AdjustsAt grantF := by
  intro a
  refine ⟨?_, rfl, rfl⟩
  have h1 : (grantF a).accrued = 0 := rfl
  have h2 : (grantF a).wallet = a.wallet + a.accrued := rfl
  show (grantF a).accrued + (grantF a).wallet ≤ a.accrued + a.wallet
  rw [h1, h2]
  omega

theorem grantStep (s' : St) (who : Account) : M.Step s' (grant s' who) := by
  by_cases hc : 0 < (s'.acct who).accrued ∧ (s'.acct who).accrued ≤ s'.reserve
  · have heq : grant s' who = { s' with reserve := s'.reserve - (s'.acct who).accrued, accts := s'.accts.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) } := by
      simp only [grant, if_pos hc]
    refine .adjust (w := who) ⟨?_, grantF, ?_, grantAdjusts, Or.inl (fun _ => rfl), Or.inl (fun _ => rfl)⟩
    · rw [heq]; rfl
    · rw [heq]; rfl
  · have heq : grant s' who = s' := by
      simp only [grant, if_neg hc]
    exact .same (by rw [heq]) (by rw [heq])

theorem claimTop_eq (s : St) (who : Account) :
    claimTop s who = supplyTop (claimMid s who) who := rfl

theorem claimReach (s : St) (who : Account) :
    M.Reach s (grant (claimTop s who) who) := by
  have h1 : M.Settle₂ who s (claimMid s who) := settleBorrow s who
  have h2 : M.Settle₁ who (claimMid s who) (claimTop s who) :=
    settleSupply (claimMid s who) who
  exact ((Market.Reach.single (.settle₂ h1)).tail (.settle₁ h2)).tail
    (grantStep (claimTop s who) who)

/-- Rate and side projections of `speedsTop`, as equations. -/
theorem speedsTop_supply_index (s : St) (a b : Nat) :
    (M.clock (speedsTop s a b)).index₁ =
      (if s.supplyState.speed = a then s.supplyState
       else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }).index := rfl

theorem speedsTop_supply_block (s : St) (a b : Nat) :
    (M.clock (speedsTop s a b)).last₁ =
      (if s.supplyState.speed = a then s.supplyState
       else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }).block := rfl

theorem speedsTop_supply_rate (s : St) (a b : Nat) :
    (M.clock (speedsTop s a b)).rate₁ =
      (if s.supplyState.speed = a then s.supplyState
       else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }).speed := rfl

theorem speedsTop_borrow_index (s : St) (a b : Nat) :
    (M.clock (speedsTop s a b)).index₂ =
      (if s.borrowState.speed = b then s.borrowState
       else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }).index := rfl

theorem speedsTop_borrow_block (s : St) (a b : Nat) :
    (M.clock (speedsTop s a b)).last₂ =
      (if s.borrowState.speed = b then s.borrowState
       else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }).block := rfl

theorem speedsTop_borrow_rate (s : St) (a b : Nat) :
    (M.clock (speedsTop s a b)).rate₂ =
      (if s.borrowState.speed = b then s.borrowState
       else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }).speed := rfl

theorem speedsRetune (s : St) (a b : Nat) : M.Retune s (speedsTop s a b) := by
  have hT1 : M.total₁ s = totalSupply s := rfl
  have hT2 : M.total₂ s = totalBorrows s := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show M.accts (speedsTop s a b) = M.accts s
    rfl
  · show (M.clock (speedsTop s a b)).now = (M.clock s).now
    rfl
  · show Market.SideMove M.one (M.total₁ s) (M.clock s).now (M.clock s).index₁
      (M.clock s).last₁ (M.clock s).rate₁ (M.clock (speedsTop s a b)).index₁
      (M.clock (speedsTop s a b)).last₁ (M.clock (speedsTop s a b)).rate₁
    rw [speedsTop_supply_index, speedsTop_supply_block, speedsTop_supply_rate, hT1]
    by_cases he : s.supplyState.speed = a
    · rw [if_pos he]
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · rw [if_neg he]
      refine Or.inr ⟨?_, ?_⟩
      · exact accrueSide_catchUp _ _ _
      · exact accrueSide_block_eq _ _ _
  · show Market.SideMove M.one (M.total₂ s) (M.clock s).now (M.clock s).index₂
      (M.clock s).last₂ (M.clock s).rate₂ (M.clock (speedsTop s a b)).index₂
      (M.clock (speedsTop s a b)).last₂ (M.clock (speedsTop s a b)).rate₂
    rw [speedsTop_borrow_index, speedsTop_borrow_block, speedsTop_borrow_rate, hT2]
    by_cases he : s.borrowState.speed = b
    · rw [if_pos he]
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · rw [if_neg he]
      refine Or.inr ⟨?_, ?_⟩
      · exact accrueSide_catchUp _ _ _
      · exact accrueSide_block_eq _ _ _

theorem speedsRate1 (s : St) (a b : Nat) :
    (M.clock (speedsTop s a b)).rate₁ = a := by
  rw [speedsTop_supply_rate]
  by_cases he : s.supplyState.speed = a
  · rw [if_pos he]; exact he
  · rw [if_neg he]

theorem speedsRate2 (s : St) (a b : Nat) :
    (M.clock (speedsTop s a b)).rate₂ = b := by
  rw [speedsTop_borrow_rate]
  by_cases he : s.borrowState.speed = b
  · rw [if_pos he]; exact he
  · rw [if_neg he]

theorem advanceStep (s : St) (k : Nat) :
    M.Advance k s ({ s with blockNumber := s.blockNumber + k }) := by
  refine ⟨?_, ?_⟩
  · show M.clock { s with blockNumber := s.blockNumber + k } = (M.clock s).advance k
    rfl
  · show M.accts { s with blockNumber := s.blockNumber + k } = M.accts s
    rfl

theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (op : Op)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  cases op with
  | mint who x =>
    have e1 : nextSpeeds sp (.mint who x) = sp := rfl
    have e2 : emittedBy sp (.mint who x) = 0 := rfl
    by_cases hlen : who < s.accts.length
    · have hok : supplyOk s who := supplyOk_of_Inv hI who
      have hc : comptroller s (.supplyHook who) = some (supplyTop s who) := by
        simp only [comptroller, if_pos hok]
      simp only [exec, if_pos hlen, hc, e1, e2]
      exact .moves (Market.Settle₁.then_adjust (settleSupply s who) rfl rfl
        (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
    · simp only [exec, if_neg hlen, e1, e2]
      exact .moves (Market.Reach.refl _)
  | redeem who x =>
    have e1 : nextSpeeds sp (.redeem who x) = sp := rfl
    have e2 : emittedBy sp (.redeem who x) = 0 := rfl
    by_cases hlen : who < s.accts.length
    · have hok : supplyOk s who := supplyOk_of_Inv hI who
      have hc : comptroller s (.supplyHook who) = some (supplyTop s who) := by
        simp only [comptroller, if_pos hok]
      by_cases hx : x ≤ ((supplyTop s who).acct who).supply
      · simp only [exec, if_pos hlen, hc, if_pos hx, e1, e2]
        exact .moves (Market.Settle₁.then_adjust (settleSupply s who) rfl rfl
          (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
      · simp only [exec, if_pos hlen, hc, if_neg hx, e1, e2]
        exact .moves (Market.Reach.refl _)
    · simp only [exec, if_neg hlen, e1, e2]
      exact .moves (Market.Reach.refl _)
  | transfer src dst x =>
    have e1 : nextSpeeds sp (.transfer src dst x) = sp := rfl
    have e2 : emittedBy sp (.transfer src dst x) = 0 := rfl
    by_cases hlen : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · have hok1 : supplyOk s src := supplyOk_of_Inv hI src
      have hc1 : comptroller s (.supplyHook src) = some (supplyTop s src) := by
        simp only [comptroller, if_pos hok1]
      have hI1 := (Market.Step.bound (.settle₁ (settleSupply s src)) hI).1
      have hok2 : supplyOk (supplyTop s src) dst := supplyOk_of_Inv hI1 dst
      have hc2 : comptroller (supplyTop s src) (.supplyHook dst) =
          some (supplyTop (supplyTop s src) dst) := by
        simp only [comptroller, if_pos hok2]
      by_cases hx : x ≤ ((supplyTop (supplyTop s src) dst).acct src).supply
      · simp only [exec, if_pos hlen, hc1, hc2, if_pos hx, e1, e2]
        exact .moves (Market.Settle₁.transfer (settleSupply s src)
          (settleSupply (supplyTop s src) dst) rfl rfl
          (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
          (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
          (fun _ => rfl) (fun _ => rfl))
      · simp only [exec, if_pos hlen, hc1, hc2, if_neg hx, e1, e2]
        exact .moves (Market.Reach.refl _)
    · simp only [exec, if_neg hlen, e1, e2]
      exact .moves (Market.Reach.refl _)
  | borrow who x =>
    have e1 : nextSpeeds sp (.borrow who x) = sp := rfl
    have e2 : emittedBy sp (.borrow who x) = 0 := rfl
    by_cases hlen : who < s.accts.length
    · have hok : borrowOk s who := borrowOk_of_Inv hI who
      have hc : comptroller s (.borrowHook who) = some (borrowTop s who) := by
        simp only [comptroller, if_pos hok]
      simp only [exec, if_pos hlen, hc, e1, e2]
      exact .moves (Market.Settle₂.then_adjust (settleBorrow s who) rfl rfl
        (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
    · simp only [exec, if_neg hlen, e1, e2]
      exact .moves (Market.Reach.refl _)
  | repay who x =>
    have e1 : nextSpeeds sp (.repay who x) = sp := rfl
    have e2 : emittedBy sp (.repay who x) = 0 := rfl
    by_cases hlen : who < s.accts.length
    · have hok : borrowOk s who := borrowOk_of_Inv hI who
      have hc : comptroller s (.borrowHook who) = some (borrowTop s who) := by
        simp only [comptroller, if_pos hok]
      by_cases hx : x ≤ ((borrowTop s who).acct who).borrow
      · simp only [exec, if_pos hlen, hc, if_pos hx, e1, e2]
        exact .moves (Market.Settle₂.then_adjust (settleBorrow s who) rfl rfl
          (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
      · simp only [exec, if_pos hlen, hc, if_neg hx, e1, e2]
        exact .moves (Market.Reach.refl _)
    · simp only [exec, if_neg hlen, e1, e2]
      exact .moves (Market.Reach.refl _)
  | claim who =>
    have e1 : nextSpeeds sp (.claim who) = sp := rfl
    have e2 : emittedBy sp (.claim who) = 0 := rfl
    have hok : claimOk s who := claimOk_of_Inv hI who
    have hc : comptroller s (.claim who) = some (grant (claimTop s who) who) := by
      simp only [comptroller, if_pos hok]
    simp only [exec, hc, Option.getD_some, e1, e2]
    exact .moves (claimReach s who)
  | setSpeeds a b =>
    have e1 : nextSpeeds sp (.setSpeeds a b) = (a, b) := rfl
    have e2 : emittedBy sp (.setSpeeds a b) = 0 := rfl
    have hok : speedsOk s a b := speedsOk_of_Inv hI a b
    have hc : comptroller s (.setSpeeds a b) = some (speedsTop s a b) := by
      simp only [comptroller, if_pos hok]
    simp only [exec, hc, Option.getD_some, e1, e2]
    exact .retune (speedsRetune s a b) (speedsRate1 s a b) (speedsRate2 s a b)
  | advance k =>
    have e1 : nextSpeeds sp (.advance k) = sp := rfl
    have e2 : emittedBy sp (.advance k) = k * (sp.1 + sp.2) := rfl
    have he : exec comptroller s (.advance k) = { s with blockNumber := s.blockNumber + k } := rfl
    rw [e1, e2, he]
    exact .advance k (advanceStep s k)
  | drip x =>
    have e1 : nextSpeeds sp (.drip x) = sp := rfl
    have e2 : emittedBy sp (.drip x) = 0 := rfl
    have he : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := rfl
    rw [e1, e2, he]
    exact .moves (Market.Reach.single (.same rfl rfl))

theorem req_rewards_bounded : RewardsBounded comptroller := by
  intro L ops hW
  have hInv := upgrade_inv L hW
  have hs := upgrade_pot L hW
  have h := M.rewards_bounded (run comptroller) emitted speedsAfter
    (fun sp s op hI => exec_act _ _ sp s op hI) hone hInv hs ops
  rw [creditSum_eq, creditSum_eq] at h
  exact h

theorem req_account_bounded : AccountBounded comptroller := by
  intro L ops who hW
  have hInv := upgrade_inv L hW
  have hs := upgrade_potOf L hW who
  have h := M.account_rewards_bounded (run comptroller) emitted speedsAfter
    (fun sp s op hI => exec_act _ _ sp s op hI) hone hInv who hs ops
  simp only [creditedTo_eq] at h
  exact h

theorem req_no_backdated : NoBackdatedRewards comptroller := by
  intro L history ops who hW hpos
  have hInv := upgrade_inv L hW
  have h1 : M.units₁ (M.acct (run comptroller (upgrade L) history) who) = 0 := hpos.1
  have h2 : M.units₂ (M.acct (run comptroller (upgrade L) history) who) = 0 := hpos.2
  have h := M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter
    (fun sp s op hI => exec_act _ _ sp s op hI) hone
    hInv history ops who h1 h2
  simp only [creditedTo_eq] at h
  exact h

end CompRewards
