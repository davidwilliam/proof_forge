import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
/-!
Fixed COMP distribution: Proposal 62's off-by-one (`> compInitialIndex` instead of
`>=`) is corrected by using the specification's `accrualStart` (`firstStart`) directly.
Each call is written in closed form with the specification's own update functions, so the
effect requirements follow by case analysis on the preconditions.
-/
namespace CompRewards

-- Market library names are referenced by full path where needed.

/-- Supply hook result in closed form (spec `SupplyDistributed`). -/
def supplyNext (s : St) (who : Account) : St :=
  let sd' := accrueSide s.supplyState s.blockNumber (totalSupply s)
  { s with
    supplyState := sd',
    accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := sd'.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex sd'.index) sd'.index } }

/-- Supply hook precondition. -/
def supplyOk (s : St) (who : Account) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index

instance (s : St) (who : Account) : Decidable (supplyOk s who) := by
  unfold supplyOk; infer_instance

/-- Borrow hook result in closed form (spec `BorrowDistributed`). -/
def borrowNext (s : St) (who : Account) : St :=
  let sd' := accrueSide s.borrowState s.blockNumber (totalBorrows s)
  { s with
    borrowState := sd',
    accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := sd'.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex sd'.index) sd'.index } }

/-- Borrow hook precondition. -/
def borrowOk (s : St) (who : Account) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index

instance (s : St) (who : Account) : Decidable (borrowOk s who) := by
  unfold borrowOk; infer_instance

/-- Claim precondition: borrow step on `s`, then supply step on `borrowNext s who`. -/
def claimOk (s : St) (who : Account) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ∧
  (borrowNext s who).supplyState.block ≤ (borrowNext s who).blockNumber ∧
  accrualStart ((borrowNext s who).acct who).supplierIndex
      (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber
        (totalSupply (borrowNext s who))).index ≤
    (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber
        (totalSupply (borrowNext s who))).index

instance (s : St) (who : Account) : Decidable (claimOk s who) := by
  unfold claimOk; infer_instance

/-- Speed-change result in closed form (spec `SpeedsSet`). -/
def setNext (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }

/-- Speed-change precondition. -/
def setOk (s : St) (sup bor : Nat) : Prop :=
  (s.supplyState.speed = sup ∨ s.supplyState.block ≤ s.blockNumber) ∧
  (s.borrowState.speed = bor ∨ s.borrowState.block ≤ s.blockNumber)

instance (s : St) (sup bor : Nat) : Decidable (setOk s sup bor) := by
  unfold setOk; infer_instance

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => if supplyOk s who then some (supplyNext s who) else none
  | .borrowHook who => if borrowOk s who then some (borrowNext s who) else none
  | .claim who => if claimOk s who then some (grant (supplyNext (borrowNext s who) who) who) else none
  | .setSpeeds a b => if setOk s a b then some (setNext s a b) else none

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hc : supplyOk s who
  · simp only [hc, ↓reduceIte] at h
    rw [Option.some_inj] at h
    subst h
    obtain ⟨h1, h2⟩ := hc
    exact ⟨h1, h2, rfl⟩
  · simp only [hc, ↓reduceIte] at h
    cases h

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hc : borrowOk s who
  · simp only [hc, ↓reduceIte] at h
    rw [Option.some_inj] at h
    subst h
    obtain ⟨h1, h2⟩ := hc
    exact ⟨h1, h2, rfl⟩
  · simp only [hc, ↓reduceIte] at h
    cases h

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hc : claimOk s who
  · simp only [hc, ↓reduceIte] at h
    rw [Option.some_inj] at h
    subst h
    obtain ⟨h1, h2, h3, h4⟩ := hc
    exact ⟨borrowNext s who, supplyNext (borrowNext s who) who,
      ⟨h1, h2, rfl⟩, ⟨h3, h4, rfl⟩, rfl⟩
  · simp only [hc, ↓reduceIte] at h
    cases h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller] at h
  by_cases hc : setOk s a b
  · simp only [hc, ↓reduceIte] at h
    rw [Option.some_inj] at h
    subst h
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, ?_, rfl⟩
    · intro hne
      cases h1 with
      | inl he => exact absurd he hne
      | inr hle => exact hle
    · intro hne
      cases h2 with
      | inl he => exact absurd he hne
      | inr hle => exact hle
  · simp only [hc, ↓reduceIte] at h
    cases h

theorem accrue_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem start_le (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  split
  · split <;> omega
  · exact h

theorem acct_supply_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct
  exact ProofForgeFin.Ledger.getD_of_forall
    (P := fun a => a.supplierIndex ≤ s.supplyState.index)
    s.accts who (d := noAcct) (fun a ha => (hc.2.2 a ha).1) (Nat.zero_le _)

theorem acct_borrow_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct
  exact ProofForgeFin.Ledger.getD_of_forall
    (P := fun a => a.borrowerIndex ≤ s.borrowState.index)
    s.accts who (d := noAcct) (fun a ha => (hc.2.2 a ha).2) (Nat.zero_le _)

theorem borrowNext_supplyState (s : St) (who : Account) :
    (borrowNext s who).supplyState = s.supplyState := rfl

theorem borrowNext_block (s : St) (who : Account) :
    (borrowNext s who).blockNumber = s.blockNumber := rfl

theorem borrowNext_supplierIndex (s : St) (who : Account) :
    ((borrowNext s who).acct who).supplierIndex = (s.acct who).supplierIndex :=
  ProofForgeFin.Ledger.getD_modify_of_keeps s.accts who who noAcct
    (fun a => a.supplierIndex) (fun _ => rfl)

theorem totalSupply_borrowNext (s : St) (who : Account) :
    totalSupply (borrowNext s who) = totalSupply s := by
  unfold totalSupply borrowNext
  simp only
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ (fun a => a.supply)
    noAcct (fun _ => rfl)

theorem supplyOk_of_consistent (s : St) (hc : Consistent s) (who : Account) :
    supplyOk s who := by
  refine ⟨hc.1, ?_⟩
  apply start_le
  exact Nat.le_trans (acct_supply_le s hc who) (accrue_le _ _ _)

theorem borrowOk_of_consistent (s : St) (hc : Consistent s) (who : Account) :
    borrowOk s who := by
  refine ⟨hc.2.1, ?_⟩
  apply start_le
  exact Nat.le_trans (acct_borrow_le s hc who) (accrue_le _ _ _)

theorem claimOk_of_consistent (s : St) (hc : Consistent s) (who : Account) :
    claimOk s who := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (borrowOk_of_consistent s hc who).1
  · exact (borrowOk_of_consistent s hc who).2
  · rw [borrowNext_supplyState, borrowNext_block]
    exact hc.1
  · rw [borrowNext_supplierIndex, borrowNext_supplyState, borrowNext_block,
      totalSupply_borrowNext]
    exact (supplyOk_of_consistent s hc who).2

/-- The market reading for the library: supply is side 1, borrow is side 2. -/
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

theorem M_clock (s : St) : M.clock s =
    ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed,
     s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩ := rfl

theorem M_total₁ (s : St) : M.total₁ s = totalSupply s := rfl

theorem M_total₂ (s : St) : M.total₂ s = totalBorrows s := rfl

theorem accrue_index_bridge (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem accrue_block_bridge (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split <;> rfl

theorem accrue_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split <;> rfl

theorem accrualStart_firstStart (recorded index : Nat) :
    accrualStart recorded index =
      ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex recorded index := rfl

theorem Consistent_of_Inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St}
    (h : M.Inv g₁ g₂ sp s) : Consistent s :=
  ⟨h.last₁, h.last₂, h.recs⟩

/-- A supply hook settles the account on side 1. -/
theorem settle₁ (s : St) (who : Account) : M.Settle₁ who s (supplyNext s who) := by
  refine ⟨?_, ?_⟩
  · have hi : (supplyNext s who).supplyState.index =
        ProofForgeFin.Accumulator.catchUp M.one s.supplyState.index s.supplyState.block
          s.supplyState.speed s.blockNumber (M.total₁ s) :=
      accrue_index_bridge _ _ _
    have hb : (supplyNext s who).supplyState.block = s.blockNumber :=
      accrue_block_bridge _ _ _
    have hn : (supplyNext s who).blockNumber = s.blockNumber := rfl
    have hs : (supplyNext s who).supplyState.speed = s.supplyState.speed :=
      accrue_speed _ _ _
    have hb1 : (supplyNext s who).borrowState.index = s.borrowState.index := rfl
    have hb2 : (supplyNext s who).borrowState.block = s.borrowState.block := rfl
    have hb3 : (supplyNext s who).borrowState.speed = s.borrowState.speed := rfl
    simp only [M_clock, ProofForgeFin.Accumulator.Clock.catchUp₁_mk, hi, hb, hn, hs,
      hb1, hb2, hb3]
  · refine ⟨_, rfl, ?_⟩
    intro a
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    show a.accrued + (a.supply *
        ((supplyNext s who).supplyState.index - accrualStart a.supplierIndex
          (supplyNext s who).supplyState.index) / doubleScale) + a.wallet ≤
      a.accrued + a.wallet + (a.supply *
        ((supplyNext s who).supplyState.index - accrualStart a.supplierIndex
          (supplyNext s who).supplyState.index) / doubleScale)
    exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

/-- A borrow hook settles the account on side 2. -/
theorem settle₂ (s : St) (who : Account) : M.Settle₂ who s (borrowNext s who) := by
  refine ⟨?_, ?_⟩
  · have hi : (borrowNext s who).borrowState.index =
        ProofForgeFin.Accumulator.catchUp M.one s.borrowState.index s.borrowState.block
          s.borrowState.speed s.blockNumber (M.total₂ s) :=
      accrue_index_bridge _ _ _
    have hb : (borrowNext s who).borrowState.block = s.blockNumber :=
      accrue_block_bridge _ _ _
    have hn : (borrowNext s who).blockNumber = s.blockNumber := rfl
    have hs : (borrowNext s who).borrowState.speed = s.borrowState.speed :=
      accrue_speed _ _ _
    have hb1 : (borrowNext s who).supplyState.index = s.supplyState.index := rfl
    have hb2 : (borrowNext s who).supplyState.block = s.supplyState.block := rfl
    have hb3 : (borrowNext s who).supplyState.speed = s.supplyState.speed := rfl
    simp only [M_clock, ProofForgeFin.Accumulator.Clock.catchUp₂_mk, hi, hb, hn, hs,
      hb1, hb2, hb3]
  · refine ⟨_, rfl, ?_⟩
    intro a
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    show a.accrued + (a.borrow *
        ((borrowNext s who).borrowState.index - accrualStart a.borrowerIndex
          (borrowNext s who).borrowState.index) / doubleScale) + a.wallet ≤
      a.accrued + a.wallet + (a.borrow *
        ((borrowNext s who).borrowState.index - accrualStart a.borrowerIndex
          (borrowNext s who).borrowState.index) / doubleScale)
    exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

/-- The payment of accrued COMP is one adjustment step (or nothing). -/
theorem grant_reach (s : St) (who : Account) : M.Reach s (grant s who) := by
  unfold grant
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [if_pos h]
    apply ProofForgeFin.Accumulator.Market.Reach.single
    refine ProofForgeFin.Accumulator.Market.Step.adjust (w := who)
      ⟨rfl, (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }),
      ?_, ?_, ?_, ?_⟩
    · exact ProofForgeFin.Ledger.modify_congr s.accts who noAcct (fun _ => rfl)
    · intro a
      refine ⟨?_, rfl, rfl⟩
      show 0 + (a.wallet + a.accrued) ≤ a.accrued + a.wallet
      omega
    · exact Or.inl fun a => rfl
    · exact Or.inl fun a => rfl
  · simp only [if_neg h]
    exact ProofForgeFin.Accumulator.Market.Reach.refl s

/-- The account change of a supply hook, as a function. -/
def supplyModF (s : St) (b : Acct) : Acct := { b with
    supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
    accrued := b.accrued + creditFor b.supply
      (accrualStart b.supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }

/-- The account change of a borrow hook, as a function. -/
def borrowModF (s : St) (b : Acct) : Acct := { b with
    borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
    accrued := b.accrued + creditFor b.borrow
      (accrualStart b.borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }

/-- A supply hook preserves consistency. -/
theorem Consistent_supplyNext (s : St) (hc : Consistent s) (who : Account) :
    Consistent (supplyNext s who) := by
  have hmod : (supplyNext s who).accts = s.accts.modify who (supplyModF s) := rfl
  have hP : ∀ b ∈ s.accts, b.supplierIndex ≤ (supplyNext s who).supplyState.index ∧
      b.borrowerIndex ≤ (supplyNext s who).borrowState.index := by
    intro b hb
    refine ⟨?_, ?_⟩
    · exact Nat.le_trans (hc.2.2 b hb).1 (accrue_le _ _ _)
    · exact (hc.2.2 b hb).2
  have hPf : ∀ b ∈ s.accts, (supplyModF s b).supplierIndex ≤
      (supplyNext s who).supplyState.index ∧
      (supplyModF s b).borrowerIndex ≤ (supplyNext s who).borrowState.index := by
    intro b hb
    exact ⟨Nat.le_refl _, (hc.2.2 b hb).2⟩
  refine ⟨?_, ?_, ?_⟩
  · have hbn : (supplyNext s who).blockNumber = s.blockNumber := rfl
    show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block ≤
      (supplyNext s who).blockNumber
    rw [accrue_block_bridge, hbn]
    exact Nat.le_refl _
  · exact hc.2.1
  · rw [hmod]
    exact ProofForgeFin.DeFi.Rewards.forall_mem_modify hP hPf

/-- A borrow hook preserves consistency. -/
theorem Consistent_borrowNext (s : St) (hc : Consistent s) (who : Account) :
    Consistent (borrowNext s who) := by
  have hmod : (borrowNext s who).accts = s.accts.modify who (borrowModF s) := rfl
  have hP : ∀ b ∈ s.accts, b.supplierIndex ≤ (borrowNext s who).supplyState.index ∧
      b.borrowerIndex ≤ (borrowNext s who).borrowState.index := by
    intro b hb
    refine ⟨?_, ?_⟩
    · exact (hc.2.2 b hb).1
    · exact Nat.le_trans (hc.2.2 b hb).2 (accrue_le _ _ _)
  have hPf : ∀ b ∈ s.accts, (borrowModF s b).supplierIndex ≤
      (borrowNext s who).supplyState.index ∧
      (borrowModF s b).borrowerIndex ≤ (borrowNext s who).borrowState.index := by
    intro b hb
    exact ⟨(hc.2.2 b hb).1, Nat.le_refl _⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hc.1
  · have hbn : (borrowNext s who).blockNumber = s.blockNumber := rfl
    show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block ≤
      (borrowNext s who).blockNumber
    rw [accrue_block_bridge, hbn]
    exact Nat.le_refl _
  · rw [hmod]
    exact ProofForgeFin.DeFi.Rewards.forall_mem_modify hP hPf

theorem setNext_supply_keep (s : St) (sup bor : Nat) (h : s.supplyState.speed = sup) :
    (setNext s sup bor).supplyState = s.supplyState := by
  show (if s.supplyState.speed = sup then s.supplyState else
    { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup }) =
    s.supplyState
  exact if_pos h

theorem setNext_supply_accrue (s : St) (sup bor : Nat) (h : s.supplyState.speed ≠ sup) :
    (setNext s sup bor).supplyState =
      { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } := by
  show (if s.supplyState.speed = sup then s.supplyState else
    { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup }) =
    { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup }
  exact if_neg h

theorem setNext_borrow_keep (s : St) (sup bor : Nat) (h : s.borrowState.speed = bor) :
    (setNext s sup bor).borrowState = s.borrowState := by
  show (if s.borrowState.speed = bor then s.borrowState else
    { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor }) =
    s.borrowState
  exact if_pos h

theorem setNext_borrow_accrue (s : St) (sup bor : Nat) (h : s.borrowState.speed ≠ bor) :
    (setNext s sup bor).borrowState =
      { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } := by
  show (if s.borrowState.speed = bor then s.borrowState else
    { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor }) =
    { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor }
  exact if_neg h

theorem setNext_supply_speed (s : St) (sup bor : Nat) :
    (setNext s sup bor).supplyState.speed = sup := by
  by_cases h : s.supplyState.speed = sup
  · have hs : (setNext s sup bor).supplyState = s.supplyState :=
      setNext_supply_keep s sup bor h
    rw [hs]
    exact h
  · have hs : (setNext s sup bor).supplyState =
        { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } :=
      setNext_supply_accrue s sup bor h
    rw [hs]

theorem setNext_borrow_speed (s : St) (sup bor : Nat) :
    (setNext s sup bor).borrowState.speed = bor := by
  by_cases h : s.borrowState.speed = bor
  · have hs : (setNext s sup bor).borrowState = s.borrowState :=
      setNext_borrow_keep s sup bor h
    rw [hs]
    exact h
  · have hs : (setNext s sup bor).borrowState =
        { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } :=
      setNext_borrow_accrue s sup bor h
    rw [hs]

theorem M_init_eq : M.init = compInitialIndex := rfl

theorem initSide_index (now idx blk spd : Nat) :
    (initSide now ⟨idx, blk, spd⟩).index =
      if idx = 0 then compInitialIndex else idx := by
  unfold initSide
  split <;> rfl

theorem initSide_block (now idx blk spd : Nat) :
    (initSide now ⟨idx, blk, spd⟩).block =
      if idx = 0 then now else blk := by
  unfold initSide
  split <;> rfl

theorem initSide_speed (now idx blk spd : Nat) :
    (initSide now ⟨idx, blk, spd⟩).speed = spd := by
  unfold initSide
  split <;> rfl

/-- The clock after the upgrade is the pre-upgrade clock re-initialized. -/
theorem hclock (L : Legacy) : M.clock (upgrade L) =
    (⟨L.blockNumber, L.supplyIndex, L.supplyBlock, L.compSpeed,
      L.borrowIndex, L.borrowBlock, L.compSpeed⟩ :
      ProofForgeFin.Accumulator.Clock).reinit M.init := by
  simp only [M_clock, upgrade, initSide_index, initSide_block, initSide_speed,
    ProofForgeFin.Accumulator.Clock.reinit, M_init_eq]

/-- Every operation is one of the market's actions. -/
theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (op : Op)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  have hc : Consistent s := Consistent_of_Inv hI
  cases op with
  | mint who x =>
    by_cases hw : who < s.accts.length
    · have hok := supplyOk_of_consistent s hc who
      have hcall : comptroller s (.supplyHook who) = some (supplyNext s who) := by
        simp [comptroller, hok]
      have hexec : exec comptroller s (.mint who x) =
          (supplyNext s who).withAcct who (fun a => { a with supply := a.supply + x }) := by
        simp [exec, hw, hcall]
      have ha : M.accts ((supplyNext s who).withAcct who
          (fun a => { a with supply := a.supply + x })) =
          (M.accts (supplyNext s who)).modify who
          (fun a => { a with supply := a.supply + x }) := rfl
      have hcc : M.clock ((supplyNext s who).withAcct who
          (fun a => { a with supply := a.supply + x })) =
          M.clock (supplyNext s who) := rfl
      rw [hexec]
      apply ProofForgeFin.Accumulator.Market.Act.moves
      apply ProofForgeFin.Accumulator.Market.Settle₁.then_adjust (settle₁ s who) ha hcc _ _
      · intro a
        exact ⟨Nat.le_refl _, rfl, rfl⟩
      · intro a
        exact rfl
    · have hexec : exec comptroller s (.mint who x) = s := by simp [exec, hw]
      rw [hexec]
      apply ProofForgeFin.Accumulator.Market.Act.moves
      exact ProofForgeFin.Accumulator.Market.Reach.refl s
  | redeem who x =>
    by_cases hw : who < s.accts.length
    · have hok := supplyOk_of_consistent s hc who
      have hcall : comptroller s (.supplyHook who) = some (supplyNext s who) := by
        simp [comptroller, hok]
      by_cases hx : x ≤ ((supplyNext s who).acct who).supply
      · have hexec : exec comptroller s (.redeem who x) =
            (supplyNext s who).withAcct who (fun a => { a with supply := a.supply - x }) := by
          simp [exec, hw, hcall, hx]
        have ha : M.accts ((supplyNext s who).withAcct who
            (fun a => { a with supply := a.supply - x })) =
            (M.accts (supplyNext s who)).modify who
            (fun a => { a with supply := a.supply - x }) := rfl
        have hcc : M.clock ((supplyNext s who).withAcct who
            (fun a => { a with supply := a.supply - x })) =
            M.clock (supplyNext s who) := rfl
        rw [hexec]
        apply ProofForgeFin.Accumulator.Market.Act.moves
        apply ProofForgeFin.Accumulator.Market.Settle₁.then_adjust (settle₁ s who) ha hcc _ _
        · intro a
          exact ⟨Nat.le_refl _, rfl, rfl⟩
        · intro a
          exact rfl
      · have hexec : exec comptroller s (.redeem who x) = s := by
          simp [exec, hw, hcall, hx]
        rw [hexec]
        apply ProofForgeFin.Accumulator.Market.Act.moves
        exact ProofForgeFin.Accumulator.Market.Reach.refl s
    · have hexec : exec comptroller s (.redeem who x) = s := by simp [exec, hw]
      rw [hexec]
      apply ProofForgeFin.Accumulator.Market.Act.moves
      exact ProofForgeFin.Accumulator.Market.Reach.refl s
  | transfer src dst x =>
    by_cases hw : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · obtain ⟨hsrc, hdst, hne⟩ := hw
      have hok₁ := supplyOk_of_consistent s hc src
      have hcall₁ : comptroller s (.supplyHook src) = some (supplyNext s src) := by
        simp [comptroller, hok₁]
      have hc₁ : Consistent (supplyNext s src) := Consistent_supplyNext s hc src
      have hok₂ := supplyOk_of_consistent _ hc₁ dst
      have hcall₂ : comptroller (supplyNext s src) (.supplyHook dst) =
          some (supplyNext (supplyNext s src) dst) := by simp [comptroller, hok₂]
      by_cases hx : x ≤ ((supplyNext (supplyNext s src) dst).acct src).supply
      · have hexec : exec comptroller s (.transfer src dst x) =
            ((supplyNext (supplyNext s src) dst).withAcct src
              (fun a => { a with supply := a.supply - x })).withAcct dst
              (fun a => { a with supply := a.supply + x }) := by
          simp [exec, hsrc, hdst, hne, hcall₁, hcall₂, hx]
        have ha : M.accts (((supplyNext (supplyNext s src) dst).withAcct src
            (fun a => { a with supply := a.supply - x })).withAcct dst
            (fun a => { a with supply := a.supply + x })) =
            ((M.accts (supplyNext (supplyNext s src) dst)).modify src
              (fun a => { a with supply := a.supply - x })).modify dst
              (fun a => { a with supply := a.supply + x }) := rfl
        have hcc : M.clock (((supplyNext (supplyNext s src) dst).withAcct src
            (fun a => { a with supply := a.supply - x })).withAcct dst
            (fun a => { a with supply := a.supply + x })) =
            M.clock (supplyNext (supplyNext s src) dst) := rfl
        rw [hexec]
        apply ProofForgeFin.Accumulator.Market.Act.moves
        apply ProofForgeFin.Accumulator.Market.Settle₁.transfer
          (settle₁ s src) (settle₁ _ dst) ha hcc _ _ _ _
        · intro a
          exact ⟨Nat.le_refl _, rfl, rfl⟩
        · intro a
          exact ⟨Nat.le_refl _, rfl, rfl⟩
        · intro a
          exact rfl
        · intro a
          exact rfl
      · have hexec : exec comptroller s (.transfer src dst x) = s := by
          simp [exec, hsrc, hdst, hne, hcall₁, hcall₂, hx]
        rw [hexec]
        apply ProofForgeFin.Accumulator.Market.Act.moves
        exact ProofForgeFin.Accumulator.Market.Reach.refl s
    · have hexec : exec comptroller s (.transfer src dst x) = s := by
        simp [exec, hw]
      rw [hexec]
      apply ProofForgeFin.Accumulator.Market.Act.moves
      exact ProofForgeFin.Accumulator.Market.Reach.refl s
  | borrow who x =>
    by_cases hw : who < s.accts.length
    · have hok := borrowOk_of_consistent s hc who
      have hcall : comptroller s (.borrowHook who) = some (borrowNext s who) := by
        simp [comptroller, hok]
      have hexec : exec comptroller s (.borrow who x) =
          (borrowNext s who).withAcct who (fun a => { a with borrow := a.borrow + x }) := by
        simp [exec, hw, hcall]
      have ha : M.accts ((borrowNext s who).withAcct who
          (fun a => { a with borrow := a.borrow + x })) =
          (M.accts (borrowNext s who)).modify who
          (fun a => { a with borrow := a.borrow + x }) := rfl
      have hcc : M.clock ((borrowNext s who).withAcct who
          (fun a => { a with borrow := a.borrow + x })) =
          M.clock (borrowNext s who) := rfl
      rw [hexec]
      apply ProofForgeFin.Accumulator.Market.Act.moves
      apply ProofForgeFin.Accumulator.Market.Settle₂.then_adjust (settle₂ s who) ha hcc _ _
      · intro a
        exact ⟨Nat.le_refl _, rfl, rfl⟩
      · intro a
        exact rfl
    · have hexec : exec comptroller s (.borrow who x) = s := by simp [exec, hw]
      rw [hexec]
      apply ProofForgeFin.Accumulator.Market.Act.moves
      exact ProofForgeFin.Accumulator.Market.Reach.refl s
  | repay who x =>
    by_cases hw : who < s.accts.length
    · have hok := borrowOk_of_consistent s hc who
      have hcall : comptroller s (.borrowHook who) = some (borrowNext s who) := by
        simp [comptroller, hok]
      by_cases hx : x ≤ ((borrowNext s who).acct who).borrow
      · have hexec : exec comptroller s (.repay who x) =
            (borrowNext s who).withAcct who (fun a => { a with borrow := a.borrow - x }) := by
          simp [exec, hw, hcall, hx]
        have ha : M.accts ((borrowNext s who).withAcct who
            (fun a => { a with borrow := a.borrow - x })) =
            (M.accts (borrowNext s who)).modify who
            (fun a => { a with borrow := a.borrow - x }) := rfl
        have hcc : M.clock ((borrowNext s who).withAcct who
            (fun a => { a with borrow := a.borrow - x })) =
            M.clock (borrowNext s who) := rfl
        rw [hexec]
        apply ProofForgeFin.Accumulator.Market.Act.moves
        apply ProofForgeFin.Accumulator.Market.Settle₂.then_adjust (settle₂ s who) ha hcc _ _
        · intro a
          exact ⟨Nat.le_refl _, rfl, rfl⟩
        · intro a
          exact rfl
      · have hexec : exec comptroller s (.repay who x) = s := by
          simp [exec, hw, hcall, hx]
        rw [hexec]
        apply ProofForgeFin.Accumulator.Market.Act.moves
        exact ProofForgeFin.Accumulator.Market.Reach.refl s
    · have hexec : exec comptroller s (.repay who x) = s := by simp [exec, hw]
      rw [hexec]
      apply ProofForgeFin.Accumulator.Market.Act.moves
      exact ProofForgeFin.Accumulator.Market.Reach.refl s
  | claim who =>
    have hok := claimOk_of_consistent s hc who
    have hcall : comptroller s (.claim who) =
        some (grant (supplyNext (borrowNext s who) who) who) := by
      simp [comptroller, hok]
    have hexec : exec comptroller s (.claim who) =
        grant (supplyNext (borrowNext s who) who) who := by simp [exec, hcall]
    rw [hexec]
    apply ProofForgeFin.Accumulator.Market.Act.moves
    apply ProofForgeFin.Accumulator.Market.Reach.trans _ (grant_reach _ _)
    exact (ProofForgeFin.Accumulator.Market.Reach.single
      (ProofForgeFin.Accumulator.Market.Step.settle₂ (settle₂ s who))).tail
      (ProofForgeFin.Accumulator.Market.Step.settle₁ (settle₁ _ who))
  | setSpeeds a b =>
    have hok : setOk s a b := ⟨Or.inr hc.1, Or.inr hc.2.1⟩
    have hcall : comptroller s (.setSpeeds a b) = some (setNext s a b) := by
      simp [comptroller, hok]
    have hexec : exec comptroller s (.setSpeeds a b) = setNext s a b := by
      simp [exec, hcall]
    rw [hexec]
    apply ProofForgeFin.Accumulator.Market.Act.retune _ _ _
    · refine ⟨rfl, rfl, ?_, ?_⟩
      · by_cases heq : s.supplyState.speed = a
        · refine Or.inl ⟨?_, ?_, ?_⟩ <;>
            simp only [M_clock, setNext_supply_keep s a b heq]
        · refine Or.inr ⟨?_, ?_⟩
          · simp only [M_clock, setNext_supply_accrue s a b heq]
            exact accrue_index_bridge _ _ _
          · simp only [M_clock, setNext_supply_accrue s a b heq]
            exact accrue_block_bridge _ _ _
      · by_cases heq : s.borrowState.speed = b
        · refine Or.inl ⟨?_, ?_, ?_⟩ <;>
            simp only [M_clock, setNext_borrow_keep s a b heq]
        · refine Or.inr ⟨?_, ?_⟩
          · simp only [M_clock, setNext_borrow_accrue s a b heq]
            exact accrue_index_bridge _ _ _
          · simp only [M_clock, setNext_borrow_accrue s a b heq]
            exact accrue_block_bridge _ _ _
    · exact setNext_supply_speed s a b
    · exact setNext_borrow_speed s a b
  | advance k =>
    have hexec : exec comptroller s (.advance k) =
        { s with blockNumber := s.blockNumber + k } := rfl
    rw [hexec]
    apply ProofForgeFin.Accumulator.Market.Act.advance k
    exact ⟨rfl, rfl⟩
  | drip x =>
    have hexec : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := rfl
    rw [hexec]
    apply ProofForgeFin.Accumulator.Market.Act.moves
    apply ProofForgeFin.Accumulator.Market.Reach.single
    refine ProofForgeFin.Accumulator.Market.Step.same rfl rfl

/-- The invariant holds at the upgrade. -/
theorem start_inv (L : Legacy) (hW : L.WellFormed) :
    M.Inv (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart)
      (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart)
      (L.compSpeed, L.compSpeed) (upgrade L) := by
  obtain ⟨hs1, hsle1, hb1, hble1, hsb, hbb, hrec⟩ := hW
  exact M.inv_reinit (hclock L) hs1 hsle1 hb1 hble1 hsb hbb (fun a ha => hrec a ha)

/-- The potential at the upgrade is covered by what was owed plus the unindexed emission. -/
theorem start_pot (L : Legacy) (hW : L.WellFormed) :
    M.pot (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart)
      (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart)
      (upgrade L) ≤
      M.creditSum (upgrade L) * M.one +
      (L.accts.map L.pendingScaled).sum +
      M.one * (L.unindexedSupply + L.unindexedBorrow) := by
  obtain ⟨hs1, hsle1, hb1, hble1, hsb, hbb, hrec⟩ := hW
  have hR : ((M.accts (upgrade L)).map (M.owed L.supplyStart L.borrowStart
      ⟨L.blockNumber, L.supplyIndex, L.supplyBlock, L.compSpeed,
       L.borrowIndex, L.borrowBlock, L.compSpeed⟩)).sum =
      (L.accts.map L.pendingScaled).sum := rfl
  have hU1 : (⟨L.blockNumber, L.supplyIndex, L.supplyBlock, L.compSpeed,
      L.borrowIndex, L.borrowBlock, L.compSpeed⟩ :
      ProofForgeFin.Accumulator.Clock).un₁ = L.unindexedSupply := rfl
  have hU2 : (⟨L.blockNumber, L.supplyIndex, L.supplyBlock, L.compSpeed,
      L.borrowIndex, L.borrowBlock, L.compSpeed⟩ :
      ProofForgeFin.Accumulator.Clock).un₂ = L.unindexedBorrow := rfl
  have h := M.pot_reinit_le L.supplyStart L.borrowStart (hclock L) (fun a ha => hrec a ha)
  rw [hR, hU1, hU2] at h
  exact h

/-- The potential of one account at the upgrade. -/
theorem start_potOf (L : Legacy) (hW : L.WellFormed) (who : Account) :
    M.potOf (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart)
      (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart)
      who (upgrade L) ≤
      M.credited (M.acct (upgrade L) who) * M.one +
      M.owed L.supplyStart L.borrowStart
        ⟨L.blockNumber, L.supplyIndex, L.supplyBlock, L.compSpeed,
         L.borrowIndex, L.borrowBlock, L.compSpeed⟩ (M.acct (upgrade L) who) +
      M.one * ((if 0 < M.units₁ (M.acct (upgrade L) who) then L.unindexedSupply else 0) +
        (if 0 < M.units₂ (M.acct (upgrade L) who) then L.unindexedBorrow else 0)) := by
  obtain ⟨hs1, hsle1, hb1, hble1, hsb, hbb, hrec⟩ := hW
  have hrw : M.rec₁ (M.acct (upgrade L) who) ≤ L.supplyIndex ∧
      M.rec₂ (M.acct (upgrade L) who) ≤ L.borrowIndex := by
    refine ⟨?_, ?_⟩
    · show ((L.accts.getD who noAcct)).supplierIndex ≤ L.supplyIndex
      exact ProofForgeFin.Ledger.getD_of_forall (P := fun a => a.supplierIndex ≤ L.supplyIndex)
        L.accts who (d := noAcct) (fun a ha => (hrec a ha).1) (Nat.zero_le _)
    · show ((L.accts.getD who noAcct)).borrowerIndex ≤ L.borrowIndex
      exact ProofForgeFin.Ledger.getD_of_forall (P := fun a => a.borrowerIndex ≤ L.borrowIndex)
        L.accts who (d := noAcct) (fun a ha => (hrec a ha).2) (Nat.zero_le _)
  exact M.potOf_reinit_le L.supplyStart L.borrowStart who (hclock L) hrw

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    have hok := supplyOk_of_consistent s hc who
    simp [comptroller, hok]
  | borrowHook who =>
    have hok := borrowOk_of_consistent s hc who
    simp [comptroller, hok]
  | claim who =>
    have hok := claimOk_of_consistent s hc who
    simp [comptroller, hok]
  | setSpeeds a b =>
    have hok : setOk s a b := ⟨Or.inr hc.1, Or.inr hc.2.1⟩
    simp [comptroller, hok]
theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hW
  have h0 := start_inv L hW
  have hs := start_pot L hW
  have hone : 0 < M.one := by show 0 < 10 ^ 36; decide
  exact M.rewards_bounded (run comptroller) emitted speedsAfter (exec_act _ _) hone h0 hs ops

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hW
  have h0 := start_inv L hW
  have hs := start_potOf L hW who
  have hone : 0 < M.one := by show 0 < 10 ^ 36; decide
  exact M.account_rewards_bounded (run comptroller) emitted speedsAfter (exec_act _ _) hone h0 who hs ops

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hW hN
  have h0 := start_inv L hW
  have hone : 0 < M.one := by show 0 < 10 ^ 36; decide
  obtain ⟨h1, h2⟩ := hN
  exact M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone h0 history ops who h1 h2

end CompRewards
