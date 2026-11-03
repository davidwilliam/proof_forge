import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Ledger

namespace CompRewards

open ProofForgeFin.Accumulator ProofForgeFin.DeFi.Rewards

/-- Next state of a supply hook, in the spec's own terms. -/
def supplyNext (s : St) (who : Account) : St :=
  { s with
    supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
    accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }

/-- Next state of a borrow hook, in the spec's own terms. -/
def borrowNext (s : St) (who : Account) : St :=
  { s with
    borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
    accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }

/-- Next state of a speed change, in the spec's own terms. -/
def speedsNext (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }

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

def speedsOk (s : St) (sup bor : Nat) : Prop :=
  (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
  (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber)

instance (s : St) (who : Account) : Decidable (supplyOk s who) := by
  unfold supplyOk; infer_instance
instance (s : St) (who : Account) : Decidable (borrowOk s who) := by
  unfold borrowOk; infer_instance
instance (s : St) (a b : Nat) : Decidable (speedsOk s a b) := by
  unfold speedsOk; infer_instance

def supplyOpt (s : St) (who : Account) : Option St :=
  if supplyOk s who then some (supplyNext s who) else none

def borrowOpt (s : St) (who : Account) : Option St :=
  if borrowOk s who then some (borrowNext s who) else none

def speedsOpt (s : St) (sup bor : Nat) : Option St :=
  if speedsOk s sup bor then some (speedsNext s sup bor) else none

def claimOpt (s : St) (who : Account) : Option St :=
  match borrowOpt s who with
  | none => none
  | some m₁ =>
    match supplyOpt m₁ who with
    | none => none
    | some m₂ => some (grant m₂ who)

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => supplyOpt s who
  | .borrowHook who => borrowOpt s who
  | .claim who => claimOpt s who
  | .setSpeeds a b => speedsOpt s a b

open ProofForgeFin.Ledger

theorem accrue_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrualStart_le_of (rec idx newIdx : Nat) (h1 : rec ≤ idx) (h2 : idx ≤ newIdx) :
    accrualStart rec newIdx ≤ newIdx := by
  unfold accrualStart
  split
  · rename_i hrec
    split
    · omega
    · exact Nat.zero_le _
  · omega

theorem acct_sup_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  unfold St.acct
  exact getD_of_forall _ _ (fun a ha => (hmem a ha).1) (by simp [noAcct])

theorem acct_bor_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  unfold St.acct
  exact getD_of_forall _ _ (fun a ha => (hmem a ha).2) (by simp [noAcct])

theorem supplyOk_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    supplyOk s who := by
  unfold supplyOk
  refine ⟨hc.1, ?_⟩
  exact accrualStart_le_of _ _ _
    (acct_sup_le s who hc) (accrue_le _ _ _)

theorem borrowOk_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    borrowOk s who := by
  unfold borrowOk
  refine ⟨hc.2.1, ?_⟩
  exact accrualStart_le_of _ _ _
    (acct_bor_le s who hc) (accrue_le _ _ _)

theorem borrowNext_supplyState (s : St) (who : Account) :
    (borrowNext s who).supplyState = s.supplyState := rfl

theorem borrowNext_block (s : St) (who : Account) :
    (borrowNext s who).blockNumber = s.blockNumber := rfl

theorem borrowNext_totalSupply (s : St) (who : Account) :
    totalSupply (borrowNext s who) = totalSupply s := by
  unfold totalSupply borrowNext
  simp only
  exact sum_map_modify_eq _ _ _ _ noAcct (fun _ => rfl)

theorem borrowNext_supplierIndex (s : St) (who v : Account) :
    ((borrowNext s who).acct v).supplierIndex = (s.acct v).supplierIndex := by
  unfold borrowNext St.acct
  simp only
  exact getD_modify_of_keeps _ _ _ _ (fun a : Acct => a.supplierIndex) (fun _ => rfl)

theorem borrowNext_supply (s : St) (who v : Account) :
    ((borrowNext s who).acct v).supply = (s.acct v).supply := by
  unfold borrowNext St.acct
  simp only
  exact getD_modify_of_keeps _ _ _ _ (fun a : Acct => a.supply) (fun _ => rfl)

theorem supplyNext_borrowState (s : St) (who : Account) :
    (supplyNext s who).borrowState = s.borrowState := rfl

theorem supplyNext_block (s : St) (who : Account) :
    (supplyNext s who).blockNumber = s.blockNumber := rfl

theorem supplyNext_consistent_block_supply (s : St) (who : Account) (hc : Consistent s) :
    (borrowNext s who).supplyState.block ≤ (borrowNext s who).blockNumber := by
  rw [borrowNext_supplyState, borrowNext_block]
  exact hc.1

theorem supplyOk_of_borrowNext (s : St) (who : Account) (hc : Consistent s) :
    supplyOk (borrowNext s who) who := by
  have h := supplyOk_of_consistent s who hc
  unfold supplyOk at h ⊢
  rw [borrowNext_supplyState, borrowNext_block, borrowNext_totalSupply,
    borrowNext_supplierIndex] at ⊢
  exact h

theorem supplyOpt_some (s : St) (who : Account) (m : St) (h : supplyOpt s who = some m) :
    supplyOk s who ∧ supplyNext s who = m := by
  unfold supplyOpt at h
  split at h
  · rename_i hok
    cases h
    exact ⟨hok, rfl⟩
  · contradiction

theorem borrowOpt_some (s : St) (who : Account) (m : St) (h : borrowOpt s who = some m) :
    borrowOk s who ∧ borrowNext s who = m := by
  unfold borrowOpt at h
  split at h
  · rename_i hok
    cases h
    exact ⟨hok, rfl⟩
  · contradiction

theorem speedsOpt_some (s : St) (a b : Nat) (m : St) (h : speedsOpt s a b = some m) :
    speedsOk s a b ∧ speedsNext s a b = m := by
  unfold speedsOpt at h
  split at h
  · rename_i hok
    cases h
    exact ⟨hok, rfl⟩
  · contradiction

theorem supplyDistributed_eq (s : St) (who : Account) :
    SupplyDistributed s who (supplyNext s who) ↔ supplyOk s who := by
  constructor
  · intro h
    obtain ⟨hb, hs, _⟩ := h
    exact ⟨hb, hs⟩
  · intro h
    obtain ⟨hb, hs⟩ := h
    exact ⟨hb, hs, rfl⟩

theorem borrowDistributed_eq (s : St) (who : Account) :
    BorrowDistributed s who (borrowNext s who) ↔ borrowOk s who := by
  constructor
  · intro h
    obtain ⟨hb, hs, _⟩ := h
    exact ⟨hb, hs⟩
  · intro h
    obtain ⟨hb, hs⟩ := h
    exact ⟨hb, hs, rfl⟩

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    have h2 : supplyOpt s who = some (supplyNext s who) := by
      unfold supplyOpt
      rw [if_pos (supplyOk_of_consistent s who hc)]
    exact Option.isSome_iff_exists.mpr ⟨_, h2⟩
  | borrowHook who =>
    have h2 : borrowOpt s who = some (borrowNext s who) := by
      unfold borrowOpt
      rw [if_pos (borrowOk_of_consistent s who hc)]
    exact Option.isSome_iff_exists.mpr ⟨_, h2⟩
  | claim who =>
    have hB : borrowOpt s who = some (borrowNext s who) := by
      unfold borrowOpt
      rw [if_pos (borrowOk_of_consistent s who hc)]
    have hS : supplyOpt (borrowNext s who) who = some (supplyNext (borrowNext s who) who) := by
      unfold supplyOpt
      rw [if_pos (supplyOk_of_borrowNext s who hc)]
    show (claimOpt s who).isSome
    simp [claimOpt, hB, hS]
  | setSpeeds a b =>
    have hok : speedsOk s a b := by
      unfold speedsOk
      obtain ⟨h1, h2, _⟩ := hc
      exact ⟨fun _ => h1, fun _ => h2⟩
    have h2 : speedsOpt s a b = some (speedsNext s a b) := by
      unfold speedsOpt
      rw [if_pos hok]
    exact Option.isSome_iff_exists.mpr ⟨_, h2⟩

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  have h2 : supplyOpt s who = some s' := h
  obtain ⟨hok, heq⟩ := supplyOpt_some s who s' h2
  subst heq
  exact (supplyDistributed_eq s who).mpr hok

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  have h2 : borrowOpt s who = some s' := h
  obtain ⟨hok, heq⟩ := borrowOpt_some s who s' h2
  subst heq
  exact (borrowDistributed_eq s who).mpr hok

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  have h2 : claimOpt s who = some s' := h
  unfold claimOpt at h2
  cases hB : borrowOpt s who with
  | none => simp [hB] at h2
  | some m₁ =>
    simp only [hB] at h2
    cases hS : supplyOpt m₁ who with
    | none => simp [hS] at h2
    | some m₂ =>
      simp only [hS] at h2
      cases h2
      obtain ⟨hokB, heqB⟩ := borrowOpt_some s who m₁ hB
      obtain ⟨hokS, heqS⟩ := supplyOpt_some m₁ who m₂ hS
      subst heqB
      subst heqS
      exact ⟨_, _, (borrowDistributed_eq s who).mpr hokB,
        (supplyDistributed_eq _ who).mpr hokS, rfl⟩

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  have h2 : speedsOpt s a b = some s' := h
  obtain ⟨hok, heq⟩ := speedsOpt_some s a b s' h2
  subst heq
  obtain ⟨h1, h2⟩ := hok
  exact ⟨h1, h2, rfl⟩
/-- Market reading for the two-sided bound. Supply is side 1, borrow side 2. -/
def M : Market St Acct where
  one := doubleScale
  init := compInitialIndex
  clock s := ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed,
    s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩
  accts s := s.accts
  dflt := noAcct
  units₁ := fun a => a.supply
  units₂ := fun a => a.borrow
  rec₁ := fun a => a.supplierIndex
  rec₂ := fun a => a.borrowerIndex
  credited := fun a => a.accrued + a.wallet
  dflt_units₁ := rfl
  dflt_units₂ := rfl

theorem M_total1 (s : St) : M.total₁ s = totalSupply s := rfl
theorem M_total2 (s : St) : M.total₂ s = totalBorrows s := rfl
theorem M_creditSum (s : St) : M.creditSum s = St.credited s := rfl
theorem M_credited (s : St) (w : Account) :
    M.credited (M.acct s w) = St.creditedTo s w := rfl
theorem M_units1 (s : St) (w : Account) :
    M.units₁ (M.acct s w) = (s.acct w).supply := rfl
theorem M_units2 (s : St) (w : Account) :
    M.units₂ (M.acct s w) = (s.acct w).borrow := rfl

theorem accrue_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split <;> rfl

theorem accrue_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split <;> rfl

theorem accrue_index (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      catchUp doubleScale sd.index sd.block sd.speed now total := by
  unfold accrueSide catchUp
  split
  · rfl
  · rfl

theorem settle_supply (s : St) (who : Account) :
    M.Settle₁ who s (supplyNext s who) := by
  refine ⟨?_, _, rfl, ?_⟩
  · show M.clock (supplyNext s who) = (M.clock s).catchUp₁ M.one (M.total₁ s)
    rw [M_total1]
    show Clock.mk _ _ _ _ _ _ _ = _
    simp only [M, supplyNext, Clock.catchUp₁_mk]
    rw [accrue_index, accrue_block, accrue_speed]
  · intro a
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    have e : (M.clock (supplyNext s who)).index₁ =
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
    rw [e]
    exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

theorem settle_borrow (s : St) (who : Account) :
    M.Settle₂ who s (borrowNext s who) := by
  refine ⟨?_, _, rfl, ?_⟩
  · show M.clock (borrowNext s who) = (M.clock s).catchUp₂ M.one (M.total₂ s)
    rw [M_total2]
    show Clock.mk _ _ _ _ _ _ _ = _
    simp only [M, borrowNext, Clock.catchUp₂_mk]
    rw [accrue_index, accrue_block, accrue_speed]
  · intro a
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    have e : (M.clock (borrowNext s who)).index₂ =
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
    rw [e]
    exact Nat.le_of_eq (Nat.add_right_comm _ _ _)
theorem inv_consistent (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St)
    (h : M.Inv g₁ g₂ sp s) : Consistent s := by
  obtain ⟨hl1, hl2, hrec, _, _, _, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa [M] using hl1
  · simpa [M] using hl2
  · intro a ha
    have := hrec a ha
    simpa [M] using this

theorem adjusts_supply_add (x : Nat) :
    M.AdjustsAt (fun a : Acct => { a with supply := a.supply + x }) := by
  intro a
  exact ⟨Nat.le_refl _, rfl, rfl⟩

theorem adjusts_supply_sub (x : Nat) :
    M.AdjustsAt (fun a : Acct => { a with supply := a.supply - x }) := by
  intro a
  exact ⟨Nat.le_refl _, rfl, rfl⟩

theorem adjusts_borrow_add (x : Nat) :
    M.AdjustsAt (fun a : Acct => { a with borrow := a.borrow + x }) := by
  intro a
  exact ⟨Nat.le_refl _, rfl, rfl⟩

theorem adjusts_borrow_sub (x : Nat) :
    M.AdjustsAt (fun a : Acct => { a with borrow := a.borrow - x }) := by
  intro a
  exact ⟨Nat.le_refl _, rfl, rfl⟩

theorem adjusts_grant :
    M.AdjustsAt (fun a : Acct => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  intro a
  refine ⟨?_, rfl, rfl⟩
  show (0 + (a.wallet + a.accrued)) ≤ a.accrued + a.wallet
  omega

theorem grant_clock (s : St) (who : Account) : M.clock (grant s who) = M.clock s := by
  unfold grant
  split <;> rfl

theorem grant_is_adjust_or_same (s : St) (who : Account) :
    M.Step s (grant s who) := by
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · have hc : M.clock (grant s who) = M.clock s := grant_clock s who
    have ha : M.accts (grant s who) = (M.accts s).modify who
        (fun a : Acct => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
      show (grant s who).accts = s.accts.modify who _
      unfold grant
      simp [h]
    exact .adjust ⟨hc, _, ha, adjusts_grant, .inl fun _ => rfl, .inl fun _ => rfl⟩
  · have hc : M.clock (grant s who) = M.clock s := grant_clock s who
    have ha : M.accts (grant s who) = M.accts s := by
      show (grant s who).accts = s.accts
      unfold grant
      simp [h]
    exact .same hc ha

open ProofForgeFin.Accumulator in
theorem side_supply_move (s : St) (sup bor : Nat) :
    Market.SideMove doubleScale (M.total₁ s) (M.clock s).now (M.clock s).index₁
      (M.clock s).last₁ (M.clock s).rate₁
      (M.clock (speedsNext s sup bor)).index₁
      (M.clock (speedsNext s sup bor)).last₁
      (M.clock (speedsNext s sup bor)).rate₁ := by
  have hT : M.total₁ s = totalSupply s := rfl
  unfold speedsNext
  split
  · left
    exact ⟨rfl, rfl, rfl⟩
  · right
    refine ⟨?_, ?_⟩
    · show (M.clock _).index₁ = catchUp doubleScale _ _ _ _ _
      rw [hT]
      simp only [M]
      exact accrue_index _ _ _
    · show (M.clock _).last₁ = (M.clock s).now
      simp only [M]
      exact accrue_block _ _ _

open ProofForgeFin.Accumulator in
theorem side_borrow_move (s : St) (sup bor : Nat) :
    Market.SideMove doubleScale (M.total₂ s) (M.clock s).now (M.clock s).index₂
      (M.clock s).last₂ (M.clock s).rate₂
      (M.clock (speedsNext s sup bor)).index₂
      (M.clock (speedsNext s sup bor)).last₂
      (M.clock (speedsNext s sup bor)).rate₂ := by
  have hT : M.total₂ s = totalBorrows s := rfl
  by_cases h : s.borrowState.speed = bor
  · left
    have hi : (M.clock (speedsNext s sup bor)).index₂ = (M.clock s).index₂ := by
      simp only [M, speedsNext, h, ↓reduceIte]
    have hl : (M.clock (speedsNext s sup bor)).last₂ = (M.clock s).last₂ := by
      simp only [M, speedsNext, h, ↓reduceIte]
    have hr : (M.clock (speedsNext s sup bor)).rate₂ = (M.clock s).rate₂ := by
      simp only [M, speedsNext, h, ↓reduceIte]
    rw [hi, hl, hr]
    exact ⟨rfl, rfl, rfl⟩
  · right
    have hi : (M.clock (speedsNext s sup bor)).index₂ =
        catchUp doubleScale (M.clock s).index₂ (M.clock s).last₂ (M.clock s).rate₂
          (M.clock s).now (M.total₂ s) := by
      rw [hT]
      simp only [M, speedsNext, h, ↓reduceIte]
      exact accrue_index _ _ _
    have hl : (M.clock (speedsNext s sup bor)).last₂ = (M.clock s).now := by
      simp only [M, speedsNext, h, ↓reduceIte]
      exact accrue_block _ _ _
    exact ⟨hi, hl⟩

theorem speeds_retune (s : St) (sup bor : Nat) : M.Retune s (speedsNext s sup bor) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (speedsNext s sup bor).accts = s.accts
    unfold speedsNext
    split <;> split <;> rfl
  · show (M.clock (speedsNext s sup bor)).now = (M.clock s).now
    simp only [M, speedsNext]
  · exact side_supply_move s sup bor
  · exact side_borrow_move s sup bor

theorem speeds_rate1 (s : St) (sup bor : Nat) :
    (M.clock (speedsNext s sup bor)).rate₁ = sup := by
  simp only [M, speedsNext]
  by_cases h : s.supplyState.speed = sup <;> simp [h]

theorem speeds_rate2 (s : St) (sup bor : Nat) :
    (M.clock (speedsNext s sup bor)).rate₂ = bor := by
  simp only [M, speedsNext]
  by_cases h : s.borrowState.speed = bor <;> simp [h]

theorem advance_step (s : St) (k : Nat) :
    M.Advance k s { s with blockNumber := s.blockNumber + k } := by
  refine ⟨?_, ?_⟩
  · show M.clock { s with blockNumber := s.blockNumber + k } = (M.clock s).advance k
    simp only [M, Clock.advance_mk]
  · show M.accts { s with blockNumber := s.blockNumber + k } = M.accts s
    rfl

theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (op : Op)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  have hc : Consistent s := inv_consistent g₁ g₂ sp s hI
  cases op with
  | mint who x =>
    have hok := supplyOk_of_consistent s who hc
    have hOpt : supplyOpt s who = some (supplyNext s who) := by
      unfold supplyOpt; rw [if_pos hok]
    have hC : comptroller s (.supplyHook who) = some (supplyNext s who) := hOpt
    have hE : exec comptroller s (.mint who x) =
        if who < s.accts.length then
          (supplyNext s who).withAcct who (fun a : Acct => { a with supply := a.supply + x })
        else s := by simp only [exec, hC]
    by_cases hlen : who < s.accts.length
    · have hE2 : exec comptroller s (.mint who x) =
          (supplyNext s who).withAcct who (fun a : Acct => { a with supply := a.supply + x }) := by
        simp [hE, hlen]
      rw [hE2]
      have hR : M.Reach s ((supplyNext s who).withAcct who
          (fun a : Acct => { a with supply := a.supply + x })) :=
        Market.Settle₁.then_adjust (settle_supply s who) rfl rfl
          (adjusts_supply_add x) (fun _ => rfl)
      have hsp : nextSpeeds sp (.mint who x) = sp := rfl
      have he : emittedBy sp (.mint who x) = 0 := rfl
      rw [hsp, he]
      exact .moves hR
    · have hE2 : exec comptroller s (.mint who x) = s := by simp [hE, hlen]
      rw [hE2]
      have hsp : nextSpeeds sp (.mint who x) = sp := rfl
      have he : emittedBy sp (.mint who x) = 0 := rfl
      rw [hsp, he]
      exact .moves (Market.Reach.refl s)
  | redeem who x =>
    have hok := supplyOk_of_consistent s who hc
    have hOpt : supplyOpt s who = some (supplyNext s who) := by
      unfold supplyOpt; rw [if_pos hok]
    have hC : comptroller s (.supplyHook who) = some (supplyNext s who) := hOpt
    by_cases hlen : who < s.accts.length
    · by_cases hx : x ≤ ((supplyNext s who).acct who).supply
      · have hE : exec comptroller s (.redeem who x) =
            (supplyNext s who).withAcct who (fun a : Acct => { a with supply := a.supply - x }) := by
          simp [exec, hC, hlen, hx]
        rw [hE]
        have hR : M.Reach s ((supplyNext s who).withAcct who
            (fun a : Acct => { a with supply := a.supply - x })) :=
          Market.Settle₁.then_adjust (settle_supply s who) rfl rfl
            (adjusts_supply_sub x) (fun _ => rfl)
        have hsp : nextSpeeds sp (.redeem who x) = sp := rfl
        have he : emittedBy sp (.redeem who x) = 0 := rfl
        rw [hsp, he]
        exact .moves hR
      · have hE : exec comptroller s (.redeem who x) = s := by
          simp [exec, hC, hlen, hx]
        rw [hE]
        have hsp : nextSpeeds sp (.redeem who x) = sp := rfl
        have he : emittedBy sp (.redeem who x) = 0 := rfl
        rw [hsp, he]
        exact .moves (Market.Reach.refl s)
    · have hE : exec comptroller s (.redeem who x) = s := by
        simp [exec, hlen]
      rw [hE]
      have hsp : nextSpeeds sp (.redeem who x) = sp := rfl
      have he : emittedBy sp (.redeem who x) = 0 := rfl
      rw [hsp, he]
      exact .moves (Market.Reach.refl s)
  | transfer src dst x =>
    by_cases hlen : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · obtain ⟨hs, hd, hne⟩ := hlen
      have hB1 : comptroller s (.supplyHook src) = some (supplyNext s src) := by
        have hok := supplyOk_of_consistent s src hc
        have hOpt : supplyOpt s src = some (supplyNext s src) := by
          unfold supplyOpt; rw [if_pos hok]
        exact hOpt
      have hI1 : M.Inv g₁ g₂ sp (supplyNext s src) :=
        ((settle_supply s src).inv hI)
      have hc1 : Consistent (supplyNext s src) := inv_consistent g₁ g₂ sp _ hI1
      have hok2 := supplyOk_of_consistent (supplyNext s src) dst hc1
      have hB2 : comptroller (supplyNext s src) (.supplyHook dst) =
          some (supplyNext (supplyNext s src) dst) := by
        have hOpt : supplyOpt (supplyNext s src) dst =
            some (supplyNext (supplyNext s src) dst) := by
          unfold supplyOpt; rw [if_pos hok2]
        exact hOpt
      by_cases hx : x ≤ ((supplyNext (supplyNext s src) dst).acct src).supply
      · have hE : exec comptroller s (.transfer src dst x) =
            ((supplyNext (supplyNext s src) dst).withAcct src
              (fun a : Acct => { a with supply := a.supply - x })).withAcct dst
              (fun a : Acct => { a with supply := a.supply + x }) := by
          simp [exec, hs, hd, hne, hB1, hB2, hx]
        rw [hE]
        have hR : M.Reach s (((supplyNext (supplyNext s src) dst).withAcct src
            (fun a : Acct => { a with supply := a.supply - x })).withAcct dst
            (fun a : Acct => { a with supply := a.supply + x })) :=
          Market.Settle₁.transfer (settle_supply s src) (settle_supply _ dst)
            rfl rfl (adjusts_supply_sub x) (adjusts_supply_add x)
            (fun _ => rfl) (fun _ => rfl)
        have hsp : nextSpeeds sp (.transfer src dst x) = sp := rfl
        have he : emittedBy sp (.transfer src dst x) = 0 := rfl
        rw [hsp, he]
        exact .moves hR
      · have hE : exec comptroller s (.transfer src dst x) = s := by
          simp [exec, hs, hd, hne, hB1, hB2, hx]
        rw [hE]
        have hsp : nextSpeeds sp (.transfer src dst x) = sp := rfl
        have he : emittedBy sp (.transfer src dst x) = 0 := rfl
        rw [hsp, he]
        exact .moves (Market.Reach.refl s)
    · have hE : exec comptroller s (.transfer src dst x) = s := by
        simp [exec, hlen]
      rw [hE]
      have hsp : nextSpeeds sp (.transfer src dst x) = sp := rfl
      have he : emittedBy sp (.transfer src dst x) = 0 := rfl
      rw [hsp, he]
      exact .moves (Market.Reach.refl s)
  | borrow who x =>
    have hok := borrowOk_of_consistent s who hc
    have hOpt : borrowOpt s who = some (borrowNext s who) := by
      unfold borrowOpt; rw [if_pos hok]
    have hC : comptroller s (.borrowHook who) = some (borrowNext s who) := hOpt
    have hE : exec comptroller s (.borrow who x) =
        if who < s.accts.length then
          (borrowNext s who).withAcct who (fun a : Acct => { a with borrow := a.borrow + x })
        else s := by simp only [exec, hC]
    by_cases hlen : who < s.accts.length
    · have hE2 : exec comptroller s (.borrow who x) =
          (borrowNext s who).withAcct who (fun a : Acct => { a with borrow := a.borrow + x }) := by
        simp [hE, hlen]
      rw [hE2]
      have hR : M.Reach s ((borrowNext s who).withAcct who
          (fun a : Acct => { a with borrow := a.borrow + x })) :=
        Market.Settle₂.then_adjust (settle_borrow s who) rfl rfl
          (adjusts_borrow_add x) (fun _ => rfl)
      have hsp : nextSpeeds sp (.borrow who x) = sp := rfl
      have he : emittedBy sp (.borrow who x) = 0 := rfl
      rw [hsp, he]
      exact .moves hR
    · have hE2 : exec comptroller s (.borrow who x) = s := by simp [hE, hlen]
      rw [hE2]
      have hsp : nextSpeeds sp (.borrow who x) = sp := rfl
      have he : emittedBy sp (.borrow who x) = 0 := rfl
      rw [hsp, he]
      exact .moves (Market.Reach.refl s)
  | repay who x =>
    have hok := borrowOk_of_consistent s who hc
    have hOpt : borrowOpt s who = some (borrowNext s who) := by
      unfold borrowOpt; rw [if_pos hok]
    have hC : comptroller s (.borrowHook who) = some (borrowNext s who) := hOpt
    by_cases hlen : who < s.accts.length
    · by_cases hx : x ≤ ((borrowNext s who).acct who).borrow
      · have hE : exec comptroller s (.repay who x) =
            (borrowNext s who).withAcct who (fun a : Acct => { a with borrow := a.borrow - x }) := by
          simp [exec, hC, hlen, hx]
        rw [hE]
        have hR : M.Reach s ((borrowNext s who).withAcct who
            (fun a : Acct => { a with borrow := a.borrow - x })) :=
          Market.Settle₂.then_adjust (settle_borrow s who) rfl rfl
            (adjusts_borrow_sub x) (fun _ => rfl)
        have hsp : nextSpeeds sp (.repay who x) = sp := rfl
        have he : emittedBy sp (.repay who x) = 0 := rfl
        rw [hsp, he]
        exact .moves hR
      · have hE : exec comptroller s (.repay who x) = s := by
          simp [exec, hC, hlen, hx]
        rw [hE]
        have hsp : nextSpeeds sp (.repay who x) = sp := rfl
        have he : emittedBy sp (.repay who x) = 0 := rfl
        rw [hsp, he]
        exact .moves (Market.Reach.refl s)
    · have hE : exec comptroller s (.repay who x) = s := by
        simp [exec, hlen]
      rw [hE]
      have hsp : nextSpeeds sp (.repay who x) = sp := rfl
      have he : emittedBy sp (.repay who x) = 0 := rfl
      rw [hsp, he]
      exact .moves (Market.Reach.refl s)
  | claim who =>
    have hB : borrowOpt s who = some (borrowNext s who) := by
      unfold borrowOpt; rw [if_pos (borrowOk_of_consistent s who hc)]
    have hS : supplyOpt (borrowNext s who) who =
        some (supplyNext (borrowNext s who) who) := by
      unfold supplyOpt; rw [if_pos (supplyOk_of_borrowNext s who hc)]
    have hE : exec comptroller s (.claim who) =
        grant (supplyNext (borrowNext s who) who) who := by
      show (claimOpt s who).getD s = _
      simp [claimOpt, hB, hS]
    rw [hE]
    have hR : M.Reach s (grant (supplyNext (borrowNext s who) who) who) :=
      ((Market.Reach.single (.settle₂ (settle_borrow s who))).tail
        (.settle₁ (settle_supply _ who))).tail
        (grant_is_adjust_or_same _ _)
    have hsp : nextSpeeds sp (.claim who) = sp := rfl
    have he : emittedBy sp (.claim who) = 0 := rfl
    rw [hsp, he]
    exact .moves hR
  | setSpeeds a b =>
    have hok : speedsOk s a b := ⟨fun _ => hc.1, fun _ => hc.2.1⟩
    have hOpt : speedsOpt s a b = some (speedsNext s a b) := by
      unfold speedsOpt; rw [if_pos hok]
    have hE : exec comptroller s (.setSpeeds a b) = speedsNext s a b := by
      show (speedsOpt s a b).getD s = _
      simp [hOpt]
    rw [hE]
    have hsp : nextSpeeds sp (.setSpeeds a b) = (a, b) := rfl
    have he : emittedBy sp (.setSpeeds a b) = 0 := rfl
    rw [hsp, he]
    exact .retune (speeds_retune s a b) (speeds_rate1 s a b) (speeds_rate2 s a b)
  | advance k =>
    have hE : exec comptroller s (.advance k) = { s with blockNumber := s.blockNumber + k } := rfl
    rw [hE]
    have hsp : nextSpeeds sp (.advance k) = sp := rfl
    have he : emittedBy sp (.advance k) = k * (sp.1 + sp.2) := rfl
    rw [hsp, he]
    exact .advance k (advance_step s k)
  | drip x =>
    have hE : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := rfl
    rw [hE]
    have hR : M.Step s { s with reserve := s.reserve + x } :=
      .same (by simp only [M]) rfl
    have hsp : nextSpeeds sp (.drip x) = sp := rfl
    have he : emittedBy sp (.drip x) = 0 := rfl
    rw [hsp, he]
    exact .moves (Market.Reach.single hR)
open ProofForgeFin.Accumulator in
theorem upgrade_clock (L : Legacy) :
    M.clock (upgrade L) =
      (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
        L.borrowIndex L.borrowBlock L.compSpeed).reinit M.init := by
  show Clock.mk _ _ _ _ _ _ _ = _
  simp only [M, upgrade, initSide, Clock.reinit]
  split <;> split <;> rfl

theorem hone : 0 < M.one := by
  show 0 < doubleScale
  unfold doubleScale
  decide

theorem start_inv (L : Legacy) (hW : L.WellFormed) :
    M.Inv (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart)
      (L.compSpeed, L.compSpeed) (upgrade L) := by
  have hc := upgrade_clock L
  obtain ⟨hs1, hsi1, hb1, hbi1, hbl1, hbl2, hmem⟩ := hW
  exact M.inv_reinit hc hs1 hsi1 hb1 hbi1 hbl1 hbl2 (fun a ha => by simpa [M] using hmem a ha)

theorem req_rewards_bounded : RewardsBounded comptroller := by
  intro L ops hW
  have hI := start_inv L hW
  obtain ⟨_, _, _, _, _, _, hmem⟩ := hW
  have hc := upgrade_clock L
  have hr : ∀ a ∈ M.accts (upgrade L),
      M.rec₁ a ≤ (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
        L.borrowIndex L.borrowBlock L.compSpeed).index₁ ∧
      M.rec₂ a ≤ (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
        L.borrowIndex L.borrowBlock L.compSpeed).index₂ :=
    fun a ha => by simpa [M] using hmem a ha
  have hs := M.pot_reinit_le L.supplyStart L.borrowStart hc hr
  have hR := M.rewards_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone hI hs ops
  have e1 : M.creditSum (run comptroller (upgrade L) ops) =
      (run comptroller (upgrade L) ops).credited := rfl
  have e2 : M.creditSum (upgrade L) = (upgrade L).credited := rfl
  have e6 : M.one = doubleScale := rfl
  rw [e1, e2, e6] at hR
  have eU1 : (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
      L.borrowIndex L.borrowBlock L.compSpeed).un₁ = L.unindexedSupply := rfl
  have eU2 : (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
      L.borrowIndex L.borrowBlock L.compSpeed).un₂ = L.unindexedBorrow := rfl
  simp only [M, upgrade] at hR
  simp only [Legacy.owed, eU1, eU2] at hR ⊢
  exact hR

theorem req_account_bounded : AccountBounded comptroller := by
  intro L ops who hW
  have hI := start_inv L hW
  have hc0 : M.rec₁ (M.acct (upgrade L) who) ≤
      (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
        L.borrowIndex L.borrowBlock L.compSpeed).index₁ ∧
      M.rec₂ (M.acct (upgrade L) who) ≤
      (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
        L.borrowIndex L.borrowBlock L.compSpeed).index₂ := by
    obtain ⟨_, _, _, _, _, _, hmem⟩ := hW
    have h1 : M.rec₁ (M.acct (upgrade L) who) ≤ L.supplyIndex := by
      have h := getD_of_forall (d := noAcct) L.accts who
        (fun a ha => (hmem a ha).1) (Nat.zero_le _)
      exact h
    have h2 : M.rec₂ (M.acct (upgrade L) who) ≤ L.borrowIndex := by
      have h := getD_of_forall (d := noAcct) L.accts who
        (fun a ha => (hmem a ha).2) (Nat.zero_le _)
      exact h
    exact ⟨h1, h2⟩
  have hs := M.potOf_reinit_le L.supplyStart L.borrowStart who
    (upgrade_clock L) hc0
  have hR := M.account_rewards_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone hI who hs ops
  have e1 : M.credited (M.acct (run comptroller (upgrade L) ops) who) =
      (run comptroller (upgrade L) ops).creditedTo who := rfl
  have e2 : M.credited (M.acct (upgrade L) who) = (upgrade L).creditedTo who := rfl
  have e3 : M.owed L.supplyStart L.borrowStart
      (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
        L.borrowIndex L.borrowBlock L.compSpeed)
      (M.acct (upgrade L) who) =
      L.pendingScaled (L.accts.getD who noAcct) := rfl
  have e4 : M.units₁ (M.acct (upgrade L) who) = (L.accts.getD who noAcct).supply := rfl
  have e5 : M.units₂ (M.acct (upgrade L) who) = (L.accts.getD who noAcct).borrow := rfl
  have e6 : M.one = doubleScale := rfl
  have e7 : (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
      L.borrowIndex L.borrowBlock L.compSpeed).un₁ = L.unindexedSupply := rfl
  have e8 : (Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
      L.borrowIndex L.borrowBlock L.compSpeed).un₂ = L.unindexedBorrow := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8] at hR
  simpa [Legacy.owedTo] using hR

theorem req_no_backdated : NoBackdatedRewards comptroller := by
  intro L history ops who hW hpos
  have hI := start_inv L hW
  have h1 : M.units₁ (M.acct (run comptroller (upgrade L) history) who) = 0 := by
    rw [M_units1]
    exact hpos.1
  have h2 : M.units₂ (M.acct (run comptroller (upgrade L) history) who) = 0 := by
    rw [M_units2]
    exact hpos.2
  have hR := M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone hI history ops who h1 h2
  have e1 : M.credited (M.acct (run comptroller (run comptroller (upgrade L) history) ops) who) =
      (run comptroller (run comptroller (upgrade L) history) ops).creditedTo who := rfl
  have e2 : M.credited (M.acct (run comptroller (upgrade L) history) who) =
      (run comptroller (upgrade L) history).creditedTo who := rfl
  rw [e1, e2] at hR
  exact hR

end CompRewards
