import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
import ProofForgeFin.Ledger
import ProofForgeFin.DeFi.Rewards

namespace CompRewards

open ProofForgeFin.Accumulator

/-- Supply side after the hook: index up to date, `who` credited. -/
def nextSupply (s : St) (who : Account) : St :=
  { s with
    supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
    accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }

/-- Preconditions of the supply hook (both `sub_` underflows absent). -/
def supplyPre (s : St) (who : Account) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index

instance (s : St) (who : Account) : Decidable (supplyPre s who) := by
  unfold supplyPre; infer_instance

/-- Borrow side after the hook. -/
def nextBorrow (s : St) (who : Account) : St :=
  { s with
    borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
    accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }

/-- Preconditions of the borrow hook. -/
def borrowPre (s : St) (who : Account) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index

instance (s : St) (who : Account) : Decidable (borrowPre s who) := by
  unfold borrowPre; infer_instance

/-- Claim result: borrow side, then supply side, then payment. -/
def claimNext (s : St) (who : Account) : St :=
  grant (nextSupply (nextBorrow s who) who) who

/-- Preconditions of a claim: both hooks' preconditions in sequence. -/
def claimPre (s : St) (who : Account) : Prop :=
  borrowPre s who ∧ supplyPre (nextBorrow s who) who

instance (s : St) (who : Account) : Decidable (claimPre s who) := by
  unfold claimPre; infer_instance

/-- Speed-change result. -/
def nextSpeedState (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }

/-- Preconditions of a speed change. -/
def speedsPre (s : St) (sup bor : Nat) : Prop :=
  (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
  (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber)

instance (s : St) (sup bor : Nat) : Decidable (speedsPre s sup bor) := by
  unfold speedsPre; infer_instance

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => if supplyPre s who then some (nextSupply s who) else none
  | .borrowHook who => if borrowPre s who then some (nextBorrow s who) else none
  | .claim who => if claimPre s who then some (claimNext s who) else none
  | .setSpeeds a b => if speedsPre s a b then some (nextSpeedState s a b) else none

theorem accrue_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem start_le (r old new : Nat) (h1 : r ≤ old) (h2 : old ≤ new) :
    accrualStart r new ≤ new := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp only [hr, ite_true]
    by_cases hi : compInitialIndex ≤ new
    · simp [hi]
    · simp [hi]
  · simp [hr]; omega

theorem borrow_block_eq (s : St) (who : Account) :
    (nextBorrow s who).blockNumber = s.blockNumber := by
  unfold nextBorrow; rfl

theorem borrow_supply_eq (s : St) (who : Account) :
    (nextBorrow s who).supplyState = s.supplyState := by
  unfold nextBorrow; rfl

theorem borrow_total_eq (s : St) (who : Account) :
    totalSupply (nextBorrow s who) = totalSupply s := by
  unfold nextBorrow totalSupply
  exact ProofForgeFin.Ledger.sum_map_modify_eq _ _ _ _ noAcct (fun h => rfl)

theorem borrow_supp_idx_eq (s : St) (who : Account) :
    ((nextBorrow s who).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold nextBorrow St.acct
  exact ProofForgeFin.Ledger.getD_modify_of_keeps _ _ _ _ _ (fun a => rfl)

theorem acct_sup_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  unfold St.acct
  obtain ⟨_, _, hall⟩ := hc
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hall _ hm).1
  · rw [hm]; simp [noAcct]

theorem acct_bor_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  unfold St.acct
  obtain ⟨_, _, hall⟩ := hc
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hall _ hm).2
  · rw [hm]; simp [noAcct]

theorem supplyPre_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    supplyPre s who := by
  have hc0 := hc
  unfold Consistent at hc
  unfold supplyPre
  obtain ⟨h1, _, _⟩ := hc
  refine ⟨h1, ?_⟩
  exact start_le _ _ _ (acct_sup_le s who hc0) (accrue_le _ _ _)

theorem borrowPre_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    borrowPre s who := by
  have hc0 := hc
  unfold Consistent at hc
  unfold borrowPre
  obtain ⟨_, h2, _⟩ := hc
  refine ⟨h2, ?_⟩
  exact start_le _ _ _ (acct_bor_le s who hc0) (accrue_le _ _ _)

theorem claimPre_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    claimPre s who := by
  unfold claimPre
  refine ⟨borrowPre_of_consistent s who hc, ?_⟩
  have hsup : supplyPre (nextBorrow s who) who := by
    unfold supplyPre
    have hc1 : s.supplyState.block ≤ s.blockNumber := by
      have hcC := hc
      unfold Consistent at hcC
      obtain ⟨h1, _, _⟩ := hcC
      exact h1
    have hb : (nextBorrow s who).supplyState.block ≤ (nextBorrow s who).blockNumber := by
      rw [borrow_supply_eq, borrow_block_eq]
      exact hc1
    refine ⟨hb, ?_⟩
    have e1 : (nextBorrow s who).supplyState = s.supplyState := borrow_supply_eq s who
    have e2 : (nextBorrow s who).blockNumber = s.blockNumber := borrow_block_eq s who
    have e3 : totalSupply (nextBorrow s who) = totalSupply s := borrow_total_eq s who
    have e4 : ((nextBorrow s who).acct who).supplierIndex = (s.acct who).supplierIndex :=
      borrow_supp_idx_eq s who
    rw [e1, e2, e3, e4]
    exact start_le _ _ _ (acct_sup_le s who hc) (accrue_le _ _ _)
  exact hsup

theorem speedsPre_of_consistent (s : St) (a b : Nat) (hc : Consistent s) :
    speedsPre s a b := by
  unfold Consistent at hc
  unfold speedsPre
  obtain ⟨h1, h2, _⟩ := hc
  exact ⟨fun _ => h1, fun _ => h2⟩

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    simp [supplyPre_of_consistent s who hc]
  | borrowHook who =>
    unfold comptroller
    simp [borrowPre_of_consistent s who hc]
  | claim who =>
    unfold comptroller
    simp [claimPre_of_consistent s who hc]
  | setSpeeds a b =>
    unfold comptroller
    simp [speedsPre_of_consistent s a b hc]
theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  have hc : comptroller s (.supplyHook who) = if supplyPre s who then some (nextSupply s who) else none := rfl
  rw [hc] at h
  by_cases hp : supplyPre s who
  · simp [hp] at h
    subst h
    unfold supplyPre at hp
    unfold SupplyDistributed nextSupply
    obtain ⟨h1, h2⟩ := hp
    exact ⟨h1, h2, rfl⟩
  · simp [hp] at h
theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  have hc : comptroller s (.borrowHook who) = if borrowPre s who then some (nextBorrow s who) else none := rfl
  rw [hc] at h
  by_cases hp : borrowPre s who
  · simp [hp] at h
    subst h
    unfold borrowPre at hp
    unfold BorrowDistributed nextBorrow
    obtain ⟨h1, h2⟩ := hp
    exact ⟨h1, h2, rfl⟩
  · simp [hp] at h
theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  have hc : comptroller s (.claim who) = if claimPre s who then some (claimNext s who) else none := rfl
  rw [hc] at h
  by_cases hp : claimPre s who
  · simp [hp] at h
    subst h
    unfold claimPre at hp
    unfold Claimed claimNext nextBorrow nextSupply
    obtain ⟨hb, hs⟩ := hp
    unfold borrowPre at hb
    unfold supplyPre at hs
    exact ⟨_, _, ⟨hb.1, hb.2, rfl⟩, ⟨hs.1, hs.2, rfl⟩, rfl⟩
  · simp [hp] at h
theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  have hc : comptroller s (.setSpeeds a b) = if speedsPre s a b then some (nextSpeedState s a b) else none := rfl
  rw [hc] at h
  by_cases hp : speedsPre s a b
  · simp [hp] at h
    subst h
    unfold speedsPre at hp
    unfold SpeedsSet nextSpeedState
    obtain ⟨h1, h2⟩ := hp
    exact ⟨h1, h2, rfl⟩
  · simp [hp] at h
/-- Reading the state as a two-sided reward market. Side 1 is supply, side 2 is borrow. -/
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

theorem total1_eq (s : St) : M.total₁ s = totalSupply s := rfl

theorem total2_eq (s : St) : M.total₂ s = totalBorrows s := rfl

theorem one_eq : M.one = doubleScale := rfl

theorem clock_supply (s : St) (w : Nat) :
    M.clock (nextSupply s w) = (M.clock s).catchUp₁ M.one (M.total₁ s) := by
  have hT : M.total₁ s = totalSupply s := rfl
  have hO : M.one = doubleScale := rfl
  show Clock.mk (nextSupply s w).blockNumber (nextSupply s w).supplyState.index
    (nextSupply s w).supplyState.block (nextSupply s w).supplyState.speed
    (nextSupply s w).borrowState.index (nextSupply s w).borrowState.block
    (nextSupply s w).borrowState.speed
    = Clock.catchUp₁ M.one (M.total₁ s) (Clock.mk s.blockNumber s.supplyState.index
      s.supplyState.block s.supplyState.speed s.borrowState.index s.borrowState.block
      s.borrowState.speed)
  simp only [nextSupply, Clock.catchUp₁_mk, hT, hO]
  congr 1
  · unfold accrueSide ProofForgeFin.Accumulator.catchUp
    split <;> rfl
  · unfold accrueSide
    split <;> rfl
  · unfold accrueSide
    split <;> rfl

theorem clock_borrow (s : St) (w : Nat) :
    M.clock (nextBorrow s w) = (M.clock s).catchUp₂ M.one (M.total₂ s) := by
  have hT : M.total₂ s = totalBorrows s := rfl
  have hO : M.one = doubleScale := rfl
  show Clock.mk (nextBorrow s w).blockNumber (nextBorrow s w).supplyState.index
    (nextBorrow s w).supplyState.block (nextBorrow s w).supplyState.speed
    (nextBorrow s w).borrowState.index (nextBorrow s w).borrowState.block
    (nextBorrow s w).borrowState.speed
    = Clock.catchUp₂ M.one (M.total₂ s) (Clock.mk s.blockNumber s.supplyState.index
      s.supplyState.block s.supplyState.speed s.borrowState.index s.borrowState.block
      s.borrowState.speed)
  simp only [nextBorrow, Clock.catchUp₂_mk, hT, hO]
  congr 1
  · unfold accrueSide ProofForgeFin.Accumulator.catchUp
    split <;> rfl
  · unfold accrueSide
    split <;> rfl
  · unfold accrueSide
    split <;> rfl

theorem settle_supply (s : St) (w : Nat) : M.Settle₁ w s (nextSupply s w) := by
  constructor
  · exact clock_supply s w
  · exact ⟨_, rfl, fun a => ⟨rfl, rfl, rfl, rfl, Nat.le_of_eq (Nat.add_right_comm _ _ _)⟩⟩

theorem settle_borrow (s : St) (w : Nat) : M.Settle₂ w s (nextBorrow s w) := by
  constructor
  · exact clock_borrow s w
  · exact ⟨_, rfl, fun a => ⟨rfl, rfl, rfl, rfl, Nat.le_of_eq (Nat.add_right_comm _ _ _)⟩⟩

theorem consistent_of_inv (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St)
    (hI : M.Inv g₁ g₂ sp s) : Consistent s := by
  unfold Consistent
  refine ⟨?_, ?_, ?_⟩
  · have h : (M.clock s).last₁ ≤ (M.clock s).now := hI.last₁
    simpa [M] using h
  · have h : (M.clock s).last₂ ≤ (M.clock s).now := hI.last₂
    simpa [M] using h
  · intro a ha
    have h := hI.recs a (by simpa [M] using ha)
    simpa [M] using h

theorem side1_move (s : St) (sup bor : Nat) :
    Market.SideMove M.one (M.total₁ s) (M.clock s).now (M.clock s).index₁ (M.clock s).last₁
      (M.clock s).rate₁ (M.clock (nextSpeedState s sup bor)).index₁
      (M.clock (nextSpeedState s sup bor)).last₁
      (M.clock (nextSpeedState s sup bor)).rate₁ := by
  by_cases heq : s.supplyState.speed = sup
  · left
    have e1 : (M.clock (nextSpeedState s sup bor)).index₁ = (M.clock s).index₁ := by
      show (nextSpeedState s sup bor).supplyState.index = s.supplyState.index
      unfold nextSpeedState
      rw [if_pos heq]
    have e2 : (M.clock (nextSpeedState s sup bor)).last₁ = (M.clock s).last₁ := by
      show (nextSpeedState s sup bor).supplyState.block = s.supplyState.block
      unfold nextSpeedState
      rw [if_pos heq]
    have e3 : (M.clock (nextSpeedState s sup bor)).rate₁ = (M.clock s).rate₁ := by
      show (nextSpeedState s sup bor).supplyState.speed = s.supplyState.speed
      unfold nextSpeedState
      rw [if_pos heq]
    exact ⟨e1, e2, e3⟩
  · right
    have e1 : (M.clock (nextSpeedState s sup bor)).index₁ =
        ProofForgeFin.Accumulator.catchUp M.one (M.clock s).index₁ (M.clock s).last₁
          (M.clock s).rate₁ (M.clock s).now (M.total₁ s) := by
      show (nextSpeedState s sup bor).supplyState.index =
        ProofForgeFin.Accumulator.catchUp doubleScale s.supplyState.index s.supplyState.block
          s.supplyState.speed s.blockNumber (totalSupply s)
      unfold nextSpeedState
      rw [if_neg heq]
      unfold accrueSide ProofForgeFin.Accumulator.catchUp
      split <;> rfl
    have e2 : (M.clock (nextSpeedState s sup bor)).last₁ = (M.clock s).now := by
      show (nextSpeedState s sup bor).supplyState.block = s.blockNumber
      unfold nextSpeedState
      rw [if_neg heq]
      unfold accrueSide
      split <;> rfl
    exact ⟨e1, e2⟩

theorem side2_move (s : St) (sup bor : Nat) :
    Market.SideMove M.one (M.total₂ s) (M.clock s).now (M.clock s).index₂ (M.clock s).last₂
      (M.clock s).rate₂ (M.clock (nextSpeedState s sup bor)).index₂
      (M.clock (nextSpeedState s sup bor)).last₂
      (M.clock (nextSpeedState s sup bor)).rate₂ := by
  by_cases heq : s.borrowState.speed = bor
  · left
    have e1 : (M.clock (nextSpeedState s sup bor)).index₂ = (M.clock s).index₂ := by
      show (nextSpeedState s sup bor).borrowState.index = s.borrowState.index
      unfold nextSpeedState
      simp [heq]
    have e2 : (M.clock (nextSpeedState s sup bor)).last₂ = (M.clock s).last₂ := by
      show (nextSpeedState s sup bor).borrowState.block = s.borrowState.block
      unfold nextSpeedState
      simp [heq]
    have e3 : (M.clock (nextSpeedState s sup bor)).rate₂ = (M.clock s).rate₂ := by
      show (nextSpeedState s sup bor).borrowState.speed = s.borrowState.speed
      unfold nextSpeedState
      simp [heq]
    exact ⟨e1, e2, e3⟩
  · right
    have e1 : (M.clock (nextSpeedState s sup bor)).index₂ =
        ProofForgeFin.Accumulator.catchUp M.one (M.clock s).index₂ (M.clock s).last₂
          (M.clock s).rate₂ (M.clock s).now (M.total₂ s) := by
      show (nextSpeedState s sup bor).borrowState.index =
        ProofForgeFin.Accumulator.catchUp doubleScale s.borrowState.index s.borrowState.block
          s.borrowState.speed s.blockNumber (totalBorrows s)
      unfold nextSpeedState
      simp [heq]
      unfold accrueSide ProofForgeFin.Accumulator.catchUp
      split <;> rfl
    have e2 : (M.clock (nextSpeedState s sup bor)).last₂ = (M.clock s).now := by
      show (nextSpeedState s sup bor).borrowState.block = s.blockNumber
      unfold nextSpeedState
      simp [heq]
      unfold accrueSide
      split <;> rfl
    exact ⟨e1, e2⟩

theorem retune_state (s : St) (sup bor : Nat) : M.Retune s (nextSpeedState s sup bor) := by
  constructor
  · rfl
  · rfl
  · exact side1_move s sup bor
  · exact side2_move s sup bor

theorem mint_reach (s : St) (who x : Nat) :
    M.Reach s ((nextSupply s who).withAcct who fun a => { a with supply := a.supply + x }) :=
  Market.Settle₁.then_adjust (settle_supply s who) rfl rfl
    (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl)

theorem borrow_reach (s : St) (who x : Nat) :
    M.Reach s ((nextBorrow s who).withAcct who fun a => { a with borrow := a.borrow + x }) :=
  Market.Settle₂.then_adjust (settle_borrow s who) rfl rfl
    (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl)

theorem grant_adjust_pay (m : St) (who : Nat)
    (hc : 0 < (m.acct who).accrued ∧ (m.acct who).accrued ≤ m.reserve) :
    M.Adjust who m (grant m who) := by
  let fpay : Acct → Acct := fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }
  constructor
  · simp [grant, hc, M]
  · refine ⟨fpay, by simp [grant, hc, M, fpay], ?_, .inl fun _ => rfl, .inl fun _ => rfl⟩
    intro a
    have e1 : M.credited (fpay a) = a.wallet + a.accrued := by simp [M, fpay]
    have e2 : M.credited a = a.accrued + a.wallet := by simp [M]
    rw [e1, e2]
    exact ⟨by omega, rfl, rfl⟩

theorem grant_same_nopay (m : St) (who : Nat)
    (hc : ¬ (0 < (m.acct who).accrued ∧ (m.acct who).accrued ≤ m.reserve)) :
    M.Step m (grant m who) := by
  apply Market.Step.same
  · simp [grant, hc, M]
  · simp [grant, hc, M]

theorem redeem_reach (s : St) (who x : Nat) :
    M.Reach s ((nextSupply s who).withAcct who fun a => { a with supply := a.supply - x }) :=
  Market.Settle₁.then_adjust (settle_supply s who) rfl rfl
    (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl)

theorem repay_reach (s : St) (who x : Nat) :
    M.Reach s ((nextBorrow s who).withAcct who fun a => { a with borrow := a.borrow - x }) :=
  Market.Settle₂.then_adjust (settle_borrow s who) rfl rfl
    (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl)

theorem transfer_reach (s : St) (src dst x : Nat) :
    let s1 := nextSupply s src
    let s2 := nextSupply s1 dst
    M.Reach s ((s2.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst
      fun a => { a with supply := a.supply + x }) :=
  Market.Settle₁.transfer (settle_supply s src) (settle_supply (nextSupply s src) dst)
    rfl rfl (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
    (fun _ => rfl) (fun _ => rfl)

theorem claim_reach (s : St) (who : Nat) : M.Reach s (grant (nextSupply (nextBorrow s who) who) who) := by
  let m2 := nextSupply (nextBorrow s who) who
  have h2 := settle_borrow s who
  have h1 := settle_supply (nextBorrow s who) who
  have hbase : M.Reach s m2 :=
    (Market.Reach.single (Market.Step.settle₂ h2)).tail (Market.Step.settle₁ h1)
  by_cases hc : 0 < (m2.acct who).accrued ∧ (m2.acct who).accrued ≤ m2.reserve
  · exact hbase.tail (Market.Step.adjust (grant_adjust_pay m2 who hc))
  · exact hbase.tail (grant_same_nopay m2 who hc)

theorem advance_reach (s : St) (k : Nat) :
    M.Advance k s { s with blockNumber := s.blockNumber + k } := by
  constructor
  · show M.clock { s with blockNumber := s.blockNumber + k } = (M.clock s).advance k
    simp [M, Clock.advance]
  · rfl

theorem drip_step (s : St) (x : Nat) : M.Step s { s with reserve := s.reserve + x } := by
  apply Market.Step.same
  · rfl
  · rfl

theorem supply_kept_supply (s : St) (who : Account) :
    ((nextSupply s who).acct who).supply = (s.acct who).supply := by
  unfold nextSupply St.acct
  exact ProofForgeFin.Ledger.getD_modify_of_keeps _ _ _ _ _ (fun a => rfl)

theorem borrow_kept_borrow (s : St) (who : Account) :
    ((nextBorrow s who).acct who).borrow = (s.acct who).borrow := by
  unfold nextBorrow St.acct
  exact ProofForgeFin.Ledger.getD_modify_of_keeps _ _ _ _ _ (fun a => rfl)

theorem supply_kept_borrow (s : St) (who v : Account) :
    ((nextSupply s who).acct v).borrow = (s.acct v).borrow := by
  unfold nextSupply St.acct
  exact ProofForgeFin.Ledger.getD_modify_of_keeps _ _ _ _ _ (fun a => rfl)

theorem borrow_kept_supply (s : St) (who v : Account) :
    ((nextBorrow s who).acct v).supply = (s.acct v).supply := by
  unfold nextBorrow St.acct
  exact ProofForgeFin.Ledger.getD_modify_of_keeps _ _ _ _ _ (fun a => rfl)

theorem supply_supply_kept (s : St) (who v : Account) :
    ((nextSupply s who).acct v).supply = (s.acct v).supply := by
  unfold nextSupply St.acct
  exact ProofForgeFin.Ledger.getD_modify_of_keeps _ _ _ _ _ (fun a => rfl)

theorem borrow_borrow_kept (s : St) (who v : Account) :
    ((nextBorrow s who).acct v).borrow = (s.acct v).borrow := by
  unfold nextBorrow St.acct
  exact ProofForgeFin.Ledger.getD_modify_of_keeps _ _ _ _ _ (fun a => rfl)

theorem transfer_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (src dst x : Nat)
    (hI : M.Inv g₁ g₂ sp s) : M.Act sp s sp 0 (exec comptroller s (.transfer src dst x)) := by
  have hcon := consistent_of_inv g₁ g₂ sp s hI
  by_cases hok : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
  · obtain ⟨hsrc, hdst, hne⟩ := hok
    have hpre1 := supplyPre_of_consistent s src hcon
    have hcomp1 : comptroller s (.supplyHook src) = some (nextSupply s src) := by
      simp [comptroller, hpre1]
    have hI1 : M.Inv g₁ g₂ sp (nextSupply s src) := (settle_supply s src).inv hI
    have hcon1 := consistent_of_inv g₁ g₂ sp (nextSupply s src) hI1
    have hpre2 := supplyPre_of_consistent (nextSupply s src) dst hcon1
    have hcomp2 : comptroller (nextSupply s src) (.supplyHook dst) =
        some (nextSupply (nextSupply s src) dst) := by
      simp [comptroller, hpre2]
    have hsup : ((nextSupply (nextSupply s src) dst).acct src).supply = (s.acct src).supply := by
      rw [supply_supply_kept _ dst src, supply_kept_supply]
    by_cases hbal : x ≤ (s.acct src).supply
    · have hex : exec comptroller s (.transfer src dst x) =
          ((nextSupply (nextSupply s src) dst).withAcct src fun a => { a with supply := a.supply - x }).withAcct dst
            fun a => { a with supply := a.supply + x } := by
        simp [exec, hsrc, hdst, hne, hcomp1, hcomp2, hsup, hbal]
      rw [hex]
      exact .moves (transfer_reach s src dst x)
    · have hex : exec comptroller s (.transfer src dst x) = s := by
        simp [exec, hsrc, hdst, hne, hcomp1, hcomp2, hsup, hbal]
      rw [hex]
      exact .moves (Market.Reach.refl s)
  · have hex : exec comptroller s (.transfer src dst x) = s := by
      simp [exec, hok]
    rw [hex]
    exact .moves (Market.Reach.refl s)

theorem claim_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who : Nat)
    (hI : M.Inv g₁ g₂ sp s) : M.Act sp s sp 0 (exec comptroller s (.claim who)) := by
  have hcon := consistent_of_inv g₁ g₂ sp s hI
  have hpre := claimPre_of_consistent s who hcon
  have hcomp : comptroller s (.claim who) = some (claimNext s who) := by
    simp [comptroller, hpre]
  have hex : exec comptroller s (.claim who) = claimNext s who := by
    simp [exec, hcomp, claimNext]
  rw [hex]
  have hr : claimNext s who = grant (nextSupply (nextBorrow s who) who) who := rfl
  rw [hr]
  exact .moves (claim_reach s who)

theorem setSpeeds_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (a b : Nat)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (a, b) 0 (exec comptroller s (.setSpeeds a b)) := by
  have hcon := consistent_of_inv g₁ g₂ sp s hI
  have hpre := speedsPre_of_consistent s a b hcon
  have hcomp : comptroller s (.setSpeeds a b) = some (nextSpeedState s a b) := by
    simp [comptroller, hpre]
  have hex : exec comptroller s (.setSpeeds a b) = nextSpeedState s a b := by
    simp [exec, hcomp]
  rw [hex]
  have e1 : (M.clock (nextSpeedState s a b)).rate₁ = a := by
    show (nextSpeedState s a b).supplyState.speed = a
    unfold nextSpeedState
    by_cases h : s.supplyState.speed = a
    · simp [h]
    · simp [h]
  have e2 : (M.clock (nextSpeedState s a b)).rate₂ = b := by
    show (nextSpeedState s a b).borrowState.speed = b
    unfold nextSpeedState
    by_cases h : s.borrowState.speed = b
    · simp [h]
    · simp [h]
  exact .retune (retune_state s a b) e1 e2

theorem advance_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (k : Nat)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s sp (k * (sp.1 + sp.2)) (exec comptroller s (.advance k)) := by
  have hex : exec comptroller s (.advance k) = { s with blockNumber := s.blockNumber + k } := rfl
  rw [hex]
  exact .advance k (advance_reach s k)

theorem drip_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (x : Nat)
    (hI : M.Inv g₁ g₂ sp s) : M.Act sp s sp 0 (exec comptroller s (.drip x)) := by
  have hex : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := rfl
  rw [hex]
  exact .moves (Market.Reach.single (drip_step s x))

theorem mint_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who x : Nat)
    (hI : M.Inv g₁ g₂ sp s) : M.Act sp s sp 0 (exec comptroller s (.mint who x)) := by
  have hcon := consistent_of_inv g₁ g₂ sp s hI
  have hpre := supplyPre_of_consistent s who hcon
  have hcomp : comptroller s (.supplyHook who) = some (nextSupply s who) := by
    simp [comptroller, hpre]
  by_cases hlen : who < s.accts.length
  · have hex : exec comptroller s (.mint who x) =
        (nextSupply s who).withAcct who fun a => { a with supply := a.supply + x } := by
      simp [exec, hlen, hcomp]
    rw [hex]
    exact .moves (mint_reach s who x)
  · have hex : exec comptroller s (.mint who x) = s := by
      simp [exec, hlen]
    rw [hex]
    exact .moves (Market.Reach.refl s)

theorem borrow_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who x : Nat)
    (hI : M.Inv g₁ g₂ sp s) : M.Act sp s sp 0 (exec comptroller s (.borrow who x)) := by
  have hcon := consistent_of_inv g₁ g₂ sp s hI
  have hpre := borrowPre_of_consistent s who hcon
  have hcomp : comptroller s (.borrowHook who) = some (nextBorrow s who) := by
    simp [comptroller, hpre]
  by_cases hlen : who < s.accts.length
  · have hex : exec comptroller s (.borrow who x) =
        (nextBorrow s who).withAcct who fun a => { a with borrow := a.borrow + x } := by
      simp [exec, hlen, hcomp]
    rw [hex]
    exact .moves (borrow_reach s who x)
  · have hex : exec comptroller s (.borrow who x) = s := by
      simp [exec, hlen]
    rw [hex]
    exact .moves (Market.Reach.refl s)

theorem redeem_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who x : Nat)
    (hI : M.Inv g₁ g₂ sp s) : M.Act sp s sp 0 (exec comptroller s (.redeem who x)) := by
  have hcon := consistent_of_inv g₁ g₂ sp s hI
  have hpre := supplyPre_of_consistent s who hcon
  have hcomp : comptroller s (.supplyHook who) = some (nextSupply s who) := by
    simp [comptroller, hpre]
  by_cases hlen : who < s.accts.length
  · have hsup : ((nextSupply s who).acct who).supply = (s.acct who).supply :=
      supply_kept_supply s who
    by_cases hbal : x ≤ (s.acct who).supply
    · have hex : exec comptroller s (.redeem who x) =
          (nextSupply s who).withAcct who fun a => { a with supply := a.supply - x } := by
        simp [exec, hlen, hcomp, hsup, hbal]
      rw [hex]
      exact .moves (redeem_reach s who x)
    · have hex : exec comptroller s (.redeem who x) = s := by
        simp [exec, hlen, hcomp, hsup, hbal]
      rw [hex]
      exact .moves (Market.Reach.refl s)
  · have hex : exec comptroller s (.redeem who x) = s := by
      simp [exec, hlen]
    rw [hex]
    exact .moves (Market.Reach.refl s)

theorem repay_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who x : Nat)
    (hI : M.Inv g₁ g₂ sp s) : M.Act sp s sp 0 (exec comptroller s (.repay who x)) := by
  have hcon := consistent_of_inv g₁ g₂ sp s hI
  have hpre := borrowPre_of_consistent s who hcon
  have hcomp : comptroller s (.borrowHook who) = some (nextBorrow s who) := by
    simp [comptroller, hpre]
  by_cases hlen : who < s.accts.length
  · have hbor : ((nextBorrow s who).acct who).borrow = (s.acct who).borrow :=
      borrow_kept_borrow s who
    by_cases hbal : x ≤ (s.acct who).borrow
    · have hex : exec comptroller s (.repay who x) =
          (nextBorrow s who).withAcct who fun a => { a with borrow := a.borrow - x } := by
        simp [exec, hlen, hcomp, hbor, hbal]
      rw [hex]
      exact .moves (repay_reach s who x)
    · have hex : exec comptroller s (.repay who x) = s := by
        simp [exec, hlen, hcomp, hbor, hbal]
      rw [hex]
      exact .moves (Market.Reach.refl s)
  · have hex : exec comptroller s (.repay who x) = s := by
      simp [exec, hlen]
    rw [hex]
    exact .moves (Market.Reach.refl s)

theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (op : Op)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  cases op with
  | mint who x => exact mint_act g₁ g₂ sp s who x hI
  | redeem who x => exact redeem_act g₁ g₂ sp s who x hI
  | transfer src dst x => exact transfer_act g₁ g₂ sp s src dst x hI
  | borrow who x => exact borrow_act g₁ g₂ sp s who x hI
  | repay who x => exact repay_act g₁ g₂ sp s who x hI
  | claim who => exact claim_act g₁ g₂ sp s who hI
  | setSpeeds a b => exact setSpeeds_act g₁ g₂ sp s a b hI
  | advance k => exact advance_act g₁ g₂ sp s k hI
  | drip x => exact drip_act g₁ g₂ sp s x hI

/-- The clock before the upgrade. -/
def legacyClock (L : Legacy) : Clock :=
  ⟨L.blockNumber, L.supplyIndex, L.supplyBlock, L.compSpeed,
    L.borrowIndex, L.borrowBlock, L.compSpeed⟩

theorem clock_upgrade (L : Legacy) :
    M.clock (upgrade L) = (legacyClock L).reinit M.init := by
  have hM : M.init = compInitialIndex := rfl
  rw [hM]
  unfold upgrade initSide legacyClock M Clock.reinit
  by_cases hs : L.supplyIndex = 0 <;> by_cases hb : L.borrowIndex = 0 <;>
    simp [hs, hb]

theorem hone_pos : 0 < M.one := by
  show 0 < doubleScale
  unfold doubleScale
  decide

theorem owed_eq (L : Legacy) (a : Acct) :
    M.owed L.supplyStart L.borrowStart (legacyClock L) a = L.pendingScaled a := rfl

theorem creditSum_eq (s : St) : M.creditSum s = s.credited := rfl

theorem un1_eq (L : Legacy) : (legacyClock L).un₁ = L.unindexedSupply := rfl

theorem un2_eq (L : Legacy) : (legacyClock L).un₂ = L.unindexedBorrow := rfl

theorem credited_eq (s : St) (who : Account) :
    M.credited (M.acct s who) = s.creditedTo who := rfl

theorem inv_upgrade (L : Legacy) (hW : L.WellFormed) :
    M.Inv (reinitStart M.init (legacyClock L).index₁ L.supplyStart)
      (reinitStart M.init (legacyClock L).index₂ L.borrowStart)
      ((legacyClock L).rate₁, (legacyClock L).rate₂) (upgrade L) := by
  apply M.inv_reinit (clock_upgrade L)
  · unfold Legacy.WellFormed at hW
    obtain ⟨h1, _, _, _, _, _, _⟩ := hW
    simpa [M] using h1
  · unfold Legacy.WellFormed at hW
    obtain ⟨_, h2, _, _, _, _, _⟩ := hW
    simpa [M, legacyClock] using h2
  · unfold Legacy.WellFormed at hW
    obtain ⟨_, _, h3, _, _, _, _⟩ := hW
    simpa [M] using h3
  · unfold Legacy.WellFormed at hW
    obtain ⟨_, _, _, h4, _, _, _⟩ := hW
    simpa [M, legacyClock] using h4
  · unfold Legacy.WellFormed at hW
    obtain ⟨_, _, _, _, h5, _, _⟩ := hW
    simpa [M, legacyClock] using h5
  · unfold Legacy.WellFormed at hW
    obtain ⟨_, _, _, _, _, h6, _⟩ := hW
    simpa [M, legacyClock] using h6
  · intro a ha
    have ha' : a ∈ L.accts := by simpa [M, upgrade] using ha
    unfold Legacy.WellFormed at hW
    obtain ⟨_, _, _, _, _, _, hall⟩ := hW
    have h := hall a ha'
    simpa [M, legacyClock] using h

theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hW
  have hI := inv_upgrade L hW
  have hpot := M.pot_reinit_le L.supplyStart L.borrowStart (clock_upgrade L)
    (fun a ha => by
      have ha' : a ∈ L.accts := by simpa [M, upgrade] using ha
      unfold Legacy.WellFormed at hW
      obtain ⟨_, _, _, _, _, _, hall⟩ := hW
      have h := hall a ha'
      simpa [M, legacyClock] using h)
  have h0 : M.Inv (reinitStart M.init (legacyClock L).index₁ L.supplyStart)
      (reinitStart M.init (legacyClock L).index₂ L.borrowStart)
      (L.compSpeed, L.compSpeed) (upgrade L) := by
    simpa [M, legacyClock] using hI
  exact M.rewards_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone_pos h0 hpot ops

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hW
  have hI := inv_upgrade L hW
  have hr : M.rec₁ (M.acct (upgrade L) who) ≤ (legacyClock L).index₁ ∧
      M.rec₂ (M.acct (upgrade L) who) ≤ (legacyClock L).index₂ := by
    have h1 : M.acct (upgrade L) who = L.accts.getD who noAcct := rfl
    rw [h1]
    have hW0 := hW
    unfold Legacy.WellFormed at hW
    obtain ⟨_, _, _, _, _, _, hall⟩ := hW
    rcases ProofForgeFin.Ledger.getD_mem_or L.accts who noAcct with hm | hm
    · have h := hall _ hm
      simpa [M, legacyClock] using h
    · rw [hm]; simp [M, legacyClock, noAcct]
  have hpot := M.potOf_reinit_le L.supplyStart L.borrowStart who (clock_upgrade L) hr
  have h0 : M.Inv (reinitStart M.init (legacyClock L).index₁ L.supplyStart)
      (reinitStart M.init (legacyClock L).index₂ L.borrowStart)
      (L.compSpeed, L.compSpeed) (upgrade L) := by
    simpa [M, legacyClock] using hI
  exact M.account_rewards_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone_pos h0 who hpot ops

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hW hN
  have hI := inv_upgrade L hW
  have h0 : M.Inv (reinitStart M.init (legacyClock L).index₁ L.supplyStart)
      (reinitStart M.init (legacyClock L).index₂ L.borrowStart)
      (L.compSpeed, L.compSpeed) (upgrade L) := by
    simpa [M, legacyClock] using hI
  have h1 : M.units₁ (M.acct (run comptroller (upgrade L) history) who) = 0 := hN.1
  have h2 : M.units₂ (M.acct (run comptroller (upgrade L) history) who) = 0 := hN.2
  exact M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter
    (exec_act _ _) hone_pos h0 history ops who h1 h2

end CompRewards
