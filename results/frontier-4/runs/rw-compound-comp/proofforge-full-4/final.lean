import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
namespace CompRewards
open ProofForgeFin.Accumulator

/-- Supply side brought up to date and `who` credited, in closed form. -/
def supplyNext (s : St) (who : Account) : St :=
  let sd := accrueSide s.supplyState s.blockNumber (totalSupply s)
  { s with
    supplyState := sd,
    accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := sd.index,
        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex sd.index) sd.index } }

/-- Borrow side brought up to date and `who` credited, in closed form. -/
def borrowNext (s : St) (who : Account) : St :=
  let bd := accrueSide s.borrowState s.blockNumber (totalBorrows s)
  { s with
    borrowState := bd,
    accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := bd.index,
        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex bd.index) bd.index } }

/-- Claim in closed form: borrow side for `who`, then supply side, then payment. -/
def claimNext (s : St) (who : Account) : St :=
  grant (supplyNext (borrowNext s who) who) who

/-- Speed change in closed form. -/
def speedsNext (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }

/-- Precondition for a supply hook. -/
def supplyOk (s : St) (who : Account) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index

/-- Precondition for a borrow hook. -/
def borrowOk (s : St) (who : Account) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index

/-- Precondition for a claim: both sides distribute. -/
def claimOk (s : St) (who : Account) : Prop :=
  borrowOk s who ∧ supplyOk (borrowNext s who) who

/-- Precondition for a speed change. -/
def speedsOk (s : St) (sup bor : Nat) : Prop :=
  (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
  (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber)

instance (s : St) (who : Account) : Decidable (supplyOk s who) := by
  unfold supplyOk; infer_instance
instance (s : St) (who : Account) : Decidable (borrowOk s who) := by
  unfold borrowOk; infer_instance
instance (s : St) (who : Account) : Decidable (claimOk s who) := by
  unfold claimOk; infer_instance
instance (s : St) (a b : Nat) : Decidable (speedsOk s a b) := by
  unfold speedsOk; infer_instance

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => if supplyOk s who then some (supplyNext s who) else none
  | .borrowHook who => if borrowOk s who then some (borrowNext s who) else none
  | .claim who => if claimOk s who then some (claimNext s who) else none
  | .setSpeeds a b => if speedsOk s a b then some (speedsNext s a b) else none

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  split at h
  · obtain ⟨h1, h2⟩ := ‹supplyOk s who›
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp at h

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  split at h
  · obtain ⟨h1, h2⟩ := ‹borrowOk s who›
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp at h

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  split at h
  · obtain ⟨hb, hs⟩ := ‹claimOk s who›
    cases h
    exact ⟨borrowNext s who, supplyNext (borrowNext s who) who,
      ⟨hb.1, hb.2, rfl⟩, ⟨hs.1, hs.2, rfl⟩, rfl⟩
  · simp at h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller] at h
  split at h
  · cases h
    obtain ⟨h1, h2⟩ := ‹speedsOk s a b›
    exact ⟨h1, h2, rfl⟩
  · simp at h

theorem accrue_supply_ge (s : St) :
    s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  have h : (accrueSide s.supplyState s.blockNumber (totalSupply s)).index =
      ProofForgeFin.Accumulator.catchUp doubleScale s.supplyState.index s.supplyState.block
        s.supplyState.speed s.blockNumber (totalSupply s) := by
    unfold accrueSide ProofForgeFin.Accumulator.catchUp
    split <;> rfl
  rw [h]
  exact ProofForgeFin.Accumulator.le_catchUp _ _ _ _ _ _

theorem accrue_borrow_ge (s : St) :
    s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  have h : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index =
      ProofForgeFin.Accumulator.catchUp doubleScale s.borrowState.index s.borrowState.block
        s.borrowState.speed s.blockNumber (totalBorrows s) := by
    unfold accrueSide ProofForgeFin.Accumulator.catchUp
    split <;> rfl
  rw [h]
  exact ProofForgeFin.Accumulator.le_catchUp _ _ _ _ _ _

theorem recorded_supply_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨-, -, hrec⟩ := hc
  have h1 : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
    fun a ha => (hrec a ha).1
  have h0 : (noAcct).supplierIndex ≤ s.supplyState.index := Nat.zero_le _
  unfold St.acct
  exact ProofForgeFin.Ledger.getD_of_forall s.accts who h1 h0

theorem recorded_borrow_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨-, -, hrec⟩ := hc
  have h1 : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
    fun a ha => (hrec a ha).2
  have h0 : (noAcct).borrowerIndex ≤ s.borrowState.index := Nat.zero_le _
  unfold St.acct
  exact ProofForgeFin.Ledger.getD_of_forall s.accts who h1 h0

theorem accrualStart_le (rec idx : Nat) (h : rec ≤ idx) :
    accrualStart rec idx ≤ idx := by
  unfold accrualStart
  split
  · split <;> omega
  · exact h

theorem totalSupply_borrowNext (s : St) (who : Account) :
    totalSupply (borrowNext s who) = totalSupply s :=
  ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ Acct.supply noAcct (fun _ => rfl)

theorem totalBorrows_supplyNext (s : St) (who : Account) :
    totalBorrows (supplyNext s who) = totalBorrows s :=
  ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ Acct.borrow noAcct (fun _ => rfl)

theorem acct_supplierIndex_borrowNext (s : St) (who : Account) :
    ((borrowNext s who).acct who).supplierIndex = (s.acct who).supplierIndex :=
  ProofForgeFin.Ledger.getD_modify_of_keeps s.accts who who noAcct Acct.supplierIndex (fun _ => rfl)

theorem supplyOk_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    supplyOk s who := by
  refine ⟨hc.1, ?_⟩
  apply accrualStart_le
  exact Nat.le_trans (recorded_supply_le s who hc) (accrue_supply_ge s)

theorem borrowOk_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    borrowOk s who := by
  refine ⟨hc.2.1, ?_⟩
  apply accrualStart_le
  exact Nat.le_trans (recorded_borrow_le s who hc) (accrue_borrow_ge s)

theorem claimOk_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    claimOk s who := by
  refine ⟨borrowOk_of_consistent s who hc, ?_⟩
  have hs := supplyOk_of_consistent s who hc
  unfold supplyOk at hs ⊢
  obtain ⟨h1, h2⟩ := hs
  have e1 : (borrowNext s who).supplyState = s.supplyState := rfl
  have e2 : (borrowNext s who).blockNumber = s.blockNumber := rfl
  have e3 : totalSupply (borrowNext s who) = totalSupply s := totalSupply_borrowNext s who
  have e4 : ((borrowNext s who).acct who).supplierIndex = (s.acct who).supplierIndex :=
    acct_supplierIndex_borrowNext s who
  rw [e1, e2, e3, e4]
  exact ⟨h1, h2⟩

theorem speedsOk_of_consistent (s : St) (a b : Nat) (hc : Consistent s) :
    speedsOk s a b :=
  ⟨fun _ => hc.1, fun _ => hc.2.1⟩

/-- Reading the state as a two-sided reward market. -/
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
theorem M_creditSum (s : St) : M.creditSum s = s.credited := rfl
theorem M_acct (s : St) (who : Account) : M.acct s who = s.acct who := rfl

theorem accrueSide_index (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  split <;> rfl

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split <;> rfl

theorem accrualStart_firstStart (rec idx : Nat) :
    accrualStart rec idx = ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex rec idx := rfl

theorem creditFor_credit (units start idx : Nat) :
    creditFor units start idx =
      ProofForgeFin.DeFi.Rewards.credit doubleScale units start idx := rfl

theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split <;> rfl

theorem settle₁ (s : St) (w : Nat) : M.Settle₁ w s (supplyNext s w) := by
  refine ⟨?hc, _, rfl, ?hf⟩
  · rw [M_total₁]
    show M.clock (supplyNext s w) = (M.clock s).catchUp₁ M.one (totalSupply s)
    simp only [M, supplyNext, accrueSide_index, accrueSide_block, accrueSide_speed]
    rfl
  · intro a
    have hi : (M.clock (supplyNext s w)).index₁ =
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
    rw [hi]
    simp only []
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only [M, creditFor, accrualStart, ProofForgeFin.DeFi.Rewards.firstStart]
    exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

theorem settle₂ (s : St) (w : Nat) : M.Settle₂ w s (borrowNext s w) := by
  refine ⟨?hc, _, rfl, ?hf⟩
  · rw [M_total₂]
    show M.clock (borrowNext s w) = (M.clock s).catchUp₂ M.one (totalBorrows s)
    simp only [M, borrowNext, accrueSide_index, accrueSide_block, accrueSide_speed]
    rfl
  · intro a
    have hi : (M.clock (borrowNext s w)).index₂ =
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
    rw [hi]
    simp only []
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only [M, creditFor, accrualStart, ProofForgeFin.DeFi.Rewards.firstStart]
    exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

theorem Consistent_of_Inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St}
    (hI : M.Inv g₁ g₂ sp s) : Consistent s := by
  obtain ⟨hl1, hl2, hrec, -, -, -, -⟩ := hI
  exact ⟨hl1, hl2, hrec⟩

theorem impl_supply (s : St) (who : Nat) (h : supplyOk s who) :
    comptroller s (.supplyHook who) = some (supplyNext s who) := by
  unfold comptroller
  simp [h]

theorem impl_borrow (s : St) (who : Nat) (h : borrowOk s who) :
    comptroller s (.borrowHook who) = some (borrowNext s who) := by
  unfold comptroller
  simp [h]

theorem impl_claim (s : St) (who : Nat) (h : claimOk s who) :
    comptroller s (.claim who) = some (claimNext s who) := by
  unfold comptroller
  simp [h]

theorem impl_speeds (s : St) (a b : Nat) (h : speedsOk s a b) :
    comptroller s (.setSpeeds a b) = some (speedsNext s a b) := by
  unfold comptroller
  simp [h]

theorem adjusts_mint (x : Nat) :
    M.AdjustsAt (fun a => ({ a with supply := a.supply + x } : Acct)) := by
  intro a
  exact ⟨Nat.le_refl _, rfl, rfl⟩

theorem adjusts_redeem (x : Nat) :
    M.AdjustsAt (fun a => ({ a with supply := a.supply - x } : Acct)) := by
  intro a
  exact ⟨Nat.le_refl _, rfl, rfl⟩

theorem adjusts_borrow (x : Nat) :
    M.AdjustsAt (fun a => ({ a with borrow := a.borrow + x } : Acct)) := by
  intro a
  exact ⟨Nat.le_refl _, rfl, rfl⟩

theorem adjusts_repay (x : Nat) :
    M.AdjustsAt (fun a => ({ a with borrow := a.borrow - x } : Acct)) := by
  intro a
  exact ⟨Nat.le_refl _, rfl, rfl⟩

theorem adjusts_grant :
    M.AdjustsAt (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) := by
  intro a
  simp only [M]
  refine ⟨?_, trivial, trivial⟩
  omega

theorem Consistent_supplyNext (s : St) (who : Nat) (hc : Consistent s) :
    Consistent (supplyNext s who) := by
  obtain ⟨hb1, hb2, hrec⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block ≤ s.blockNumber
    rw [accrueSide_block]
    exact Nat.le_refl _
  · exact hb2
  · show ∀ a ∈ s.accts.modify who (fun a => ({ a with
      supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
      accrued := a.accrued + creditFor a.supply
        (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } : Acct)),
      a.supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ∧
      a.borrowerIndex ≤ s.borrowState.index
    refine ProofForgeFin.DeFi.Rewards.forall_mem_modify ?_ ?_
    · intro a ha
      obtain ⟨hs, hb⟩ := hrec a ha
      exact ⟨Nat.le_trans hs (accrue_supply_ge s), hb⟩
    · intro a ha
      exact ⟨Nat.le_refl _, (hrec a ha).2⟩

theorem supplyOk_after_supplyNext (s : St) (src dst : Nat) (hc : Consistent s) :
    supplyOk (supplyNext s src) dst :=
  supplyOk_of_consistent _ _ (Consistent_supplyNext s src hc)

theorem adjust_grant_pay (m₂ : St) (who : Nat)
    (hp : 0 < (m₂.acct who).accrued ∧ (m₂.acct who).accrued ≤ m₂.reserve) :
    M.Adjust who m₂ (grant m₂ who) := by
  refine ⟨?hc, (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)),
    ?ha, adjusts_grant, Or.inl (fun _ => rfl), Or.inl (fun _ => rfl)⟩
  · unfold grant
    rw [if_pos hp]
    rfl
  · unfold grant
    rw [if_pos hp]
    rfl

theorem sideMove₁ (s : St) (a b : Nat) :
    Market.SideMove M.one (M.total₁ s) (M.clock s).now (M.clock s).index₁ (M.clock s).last₁
      (M.clock s).rate₁ (M.clock (speedsNext s a b)).index₁ (M.clock (speedsNext s a b)).last₁
      (M.clock (speedsNext s a b)).rate₁ := by
  simp only [M, speedsNext]
  split
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨accrueSide_index _ _ _, accrueSide_block _ _ _⟩

theorem sideMove₂ (s : St) (a b : Nat) :
    Market.SideMove M.one (M.total₂ s) (M.clock s).now (M.clock s).index₂ (M.clock s).last₂
      (M.clock s).rate₂ (M.clock (speedsNext s a b)).index₂ (M.clock (speedsNext s a b)).last₂
      (M.clock (speedsNext s a b)).rate₂ := by
  simp only [M, speedsNext]
  split
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨accrueSide_index _ _ _, accrueSide_block _ _ _⟩

theorem rateEq₁ (s : St) (a b : Nat) : (M.clock (speedsNext s a b)).rate₁ = a := by
  simp only [M, speedsNext]
  split
  · assumption
  · rfl

theorem rateEq₂ (s : St) (a b : Nat) : (M.clock (speedsNext s a b)).rate₂ = b := by
  simp only [M, speedsNext]
  split
  · assumption
  · rfl

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    have h := supplyOk_of_consistent s who hc
    simp only [comptroller, h, ↓reduceIte, Option.isSome_some]
  | borrowHook who =>
    have h := borrowOk_of_consistent s who hc
    simp only [comptroller, h, ↓reduceIte, Option.isSome_some]
  | claim who =>
    have h := claimOk_of_consistent s who hc
    simp only [comptroller, h, ↓reduceIte, Option.isSome_some]
  | setSpeeds a b =>
    have h := speedsOk_of_consistent s a b hc
    simp only [comptroller, h, ↓reduceIte, Option.isSome_some]
theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (op : Op)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  have hc : Consistent s := Consistent_of_Inv hI
  cases op with
  | mint who x =>
    by_cases hwho : who < s.accts.length
    · have hs := supplyOk_of_consistent s who hc
      simp only [exec, nextSpeeds, emittedBy, hwho, ↓reduceIte, impl_supply s who hs]
      exact .moves (Market.Settle₁.then_adjust (settle₁ s who) rfl rfl
        (adjusts_mint x) (fun _ => rfl))
    · simp only [exec, nextSpeeds, emittedBy, hwho, ↓reduceIte]
      exact .moves (Market.Reach.refl s)
  | redeem who x =>
    by_cases hwho : who < s.accts.length
    · have hs := supplyOk_of_consistent s who hc
      simp only [exec, nextSpeeds, emittedBy, hwho, ↓reduceIte, impl_supply s who hs]
      by_cases hx : x ≤ ((supplyNext s who).acct who).supply
      · simp only [hx, ↓reduceIte]
        exact .moves (Market.Settle₁.then_adjust (settle₁ s who) rfl rfl
          (adjusts_redeem x) (fun _ => rfl))
      · simp only [hx, ↓reduceIte]
        exact .moves (Market.Reach.refl s)
    · simp only [exec, nextSpeeds, emittedBy, hwho, ↓reduceIte]
      exact .moves (Market.Reach.refl s)
  | transfer src dst x =>
    by_cases htd : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · have hs1 := supplyOk_of_consistent s src hc
      have hs2 := supplyOk_after_supplyNext s src dst hc
      simp only [exec, nextSpeeds, emittedBy]
      rw [if_pos htd, impl_supply s src hs1]
      simp only [impl_supply (supplyNext s src) dst hs2]
      by_cases hx : x ≤ ((supplyNext (supplyNext s src) dst).acct src).supply
      · simp only [hx, ↓reduceIte]
        exact .moves (Market.Settle₁.transfer (settle₁ s src) (settle₁ _ dst) rfl rfl
          (adjusts_redeem x) (adjusts_mint x) (fun _ => rfl) (fun _ => rfl))
      · simp only [hx, ↓reduceIte]
        exact .moves (Market.Reach.refl s)
    · simp only [exec, nextSpeeds, emittedBy, htd, ↓reduceIte]
      exact .moves (Market.Reach.refl s)
  | borrow who x =>
    by_cases hwho : who < s.accts.length
    · have hs := borrowOk_of_consistent s who hc
      simp only [exec, nextSpeeds, emittedBy, hwho, ↓reduceIte, impl_borrow s who hs]
      exact .moves (Market.Settle₂.then_adjust (settle₂ s who) rfl rfl
        (adjusts_borrow x) (fun _ => rfl))
    · simp only [exec, nextSpeeds, emittedBy, hwho, ↓reduceIte]
      exact .moves (Market.Reach.refl s)
  | repay who x =>
    by_cases hwho : who < s.accts.length
    · have hs := borrowOk_of_consistent s who hc
      simp only [exec, nextSpeeds, emittedBy, hwho, ↓reduceIte, impl_borrow s who hs]
      by_cases hx : x ≤ ((borrowNext s who).acct who).borrow
      · simp only [hx, ↓reduceIte]
        exact .moves (Market.Settle₂.then_adjust (settle₂ s who) rfl rfl
          (adjusts_repay x) (fun _ => rfl))
      · simp only [hx, ↓reduceIte]
        exact .moves (Market.Reach.refl s)
    · simp only [exec, nextSpeeds, emittedBy, hwho, ↓reduceIte]
      exact .moves (Market.Reach.refl s)
  | claim who =>
    have hs := claimOk_of_consistent s who hc
    simp only [exec, nextSpeeds, emittedBy, impl_claim s who hs, Option.getD_some, claimNext]
    by_cases hp : 0 < ((supplyNext (borrowNext s who) who).acct who).accrued ∧
        ((supplyNext (borrowNext s who) who).acct who).accrued ≤
          (supplyNext (borrowNext s who) who).reserve
    · exact .moves (((Market.Reach.single (.settle₂ (settle₂ s who))).tail
        (.settle₁ (settle₁ (borrowNext s who) who))).tail
        (.adjust (adjust_grant_pay _ who hp)))
    · have e : grant (supplyNext (borrowNext s who) who) who =
          supplyNext (borrowNext s who) who := by
        unfold grant
        rw [if_neg hp]
      rw [e]
      exact .moves (((Market.Reach.single (.settle₂ (settle₂ s who))).tail
        (.settle₁ (settle₁ (borrowNext s who) who))).tail (.same rfl rfl))
  | setSpeeds a b =>
    have hs := speedsOk_of_consistent s a b hc
    simp only [exec, nextSpeeds, emittedBy, impl_speeds s a b hs, Option.getD_some]
    exact .retune ⟨rfl, rfl, sideMove₁ s a b, sideMove₂ s a b⟩ (rateEq₁ s a b) (rateEq₂ s a b)
  | advance k =>
    simp only [exec, nextSpeeds, emittedBy]
    exact .advance k ⟨rfl, rfl⟩
  | drip x =>
    simp only [exec, nextSpeeds, emittedBy]
    exact .moves (Market.Reach.single (.same rfl rfl))

theorem clock_upgrade (L : Legacy) :
    M.clock (upgrade L) = (ProofForgeFin.Accumulator.Clock.mk L.blockNumber L.supplyIndex
      L.supplyBlock L.compSpeed L.borrowIndex L.borrowBlock L.compSpeed).reinit M.init := by
  show ProofForgeFin.Accumulator.Clock.mk (upgrade L).blockNumber
    (upgrade L).supplyState.index (upgrade L).supplyState.block (upgrade L).supplyState.speed
    (upgrade L).borrowState.index (upgrade L).borrowState.block (upgrade L).borrowState.speed = _
  simp only [upgrade, initSide, ProofForgeFin.Accumulator.Clock.reinit, M]
  split
  · split <;> rfl
  · split <;> rfl

theorem owed_bridge (L : Legacy) (a : Acct) :
    M.owed L.supplyStart L.borrowStart (ProofForgeFin.Accumulator.Clock.mk L.blockNumber
      L.supplyIndex L.supplyBlock L.compSpeed L.borrowIndex L.borrowBlock L.compSpeed) a =
      L.pendingScaled a := rfl

theorem un1_bridge (L : Legacy) :
    (ProofForgeFin.Accumulator.Clock.mk L.blockNumber
      L.supplyIndex L.supplyBlock L.compSpeed L.borrowIndex L.borrowBlock L.compSpeed).un₁ =
      L.unindexedSupply := rfl

theorem un2_bridge (L : Legacy) :
    (ProofForgeFin.Accumulator.Clock.mk L.blockNumber
      L.supplyIndex L.supplyBlock L.compSpeed L.borrowIndex L.borrowBlock L.compSpeed).un₂ =
      L.unindexedBorrow := rfl

theorem hone : 0 < M.one := by
  show (0 : Nat) < 10 ^ 36
  decide

theorem accts_upgrade (L : Legacy) : M.accts (upgrade L) = L.accts := rfl

theorem owed_fun_bridge (L : Legacy) :
    M.owed L.supplyStart L.borrowStart
      (ProofForgeFin.Accumulator.Clock.mk L.blockNumber L.supplyIndex L.supplyBlock L.compSpeed
        L.borrowIndex L.borrowBlock L.compSpeed) = L.pendingScaled := rfl

theorem creditedTo_bridge (L : Legacy) (who : Nat) :
    M.credited (M.acct (upgrade L) who) = (upgrade L).creditedTo who := rfl

theorem owedTo_bridge (L : Legacy) (who : Nat) :
    M.owed L.supplyStart L.borrowStart (ProofForgeFin.Accumulator.Clock.mk L.blockNumber
      L.supplyIndex L.supplyBlock L.compSpeed L.borrowIndex L.borrowBlock L.compSpeed)
      (M.acct (upgrade L) who) = L.pendingScaled (L.accts.getD who noAcct) := rfl

theorem inv_upgrade (L : Legacy) (hL : L.WellFormed) :
    M.Inv (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart)
      (L.compSpeed, L.compSpeed) (upgrade L) := by
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, hrec⟩ := hL
  exact M.inv_reinit (clock_upgrade L) hs0 hsle hb0 hble hsb hbb hrec

theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hL
  have hI := inv_upgrade L hL
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, hrec⟩ := hL
  have h := M.pot_reinit_le L.supplyStart L.borrowStart (clock_upgrade L) hrec
  have hs : M.pot (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart) (upgrade L) ≤
      (upgrade L).credited * M.one + (L.accts.map L.pendingScaled).sum +
        M.one * (L.unindexedSupply + L.unindexedBorrow) := by
    simp only [M_creditSum, accts_upgrade, owed_fun_bridge, un1_bridge, un2_bridge] at h
    exact h
  exact M.rewards_bounded (run comptroller) emitted speedsAfter
    (exec_act (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart)) hone hI hs ops

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hL
  have hI := inv_upgrade L hL
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, hrec⟩ := hL
  have hr : M.rec₁ (M.acct (upgrade L) who) ≤ L.supplyIndex ∧
      M.rec₂ (M.acct (upgrade L) who) ≤ L.borrowIndex :=
    ProofForgeFin.Ledger.getD_of_forall _ _ hrec ⟨Nat.zero_le _, Nat.zero_le _⟩
  have h := M.potOf_reinit_le L.supplyStart L.borrowStart who (clock_upgrade L) hr
  have hs : M.potOf (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart) who (upgrade L) ≤
      (upgrade L).creditedTo who * M.one + L.pendingScaled (L.accts.getD who noAcct) +
        M.one * ((if 0 < ((upgrade L).acct who).supply then L.unindexedSupply else 0) +
          (if 0 < ((upgrade L).acct who).borrow then L.unindexedBorrow else 0)) := by
    simp only [creditedTo_bridge, owedTo_bridge, un1_bridge, un2_bridge] at h
    exact h
  exact M.account_rewards_bounded (run comptroller) emitted speedsAfter
    (exec_act (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart)) hone hI who hs ops

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hL hpos
  have hI := inv_upgrade L hL
  exact M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter
    (exec_act (reinitStart M.init L.supplyIndex L.supplyStart)
      (reinitStart M.init L.borrowIndex L.borrowStart)) hone hI history ops who hpos.1 hpos.2

end CompRewards
