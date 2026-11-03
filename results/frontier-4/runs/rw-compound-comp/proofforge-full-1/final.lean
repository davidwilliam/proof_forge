import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
import ProofForgeFin.Ledger

namespace CompRewards

open ProofForgeFin.Accumulator

/-- Supply side after a hook: index up to date, `who` credited. -/
def supplyNext (s : St) (who : Account) : St :=
  { s with
    supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
    accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }

/-- Borrow side after a hook. -/
def borrowNext (s : St) (who : Account) : St :=
  { s with
    borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
    accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }

/-- State after a claim: both sides distributed, then paid. -/
def claimNext (s : St) (who : Account) : St := grant (supplyNext (borrowNext s who) who) who

/-- State after a speed change. -/
def speedsNext (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who =>
    if s.supplyState.block ≤ s.blockNumber ∧
      accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    then some (supplyNext s who) else none
  | .borrowHook who =>
    if s.borrowState.block ≤ s.blockNumber ∧
      accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    then some (borrowNext s who) else none
  | .claim who =>
    if s.borrowState.block ≤ s.blockNumber ∧
      accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ∧
      (borrowNext s who).supplyState.block ≤ (borrowNext s who).blockNumber ∧
      accrualStart ((borrowNext s who).acct who).supplierIndex
        (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber
          (totalSupply (borrowNext s who))).index ≤
        (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber
          (totalSupply (borrowNext s who))).index
    then some (claimNext s who) else none
  | .setSpeeds a b =>
    if (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
      (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber)
    then some (speedsNext s a b) else none

theorem accrue_le_aux (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · simp
  · simp

theorem start_le_aux (recorded oldIdx newIdx : Nat) (h1 : recorded ≤ oldIdx)
    (h2 : oldIdx ≤ newIdx) : accrualStart recorded newIdx ≤ newIdx := by
  unfold accrualStart
  split
  · split
    · omega
    · omega
  · omega

theorem recSupply_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  have h := hc.2.2
  have hd : noAcct.supplierIndex ≤ s.supplyState.index ∧
    noAcct.borrowerIndex ≤ s.borrowState.index := by simp [noAcct]
  have hP := ProofForgeFin.Ledger.getD_of_forall (P := fun a =>
    a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index)
    s.accts who h hd
  have hh : (s.accts.getD who noAcct).supplierIndex ≤ s.supplyState.index := hP.1
  simpa [St.acct] using hh

theorem recBorrow_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  have h := hc.2.2
  have hd : noAcct.supplierIndex ≤ s.supplyState.index ∧
    noAcct.borrowerIndex ≤ s.borrowState.index := by simp [noAcct]
  have hP := ProofForgeFin.Ledger.getD_of_forall (P := fun a =>
    a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index)
    s.accts who h hd
  have hh : (s.accts.getD who noAcct).borrowerIndex ≤ s.borrowState.index := hP.2
  simpa [St.acct] using hh

theorem borrowNext_supply_aux (s : St) (who : Account) :
    totalSupply (borrowNext s who) = totalSupply s := by
  unfold borrowNext totalSupply
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (fun _ => rfl)

theorem borrowNext_suppIdx_aux (s : St) (who : Account) :
    ((borrowNext s who).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold borrowNext St.acct
  exact ProofForgeFin.Ledger.getD_modify_of_keeps s.accts who who noAcct
    Acct.supplierIndex (fun a => rfl)

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    simp only [comptroller]
    have h1 : s.supplyState.block ≤ s.blockNumber := hc.1
    have hrec := recSupply_le s who hc
    have hle : s.supplyState.index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrue_le_aux _ _ _
    have h2 := start_le_aux _ _ _ hrec hle
    simp [h1, h2]
  | borrowHook who =>
    simp only [comptroller]
    have h1 : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hrec := recBorrow_le s who hc
    have hle : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_le_aux _ _ _
    have h2 := start_le_aux _ _ _ hrec hle
    simp [h1, h2]
  | claim who =>
    simp only [comptroller]
    have hb1 : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hrecB := recBorrow_le s who hc
    have hleB : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_le_aux _ _ _
    have hb2 := start_le_aux _ _ _ hrecB hleB
    have hs1 : (borrowNext s who).supplyState.block ≤ (borrowNext s who).blockNumber := hc.1
    have hrecS := recSupply_le s who hc
    have hleS : s.supplyState.index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrue_le_aux _ _ _
    have h2S := start_le_aux _ _ _ hrecS hleS
    have hTS : totalSupply (borrowNext s who) = totalSupply s := borrowNext_supply_aux s who
    have hSI : ((borrowNext s who).acct who).supplierIndex = (s.acct who).supplierIndex :=
      borrowNext_suppIdx_aux s who
    have hs2 : accrualStart ((borrowNext s who).acct who).supplierIndex
        (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber
          (totalSupply (borrowNext s who))).index ≤
        (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber
          (totalSupply (borrowNext s who))).index := by
      have e1 : (borrowNext s who).supplyState = s.supplyState := rfl
      have e2 : (borrowNext s who).blockNumber = s.blockNumber := rfl
      rw [e1, e2, hTS, hSI]
      exact h2S
    simp [hb1, hb2, hs1, hs2]
  | setSpeeds a b =>
    simp only [comptroller]
    have hP : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
      (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) :=
      ⟨fun _ => hc.1, fun _ => hc.2.1⟩
    rw [if_pos hP]; rfl

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  split at h
  · rename_i hcond
    obtain ⟨h1, h2⟩ := hcond
    have heq : supplyNext s who = s' := Option.some_inj.mp h
    unfold SupplyDistributed
    unfold supplyNext at heq
    exact ⟨h1, h2, heq.symm⟩
  · rename_i hcond
    cases h

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  split at h
  · rename_i hcond
    obtain ⟨h1, h2⟩ := hcond
    have heq : borrowNext s who = s' := Option.some_inj.mp h
    unfold BorrowDistributed
    unfold borrowNext at heq
    exact ⟨h1, h2, heq.symm⟩
  · rename_i hcond
    cases h

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  split at h
  · rename_i hcond
    obtain ⟨hb1, hb2, hs1, hs2⟩ := hcond
    have heq : claimNext s who = s' := Option.some_inj.mp h
    unfold Claimed
    refine ⟨borrowNext s who, supplyNext (borrowNext s who) who, ⟨hb1, hb2, rfl⟩, ⟨hs1, hs2, rfl⟩, ?_⟩
    unfold claimNext at heq
    exact heq.symm
  · rename_i hcond
    cases h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller] at h
  split at h
  · rename_i hcond
    obtain ⟨h1, h2⟩ := hcond
    have heq : speedsNext s a b = s' := Option.some_inj.mp h
    unfold SpeedsSet
    unfold speedsNext at heq
    exact ⟨h1, h2, heq.symm⟩
  · rename_i hcond
    cases h
/-- Reading the state as a two-sided reward market. -/
def M : Market St Acct where
  one := doubleScale
  init := compInitialIndex
  clock s := ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed,
    s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩
  accts s := s.accts
  dflt := noAcct
  units₁ := Acct.supply
  units₂ := Acct.borrow
  rec₁ := Acct.supplierIndex
  rec₂ := Acct.borrowerIndex
  credited a := a.accrued + a.wallet
  dflt_units₁ := rfl
  dflt_units₂ := rfl

theorem upd_supply_index (s : St) :
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index =
    ProofForgeFin.Accumulator.catchUp M.one s.supplyState.index s.supplyState.block
      s.supplyState.speed s.blockNumber (totalSupply s) := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp M
  split <;> rfl

theorem upd_borrow_index (s : St) :
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index =
    ProofForgeFin.Accumulator.catchUp M.one s.borrowState.index s.borrowState.block
      s.borrowState.speed s.blockNumber (totalBorrows s) := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp M
  split <;> rfl

theorem upd_supply_last (s : St) :
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber := by
  unfold accrueSide
  split <;> rfl

theorem upd_borrow_last (s : St) :
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber := by
  unfold accrueSide
  split <;> rfl

theorem accrue_supply_speed (s : St) :
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed =
      s.supplyState.speed := by
  unfold accrueSide
  split <;> rfl

theorem accrue_borrow_speed (s : St) :
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed =
      s.borrowState.speed := by
  unfold accrueSide
  split <;> rfl

theorem clock_supply (s : St) (w : Nat) :
    M.clock (supplyNext s w) = (M.clock s).catchUp₁ M.one (M.total₁ s) := by
  have eT : M.total₁ s = totalSupply s := rfl
  have eC : M.clock s = ProofForgeFin.Accumulator.Clock.mk s.blockNumber
      s.supplyState.index s.supplyState.block s.supplyState.speed
      s.borrowState.index s.borrowState.block s.borrowState.speed := rfl
  have eN : M.clock (supplyNext s w) = ProofForgeFin.Accumulator.Clock.mk s.blockNumber
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).block
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed
      s.borrowState.index s.borrowState.block s.borrowState.speed := rfl
  rw [eC, eN, eT, ProofForgeFin.Accumulator.Clock.catchUp₁_mk, upd_supply_index,
    upd_supply_last, accrue_supply_speed]

theorem clock_borrow (s : St) (w : Nat) :
    M.clock (borrowNext s w) = (M.clock s).catchUp₂ M.one (M.total₂ s) := by
  have eT : M.total₂ s = totalBorrows s := rfl
  have eC : M.clock s = ProofForgeFin.Accumulator.Clock.mk s.blockNumber
      s.supplyState.index s.supplyState.block s.supplyState.speed
      s.borrowState.index s.borrowState.block s.borrowState.speed := rfl
  have eN : M.clock (borrowNext s w) = ProofForgeFin.Accumulator.Clock.mk s.blockNumber
      s.supplyState.index s.supplyState.block s.supplyState.speed
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed := rfl
  rw [eC, eN, eT, ProofForgeFin.Accumulator.Clock.catchUp₂_mk, upd_borrow_index,
    upd_borrow_last, accrue_borrow_speed]

theorem settleSupply (s : St) (w : Nat) : M.Settle₁ w s (supplyNext s w) := by
  refine ⟨clock_supply s w, _, rfl, fun a => ⟨rfl, rfl, rfl, rfl, ?_⟩⟩
  have eI : (M.clock (supplyNext s w)).index₁ =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
  rw [eI]
  show a.accrued + a.supply *
      ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        ProofForgeFin.DeFi.Rewards.firstStart M.init a.supplierIndex
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale +
      a.wallet ≤ a.accrued + a.wallet + a.supply *
      ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        ProofForgeFin.DeFi.Rewards.firstStart M.init a.supplierIndex
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale
  exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

theorem settleBorrow (s : St) (w : Nat) : M.Settle₂ w s (borrowNext s w) := by
  refine ⟨clock_borrow s w, _, rfl, fun a => ⟨rfl, rfl, rfl, rfl, ?_⟩⟩
  have eI : (M.clock (borrowNext s w)).index₂ =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
  rw [eI]
  show a.accrued + a.borrow *
      ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
        ProofForgeFin.DeFi.Rewards.firstStart M.init a.borrowerIndex
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale +
      a.wallet ≤ a.accrued + a.wallet + a.borrow *
      ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
        ProofForgeFin.DeFi.Rewards.firstStart M.init a.borrowerIndex
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale
  exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

theorem supplyNext_totalSupply (s : St) (who : Account) :
    totalSupply (supplyNext s who) = totalSupply s := by
  unfold supplyNext totalSupply
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (fun _ => rfl)

theorem supplyNext_totalBorrows (s : St) (who : Account) :
    totalBorrows (supplyNext s who) = totalBorrows s := by
  unfold supplyNext totalBorrows
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (fun _ => rfl)

theorem borrowNext_totalBorrows (s : St) (who : Account) :
    totalBorrows (borrowNext s who) = totalBorrows s := by
  unfold borrowNext totalBorrows
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (fun _ => rfl)

theorem recSupply_of_inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} (w : Nat)
    (hI : M.Inv g₁ g₂ sp s) : (M.acct s w).supplierIndex ≤ (M.clock s).index₁ := by
  have hd : M.rec₁ M.dflt ≤ (M.clock s).index₁ ∧ M.rec₂ M.dflt ≤ (M.clock s).index₂ :=
    ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hP := ProofForgeFin.Ledger.getD_of_forall (M.accts s) w hI.recs hd
  exact hP.1

theorem recBorrow_of_inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} (w : Nat)
    (hI : M.Inv g₁ g₂ sp s) : (M.acct s w).borrowerIndex ≤ (M.clock s).index₂ := by
  have hd : M.rec₁ M.dflt ≤ (M.clock s).index₁ ∧ M.rec₂ M.dflt ≤ (M.clock s).index₂ :=
    ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hP := ProofForgeFin.Ledger.getD_of_forall (M.accts s) w hI.recs hd
  exact hP.2

theorem supply_ok_of_inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {w : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    s.supplyState.block ≤ s.blockNumber ∧
      accrualStart (s.acct w).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  have h1 : s.supplyState.block ≤ s.blockNumber := hI.last₁
  have hrec : (s.acct w).supplierIndex ≤ s.supplyState.index := recSupply_of_inv w hI
  have hle : s.supplyState.index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrue_le_aux _ _ _
  exact ⟨h1, start_le_aux _ _ _ hrec hle⟩

theorem borrow_ok_of_inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {w : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    s.borrowState.block ≤ s.blockNumber ∧
      accrualStart (s.acct w).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  have h1 : s.borrowState.block ≤ s.blockNumber := hI.last₂
  have hrec : (s.acct w).borrowerIndex ≤ s.borrowState.index := recBorrow_of_inv w hI
  have hle : s.borrowState.index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    accrue_le_aux _ _ _
  exact ⟨h1, start_le_aux _ _ _ hrec hle⟩

theorem hookSupply_eq {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {w : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    comptroller s (.supplyHook w) = some (supplyNext s w) := by
  have hok := supply_ok_of_inv (w := w) hI
  simp only [comptroller]
  rw [if_pos hok]

theorem hookBorrow_eq {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {w : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    comptroller s (.borrowHook w) = some (borrowNext s w) := by
  have hok := borrow_ok_of_inv (w := w) hI
  simp only [comptroller]
  rw [if_pos hok]

theorem exec_mint_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {who x : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.mint who x)) (emittedBy sp (.mint who x))
      (exec comptroller s (.mint who x)) := by
  by_cases hwho : who < s.accts.length
  · have heq := hookSupply_eq (w := who) hI
    have eexec : exec comptroller s (.mint who x) =
        St.withAcct (supplyNext s who) who (fun a => { a with supply := a.supply + x }) := by
      simp [exec, hwho, heq]
    rw [eexec]
    exact .moves (Market.Settle₁.then_adjust (settleSupply s who) rfl rfl
      (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun a => rfl))
  · have eexec : exec comptroller s (.mint who x) = s := by
      simp [exec, hwho]
    rw [eexec]
    exact .moves (Market.Reach.refl s)

theorem exec_borrow_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {who x : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.borrow who x)) (emittedBy sp (.borrow who x))
      (exec comptroller s (.borrow who x)) := by
  by_cases hwho : who < s.accts.length
  · have heq := hookBorrow_eq (w := who) hI
    have eexec : exec comptroller s (.borrow who x) =
        St.withAcct (borrowNext s who) who (fun a => { a with borrow := a.borrow + x }) := by
      simp [exec, hwho, heq]
    rw [eexec]
    exact .moves (Market.Settle₂.then_adjust (settleBorrow s who) rfl rfl
      (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun a => rfl))
  · have eexec : exec comptroller s (.borrow who x) = s := by
      simp [exec, hwho]
    rw [eexec]
    exact .moves (Market.Reach.refl s)

theorem exec_redeem_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {who x : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.redeem who x)) (emittedBy sp (.redeem who x))
      (exec comptroller s (.redeem who x)) := by
  by_cases hwho : who < s.accts.length
  · have heq := hookSupply_eq (w := who) hI
    by_cases hamt : x ≤ ((supplyNext s who).acct who).supply
    · have eexec : exec comptroller s (.redeem who x) =
          St.withAcct (supplyNext s who) who (fun a => { a with supply := a.supply - x }) := by
        simp [exec, hwho, heq, hamt]
      rw [eexec]
      exact .moves (Market.Settle₁.then_adjust (settleSupply s who) rfl rfl
        (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun a => rfl))
    · have eexec : exec comptroller s (.redeem who x) = s := by
        simp [exec, hwho, heq, hamt]
      rw [eexec]
      exact .moves (Market.Reach.refl s)
  · have eexec : exec comptroller s (.redeem who x) = s := by
      simp [exec, hwho]
    rw [eexec]
    exact .moves (Market.Reach.refl s)

theorem exec_repay_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {who x : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.repay who x)) (emittedBy sp (.repay who x))
      (exec comptroller s (.repay who x)) := by
  by_cases hwho : who < s.accts.length
  · have heq := hookBorrow_eq (w := who) hI
    by_cases hamt : x ≤ ((borrowNext s who).acct who).borrow
    · have eexec : exec comptroller s (.repay who x) =
          St.withAcct (borrowNext s who) who (fun a => { a with borrow := a.borrow - x }) := by
        simp [exec, hwho, heq, hamt]
      rw [eexec]
      exact .moves (Market.Settle₂.then_adjust (settleBorrow s who) rfl rfl
        (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun a => rfl))
    · have eexec : exec comptroller s (.repay who x) = s := by
        simp [exec, hwho, heq, hamt]
      rw [eexec]
      exact .moves (Market.Reach.refl s)
  · have eexec : exec comptroller s (.repay who x) = s := by
      simp [exec, hwho]
    rw [eexec]
    exact .moves (Market.Reach.refl s)

theorem exec_transfer_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {src dst x : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.transfer src dst x)) (emittedBy sp (.transfer src dst x))
      (exec comptroller s (.transfer src dst x)) := by
  by_cases hcond : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
  · obtain ⟨h1, h2, h3⟩ := hcond
    have heq₁ := hookSupply_eq (w := src) hI
    have hstep₁ : M.Step s (supplyNext s src) := .settle₁ (settleSupply s src)
    have hI₁ : M.Inv g₁ g₂ sp (supplyNext s src) := (Market.Step.bound hstep₁ hI).1
    have heq₂ := hookSupply_eq (w := dst) hI₁
    by_cases hamt : x ≤ ((supplyNext (supplyNext s src) dst).acct src).supply
    · have eexec : exec comptroller s (.transfer src dst x) =
          ((supplyNext (supplyNext s src) dst).withAcct src (fun a => { a with supply := a.supply - x })).withAcct
            dst (fun a => { a with supply := a.supply + x }) := by
        simp [exec, h1, h2, h3, heq₁, heq₂, hamt]
      rw [eexec]
      exact .moves (Market.Settle₁.transfer (settleSupply s src)
        (settleSupply (supplyNext s src) dst) rfl rfl
        (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
        (fun a => rfl) (fun a => rfl))
    · have eexec : exec comptroller s (.transfer src dst x) = s := by
        simp [exec, h1, h2, h3, heq₁, heq₂, hamt]
      rw [eexec]
      exact .moves (Market.Reach.refl s)
  · have eexec : exec comptroller s (.transfer src dst x) = s := by
      simp [exec, hcond]
    rw [eexec]
    exact .moves (Market.Reach.refl s)

theorem grant_adjust {who : Nat} {m₂ : St}
    (hpay : 0 < (m₂.acct who).accrued ∧ (m₂.acct who).accrued ≤ m₂.reserve) :
    M.Adjust who m₂ (grant m₂ who) := by
  have hclock : M.clock (grant m₂ who) = M.clock m₂ := by
    unfold grant
    split <;> rfl
  have haccts : M.accts (grant m₂ who) = (M.accts m₂).modify who
      (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
    unfold grant
    rw [if_pos hpay]
    rfl
  refine ⟨hclock, (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }),
    haccts, ?_, ?_, ?_⟩
  · intro a
    refine ⟨?_, rfl, rfl⟩
    show 0 + (a.wallet + a.accrued) ≤ a.accrued + a.wallet
    omega
  · exact .inl fun a => rfl
  · exact .inl fun a => rfl

theorem claim_ok_of_inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {w : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    s.borrowState.block ≤ s.blockNumber ∧
      accrualStart (s.acct w).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ∧
      (borrowNext s w).supplyState.block ≤ (borrowNext s w).blockNumber ∧
      accrualStart ((borrowNext s w).acct w).supplierIndex
        (accrueSide (borrowNext s w).supplyState (borrowNext s w).blockNumber
          (totalSupply (borrowNext s w))).index ≤
        (accrueSide (borrowNext s w).supplyState (borrowNext s w).blockNumber
          (totalSupply (borrowNext s w))).index := by
  have hb := borrow_ok_of_inv (w := w) hI
  have hs1 : (borrowNext s w).supplyState.block ≤ (borrowNext s w).blockNumber := hI.last₁
  have hrecS : (s.acct w).supplierIndex ≤ s.supplyState.index := recSupply_of_inv w hI
  have hleS : s.supplyState.index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrue_le_aux _ _ _
  have h2S := start_le_aux _ _ _ hrecS hleS
  have hTS : totalSupply (borrowNext s w) = totalSupply s := borrowNext_supply_aux s w
  have hSI : ((borrowNext s w).acct w).supplierIndex = (s.acct w).supplierIndex :=
    borrowNext_suppIdx_aux s w
  have hs2 : accrualStart ((borrowNext s w).acct w).supplierIndex
      (accrueSide (borrowNext s w).supplyState (borrowNext s w).blockNumber
        (totalSupply (borrowNext s w))).index ≤
      (accrueSide (borrowNext s w).supplyState (borrowNext s w).blockNumber
        (totalSupply (borrowNext s w))).index := by
    have e1 : (borrowNext s w).supplyState = s.supplyState := rfl
    have e2 : (borrowNext s w).blockNumber = s.blockNumber := rfl
    rw [e1, e2, hTS, hSI]
    exact h2S
  exact ⟨hb.1, hb.2, hs1, hs2⟩

theorem hookClaim_eq {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {w : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    comptroller s (.claim w) = some (claimNext s w) := by
  have hok := claim_ok_of_inv (w := w) hI
  simp only [comptroller]
  rw [if_pos hok]

theorem exec_claim_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {who : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.claim who)) (emittedBy sp (.claim who))
      (exec comptroller s (.claim who)) := by
  have heq := hookClaim_eq (w := who) hI
  have eexec : exec comptroller s (.claim who) = claimNext s who := by
    simp [exec, heq]
  rw [eexec]
  have h₂ := settleBorrow s who
  have h₁ := settleSupply (borrowNext s who) who
  by_cases hpay : 0 < ((supplyNext (borrowNext s who) who).acct who).accrued ∧
      ((supplyNext (borrowNext s who) who).acct who).accrued ≤
        (supplyNext (borrowNext s who) who).reserve
  · have hadj := grant_adjust (who := who)
      (m₂ := supplyNext (borrowNext s who) who) hpay
    have eclaim : claimNext s who = grant (supplyNext (borrowNext s who) who) who := rfl
    rw [eclaim]
    exact .moves (((Market.Reach.single (.settle₂ h₂)).tail (.settle₁ h₁)).tail (.adjust hadj))
  · have ht : claimNext s who = supplyNext (borrowNext s who) who := by
      simp [claimNext, grant, hpay]
    rw [ht]
    exact .moves ((Market.Reach.single (.settle₂ h₂)).tail (.settle₁ h₁))

theorem speeds_ok_of_inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {a b : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) :=
  ⟨fun _ => hI.last₁, fun _ => hI.last₂⟩

theorem hookSpeeds_eq {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {a b : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    comptroller s (.setSpeeds a b) = some (speedsNext s a b) := by
  have hok := speeds_ok_of_inv (a := a) (b := b) hI
  simp only [comptroller]
  rw [if_pos hok]

theorem retune_side₁ {s : St} {a b : Nat} :
    ProofForgeFin.Accumulator.Market.SideMove M.one (M.total₁ s) (M.clock s).now
      (M.clock s).index₁ (M.clock s).last₁ (M.clock s).rate₁
      (M.clock (speedsNext s a b)).index₁ (M.clock (speedsNext s a b)).last₁
      (M.clock (speedsNext s a b)).rate₁ := by
  by_cases hsa : s.supplyState.speed = a
  · have eS : (speedsNext s a b).supplyState = s.supplyState := by simp [speedsNext, hsa]
    refine .inl ⟨?_, ?_, ?_⟩
    · show (speedsNext s a b).supplyState.index = s.supplyState.index
      rw [eS]
    · show (speedsNext s a b).supplyState.block = s.supplyState.block
      rw [eS]
    · show (speedsNext s a b).supplyState.speed = s.supplyState.speed
      rw [eS]
  · have eS : (speedsNext s a b).supplyState =
        { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } := by
      simp [speedsNext, hsa]
    have eT : M.total₁ s = totalSupply s := rfl
    refine .inr ⟨?_, ?_⟩
    · show (speedsNext s a b).supplyState.index = ProofForgeFin.Accumulator.catchUp M.one
        (M.clock s).index₁ (M.clock s).last₁ (M.clock s).rate₁ (M.clock s).now (M.total₁ s)
      rw [eS, eT]
      exact upd_supply_index s
    · show (speedsNext s a b).supplyState.block = (M.clock s).now
      rw [eS]
      exact upd_supply_last s

theorem retune_side₂ {s : St} {a b : Nat} :
    ProofForgeFin.Accumulator.Market.SideMove M.one (M.total₂ s) (M.clock s).now
      (M.clock s).index₂ (M.clock s).last₂ (M.clock s).rate₂
      (M.clock (speedsNext s a b)).index₂ (M.clock (speedsNext s a b)).last₂
      (M.clock (speedsNext s a b)).rate₂ := by
  by_cases hsa : s.borrowState.speed = b
  · have eS : (speedsNext s a b).borrowState = s.borrowState := by simp [speedsNext, hsa]
    refine .inl ⟨?_, ?_, ?_⟩
    · show (speedsNext s a b).borrowState.index = s.borrowState.index
      rw [eS]
    · show (speedsNext s a b).borrowState.block = s.borrowState.block
      rw [eS]
    · show (speedsNext s a b).borrowState.speed = s.borrowState.speed
      rw [eS]
  · have eS : (speedsNext s a b).borrowState =
        { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } := by
      simp [speedsNext, hsa]
    have eT : M.total₂ s = totalBorrows s := rfl
    refine .inr ⟨?_, ?_⟩
    · show (speedsNext s a b).borrowState.index = ProofForgeFin.Accumulator.catchUp M.one
        (M.clock s).index₂ (M.clock s).last₂ (M.clock s).rate₂ (M.clock s).now (M.total₂ s)
      rw [eS, eT]
      exact upd_borrow_index s
    · show (speedsNext s a b).borrowState.block = (M.clock s).now
      rw [eS]
      exact upd_borrow_last s

theorem exec_setSpeeds_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {a b : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.setSpeeds a b)) (emittedBy sp (.setSpeeds a b))
      (exec comptroller s (.setSpeeds a b)) := by
  have heq := hookSpeeds_eq (a := a) (b := b) hI
  have eexec : exec comptroller s (.setSpeeds a b) = speedsNext s a b := by
    simp [exec, heq]
  rw [eexec]
  have hret : M.Retune s (speedsNext s a b) :=
    ⟨rfl, rfl, retune_side₁, retune_side₂⟩
  have r1 : (M.clock (speedsNext s a b)).rate₁ = a := by
    by_cases hsa : s.supplyState.speed = a
    · have eS : (speedsNext s a b).supplyState = s.supplyState := by simp [speedsNext, hsa]
      show (speedsNext s a b).supplyState.speed = a
      rw [eS, hsa]
    · have eS : (speedsNext s a b).supplyState =
          { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } := by
        simp [speedsNext, hsa]
      show (speedsNext s a b).supplyState.speed = a
      rw [eS]
  have r2 : (M.clock (speedsNext s a b)).rate₂ = b := by
    by_cases hsa : s.borrowState.speed = b
    · have eS : (speedsNext s a b).borrowState = s.borrowState := by simp [speedsNext, hsa]
      show (speedsNext s a b).borrowState.speed = b
      rw [eS, hsa]
    · have eS : (speedsNext s a b).borrowState =
          { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } := by
        simp [speedsNext, hsa]
      show (speedsNext s a b).borrowState.speed = b
      rw [eS]
  exact .retune hret r1 r2

/-- The clock before the upgrade, read from the legacy state. -/
def legacyClock (L : Legacy) : Clock :=
  ⟨L.blockNumber, L.supplyIndex, L.supplyBlock, L.compSpeed,
    L.borrowIndex, L.borrowBlock, L.compSpeed⟩

theorem upgrade_clock (L : Legacy) :
    M.clock (upgrade L) = (legacyClock L).reinit M.init := by
  by_cases h1 : L.supplyIndex = 0 <;> by_cases h2 : L.borrowIndex = 0 <;>
    simp [M, upgrade, initSide, legacyClock, Clock.reinit, h1, h2]

theorem exec_advance_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {k : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.advance k)) (emittedBy sp (.advance k))
      (exec comptroller s (.advance k)) := by
  have eexec : exec comptroller s (.advance k) = { s with blockNumber := s.blockNumber + k } := rfl
  rw [eexec]
  refine .advance k ⟨?_, rfl⟩
  show M.clock { s with blockNumber := s.blockNumber + k } =
    (M.clock s).advance k
  simp only [M, ProofForgeFin.Accumulator.Clock.advance]

theorem exec_drip_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {x : Nat}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.drip x)) (emittedBy sp (.drip x))
      (exec comptroller s (.drip x)) := by
  have eexec : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := rfl
  rw [eexec]
  exact .moves (Market.Reach.single (.same rfl rfl))

theorem exec_act {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St} {op : Op}
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  cases op with
  | mint who x => exact exec_mint_act hI
  | redeem who x => exact exec_redeem_act hI
  | transfer src dst x => exact exec_transfer_act hI
  | borrow who x => exact exec_borrow_act hI
  | repay who x => exact exec_repay_act hI
  | claim who => exact exec_claim_act hI
  | setSpeeds a b => exact exec_setSpeeds_act hI
  | advance k => exact exec_advance_act hI
  | drip x => exact exec_drip_act hI

theorem upgrade_inv (L : Legacy) (hL : L.WellFormed) :
    M.Inv (reinitStart M.init (legacyClock L).index₁ L.supplyStart)
      (reinitStart M.init (legacyClock L).index₂ L.borrowStart)
      ((legacyClock L).rate₁, (legacyClock L).rate₂) (upgrade L) := by
  unfold Legacy.WellFormed at hL
  obtain ⟨hg₁, hgi₁, hg₂, hgi₂, hl₁, hl₂, hr⟩ := hL
  exact M.inv_reinit (upgrade_clock L) hg₁ hgi₁ hg₂ hgi₂ hl₁ hl₂ hr

theorem upgrade_rec_le (L : Legacy) (hL : L.WellFormed) :
    ∀ a ∈ M.accts (upgrade L),
      M.rec₁ a ≤ (legacyClock L).index₁ ∧ M.rec₂ a ≤ (legacyClock L).index₂ := by
  unfold Legacy.WellFormed at hL
  obtain ⟨_, _, _, _, _, _, hr⟩ := hL
  exact hr

theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hL
  have h0 := upgrade_inv L hL
  have hone : 0 < M.one := by show 0 < 10 ^ 36; decide
  have hr := upgrade_rec_le L hL
  have hs := M.pot_reinit_le L.supplyStart L.borrowStart (upgrade_clock L) hr
  have hact : ∀ (sp : Nat × Nat) (s : St) (op : Op),
      M.Inv (reinitStart M.init (legacyClock L).index₁ L.supplyStart)
        (reinitStart M.init (legacyClock L).index₂ L.borrowStart) sp s →
      M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) :=
    fun sp s op hI => exec_act hI
  have hbound := M.rewards_bounded (run comptroller) emitted speedsAfter hact hone h0 hs ops
  have eOwed : ∀ a, M.owed L.supplyStart L.borrowStart (legacyClock L) a =
      Legacy.pendingScaled L a := fun a => rfl
  have eU1 : (legacyClock L).un₁ = L.unindexedSupply := rfl
  have eU2 : (legacyClock L).un₂ = L.unindexedBorrow := rfl
  simp only [eOwed, eU1, eU2] at hbound
  exact hbound

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hL
  have h0 := upgrade_inv L hL
  have hone : 0 < M.one := by show 0 < 10 ^ 36; decide
  have hrw : M.rec₁ (M.acct (upgrade L) who) ≤ (legacyClock L).index₁ ∧
      M.rec₂ (M.acct (upgrade L) who) ≤ (legacyClock L).index₂ := by
    have hd : M.rec₁ M.dflt ≤ (legacyClock L).index₁ ∧
        M.rec₂ M.dflt ≤ (legacyClock L).index₂ := ⟨Nat.zero_le _, Nat.zero_le _⟩
    have hP := ProofForgeFin.Ledger.getD_of_forall (M.accts (upgrade L)) who
      (upgrade_rec_le L hL) hd
    exact hP
  have hs := M.potOf_reinit_le L.supplyStart L.borrowStart who (upgrade_clock L) hrw
  have hact : ∀ (sp : Nat × Nat) (s : St) (op : Op),
      M.Inv (reinitStart M.init (legacyClock L).index₁ L.supplyStart)
        (reinitStart M.init (legacyClock L).index₂ L.borrowStart) sp s →
      M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) :=
    fun sp s op hI => exec_act hI
  have hbound := M.account_rewards_bounded (run comptroller) emitted speedsAfter
    hact hone h0 who hs ops
  have eOwed : M.owed L.supplyStart L.borrowStart (legacyClock L)
      (M.acct (upgrade L) who) = Legacy.pendingScaled L (L.accts.getD who noAcct) :=
    rfl
  have eU1 : (legacyClock L).un₁ = L.unindexedSupply := rfl
  have eU2 : (legacyClock L).un₂ = L.unindexedBorrow := rfl
  simp only [eOwed, eU1, eU2] at hbound
  exact hbound

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hL hNoPos
  have h0 := upgrade_inv L hL
  have hone : 0 < M.one := by show 0 < 10 ^ 36; decide
  have hact : ∀ (sp : Nat × Nat) (s : St) (op : Op),
      M.Inv (reinitStart M.init (legacyClock L).index₁ L.supplyStart)
        (reinitStart M.init (legacyClock L).index₂ L.borrowStart) sp s →
      M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) :=
    fun sp s op hI => exec_act hI
  have h1 : M.units₁ (M.acct (run comptroller (upgrade L) history) who) = 0 := hNoPos.1
  have h2 : M.units₂ (M.acct (run comptroller (upgrade L) history) who) = 0 := hNoPos.2
  have hbound := M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter
    hact hone h0 history ops who h1 h2
  exact hbound

end CompRewards
