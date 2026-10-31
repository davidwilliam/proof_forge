/-! ## Helper definitions: pending-reward potentials and the run invariant -/

/-- COMP emitted on the supply side since the supply index was last updated. -/
def td0_unindexedSupply (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed

/-- COMP emitted on the borrow side since the borrow index was last updated. -/
def td0_unindexedBorrow (s : St) : Nat :=
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

/-- Pending rewards of one account in state `s`, scaled by `doubleScale`. -/
def td0_pendingScaled (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

/-- Total COMP still owed in state `s`: pending rewards rounded down, plus unindexed emission. -/
def td0_owed (s : St) : Nat :=
  (s.accts.map (td0_pendingScaled s)).sum / doubleScale +
    td0_unindexedSupply s + td0_unindexedBorrow s

/-- COMP still owed to account `who` in state `s`. -/
def td0_owedTo (s : St) (who : Account) : Nat :=
  td0_pendingScaled s (s.acct who) / doubleScale +
    (if 0 < (s.acct who).supply then td0_unindexedSupply s else 0) +
    (if 0 < (s.acct who).borrow then td0_unindexedBorrow s else 0)

/-- Run invariant: consistency, and the stored speeds equal the ghost speeds `sp`. -/
def td0_Inv (sp : Nat × Nat) (s : St) : Prop :=
  Consistent s ∧ s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2

/-! ## Per-call helpers -/

theorem td0_supplyHook_some (s : St) (who : Account) (hs : Consistent s) :
    (comptroller s (.supplyHook who)).isSome := by sorry

theorem td0_borrowHook_some (s : St) (who : Account) (hs : Consistent s) :
    (comptroller s (.borrowHook who)).isSome := by sorry

theorem td0_claim_some (s : St) (who : Account) (hs : Consistent s) :
    (comptroller s (.claim who)).isSome := by sorry

theorem td0_setSpeeds_some (s : St) (a b : Nat) (hs : Consistent s) :
    (comptroller s (.setSpeeds a b)).isSome := by sorry

theorem td0_supplyHook_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    SupplyDistributed s who s' := by sorry

theorem td0_borrowHook_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    BorrowDistributed s who s' := by sorry

theorem td0_claim_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    Claimed s who s' := by sorry

theorem td0_setSpeeds_effect (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    SpeedsSet s a b s' := by sorry

/-! ## One-step and run helpers for the potentials -/

theorem td0_exec_inv (sp : Nat × Nat) (s : St) (op : Op) (h : td0_Inv sp s) :
    td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by sorry

theorem td0_exec_credited_step (sp : Nat × Nat) (s : St) (op : Op) (h : td0_Inv sp s) :
    (exec comptroller s op).credited + td0_owed (exec comptroller s op) ≤
      s.credited + td0_owed s + emittedBy sp op := by sorry

theorem td0_exec_creditedTo_step (sp : Nat × Nat) (s : St) (op : Op) (h : td0_Inv sp s)
    (who : Account) :
    (exec comptroller s op).creditedTo who + td0_owedTo (exec comptroller s op) who ≤
      s.creditedTo who + td0_owedTo s who + emittedBy sp op := by sorry

theorem td0_run_inv (sp : Nat × Nat) (s : St) (ops : List Op) (h : td0_Inv sp s) :
    td0_Inv (speedsAfter sp ops) (run comptroller s ops) := by sorry

theorem td0_run_credited_bound (sp : Nat × Nat) (s : St) (ops : List Op) (h : td0_Inv sp s) :
    (run comptroller s ops).credited ≤ s.credited + td0_owed s + emitted sp ops := by sorry

theorem td0_run_creditedTo_bound (sp : Nat × Nat) (s : St) (ops : List Op) (h : td0_Inv sp s)
    (who : Account) :
    (run comptroller s ops).creditedTo who ≤
      s.creditedTo who + td0_owedTo s who + emitted sp ops := by sorry

/-! ## Helpers about the upgraded state and about positionless accounts -/

theorem td0_inv_upgrade (L : Legacy) (hWF : L.WellFormed) :
    td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by sorry

theorem td0_owed_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    td0_owed (upgrade L) ≤ L.owed := by sorry

theorem td0_owedTo_upgrade_le (L : Legacy) (hWF : L.WellFormed) (who : Account) :
    td0_owedTo (upgrade L) who ≤ L.owedTo who := by sorry

theorem td0_owedTo_of_noPosition (s : St) (who : Account) (h : NoPosition s who) :
    td0_owedTo s who = 0 := by sorry

/-! ## Required theorems -/

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hs
  cases c with
  | supplyHook who => exact td0_supplyHook_some s who hs
  | borrowHook who => exact td0_borrowHook_some s who hs
  | claim who => exact td0_claim_some s who hs
  | setSpeeds a b => exact td0_setSpeeds_some s a b hs

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  exact td0_supplyHook_effect s who s' h

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  exact td0_borrowHook_effect s who s' h

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  exact td0_claim_effect s who s' h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact td0_setSpeeds_effect s a b s' h

theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hWF
  have hrun := td0_run_credited_bound (L.compSpeed, L.compSpeed) (upgrade L) ops
    (td0_inv_upgrade L hWF)
  have howed := td0_owed_upgrade_le L hWF
  omega

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hWF
  have hrun := td0_run_creditedTo_bound (L.compSpeed, L.compSpeed) (upgrade L) ops
    (td0_inv_upgrade L hWF) who
  have howed := td0_owedTo_upgrade_le L hWF who
  omega

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hWF hNo
  have hinv := td0_run_inv (L.compSpeed, L.compSpeed) (upgrade L) history
    (td0_inv_upgrade L hWF)
  have hrun := td0_run_creditedTo_bound (speedsAfter (L.compSpeed, L.compSpeed) history)
    (run comptroller (upgrade L) history) ops hinv who
  have hzero := td0_owedTo_of_noPosition (run comptroller (upgrade L) history) who hNo
  omega
