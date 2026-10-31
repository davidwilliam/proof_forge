def td0_pendingScaledAcct (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def td0_pendingScaled (s : St) : Nat :=
  (s.accts.map (td0_pendingScaledAcct s)).sum

def td0_unindexed (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed +
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def td0_unindexedTo (s : St) (who : Account) : Nat :=
  (if 0 < (s.acct who).supply then
    (s.blockNumber - s.supplyState.block) * s.supplyState.speed else 0) +
  (if 0 < (s.acct who).borrow then
    (s.blockNumber - s.borrowState.block) * s.borrowState.speed else 0)

def td0_potential (s : St) : Nat :=
  doubleScale * s.credited + td0_pendingScaled s + doubleScale * td0_unindexed s

def td0_potentialTo (s : St) (who : Account) : Nat :=
  doubleScale * s.creditedTo who +
  td0_pendingScaledAcct s (s.acct who) +
  doubleScale * td0_unindexedTo s who

def td0_pendingOf (L : Legacy) (who : Account) : Nat :=
  L.pendingScaled (L.accts.getD who noAcct)

def td0_unindexedOf (L : Legacy) (who : Account) : Nat :=
  (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
  (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)

def td0_Inv (sp : Nat × Nat) (s : St) : Prop :=
  Consistent s ∧ s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2

theorem td0_call_some (s : St) (c : Call) :
    Consistent s → (comptroller s c).isSome := by sorry

theorem td0_supply_hook_effect (s : St) (who : Account) (s' : St) :
    comptroller s (.supplyHook who) = some s' → SupplyDistributed s who s' := by sorry

theorem td0_borrow_hook_effect (s : St) (who : Account) (s' : St) :
    comptroller s (.borrowHook who) = some s' → BorrowDistributed s who s' := by sorry

theorem td0_claim_effect (s : St) (who : Account) (s' : St) :
    comptroller s (.claim who) = some s' → Claimed s who s' := by sorry

theorem td0_set_speeds_effect (s : St) (a b : Nat) (s' : St) :
    comptroller s (.setSpeeds a b) = some s' → SpeedsSet s a b s' := by sorry

theorem td0_upgrade_inv (L : Legacy) :
    L.WellFormed → td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by sorry

theorem td0_exec_inv (sp : Nat × Nat) (s : St) (op : Op) :
    td0_Inv sp s → td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by sorry

theorem td0_exec_potential_le (sp : Nat × Nat) (s : St) (op : Op) :
    td0_Inv sp s →
      td0_potential (exec comptroller s op) ≤
        td0_potential s + doubleScale * emittedBy sp op := by sorry

theorem td0_exec_potentialTo_le (sp : Nat × Nat) (s : St) (op : Op) (who : Account) :
    td0_Inv sp s →
      td0_potentialTo (exec comptroller s op) who ≤
        td0_potentialTo s who + doubleScale * emittedBy sp op := by sorry

theorem td0_run_inv (sp : Nat × Nat) (s : St) (ops : List Op) :
    td0_Inv sp s → td0_Inv (speedsAfter sp ops) (run comptroller s ops) := by
  induction ops generalizing sp s with
  | nil =>
      intro h
      simpa [run, speedsAfter] using h
  | cons op ops ih =>
      intro h
      exact ih _ _ (td0_exec_inv sp s op h)

theorem td0_run_potential_le (sp : Nat × Nat) (s : St) (ops : List Op) :
    td0_Inv sp s →
      td0_potential (run comptroller s ops) ≤
        td0_potential s + doubleScale * emitted sp ops := by
  induction ops generalizing sp s with
  | nil =>
      intro h
      simp [run, emitted]
  | cons op ops ih =>
      intro h
      have hinv := td0_exec_inv sp s op h
      have hstep := td0_exec_potential_le sp s op h
      have hrest := ih _ _ hinv
      calc td0_potential (run comptroller s (op :: ops))
          = td0_potential (run comptroller (exec comptroller s op) ops) := rfl
        _ ≤ td0_potential (exec comptroller s op) +
              doubleScale * emitted (nextSpeeds sp op) ops := hrest
        _ ≤ (td0_potential s + doubleScale * emittedBy sp op) +
              doubleScale * emitted (nextSpeeds sp op) ops :=
            Nat.add_le_add_right hstep _
        _ = td0_potential s + doubleScale * emitted sp (op :: ops) := by
              simp [emitted, Nat.mul_add, Nat.add_assoc]

theorem td0_run_potentialTo_le (sp : Nat × Nat) (s : St) (ops : List Op) (who : Account) :
    td0_Inv sp s →
      td0_potentialTo (run comptroller s ops) who ≤
        td0_potentialTo s who + doubleScale * emitted sp ops := by
  induction ops generalizing sp s with
  | nil =>
      intro h
      simp [run, emitted]
  | cons op ops ih =>
      intro h
      have hinv := td0_exec_inv sp s op h
      have hstep := td0_exec_potentialTo_le sp s op who h
      have hrest := ih _ _ hinv
      calc td0_potentialTo (run comptroller s (op :: ops)) who
          = td0_potentialTo (run comptroller (exec comptroller s op) ops) who := rfl
        _ ≤ td0_potentialTo (exec comptroller s op) who +
              doubleScale * emitted (nextSpeeds sp op) ops := hrest
        _ ≤ (td0_potentialTo s who + doubleScale * emittedBy sp op) +
              doubleScale * emitted (nextSpeeds sp op) ops :=
            Nat.add_le_add_right hstep _
        _ = td0_potentialTo s who + doubleScale * emitted sp (op :: ops) := by
              simp [emitted, Nat.mul_add, Nat.add_assoc]

theorem td0_upgrade_potential_le (L : Legacy) :
    L.WellFormed →
      td0_potential (upgrade L) ≤
        doubleScale * (upgrade L).credited +
        (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by sorry

theorem td0_upgrade_potentialTo_le (L : Legacy) (who : Account) :
    L.WellFormed →
      td0_potentialTo (upgrade L) who ≤
        doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who := by sorry

theorem td0_credited_le_potential (s : St) :
    doubleScale * s.credited ≤ td0_potential s := by sorry

theorem td0_creditedTo_le_potential (s : St) (who : Account) :
    doubleScale * s.creditedTo who ≤ td0_potentialTo s who := by sorry

theorem td0_rewards_bound_of_scaled (s : St) (L : Legacy) (e : Nat) :
    doubleScale * s.credited ≤
        doubleScale * (upgrade L).credited +
        (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
        doubleScale * e →
      s.credited ≤ (upgrade L).credited + L.owed + e := by sorry

theorem td0_account_bound_of_scaled (s : St) (L : Legacy) (who : Account) (e : Nat) :
    doubleScale * s.creditedTo who ≤
        doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who +
        doubleScale * e →
      s.creditedTo who ≤ (upgrade L).creditedTo who + L.owedTo who + e := by sorry

theorem td0_potentialTo_of_no_position (s : St) (who : Account) :
    NoPosition s who →
      td0_potentialTo s who = doubleScale * s.creditedTo who := by sorry

theorem td0_scaled_le_add {x y e : Nat} :
    doubleScale * x ≤ doubleScale * y + doubleScale * e → x ≤ y + e := by sorry

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hs
  exact td0_call_some s c hs

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  exact td0_supply_hook_effect s who s' h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  exact td0_borrow_hook_effect s who s' h

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  exact td0_claim_effect s who s' h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact td0_set_speeds_effect s a b s' h

theorem req_rewards_bounded : RewardsBounded comptroller := by
  intro L ops hWF
  have hinv := td0_upgrade_inv L hWF
  have hrun := td0_run_potential_le (L.compSpeed, L.compSpeed) (upgrade L) ops hinv
  have hinit := td0_upgrade_potential_le L hWF
  have hscaled :
      doubleScale * (run comptroller (upgrade L) ops).credited ≤
        doubleScale * (upgrade L).credited +
        (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
        doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by
    calc doubleScale * (run comptroller (upgrade L) ops).credited
        ≤ td0_potential (run comptroller (upgrade L) ops) :=
          td0_credited_le_potential _
      _ ≤ td0_potential (upgrade L) +
            doubleScale * emitted (L.compSpeed, L.compSpeed) ops := hrun
      _ ≤ (doubleScale * (upgrade L).credited +
            (L.accts.map L.pendingScaled).sum +
            doubleScale * (L.unindexedSupply + L.unindexedBorrow)) +
            doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
          Nat.add_le_add_right hinit _
  exact td0_rewards_bound_of_scaled _ L _ hscaled

theorem req_account_bounded : AccountBounded comptroller := by
  intro L ops who hWF
  have hinv := td0_upgrade_inv L hWF
  have hrun := td0_run_potentialTo_le (L.compSpeed, L.compSpeed) (upgrade L) ops who hinv
  have hinit := td0_upgrade_potentialTo_le L who hWF
  have hscaled :
      doubleScale * (run comptroller (upgrade L) ops).creditedTo who ≤
        doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who +
        doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by
    calc doubleScale * (run comptroller (upgrade L) ops).creditedTo who
        ≤ td0_potentialTo (run comptroller (upgrade L) ops) who :=
          td0_creditedTo_le_potential _ _
      _ ≤ td0_potentialTo (upgrade L) who +
            doubleScale * emitted (L.compSpeed, L.compSpeed) ops := hrun
      _ ≤ (doubleScale * (upgrade L).creditedTo who +
            td0_pendingOf L who +
            doubleScale * td0_unindexedOf L who) +
            doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
          Nat.add_le_add_right hinit _
  exact td0_account_bound_of_scaled _ L who _ hscaled

theorem req_no_backdated : NoBackdatedRewards comptroller := by
  intro L history ops who hWF hNo
  have hinv0 := td0_upgrade_inv L hWF
  have hinv := td0_run_inv (L.compSpeed, L.compSpeed) (upgrade L) history hinv0
  have hrun :=
    td0_run_potentialTo_le
      (speedsAfter (L.compSpeed, L.compSpeed) history)
      (run comptroller (upgrade L) history) ops who hinv
  have hmid :=
    td0_potentialTo_of_no_position
      (run comptroller (upgrade L) history) who hNo
  have hscaled :
      doubleScale *
          (run comptroller (run comptroller (upgrade L) history) ops).creditedTo who ≤
        doubleScale * (run comptroller (upgrade L) history).creditedTo who +
          doubleScale *
            emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops := by
    calc doubleScale *
            (run comptroller (run comptroller (upgrade L) history) ops).creditedTo who
        ≤ td0_potentialTo
            (run comptroller (run comptroller (upgrade L) history) ops) who :=
          td0_creditedTo_le_potential _ _
      _ ≤ td0_potentialTo (run comptroller (upgrade L) history) who +
            doubleScale *
              emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops := hrun
      _ = doubleScale * (run comptroller (upgrade L) history).creditedTo who +
            doubleScale *
              emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops := by
            rw [hmid]
  exact td0_scaled_le_add hscaled
