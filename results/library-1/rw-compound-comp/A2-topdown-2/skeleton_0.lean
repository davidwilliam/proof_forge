/-! ## Shared definitions: invariant and potentials -/

/-- Pending (still uncredited) rewards of one account record in state `s`, scaled by
`doubleScale`: units times the index gained since the account's accrual start, both sides. -/
def td0_pendingAcct (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

/-- Total pending scaled rewards of all accounts in `s`. -/
def td0_pending (s : St) : Nat := (s.accts.map (td0_pendingAcct s)).sum

/-- COMP emitted since each side's index was last brought up to date. -/
def td0_unindexed (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed +
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

/-- Scaled total potential: what has been credited, plus what is still pending, plus what
has been emitted but is not yet in either index. No step raises it beyond the emission. -/
def td0_potential (s : St) : Nat :=
  doubleScale * s.credited + td0_pending s + doubleScale * td0_unindexed s

/-- Pending scaled rewards of account `who` alone. -/
def td0_pendingTo (s : St) (who : Account) : Nat := td0_pendingAcct s (s.acct who)

/-- Emission not yet indexed, counted for account `who` only on sides where it holds a
position (as in `Legacy.owedTo`). -/
def td0_unindexedTo (s : St) (who : Account) : Nat :=
  (if 0 < (s.acct who).supply then
     (s.blockNumber - s.supplyState.block) * s.supplyState.speed else 0) +
  (if 0 < (s.acct who).borrow then
     (s.blockNumber - s.borrowState.block) * s.borrowState.speed else 0)

/-- Scaled per-account potential of `who`. -/
def td0_potentialTo (s : St) (who : Account) : Nat :=
  doubleScale * s.creditedTo who + td0_pendingTo s who + doubleScale * td0_unindexedTo s who

/-- Invariant of reachable states, relative to the ghost speeds `sp`: the state is
consistent and its speeds are exactly the ghost speeds tracking `emitted`. -/
def td0_Inv (sp : Nat × Nat) (s : St) : Prop :=
  Consistent s ∧ s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2

/-! ## Single-call facts -/

theorem td0_calls_some : ∀ (s : St) (c : Call), Consistent s → (comptroller s c).isSome := by
  sorry

theorem td0_supply_hook_effect : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.supplyHook who) = some s' → SupplyDistributed s who s' := by
  sorry

theorem td0_borrow_hook_effect : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.borrowHook who) = some s' → BorrowDistributed s who s' := by
  sorry

theorem td0_claim_effect : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.claim who) = some s' → Claimed s who s' := by
  sorry

theorem td0_set_speeds_effect : ∀ (s : St) (a b : Nat) (s' : St),
    comptroller s (.setSpeeds a b) = some s' → SpeedsSet s a b s' := by
  sorry

/-! ## One-step facts about `exec` -/

theorem td0_exec_inv : ∀ (sp : Nat × Nat) (s : St) (op : Op), td0_Inv sp s →
    td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by
  sorry

theorem td0_exec_potential_le : ∀ (sp : Nat × Nat) (s : St) (op : Op), td0_Inv sp s →
    td0_potential (exec comptroller s op) ≤
      td0_potential s + doubleScale * emittedBy sp op := by
  sorry

theorem td0_exec_potentialTo_le : ∀ (sp : Nat × Nat) (s : St) (op : Op) (who : Account),
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s op) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp op := by
  sorry

/-! ## Lifting one-step facts to runs -/

theorem td0_run_inv : ∀ (ops : List Op) (sp : Nat × Nat) (s : St), td0_Inv sp s →
    td0_Inv (speedsAfter sp ops) (run comptroller s ops) := by
  intro ops
  induction ops with
  | nil =>
      intro sp s h
      exact h
  | cons op ops ih =>
      intro sp s h
      exact ih (nextSpeeds sp op) (exec comptroller s op) (td0_exec_inv sp s op h)

theorem td0_run_potential : ∀ (ops : List Op) (sp : Nat × Nat) (s : St), td0_Inv sp s →
    td0_potential (run comptroller s ops) ≤
      td0_potential s + doubleScale * emitted sp ops := by
  intro ops
  induction ops with
  | nil =>
      intro sp s h
      exact Nat.le_refl _
  | cons op ops ih =>
      intro sp s h
      have hstep := td0_exec_potential_le sp s op h
      have hinv := td0_exec_inv sp s op h
      have hrec := ih (nextSpeeds sp op) (exec comptroller s op) hinv
      have hsum := Nat.add_le_add hstep
        (Nat.le_refl (doubleScale * emitted (nextSpeeds sp op) ops))
      have htrans := Nat.le_trans hrec hsum
      have hem : emitted sp (op :: ops) =
          emittedBy sp op + emitted (nextSpeeds sp op) ops := rfl
      rw [hem, Nat.mul_add, ← Nat.add_assoc]
      exact htrans

theorem td0_run_potentialTo : ∀ (ops : List Op) (sp : Nat × Nat) (s : St) (who : Account),
    td0_Inv sp s →
    td0_potentialTo (run comptroller s ops) who ≤
      td0_potentialTo s who + doubleScale * emitted sp ops := by
  intro ops
  induction ops with
  | nil =>
      intro sp s who h
      exact Nat.le_refl _
  | cons op ops ih =>
      intro sp s who h
      have hstep := td0_exec_potentialTo_le sp s op who h
      have hinv := td0_exec_inv sp s op h
      have hrec := ih (nextSpeeds sp op) (exec comptroller s op) who hinv
      have hsum := Nat.add_le_add hstep
        (Nat.le_refl (doubleScale * emitted (nextSpeeds sp op) ops))
      have htrans := Nat.le_trans hrec hsum
      have hem : emitted sp (op :: ops) =
          emittedBy sp op + emitted (nextSpeeds sp op) ops := rfl
      rw [hem, Nat.mul_add, ← Nat.add_assoc]
      exact htrans

/-! ## The state at the upgrade -/

theorem td0_upgrade_inv : ∀ (L : Legacy), L.WellFormed →
    td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by
  sorry

theorem td0_upgrade_potential_le : ∀ (L : Legacy), L.WellFormed →
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  sorry

theorem td0_upgrade_potentialTo_le : ∀ (L : Legacy) (who : Account), L.WellFormed →
    td0_potentialTo (upgrade L) who ≤
      doubleScale * (upgrade L).creditedTo who +
        L.pendingScaled (L.accts.getD who noAcct) +
        doubleScale * ((if 0 < (L.accts.getD who noAcct).supply
                        then L.unindexedSupply else 0) +
                       (if 0 < (L.accts.getD who noAcct).borrow
                        then L.unindexedBorrow else 0)) := by
  sorry

theorem td0_potentialTo_of_noPosition : ∀ (s : St) (who : Account), NoPosition s who →
    td0_potentialTo s who = doubleScale * s.creditedTo who := by
  sorry

/-! ## From potentials to the stated bounds (division by `doubleScale`) -/

theorem td0_rewards_conclude : ∀ (L : Legacy) (ops : List Op),
    td0_potential (run comptroller (upgrade L) ops) ≤
        td0_potential (upgrade L) + doubleScale * emitted (L.compSpeed, L.compSpeed) ops →
    td0_potential (upgrade L) ≤
        doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
          doubleScale * (L.unindexedSupply + L.unindexedBorrow) →
    (run comptroller (upgrade L) ops).credited ≤
      (upgrade L).credited + L.owed + emitted (L.compSpeed, L.compSpeed) ops := by
  sorry

theorem td0_account_conclude : ∀ (L : Legacy) (ops : List Op) (who : Account),
    td0_potentialTo (run comptroller (upgrade L) ops) who ≤
        td0_potentialTo (upgrade L) who +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops →
    td0_potentialTo (upgrade L) who ≤
        doubleScale * (upgrade L).creditedTo who +
          L.pendingScaled (L.accts.getD who noAcct) +
          doubleScale * ((if 0 < (L.accts.getD who noAcct).supply
                          then L.unindexedSupply else 0) +
                         (if 0 < (L.accts.getD who noAcct).borrow
                          then L.unindexedBorrow else 0)) →
    (run comptroller (upgrade L) ops).creditedTo who ≤
      (upgrade L).creditedTo who + L.owedTo who +
        emitted (L.compSpeed, L.compSpeed) ops := by
  sorry

theorem td0_no_backdated_conclude : ∀ (s : St) (sp : Nat × Nat) (ops : List Op)
    (who : Account),
    td0_potentialTo (run comptroller s ops) who ≤
        td0_potentialTo s who + doubleScale * emitted sp ops →
    td0_potentialTo s who = doubleScale * s.creditedTo who →
    (run comptroller s ops).creditedTo who ≤ s.creditedTo who + emitted sp ops := by
  sorry

/-! ## Required theorems -/

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hs
  exact td0_calls_some s c hs

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  exact td0_supply_hook_effect s who s' h

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  exact td0_borrow_hook_effect s who s' h

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  exact td0_claim_effect s who s' h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact td0_set_speeds_effect s a b s' h

theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hWF
  have hinv := td0_upgrade_inv L hWF
  have hrun := td0_run_potential ops (L.compSpeed, L.compSpeed) (upgrade L) hinv
  have hinit := td0_upgrade_potential_le L hWF
  exact td0_rewards_conclude L ops hrun hinit

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hWF
  have hinv := td0_upgrade_inv L hWF
  have hrun := td0_run_potentialTo ops (L.compSpeed, L.compSpeed) (upgrade L) who hinv
  have hinit := td0_upgrade_potentialTo_le L who hWF
  exact td0_account_conclude L ops who hrun hinit

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hWF hNo
  have hinv0 := td0_upgrade_inv L hWF
  have hinv := td0_run_inv history (L.compSpeed, L.compSpeed) (upgrade L) hinv0
  have hrun := td0_run_potentialTo ops
    (speedsAfter (L.compSpeed, L.compSpeed) history)
    (run comptroller (upgrade L) history) who hinv
  have hzero := td0_potentialTo_of_noPosition
    (run comptroller (upgrade L) history) who hNo
  exact td0_no_backdated_conclude (run comptroller (upgrade L) history)
    (speedsAfter (L.compSpeed, L.compSpeed) history) ops who hrun hzero
