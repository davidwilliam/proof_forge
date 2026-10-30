Fixed the rewrite direction in `req_no_backdated`: `hsp` rewrites the reachable state's speed pair to `speedsAfter … history`, so it must be used forward on `h2`.

```lean
/-! ## Architecture helpers -/

/-- Scaled pending rewards of one account record in state `s`. -/
def arch0_pendingAcct (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

/-- Global scaled potential: credited COMP, all pending rewards, and COMP
emitted since each side's index was last updated. -/
def arch0_totalPot (s : St) : Nat :=
  s.credited * doubleScale +
  (s.accts.map (arch0_pendingAcct s)).sum +
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale +
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale

/-- The invariant carried along runs: exactly the spec's consistency. -/
def arch0_Inv (s : St) : Prop :=
  Consistent s

theorem arch0_updSupply_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by sorry

theorem arch0_updBorrow_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem arch0_distSupply_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by sorry

theorem arch0_distBorrow_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by sorry

theorem arch0_supplyHook_some (s : St) (who : Account) (h : Consistent s) :
    (comptroller s (.supplyHook who)).isSome := by sorry

theorem arch0_borrowHook_some (s : St) (who : Account) (h : Consistent s) :
    (comptroller s (.borrowHook who)).isSome := by sorry

theorem arch0_claim_some (s : St) (who : Account) (h : Consistent s) :
    (comptroller s (.claim who)).isSome := by sorry

theorem arch0_setSpeeds_some (s : St) (a b : Nat) (h : Consistent s) :
    (comptroller s (.setSpeeds a b)).isSome := by sorry

theorem arch0_supply_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') : SupplyDistributed s who s' := by sorry

theorem arch0_borrow_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') : BorrowDistributed s who s' := by sorry

theorem arch0_claim_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') : Claimed s who s' := by sorry

theorem arch0_setSpeeds_effect (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') : SpeedsSet s a b s' := by sorry

theorem arch0_inv_upgrade (L : Legacy) (h : L.WellFormed) :
    arch0_Inv (upgrade L) := by sorry

theorem arch0_inv_exec (s : St) (op : Op) (h : arch0_Inv s) :
    arch0_Inv (exec comptroller s op) := by sorry

theorem arch0_inv_run (s : St) (ops : List Op) (h : arch0_Inv s) :
    arch0_Inv (run comptroller s ops) := by sorry

theorem arch0_speeds_exec (s : St) (op : Op) :
    ((exec comptroller s op).supplyState.speed, (exec comptroller s op).borrowState.speed) =
      nextSpeeds (s.supplyState.speed, s.borrowState.speed) op := by sorry

theorem arch0_upgrade_speeds (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed ∧
    (upgrade L).borrowState.speed = L.compSpeed := by sorry

theorem arch0_speeds_run_upgrade (L : Legacy) (history : List Op) :
    ((run comptroller (upgrade L) history).supplyState.speed,
     (run comptroller (upgrade L) history).borrowState.speed) =
      speedsAfter (L.compSpeed, L.compSpeed) history := by sorry

theorem arch0_totalPot_exec (s : St) (op : Op) (h : arch0_Inv s) :
    arch0_totalPot (exec comptroller s op) ≤
      arch0_totalPot s + emittedBy (s.supplyState.speed, s.borrowState.speed) op * doubleScale := by sorry

theorem arch0_pot_exec (s : St) (op : Op) (who : Account) (h : arch0_Inv s) :
    pot (exec comptroller s op) who ≤
      pot s who + emittedBy (s.supplyState.speed, s.borrowState.speed) op * doubleScale := by sorry

theorem arch0_totalPot_run (s : St) (ops : List Op) (h : arch0_Inv s) :
    arch0_totalPot (run comptroller s ops) ≤
      arch0_totalPot s + emitted (s.supplyState.speed, s.borrowState.speed) ops * doubleScale := by sorry

theorem arch0_pot_run (s : St) (ops : List Op) (who : Account) (h : arch0_Inv s) :
    pot (run comptroller s ops) who ≤
      pot s who + emitted (s.supplyState.speed, s.borrowState.speed) ops * doubleScale := by sorry

theorem arch0_totalPot_upgrade (L : Legacy) (h : L.WellFormed) :
    arch0_totalPot (upgrade L) ≤
      (upgrade L).credited * doubleScale +
      (L.accts.map L.pendingScaled).sum +
      (L.unindexedSupply + L.unindexedBorrow) * doubleScale := by sorry

theorem arch0_pot_upgrade (L : Legacy) (who : Account) (h : L.WellFormed) :
    pot (upgrade L) who ≤
      (upgrade L).creditedTo who * doubleScale +
      L.pendingScaled (L.accts.getD who noAcct) +
      ((if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
       (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)) * doubleScale := by sorry

theorem arch0_credited_le_totalPot (s : St) :
    s.credited * doubleScale ≤ arch0_totalPot s := by sorry

theorem arch0_creditedTo_le_pot (s : St) (who : Account) :
    (s.creditedTo who) * doubleScale ≤ pot s who := by sorry

theorem arch0_pot_of_noPosition (s : St) (who : Account) (h : NoPosition s who) :
    pot s who = (s.creditedTo who) * doubleScale := by sorry

theorem arch0_div_bound (c c0 p u e : Nat)
    (h : c * doubleScale ≤ c0 * doubleScale + p + u * doubleScale + e * doubleScale) :
    c ≤ c0 + p / doubleScale + u + e := by sorry

theorem arch0_le_of_mul_le_emitted (c c0 e : Nat)
    (h : c * doubleScale ≤ c0 * doubleScale + e * doubleScale) :
    c ≤ c0 + e := by sorry

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hs
  cases c with
  | supplyHook who => exact arch0_supplyHook_some s who hs
  | borrowHook who => exact arch0_borrowHook_some s who hs
  | claim who => exact arch0_claim_some s who hs
  | setSpeeds a b => exact arch0_setSpeeds_some s a b hs

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  exact arch0_supply_effect s who s' h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  exact arch0_borrow_effect s who s' h

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  exact arch0_claim_effect s who s' h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact arch0_setSpeeds_effect s a b s' h

theorem req_rewards_bounded : RewardsBounded comptroller := by
  intro L ops hL
  have h1 := arch0_credited_le_totalPot (run comptroller (upgrade L) ops)
  have h2 := arch0_totalPot_run (upgrade L) ops (arch0_inv_upgrade L hL)
  have h3 := arch0_totalPot_upgrade L hL
  have hsp := arch0_upgrade_speeds L
  have hemit : emitted ((upgrade L).supplyState.speed, (upgrade L).borrowState.speed) ops =
      emitted (L.compSpeed, L.compSpeed) ops := by
    rw [hsp.1, hsp.2]
  rw [hemit] at h2
  have hcomb : (run comptroller (upgrade L) ops).credited * doubleScale ≤
      (upgrade L).credited * doubleScale +
      (L.accts.map L.pendingScaled).sum +
      (L.unindexedSupply + L.unindexedBorrow) * doubleScale +
      emitted (L.compSpeed, L.compSpeed) ops * doubleScale := by
    omega
  have hd := arch0_div_bound _ _ _ _ _ hcomb
  show (run comptroller (upgrade L) ops).credited ≤
    (upgrade L).credited +
      ((L.accts.map L.pendingScaled).sum / doubleScale +
        L.unindexedSupply + L.unindexedBorrow) +
      emitted (L.compSpeed, L.compSpeed) ops
  omega

theorem req_account_bounded : AccountBounded comptroller := by
  intro L ops who hL
  have h1 := arch0_creditedTo_le_pot (run comptroller (upgrade L) ops) who
  have h2 := arch0_pot_run (upgrade L) ops who (arch0_inv_upgrade L hL)
  have h3 := arch0_pot_upgrade L who hL
  have hsp := arch0_upgrade_speeds L
  have hemit : emitted ((upgrade L).supplyState.speed, (upgrade L).borrowState.speed) ops =
      emitted (L.compSpeed, L.compSpeed) ops := by
    rw [hsp.1, hsp.2]
  rw [hemit] at h2
  have hcomb : (run comptroller (upgrade L) ops).creditedTo who * doubleScale ≤
      (upgrade L).creditedTo who * doubleScale +
      L.pendingScaled (L.accts.getD who noAcct) +
      ((if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
       (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)) * doubleScale +
      emitted (L.compSpeed, L.compSpeed) ops * doubleScale := by
    omega
  have hd := arch0_div_bound _ _ _ _ _ hcomb
  show (run comptroller (upgrade L) ops).creditedTo who ≤
    (upgrade L).creditedTo who +
      (L.pendingScaled (L.accts.getD who noAcct) / doubleScale +
       (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
       (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)) +
      emitted (L.compSpeed, L.compSpeed) ops
  omega

theorem req_no_backdated : NoBackdatedRewards comptroller := by
  intro L history ops who hL hNP
  have hinvT : arch0_Inv (run comptroller (upgrade L) history) :=
    arch0_inv_run (upgrade L) history (arch0_inv_upgrade L hL)
  have h2 := arch0_pot_run (run comptroller (upgrade L) history) ops who hinvT
  have hsp := arch0_speeds_run_upgrade L history
  rw [hsp] at h2
  have heq := arch0_pot_of_noPosition (run comptroller (upgrade L) history) who hNP
  rw [heq] at h2
  have h1 := arch0_creditedTo_le_pot
    (run comptroller (run comptroller (upgrade L) history) ops) who
  have hcomb : (run comptroller (run comptroller (upgrade L) history) ops).creditedTo who *
        doubleScale ≤
      (run comptroller (upgrade L) history).creditedTo who * doubleScale +
      emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops * doubleScale := by
    omega
  exact arch0_le_of_mul_le_emitted _ _ _ hcomb
```