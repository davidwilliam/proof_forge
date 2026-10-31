(1) Proof plan: Extract the upgraded supply/borrow indices via `initSide`. Reduce both sides to a general natural-number inequality comparing the post-upgrade distance `up - accrualStart recorded up` with the legacy distance `orig - legacyStart start recorded`, using well-formedness (`start ∈ {0, compInitialIndex}`, `start ≤ orig`, and the account's recorded indices are `≤ orig` from membership). Prove that core inequality by case-splitting on `recorded = 0`, `orig = 0`, and whether `compInitialIndex ≤ up`, then finish each side by monotonicity of multiplication and addition.

(2)
```lean
theorem plan7_initSide_index (now : Nat) (sd : Side) :
    (initSide now sd).index =
      if sd.index = 0 then compInitialIndex else sd.index := by sorry

theorem plan7_diff_le_of_start (start recorded orig up : Nat)
    (hup : up = if orig = 0 then compInitialIndex else orig)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hstart_le : start ≤ orig)
    (hrec_le : recorded ≤ orig) :
    up - accrualStart recorded up ≤
      orig - legacyStart start recorded := by sorry

theorem plan7_upgrade_supply_diff_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    (upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index ≤
      L.supplyIndex - legacyStart L.supplyStart a.supplierIndex := by sorry

theorem plan7_upgrade_borrow_diff_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    (upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index ≤
      L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex := by sorry

theorem plan7_add_mul_le (x y xd yd xo yo : Nat)
    (hx : xd ≤ xo) (hy : yd ≤ yo) :
    x * xd + y * yd ≤ x * xo + y * yo := by sorry
```