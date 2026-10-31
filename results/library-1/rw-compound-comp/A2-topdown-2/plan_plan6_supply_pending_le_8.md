The upgraded supply index differs from the legacy index only when the legacy index is zero, in which case a recorded index must also be zero. Separating the recorded-index cases reduces both accrual starts to explicit values, after which truncated subtraction and the hypotheses on the legacy start close the index inequality, and monotonicity of multiplication lifts it to the pending amount.

```lean
theorem plan8_upgrade_supply_index (L : Legacy) :
    (upgrade L).supplyState.index =
      if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  sorry

theorem plan8_start_zero (st idx : Nat) :
    accrualStart 0 idx =
        (if compInitialIndex ≤ idx then compInitialIndex else 0) ∧
      legacyStart st 0 = st := by
  sorry

theorem plan8_start_pos {r : Nat} (hr : r ≠ 0) (st idx : Nat) :
    accrualStart r idx = r ∧ legacyStart st r = r := by
  sorry

theorem plan8_compInitialIndex_pos : 0 < compInitialIndex := by
  sorry

theorem plan8_mul_le_mono (n x y : Nat) (h : x ≤ y) :
    n * x ≤ n * y := by
  sorry

theorem plan6_supply_pending_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hstartle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
  apply plan8_mul_le_mono
  have hU := plan8_upgrade_supply_index L
  have hpos := plan8_compInitialIndex_pos
  by_cases hr : a.supplierIndex = 0
  · obtain ⟨hacc, hleg⟩ :=
      plan8_start_zero L.supplyStart ((upgrade L).supplyState.index)
    rw [hr, hacc, hleg, hU]
    by_cases hI : L.supplyIndex = 0
    · simp [hI] <;> omega
    · by_cases hle : compInitialIndex ≤ L.supplyIndex
      · simp [hI, hle] <;> omega
      · simp [hI, hle] <;> omega
  · obtain ⟨hacc, hleg⟩ :=
      plan8_start_pos hr L.supplyStart ((upgrade L).supplyState.index)
    rw [hacc, hleg, hU]
    by_cases hI : L.supplyIndex = 0
    · simp [hI] <;> omega
    · simp [hI] <;> omega
```