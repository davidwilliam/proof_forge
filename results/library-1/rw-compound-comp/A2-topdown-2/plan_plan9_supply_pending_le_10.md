Proving the upgraded-index formula first reduces the goal to comparing the two index differences. For a nonzero recorded index both starts equal that index; for a zero recorded index the upgraded start is either `compInitialIndex` or `0`, while the legacy start is `0` or `compInitialIndex` and is bounded by the legacy index. Case analysis plus monotonicity of multiplication by `a.supply` then gives the bound.

```lean
theorem plan10_upgrade_supply_index (L : Legacy) :
    (upgrade L).supplyState.index =
      if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  sorry

theorem plan10_accrualStart_zero (st idx : Nat) :
    accrualStart 0 idx =
        (if compInitialIndex ≤ idx then compInitialIndex else 0) ∧
      legacyStart st 0 = st := by
  sorry

theorem plan10_accrualStart_pos {r : Nat} (hr : r ≠ 0) (st idx : Nat) :
    accrualStart r idx = r ∧ legacyStart st r = r := by
  sorry

theorem plan10_mul_le_mono (n x y : Nat) (h : x ≤ y) :
    n * x ≤ n * y := by
  sorry

theorem plan9_supply_pending_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hstartle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
  have hU := plan10_upgrade_supply_index L
  apply plan10_mul_le_mono
  by_cases hr : a.supplierIndex = 0
  · have hz :=
      plan10_accrualStart_zero L.supplyStart (upgrade L).supplyState.index
    rw [hr, hz.1, hz.2, hU]
    by_cases hi : L.supplyIndex = 0
    · rw [if_pos hi, if_pos (Nat.le_refl compInitialIndex)]
      cases hstart with
      | inl hst => rw [hst]; omega
      | inr hst => rw [hst]; omega
    · rw [if_neg hi]
      by_cases hc : compInitialIndex ≤ L.supplyIndex
      · rw [if_pos hc]
        cases hstart with
        | inl hst => rw [hst]; omega
        | inr hst => rw [hst]; omega
      · rw [if_neg hc]
        cases hstart with
        | inl hst => rw [hst]; omega
        | inr hst => rw [hst]; omega
  · have hp :=
      plan10_accrualStart_pos hr L.supplyStart (upgrade L).supplyState.index
    rw [hp.1, hp.2, hU]
    by_cases hi : L.supplyIndex = 0
    · rw [if_pos hi]; omega
    · rw [if_neg hi]; omega
```