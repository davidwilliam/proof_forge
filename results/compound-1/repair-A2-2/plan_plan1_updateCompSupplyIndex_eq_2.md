Proof plan: split `updateCompSupplyIndex` on whether blocks have passed, the supply speed is positive, and total supply is positive. In the positive case, rewrite `accrueSide` by its defining branch and convert `fraction (delta * speed) total` to `delta * speed * doubleScale / total`. In the remaining cases, `accrueSide` only updates the block; when no blocks have passed, the stored block already equals the current block, and when the ratio is zero the index is unchanged.

```lean
theorem plan2_accrueSide_pos (sd : Side) (now total : Nat)
    (hd : 0 < now - sd.block) (hsp : 0 < sd.speed) (htot : 0 < total) :
    accrueSide sd now total =
      { sd with index := sd.index + (now - sd.block) * sd.speed * doubleScale / total, block := now } := by sorry

theorem plan2_accrueSide_not_pos (sd : Side) (now total : Nat)
    (h : ¬ (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total)) :
    accrueSide sd now total = { sd with block := now } := by sorry

theorem plan2_fraction_eq (d sp total : Nat) :
    fraction (d * sp) total = d * sp * doubleScale / total := by sorry

theorem plan2_side_block_eq_self (sd : Side) (now : Nat) (h : sd.block = now) :
    { sd with block := now } = sd := by sorry

theorem plan2_side_add_zero (sd : Side) (now : Nat) :
    { sd with index := sd.index + 0, block := now } = { sd with block := now } := by sorry
```