Short proof plan: analyse `_setCompSpeeds` as the sequential composition of the supply-speed and borrow-speed branches. Characterise each branch separately: a successful branch either leaves its side unchanged when the speed already matches, or first accrues that side to the current block (hence its old block cannot be in the future) and then installs the new speed. The supply branch does not touch the borrow side, the block number, or the accounts, so the borrow branch's accrual — stated against the intermediate state — can be rewritten against the original state. A purely structural recombination lemma then merges the two one-sided updates into the two-sided update required by `SpeedsSet`.

```lean
theorem plan11_setSupply_spec (s : St) (a : Nat) (t : St) :
    setSupplySpeed s a = some t →
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with supplyState := if s.supplyState.speed = a then s.supplyState
          else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  sorry

theorem plan11_setBorrow_spec (s : St) (b : Nat) (t : St) :
    setBorrowSpeed s b = some t →
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with borrowState := if s.borrowState.speed = b then s.borrowState
          else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  sorry

theorem plan11_setSupply_preserves (s : St) (a : Nat) (t : St) :
    setSupplySpeed s a = some t →
    t.borrowState = s.borrowState ∧ t.blockNumber = s.blockNumber ∧ t.accts = s.accts := by
  sorry

theorem plan11_combine (s s1 s' : St) (a b : Nat) :
    s1 = { s with supplyState := if s.supplyState.speed = a then s.supplyState
           else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } →
    s' = { s1 with borrowState := if s1.borrowState.speed = b then s1.borrowState
           else { accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) with speed := b } } →
    s1.borrowState = s.borrowState →
    s1.blockNumber = s.blockNumber →
    s1.accts = s.accts →
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  sorry

theorem td0_set_speeds_effect : ∀ (s : St) (a b : Nat) (s' : St),
    comptroller s (.setSpeeds a b) = some s' → SpeedsSet s a b s' := by
  intro s a b s' h
  have h1 : setCompSpeedInternal s a b = some s' := h
  unfold setCompSpeedInternal at h1
  cases hss : setSupplySpeed s a with
  | none =>
      simp [hss] at h1
  | some s1 =>
      have h2 : setBorrowSpeed s1 b = some s' := by
        simpa [hss] using h1
      obtain ⟨hsupBlock, hsupEq⟩ := plan11_setSupply_spec s a s1 hss
      obtain ⟨hborBlock0, hborEq⟩ := plan11_setBorrow_spec s1 b s' h2
      obtain ⟨hborState, hblk, haccts⟩ := plan11_setSupply_preserves s a s1 hss
      unfold SpeedsSet
      refine ⟨?_, ?_, ?_⟩
      · exact hsupBlock
      · intro hbne
        have hb1 : s1.borrowState.speed ≠ b := by
          rw [hborState]
          exact hbne
        have hb2 := hborBlock0 hb1
        rw [hborState, hblk] at hb2
        exact hb2
      · exact plan11_combine s s1 s' a b hsupEq hborEq hborState hblk haccts
```