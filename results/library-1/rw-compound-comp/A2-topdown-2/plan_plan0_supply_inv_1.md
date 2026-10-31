The first consistency goal was left as `s.blockNumber ≤ s.blockNumber` after rewriting the updated block; it needs an explicit reflexivity step. The remaining goals and helper-lemma applications were already correct.

```lean
theorem plan1_accrueSide_props (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index ∧
    (accrueSide sd now total).block = now ∧
    (accrueSide sd now total).speed = sd.speed := by
  sorry

theorem plan1_modify_mem_pred {l : List Acct} {who : Nat} {f : Acct → Acct}
    {P : Acct → Prop}
    (hP : ∀ a ∈ l, P a) (hf : ∀ a ∈ l, P (f a)) {a : Acct}
    (ha : a ∈ l.modify who f) : P a := by
  sorry

theorem plan0_supply_inv (sp : Nat × Nat) (s : St) (who : Account) (s' : St) :
    comptroller s (.supplyHook who) = some s' → td0_Inv sp s → td0_Inv sp s' := by
  intro hCall hInv
  obtain ⟨_hBlk, _hStart, rfl⟩ := td0_supply_hook_effect s who s' hCall
  obtain ⟨hCons, hSupSpd, hBorSpd⟩ := hInv
  obtain ⟨_hSupBlk, hBorBlk, hAll⟩ := hCons
  obtain ⟨hIdxGe, hNewBlk, hNewSpd⟩ :=
    plan1_accrueSide_props s.supplyState s.blockNumber (totalSupply s)
  unfold td0_Inv Consistent
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block ≤ s.blockNumber
    rw [hNewBlk]
    exact Nat.le_refl _
  · exact hBorBlk
  · intro a ha
    apply plan1_modify_mem_pred _ _ ha
    · intro b hb
      exact ⟨Nat.le_trans (hAll b hb).1 hIdxGe, (hAll b hb).2⟩
    · intro b hb
      exact ⟨Nat.le_refl _, (hAll b hb).2⟩
  · show (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = sp.1
    rw [hNewSpd]
    exact hSupSpd
  · exact hBorSpd
```