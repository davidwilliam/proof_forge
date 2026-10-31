**Proof plan.** Keep the six case helpers, but make every balance-update function explicit when applying the `withAcct` helper. Previously Lean inferred that function as the identity from the index-preservation proof; giving the supply/borrow update explicitly fixes the transfer case and the analogous cases.

```lean
theorem plan0_supply_inv (sp : Nat × Nat) (s : St) (who : Account) (s' : St) :
    comptroller s (.supplyHook who) = some s' → td0_Inv sp s → td0_Inv sp s' := by
  sorry

theorem plan0_borrow_inv (sp : Nat × Nat) (s : St) (who : Account) (s' : St) :
    comptroller s (.borrowHook who) = some s' → td0_Inv sp s → td0_Inv sp s' := by
  sorry

theorem plan0_claim_inv (sp : Nat × Nat) (s : St) (who : Account) (s' : St) :
    comptroller s (.claim who) = some s' → td0_Inv sp s → td0_Inv sp s' := by
  sorry

theorem plan0_setSpeeds_inv (s : St) (a b : Nat) (s' : St) :
    comptroller s (.setSpeeds a b) = some s' → Consistent s → td0_Inv (a, b) s' := by
  sorry

theorem plan0_withAcct_inv (sp : Nat × Nat) (s : St) (who : Account) (f : Acct → Acct) :
    td0_Inv sp s →
    (∀ a, (f a).supplierIndex = a.supplierIndex ∧ (f a).borrowerIndex = a.borrowerIndex) →
    td0_Inv sp (s.withAcct who f) := by
  sorry

theorem plan0_env_inv (sp : Nat × Nat) (s : St) (k x : Nat) :
    td0_Inv sp s →
    td0_Inv sp { s with blockNumber := s.blockNumber + k } ∧
    td0_Inv sp { s with reserve := s.reserve + x } := by
  sorry

theorem td0_exec_inv : ∀ (sp : Nat × Nat) (s : St) (op : Op), td0_Inv sp s →
    td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by
  intro sp s op h
  cases op with
  | mint who x =>
    by_cases hlen : who < s.accts.length
    · have hsome := td0_calls_some s (.supplyHook who) h.1
      obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.supplyHook who) = some t := by
        cases hc : comptroller s (.supplyHook who) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv := plan0_supply_inv sp s who s' hs' h
      have heq : exec comptroller s (Op.mint who x) =
          s'.withAcct who (fun a => { a with supply := a.supply + x }) := by
        simp [exec, hlen, hs']
      rw [heq]
      exact plan0_withAcct_inv sp s' who
        (fun a => { a with supply := a.supply + x }) hinv (fun a => ⟨rfl, rfl⟩)
    · have heq : exec comptroller s (Op.mint who x) = s := by
        simp [exec, hlen]
      rw [heq]
      exact h
  | redeem who x =>
    by_cases hlen : who < s.accts.length
    · have hsome := td0_calls_some s (.supplyHook who) h.1
      obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.supplyHook who) = some t := by
        cases hc : comptroller s (.supplyHook who) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv := plan0_supply_inv sp s who s' hs' h
      by_cases hle : x ≤ (s'.acct who).supply
      · have heq : exec comptroller s (Op.redeem who x) =
            s'.withAcct who (fun a => { a with supply := a.supply - x }) := by
          simp [exec, hlen, hs', hle]
        rw [heq]
        exact plan0_withAcct_inv sp s' who
          (fun a => { a with supply := a.supply - x }) hinv (fun a => ⟨rfl, rfl⟩)
      · have heq : exec comptroller s (Op.redeem who x) = s := by
          simp [exec, hlen, hs', hle]
        rw [heq]
        exact h
    · have heq : exec comptroller s (Op.redeem who x) = s := by
        simp [exec, hlen]
      rw [heq]
      exact h
  | transfer src dst x =>
    by_cases hcond : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · have hsome := td0_calls_some s (.supplyHook src) h.1
      obtain ⟨s1, hs1⟩ : ∃ t, comptroller s (.supplyHook src) = some t := by
        cases hc : comptroller s (.supplyHook src) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv1 := plan0_supply_inv sp s src s1 hs1 h
      have hsome2 := td0_calls_some s1 (.supplyHook dst) hinv1.1
      obtain ⟨s2, hs2⟩ : ∃ t, comptroller s1 (.supplyHook dst) = some t := by
        cases hc : comptroller s1 (.supplyHook dst) with
        | none => simp [hc] at hsome2
        | some t => exact ⟨t, rfl⟩
      have hinv2 := plan0_supply_inv sp s1 dst s2 hs2 hinv1
      by_cases hle : x ≤ (s2.acct src).supply
      · have heq : exec comptroller s (Op.transfer src dst x) =
            (s2.withAcct src (fun a => { a with supply := a.supply - x })).withAcct dst
              (fun a => { a with supply := a.supply + x }) := by
          simp [exec, hcond, hs1, hs2, hle]
        rw [heq]
        have hinvSrc : td0_Inv sp
            (s2.withAcct src (fun a => { a with supply := a.supply - x })) :=
          plan0_withAcct_inv sp s2 src
            (fun a => { a with supply := a.supply - x }) hinv2 (fun a => ⟨rfl, rfl⟩)
        exact plan0_withAcct_inv sp
          (s2.withAcct src (fun a => { a with supply := a.supply - x })) dst
          (fun a => { a with supply := a.supply + x }) hinvSrc (fun a => ⟨rfl, rfl⟩)
      · have heq : exec comptroller s (Op.transfer src dst x) = s := by
          simp [exec, hcond, hs1, hs2, hle]
        rw [heq]
        exact h
    · have heq : exec comptroller s (Op.transfer src dst x) = s := by
        simp [exec, hcond]
      rw [heq]
      exact h
  | borrow who x =>
    by_cases hlen : who < s.accts.length
    · have hsome := td0_calls_some s (.borrowHook who) h.1
      obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.borrowHook who) = some t := by
        cases hc : comptroller s (.borrowHook who) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv := plan0_borrow_inv sp s who s' hs' h
      have heq : exec comptroller s (Op.borrow who x) =
          s'.withAcct who (fun a => { a with borrow := a.borrow + x }) := by
        simp [exec, hlen, hs']
      rw [heq]
      exact plan0_withAcct_inv sp s' who
        (fun a => { a with borrow := a.borrow + x }) hinv (fun a => ⟨rfl, rfl⟩)
    · have heq : exec comptroller s (Op.borrow who x) = s := by
        simp [exec, hlen]
      rw [heq]
      exact h
  | repay who x =>
    by_cases hlen : who < s.accts.length
    · have hsome := td0_calls_some s (.borrowHook who) h.1
      obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.borrowHook who) = some t := by
        cases hc : comptroller s (.borrowHook who) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv := plan0_borrow_inv sp s who s' hs' h
      by_cases hle : x ≤ (s'.acct who).borrow
      · have heq : exec comptroller s (Op.repay who x) =
            s'.withAcct who (fun a => { a with borrow := a.borrow - x }) := by
          simp [exec, hlen, hs', hle]
        rw [heq]
        exact plan0_withAcct_inv sp s' who
          (fun a => { a with borrow := a.borrow - x }) hinv (fun a => ⟨rfl, rfl⟩)
      · have heq : exec comptroller s (Op.repay who x) = s := by
          simp [exec, hlen, hs', hle]
        rw [heq]
        exact h
    · have heq : exec comptroller s (Op.repay who x) = s := by
        simp [exec, hlen]
      rw [heq]
      exact h
  | claim who =>
    have hsome := td0_calls_some s (.claim who) h.1
    obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.claim who) = some t := by
      cases hc : comptroller s (.claim who) with
      | none => simp [hc] at hsome
      | some t => exact ⟨t, rfl⟩
    have heq : exec comptroller s (Op.claim who) = s' := by
      simp [exec, hs']
    rw [heq]
    exact plan0_claim_inv sp s who s' hs' h
  | setSpeeds a b =>
    have hsome := td0_calls_some s (.setSpeeds a b) h.1
    obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.setSpeeds a b) = some t := by
      cases hc : comptroller s (.setSpeeds a b) with
      | none => simp [hc] at hsome
      | some t => exact ⟨t, rfl⟩
    have heq : exec comptroller s (Op.setSpeeds a b) = s' := by
      simp [exec, hs']
    rw [heq]
    exact plan0_setSpeeds_inv s a b s' hs' h.1
  | advance k =>
    exact (plan0_env_inv sp s k 0 h).1
  | drip x =>
    exact (plan0_env_inv sp s 0 x h).2
```