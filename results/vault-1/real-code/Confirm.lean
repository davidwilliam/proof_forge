import ShareVault.Spec
open ShareVault

-- case 0, step 3, REQ-WITHDRAW-ROUNDS-UP: withdraw of 50030063815 burned 1 shares; exact value 1.99999999992
example : ¬ (0 < 2 ∧ 50030063815 * 2 ≤ 1 * 50030063817 ∧ 1 * 50030063817 < 50030063815 * 2 + 50030063817) := by decide

-- case 0, step 3, REQ-SHARE-VALUE: share worth 50030063817/2 fell to 2/1
example : ¬ ValueNotBelow ⟨50030063817, 2, fun _ => 0⟩ ⟨2, 1, fun _ => 0⟩ := by decide

-- case 2, step 5, REQ-WITHDRAW-ROUNDS-UP: withdraw of 35 burned 0 shares; exact value 1.32987297201e-06
example : ¬ (0 < 800 ∧ 35 * 800 ≤ 0 * 21054642503 ∧ 0 * 21054642503 < 35 * 800 + 21054642503) := by decide

-- case 2, step 5, REQ-SHARE-VALUE: share worth 21054642503/800 fell to 21054642468/800
example : ¬ ValueNotBelow ⟨21054642503, 800, fun _ => 0⟩ ⟨21054642468, 800, fun _ => 0⟩ := by decide

-- case 387, step 3, REQ-REDEEM-ROUNDS-DOWN: redeem of 300 shares paid 6; exact value 7
example : ¬ (6 * 300 ≤ 300 * 7 ∧ 300 * 7 < (6 + 1) * 300) := by decide

