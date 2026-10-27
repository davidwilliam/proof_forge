Short proof plan: For a valid payout, first bound the rounding leftover by the number of weights, which lets the floor shares plus the one-cent bonuses summed over all weight positions equal exactly `amount`. Next, accounts outside the recipient list receive zero, and recipients are duplicate-free, so summing `shareOf` over the whole account universe equals summing it over the recipients, hence equals `amount`. Finally, expanding `expectedBalance` over the accounts makes the source debit contribute `-amount` and all shares contribute `+amount`, leaving the original total unchanged.

```lean
theorem plan1_leftover_le_length (amount : Nat) (ws : List Nat)
    (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    leftover amount ws ≤ ws.length := by sorry

theorem plan1_natSum_weightedShare_range (amount : Nat) (ws : List Nat)
    (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) = amount := by sorry

theorem plan1_sumOver_eq_of_subset_zero {L M : List Nat} {f : Nat → Int}
    (hL : L.Nodup) (hM : M.Nodup)
    (hsub : ∀ x ∈ M, x ∈ L) (hzero : ∀ x, x ∉ M → f x = 0) :
    sumOver L f = sumOver M f := by sorry

theorem plan1_sumOver_recipients_shareOf (s : State) (r : Request)
    (h : ValidPayout s r) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan1_sumOver_expectedBalance_eq (s : State) (r : Request)
    (h : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance := by sorry
```