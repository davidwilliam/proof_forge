(1) Proof plan: For a valid payout, first establish the arithmetic split of `amount` into the fee, equal recipient shares, and remainder, using `Nat.div_add_mod`. Next, count the total recipient credit over the duplicate-free account list: every recipient occurs exactly once. Similarly, the provided `sumOver_ite_eq` evaluates the source debit and fee-account credit. Combining these sums over `s.accounts` shows that `expectedBalance` preserves `total s`. Finally, unfold `step` in the valid case; its accounts are unchanged and its balances are `expectedBalance`; while an invalid case cannot produce `.ok`.

(2)
```lean
theorem plan0_fee_add_net (bps amount : Nat) (hbps : bps ≤ 10000) :
    (feeOf bps amount : Int) + (netOf bps amount : Int) = (amount : Int) := by
  sorry

theorem plan0_share_feeCredit_eq (bps amount n : Nat) :
    (n : Int) * (recipientShare bps amount n : Int)
        + (feeCredit bps amount n : Int)
      = (feeOf bps amount : Int) + (netOf bps amount : Int) := by
  sorry

theorem plan0_sumOver_recipients_eq (accounts recipients : List AccountId) (c : Int)
    (haccounts : accounts.Nodup) (hrecipients : recipients.Nodup)
    (hsub : ∀ x ∈ recipients, x ∈ accounts) :
    sumOver accounts (fun a => if a ∈ recipients then c else 0)
      = (recipients.length : Int) * c := by
  sorry

theorem plan0_sumOver_expectedBalance_eq (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = total s := by
  sorry

theorem plan0_total_step_of_valid (s : State) (r : Request)
    (hv : ValidPayout s r) :
    total (step s r).2 = total s := by
  sorry
```