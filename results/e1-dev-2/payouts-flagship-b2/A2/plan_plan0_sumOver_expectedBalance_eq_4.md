Proof plan: split the expected-balance sum into the original balance sum, minus the one-off debit from the source, plus the total credits. Evaluate the debit with the duplicate-free indicator sum, show credits vanish outside the recipient list so the credit sum can be restricted to recipients, reindex that sum by position via `indexOf?`, and finally use the fair-share range identity that the shares add up to `amount`; combining the three evaluated pieces gives conservation of the total by `omega`.

```lean
theorem plan4_expectedBalance_sum_decomp (s : State) (r : Request) :
    sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance
        - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by sorry

theorem plan4_debit_sum_eq (s : State) (r : Request)
    (hNodup : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts) :
    sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by sorry

theorem plan4_shareOf_eq_zero_of_not_mem (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) :
    shareOf r a = 0 := by sorry

theorem plan4_credit_sum_eq_recipient_sum (s : State) (r : Request)
    (hAcc : s.accounts.Nodup) (hRec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))
      = sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int)) := by sorry

theorem plan4_recipient_credit_sum_eq_range (r : Request) (hRec : r.recipients.Nodup) :
    sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int)) := by sorry

theorem plan4_range_fair_sum_eq_amount (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int))
      = (amount : Int) := by sorry
```