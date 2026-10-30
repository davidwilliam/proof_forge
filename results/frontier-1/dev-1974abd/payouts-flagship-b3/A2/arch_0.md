(1) **Proof plan**

All three requirements concern a single call to `step`, so no sequence invariant is needed. The shared computation facts are:

- A successful result can only come from the `CanPay` branch (`arch0_ok_canPay`).
- In all cases the account list is unchanged; in the `CanPay` branch the authorization relation is unchanged and every balance is exactly `expectedBalance` (`arch0_accounts_eq`, `arch0_auth_eq`, `arch0_balance_eq`). This immediately gives `Effects`.
- For `NonNegative`, split on `CanPay`. The rejected branch is literally `(.rejected, s)`. In the successful branch split on whether the account is the source: the source is not a recipient, receives no share, and its balance covers `amount`; every other account only gains a nonnegative share. These are `arch0_balance_source_nonneg` and `arch0_balance_other_nonneg`.
- For `Conservation`, expand `total` over the unchanged account list and split the new balance into old balance, debit, and share credit. The debit summed over the duplicate-free account list is exactly `amount` (`arch0_debit_sum_accounts`). The shares summed over recipients equal the shares summed over `List.range n` (`arch0_share_sum_recipients_eq_range`), whose fair shares sum to `amount` (`arch0_fairShare_sum_range`); because recipients are a duplicate-free sublist of the accounts, the share sum over all accounts is also `amount` (`arch0_share_sum_accounts`). Debit and credit cancel in `arch0_total_of_canPay`, giving `Conserves`.

(2)

```lean
theorem arch0_ok_canPay (s : State) (r : Request) (h : (step s r).1 = .ok) :
    CanPay s r := by
  sorry

theorem arch0_accounts_eq (s : State) (r : Request) :
    (step s r).2.accounts = s.accounts := by
  sorry

theorem arch0_auth_eq (s : State) (r : Request) :
    (step s r).2.auth = s.auth := by
  sorry

theorem arch0_balance_eq (s : State) (r : Request) (a : AccountId) (hC : CanPay s r) :
    (step s r).2.balance a = expectedBalance s r a := by
  sorry

theorem arch0_step_of_not_canPay (s : State) (r : Request) (hC : ¬ CanPay s r) :
    step s r = (.rejected, s) := by
  sorry

theorem arch0_balance_source_nonneg (s : State) (r : Request) (hC : CanPay s r)
    (hpos : ∀ a ∈ s.accounts, 0 ≤ s.balance a) :
    0 ≤ (step s r).2.balance r.source := by
  sorry

theorem arch0_balance_other_nonneg (s : State) (r : Request) (a : AccountId)
    (hC : CanPay s r) (ha_nonneg : 0 ≤ s.balance a) (hne : a ≠ r.source) :
    0 ≤ (step s r).2.balance a := by
  sorry

theorem arch0_fairShare_sum_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  sorry

theorem arch0_share_sum_recipients_eq_range (r : Request) (hnd : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by
  sorry

theorem arch0_share_sum_recipients (r : Request) (hne : r.recipients ≠ [])
    (hnd : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  sorry

theorem arch0_debit_sum_accounts (s : State) (r : Request) (hC : CanPay s r) :
    sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
  sorry

theorem arch0_share_sum_accounts (s : State) (r : Request) (hC : CanPay s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  sorry

theorem arch0_total_of_canPay (s : State) (r : Request) (hC : CanPay s r) :
    total (step s r).2 = total s := by
  sorry

theorem req_effects : Effects step := by
  intro s r hok
  have hC : CanPay s r := arch0_ok_canPay s r hok
  exact ⟨arch0_accounts_eq s r, arch0_auth_eq s r,
    fun a => arch0_balance_eq s r a hC⟩

theorem req_nonnegative : NonNegative step := by
  intro s r hpos a ha
  have ha_mem : a ∈ s.accounts := by
    rw [arch0_accounts_eq s r] at ha
    exact ha
  by_cases hC : CanPay s r
  · by_cases hsrc : a = r.source
    · subst hsrc
      exact arch0_balance_source_nonneg s r hC hpos
    · exact arch0_balance_other_nonneg s r a hC (hpos a ha_mem) hsrc
  · rw [arch0_step_of_not_canPay s r hC]
    exact hpos a ha_mem

theorem req_conservation : Conserves step := by
  intro s r hok
  exact arch0_total_of_canPay s r (arch0_ok_canPay s r hok)
```