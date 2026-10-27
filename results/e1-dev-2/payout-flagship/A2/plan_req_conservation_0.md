## Proof plan

On the successful branch, unpack `ValidPayout` and unfold `step` and `total`. The account list is unchanged and every balance is `expectedBalance s r a`. Decompose the summed expected balances into the original total, minus `amount` at the source, plus all recipient shares. Transport the share sum from `s.accounts` to `r.recipients` (shares outside the recipients are zero), then to a sum over `List.range r.recipients.length` via `indexOf?_getElem`, and finally evaluate the fair-share range sum using `amount / n`, `amount % n`, and `Nat.div_add_mod`. Since the source belongs to `s.accounts`, the deducted and distributed amounts cancel.

```lean
theorem plan0_sumOver_range_indicator (k n : Nat) (h : k ≤ n) :
    sumOver (List.range n) (fun i => if i < k then (1 : Int) else 0) = (k : Int) := by
  sorry

theorem plan0_sum_fairShare_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  sorry

theorem plan0_sumOver_recipients_shareOf (r : Request) (h : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) =
      sumOver (List.range r.recipients.length)
        (fun i => (fairShare r.amount r.recipients.length i : Int)) := by
  sorry

theorem plan0_sumOver_accounts_shareOf (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  sorry

theorem plan0_sumOver_accounts_shareOf_amount (s : State) (r : Request)
    (h : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  sorry

theorem plan0_sumOver_expectedBalance (l : List AccountId) (hl : l.Nodup)
    (s : State) (r : Request) :
    sumOver l (fun a => expectedBalance s r a) =
      sumOver l s.balance
        - (if r.source ∈ l then (r.amount : Int) else 0)
        + sumOver l (fun a => (shareOf r a : Int)) := by
  sorry
```