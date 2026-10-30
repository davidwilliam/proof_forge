## Plan

Conservation is a single-step property, so no reachable-state invariant is needed. For an accepted payout, first recover `ValidPayout s r` and compute `step s r` explicitly. The new total then decomposes into:

- the old total;
- minus the source deduction, which sums to `r.amount` because the source occurs uniquely in the duplicate-free account list;
- plus all recipient shares, whose sum over `s.accounts` equals their sum over `r.recipients` because shares outside the recipients are zero.

Recipient shares are summed positionally: for position `i`, the share is `amount / n + 1` for the first `amount % n` positions and `amount / n` otherwise. Summing over `List.range n` gives `n * (amount / n) + amount % n = amount` by `Nat.div_add_mod`. Combining the deduction and shares proves that the expected balances have the same sum as the original balances, hence conservation.

```lean
theorem arch0_valid_of_ok (s : State) (r : Request) :
    (step s r).1 = .ok → ValidPayout s r := by sorry

theorem arch0_step_of_valid (s : State) (r : Request) :
    ValidPayout s r →
      step s r =
        (.ok, { s with
          balance := fun a => expectedBalance s r a,
          applied := r.txId :: s.applied }) := by sorry

theorem arch0_sum_deduction (s : State) (r : Request) :
    ValidPayout s r →
      sumOver s.accounts
          (fun a => if a = r.source then (r.amount : Int) else 0)
        = (r.amount : Int) := by sorry

theorem arch0_sum_range_const (n : Nat) (q : Int) :
    sumOver (List.range n) (fun _ => q) = (n : Int) * q := by sorry

theorem arch0_sum_range_indicator (n m : Nat) (hm : m ≤ n) :
    sumOver (List.range n)
        (fun i => if i < m then (1 : Int) else 0)
      = (m : Int) := by sorry

theorem arch0_fairShare_sum_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n)
        (fun i => (fairShare amount n i : Int))
      = (amount : Int) := by sorry

theorem arch0_sum_recipients_eq_range (r : Request) :
    r.recipients.Nodup →
      sumOver r.recipients (fun a => (shareOf r a : Int)) =
        sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by sorry

theorem arch0_sum_recipients_shareOf (r : Request) :
    r.recipients.Nodup →
    r.recipients ≠ [] →
      sumOver r.recipients (fun a => (shareOf r a : Int))
        = (r.amount : Int) := by sorry

theorem arch0_sumOver_subset_of_zero_outside
    (l sub : List AccountId) (f : AccountId → Int) :
    l.Nodup →
    sub.Nodup →
    (∀ x ∈ sub, x ∈ l) →
    (∀ a, a ∉ sub → f a = 0) →
      sumOver l f = sumOver sub f := by sorry

theorem arch0_sum_accounts_shares (s : State) (r : Request) :
    ValidPayout s r →
      sumOver s.accounts (fun a => (shareOf r a : Int))
        = (r.amount : Int) := by sorry

theorem arch0_sum_expected (s : State) (r : Request) :
    ValidPayout s r →
      sumOver s.accounts (fun a => expectedBalance s r a)
        = sumOver s.accounts s.balance := by sorry

theorem arch0_total_of_valid (s : State) (r : Request) :
    ValidPayout s r → total (step s r).2 = total s := by sorry

theorem req_conservation : Conserves step := by
  intro s r hok
  exact arch0_total_of_valid s r (arch0_valid_of_ok s r hok)
```