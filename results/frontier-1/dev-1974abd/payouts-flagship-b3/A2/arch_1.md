## Plan

Conservation follows once the shares paid out sum to the amount debited.  First reindex the sum of shares over the (duplicate-free) recipient list to a sum over `List.range recipients.length`, using `indexOf?_getElem`-style reasoning packaged as a generic `indexOf?` reindexing lemma proved by induction on the list, with a head-tail decomposition of `List.range`.  Next evaluate that range sum: a `fairShare` is the constant quotient `amount / n` plus an indicator for the first `amount % n` positions, so by the provided `sumOver_add`, `sumOver_congr`, the constant-sum and indicator-sum lemmas, and `Nat.div_add_mod`, it totals `amount`.  Then transfer the sum from recipients to the whole account universe: shares are zero off the recipient list (`aux_share_zero`), recipients are a duplicate-free subset of the duplicate-free accounts under `CanPay`, and a generic subset-sum lemma (proved via a `List.erase` decomposition) identifies the two sums.  Finally `arch1_total_of_canPay` combines this with the already-proved debit sum (`arch0_debit_sum_accounts`), the pointwise balance formula (`arch0_balance_eq`), and invariance of the account list (`arch0_accounts_eq`) to get `total (step s r).2 = total s`; `req_conservation` is then just this lemma applied to a successful step, whose hypothesis is exactly `CanPay` by `arch0_ok_canPay`.  This also discharges the previously stuck `arch0_share_sum_accounts`, under the new name `arch1_share_sum_accounts`.

```lean
theorem arch1_indexOf_cons_ne (x a : AccountId) (xs : List AccountId) (h : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  sorry

theorem arch1_sumOver_range_cons (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  sorry

theorem arch1_sumOver_indexOf_eq_range (l : List AccountId) (hl : l.Nodup)
    (f : Nat → Int) :
    sumOver l (fun a => match indexOf? l a with
                        | some i => f i
                        | none => 0)
      = sumOver (List.range l.length) f := by
  sorry

theorem arch1_shareOf_int_eq (r : Request) (a : AccountId) :
    (shareOf r a : Int) = match indexOf? r.recipients a with
                          | some i => (fairShare r.amount r.recipients.length i : Int)
                          | none => 0 := by
  sorry

theorem arch1_sumOver_recipients_eq_range (r : Request) (hl : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by
  sorry

theorem arch1_fairShare_int_eq (amount n i : Nat) :
    (fairShare amount n i : Int)
      = (amount / n : Int) + (if i < amount % n then (1 : Int) else 0) := by
  sorry

theorem arch1_sumOver_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  sorry

theorem arch1_sumOver_range_indicator (n m : Nat) (hm : m ≤ n) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := by
  sorry

theorem arch1_sum_range_fair (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (amount : Int) := by
  sorry

theorem arch1_sumOver_erase_of_mem (l : List AccountId) (f : AccountId → Int)
    (a : AccountId) (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by
  sorry

theorem arch1_sumOver_eq_of_subset (accounts recipients : List AccountId)
    (haN : accounts.Nodup) (hrN : recipients.Nodup)
    (hsub : ∀ x ∈ recipients, x ∈ accounts)
    (f : AccountId → Int) (hz : ∀ a, a ∉ recipients → f a = 0) :
    sumOver accounts f = sumOver recipients f := by
  sorry

theorem arch1_share_sum_recipients (s : State) (r : Request) (hC : CanPay s r) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  sorry

theorem arch1_share_sum_accounts (s : State) (r : Request) (hC : CanPay s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by
  sorry

theorem arch1_total_of_canPay (s : State) (r : Request) (hC : CanPay s r) :
    total (step s r).2 = total s := by
  sorry

theorem req_conservation : Conserves step := by
  intro s r hok
  exact arch1_total_of_canPay s r (arch0_ok_canPay s r hok)
```