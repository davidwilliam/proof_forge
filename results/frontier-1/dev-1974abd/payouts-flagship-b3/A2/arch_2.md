## Plan

`req_conservation` is a single-call requirement, so no state invariant is needed: it suffices to compute one successful `step`. The existing `arch0_ok_canPay` extracts `CanPay s r` from `(step s r).1 = .ok`, and the existing `arch0_balance_eq`, `arch0_accounts_eq`, and `arch0_debit_sum_accounts` reduce conservation to showing that the recipients' shares, summed over `s.accounts`, equal `r.amount`.

That share-sum is the real work, and it replaces the still-unproved `arch0_`/`arch1_` attempts with a fresh `arch2_` chain, each link one focused induction or case split:

1. **Arithmetic of one share** (`arch2_fairShare_int_eq`, `arch2_sumOver_range_const`, `arch2_sumOver_range_indicator`): a fair share is the constant quotient `amount / n` plus an indicator for the first `amount % n` positions; summed over `List.range n` these give `n * (amount / n)` and `min n (amount % n) = amount % n`, hence `arch2_sum_range_fair` by `Nat.div_add_mod`.
2. **Reindexing** (`arch2_sumOver_range_succ_shift`, `arch2_indexOf_cons_shift`): peeling the head of `List.range (m+1)` and of `indexOf? (x :: xs)` both shift indices by one, so by induction on a duplicate-free recipient list, summing `shareOf` over the list equals summing `fairShare` over its length (`arch2_sumOver_indexed_eq_range`, then `arch2_sumOver_recipients_eq_range` at offset `0`). The offset is generalized precisely because the tail's indices are shifted while the denominator stays the full length.
3. **From recipients to accounts** (`arch2_sumOver_erase_add`, `arch2_sumOver_eq_of_subset`): removing one element from a duplicate-free list splits off its contribution; inducting on `accounts` with this shows a function vanishing outside `recipients` (such as `shareOf`, by the existing `aux_share_zero`) has the same sum over `accounts` as over `recipients`. Combined with step 2 this gives `arch2_share_sum_accounts`.
4. **Total** (`arch2_total_of_canPay`): rewrite `total` via `arch0_accounts_eq` and `arch0_balance_eq`, split with `sumOver_add`/`sumOver_sub`, and cancel the debit sum (`arch0_debit_sum_accounts`) against the share sum.

Then `req_conservation` is a two-line derivation.

```lean
theorem arch2_fairShare_int_eq (amount n i : Nat) :
    (fairShare amount n i : Int)
      = (amount / n : Int) + (if i < amount % n then (1 : Int) else 0) := by sorry

theorem arch2_sumOver_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by sorry

theorem arch2_sumOver_range_indicator (n m : Nat) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0)
      = (Nat.min n m : Int) := by sorry

theorem arch2_sum_range_fair (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (amount : Int) := by sorry

theorem arch2_sumOver_range_succ_shift (m : Nat) (f : Nat → Int) :
    sumOver (List.range (m + 1)) f
      = f 0 + sumOver (List.range m) (fun i => f (i + 1)) := by sorry

theorem arch2_indexOf_cons_shift (amount n offset : Nat) (x a : AccountId)
    (xs : List AccountId) (hxa : x ≠ a) :
    (match indexOf? (x :: xs) a with
     | some i => (fairShare amount n (offset + i) : Int)
     | none => 0)
      = (match indexOf? xs a with
         | some i => (fairShare amount n ((offset + 1) + i) : Int)
         | none => 0) := by sorry

theorem arch2_sumOver_indexed_eq_range (l : List AccountId) (hl : l.Nodup)
    (amount n offset : Nat) :
    sumOver l (fun a => match indexOf? l a with
                        | some i => (fairShare amount n (offset + i) : Int)
                        | none => 0)
      = sumOver (List.range l.length)
          (fun i => (fairShare amount n (offset + i) : Int)) := by sorry

theorem arch2_sumOver_recipients_eq_range (r : Request) (hl : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by sorry

theorem arch2_sumOver_erase_add {l : List AccountId} (hl : l.Nodup) (a : AccountId)
    (ha : a ∈ l) (f : AccountId → Int) :
    sumOver l f = f a + sumOver (l.erase a) f := by sorry

theorem arch2_sumOver_eq_of_subset (accounts recipients : List AccountId)
    (haN : accounts.Nodup) (hrN : recipients.Nodup)
    (hsub : ∀ x ∈ recipients, x ∈ accounts)
    (f : AccountId → Int) (hz : ∀ a, a ∉ recipients → f a = 0) :
    sumOver accounts f = sumOver recipients f := by sorry

theorem arch2_share_sum_accounts (s : State) (r : Request) (hC : CanPay s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem arch2_total_of_canPay (s : State) (r : Request) (hC : CanPay s r) :
    total (step s r).2 = total s := by sorry

theorem req_conservation : Conserves step := by
  intro s r hok
  exact arch2_total_of_canPay s r (arch0_ok_canPay s r hok)
```