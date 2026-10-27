**Proof plan.** For a successful step, first recover `ValidPayout s r` by contradiction, so the next state's accounts are `s.accounts` and its balances are `expectedBalance s r a`. Then `total` becomes a sum of `expectedBalance` over `s.accounts`. This sum splits into the original balance sum, minus the source indicator (which is `amount` because the source is in the nodup account list), plus the sum of `shareOf` over all accounts. The latter is shown equal to `amount` by restricting the sum to `recipients` (shares vanish outside), reindexing recipients by `indexOf?` to a range sum of `fairShare`, and evaluating that fair-share range sum via `Nat.div_add_mod`. The pieces then cancel by `omega`.

```lean
theorem plan0_sumOver_subset_eq {f : AccountId → Int} {l sub : List AccountId}
    (hl : l.Nodup) (hsubnd : sub.Nodup)
    (hsub : ∀ x ∈ sub, x ∈ l) (hzero : ∀ x ∈ l, x ∉ sub → f x = 0) :
    sumOver l f = sumOver sub f := by sorry

theorem plan0_sum_range_cons_shift (F : Nat → Int) (k n : Nat) :
    sumOver (List.range (n + 1)) (fun i => F (k + i)) =
      F k + sumOver (List.range n) (fun i => F (k + 1 + i)) := by sorry

theorem plan0_sumOver_indexOf_shift (F : Nat → Int) (k : Nat)
    (l : List AccountId) (hl : l.Nodup) :
    sumOver l
        (fun a => match indexOf? l a with
          | some i => F (k + i)
          | none => 0) =
      sumOver (List.range l.length) (fun i => F (k + i)) := by sorry

theorem plan0_sum_range_fairShare (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n)
        (fun i => (fairShare amount n i : Int)) = (amount : Int) := by sorry

theorem plan0_sumOver_accounts_shareOf (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) (hne : r.recipients ≠ []) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan0_sumOver_expectedBalance (s : State) (r : Request)
    (l : List AccountId) (hl : l.Nodup) :
    sumOver l (fun a => expectedBalance s r a) =
      sumOver l s.balance - (if r.source ∈ l then (r.amount : Int) else 0) +
        sumOver l (fun a => (shareOf r a : Int)) := by sorry
```