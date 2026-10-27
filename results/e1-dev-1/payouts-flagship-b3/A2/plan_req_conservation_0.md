**Proof plan.** If `step s r` returns `ok`, the request must be valid, since invalid requests are rejected. By `req_effects`, the new account list is unchanged and each new balance is `expectedBalance s r`. Hence conservation reduces to showing that summing `expectedBalance` over `s.accounts` gives the old total: the source debit contributes exactly `amount` (the source is in the accounts), and the recipient shares contribute exactly `amount`. The shares are summed first over `recipients` by reindexing through `indexOf?` to `List.range` and using the fair-division identity `n * (amount / n) + amount % n = amount`, then transferred from `recipients` to the whole account universe because shares vanish outside `recipients` and `recipients ⊆ accounts` with both lists duplicate-free.

```lean
theorem plan0_sum_fairShare_range (m n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare m n i : Nat) : Int)) = (m : Int) := by sorry

theorem plan0_sumOver_indexOf_range (l : List AccountId) (hl : l.Nodup) (g : Nat → Int) :
    sumOver l (fun a => match indexOf? l a with | some i => g i | none => 0)
      = sumOver (List.range l.length) (fun i => g i) := by sorry

theorem plan0_sum_share_recipients (r : Request) (hnd : r.recipients.Nodup)
    (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan0_sumOver_eq_of_subset (l sub : List AccountId) (hl : l.Nodup) (hsubnd : sub.Nodup)
    (hsub : ∀ x ∈ sub, x ∈ l) (f : AccountId → Int) (hf : ∀ a, a ∉ sub → f a = 0) :
    sumOver l f = sumOver sub f := by sorry

theorem plan0_sum_share_accounts (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan0_sum_expectedBalance (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = sumOver s.accounts s.balance := by sorry
```