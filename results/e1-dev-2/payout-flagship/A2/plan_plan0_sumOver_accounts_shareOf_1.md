**Proof plan:** Show that `shareOf` vanishes outside `r.recipients`. Then, by induction on a duplicate-free list `l`, rewrite the sum of shares over `l` as the sum over `r.recipients` guarded by membership in `l`, splitting the guard over a cons cell and using `sumOver_ite_eq` for the head term. Finally remove the guard for `l = s.accounts` using the subset hypothesis `r.recipients ⊆ s.accounts`, yielding equality of the two sums.

```lean
theorem plan1_shareOf_eq_zero_of_not_mem (r : Request) (a : AccountId) (h : a ∉ r.recipients) : (shareOf r a : Int) = 0 := by sorry

theorem plan1_ite_mem_cons_split (z : AccountId) (zs : List AccountId) (hz : z ∉ zs) (a : AccountId) (g : AccountId → Int) : (if a ∈ (z :: zs) then g a else 0) = (if a = z then g a else 0) + (if a ∈ zs then g a else 0) := by sorry

theorem plan1_sumOver_shareOf_eq_recipients_ite (r : Request) (hrec : r.recipients.Nodup) (l : List AccountId) (hl : l.Nodup) : sumOver l (fun a => (shareOf r a : Int)) = sumOver r.recipients (fun a => if a ∈ l then (shareOf r a : Int) else 0) := by sorry

theorem plan1_sumOver_recipients_ite_eq_of_subset (r : Request) (l : List AccountId) (hsub : ∀ x ∈ r.recipients, x ∈ l) : sumOver r.recipients (fun a => if a ∈ l then (shareOf r a : Int) else 0) = sumOver r.recipients (fun a => (shareOf r a : Int)) := by sorry

theorem plan1_accounts_shareOf_eq_recipients (s : State) (r : Request) (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup) (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) : sumOver s.accounts (fun a => (shareOf r a : Int)) = sumOver r.recipients (fun a => (shareOf r a : Int)) := by sorry
```