If a payout succeeds it is valid, so accounts are unchanged and balances become `expectedBalance`. Expand `total` as `sumOver` over the accounts: the source-indicator sums to `amount` (source in a duplicate-free account list), while all `shareOf` contributions over the accounts reduce to those over the recipients. Recipient shares are the `fairShare` values indexed by position; summed over `List.range length` they total `amount`. Hence the debit and credits cancel.

```lean
theorem plan0_sum_fairShare_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by sorry

theorem plan0_sumOver_indexOf_range {l : List AccountId} (hl : l.Nodup) (f : Nat → Int) :
    sumOver l (fun a => match indexOf? l a with | some i => f i | none => 0) =
      sumOver (List.range l.length) f := by sorry

theorem plan0_sumOver_shareOf_recipients (r : Request) (hnd : r.recipients.Nodup)
    (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan0_sumOver_super_of_zero_outside (big small : List AccountId) (f : AccountId → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big) (hzero : ∀ a, a ∉ small → f a = 0) :
    sumOver big f = sumOver small f := by sorry

theorem plan0_sumOver_accounts_shareOf (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup) (hne : r.recipients ≠ [])
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan0_sumOver_expectedBalance (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts)
    (hshare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int)) :
    sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance := by sorry
```