**Proof plan.** In the successful case, obtain `ValidPayout` from `step = .ok`, so the accounts list is nodup, source and fee account belong to it, recipients are nodup and contained in it, `feeBps ≤ 10000`, and recipients are nonempty. Rewrite `total` of the updated state as `sumOver s.accounts (expectedBalance s r)`, split that sum into the original balances, the source debit, the recipient credits, and the fee credit. The two single-account indicators are evaluated by `sumOver_ite_eq`; the recipient indicator counts each recipient once. Finally, the recipient shares plus `feeCredit` reconstruct `amount` via `n * (net / n) + net % n = net` and `fee + net = amount`, cancelling the source debit.

```lean
theorem plan0_indicator_mem_cons_decomp (b : Nat) (sub : List Nat) (c : Int)
    (hb : b ∉ sub) (a : Nat) :
    (if a ∈ b :: sub then c else 0)
      = (if a = b then c else 0) + (if a ∈ sub then c else 0) := by sorry

theorem plan0_sumOver_mem_indicator (l sub : List Nat) (c : Int)
    (hl : l.Nodup) (hsub : sub.Nodup) (hcover : ∀ x ∈ sub, x ∈ l) :
    sumOver l (fun a => if a ∈ sub then c else 0)
      = (sub.length : Int) * c := by sorry

theorem plan0_split_eq_amount (bps amount n : Nat)
    (hbps : bps ≤ 10000) (hn : 0 < n) :
    n * recipientShare bps amount n + feeCredit bps amount n = amount := by sorry

theorem plan0_sumOver_expectedBalance (s : State) (r : Request)
    (hnd : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts)
    (hfee : s.feeAccount ∈ s.accounts) (hrnd : r.recipients.Nodup)
    (hrec : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (expectedBalance s r)
      = total s - (r.amount : Int)
        + (r.recipients.length : Int)
            * (recipientShare s.feeBps r.amount r.recipients.length : Int)
        + (feeCredit s.feeBps r.amount r.recipients.length : Int) := by sorry
```