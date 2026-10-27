(1) Proof plan: From `(step s r).1 = .ok`, recover `ValidPayout s r` as in the existing proofs. Then `step` replaces balances by `expectedBalance s r` and leaves `accounts` unchanged, so `total` becomes a sum of `expectedBalance` over `s.accounts`. Decompose that sum with `sumOver_add`, `sumOver_sub`, `sumOver_ite_eq`, and the recipient-sum lemma below; the source debit is exactly `amount`, the recipient credits total `length * recipientShare`, and the fee-account credit is `feeCredit`. The arithmetic lemma shows the latter two Nat credits sum to `amount`, cancelling the debit.

(2)
```lean
theorem plan0_fee_le (bps amount : Nat) (hbps : bps ≤ 10000) : feeOf bps amount ≤ amount := by sorry

theorem plan0_fee_add_net (bps amount : Nat) (hbps : bps ≤ 10000) : feeOf bps amount + netOf bps amount = amount := by sorry

theorem plan0_mul_share_add_feeCredit (bps amount n : Nat) (hbps : bps ≤ 10000) (hn : n ≠ 0) : n * recipientShare bps amount n + feeCredit bps amount n = amount := by sorry

theorem plan0_indicator_recipients_cons (x : AccountId) (recipients : List AccountId) (a : AccountId) (c : Int) (hx : x ∉ recipients) : (if a ∈ x :: recipients then c else 0) = (if a = x then c else 0) + (if a ∈ recipients then c else 0) := by sorry

theorem plan0_sum_recipients (accounts recipients : List AccountId) (c : Int) (hacc : accounts.Nodup) (hrec : recipients.Nodup) (hsub : ∀ y ∈ recipients, y ∈ accounts) : sumOver accounts (fun a => if a ∈ recipients then c else 0) = (recipients.length : Int) * c := by sorry

theorem plan0_sum_expectedBalance (s : State) (r : Request) (hv : ValidPayout s r) : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance := by sorry
```