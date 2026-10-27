**Proof plan:** Split the sum of `expectedBalance` over the account universe into the original balance sum, a source indicator, a recipient indicator, and a fee-account indicator. Evaluate the source and fee indicators using nodupness and membership, evaluate the recipient indicator as `length * share`, combine `length * share + feeCredit = amount` from the Nat division/mod identity, and close by arithmetic.

```lean
theorem plan2_sum_ite_eq_of_mem {l : List AccountId} (hl : l.Nodup) {x : AccountId} (hx : x ∈ l) (c : Int) : sumOver l (fun a => if a = x then c else 0) = c := by sorry

theorem plan2_sum_expected_split (s : State) (r : Request) : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) + sumOver s.accounts (fun a => if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) + sumOver s.accounts (fun a => if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by sorry

theorem plan2_length_mul_share_add_feeCredit (s : State) (r : Request) (hv : ValidPayout s r) : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (r.amount : Int) := by sorry

theorem plan2_sum_expectedBalance (s : State) (r : Request) (hv : ValidPayout s r) : sumOver s.accounts (expectedBalance s r) = sumOver s.accounts s.balance := by sorry
```