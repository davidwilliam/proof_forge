(1) **Plan:** Conservation follows from the already-proved valid-case bookkeeping. On success, `valid_of_ok_aux` recovers `ValidPayout s r`. For such a valid request, the next state's total is the sum of `expectedBalance s r` over `s.accounts` (the existing `arch1_total_step_eq_sum_expected_proof`), and that sum is exactly `total s` (the existing `arch0_sumOver_accounts_expected`), since the source debit `amount` is cancelled by the recipients' shares summing to `amount`. I isolate these as two `arch2_` rewrites and one combining lemma, then derive `req_conservation` by applying the combining lemma to the validity recovered from success.

(2)
```lean
theorem arch2_total_step_eq_sum_expected (s : State) (r : Request)
    (hV : ValidPayout s r) :
    total (step s r).2 = sumOver s.accounts (expectedBalance s r) := by sorry

theorem arch2_sumOver_accounts_expected_eq_total (s : State) (r : Request)
    (hV : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) = total s := by sorry

theorem arch2_total_step_of_valid (s : State) (r : Request)
    (hV : ValidPayout s r) :
    total (step s r).2 = total s := by sorry

theorem req_conservation   : Conserves step := by
  intro s r hok
  exact arch2_total_step_of_valid s r (valid_of_ok_aux s r hok)
```