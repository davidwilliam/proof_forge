(1) Plan: Conservation is a single-step calculation, so no sequence invariant is needed. If `step s r` succeeds, the already-proved `arch0_valid_of_ok` gives `ValidPayout s r`. The already-proved effects characterize the successor state: its account list is `s.accounts` and every balance is `expectedBalance s r a`. Hence the successor total is the sum of expected balances over `s.accounts`. That sum equals the original total because the debit removes exactly `r.amount` from the source while the fair shares credit exactly `r.amount` in total; this is packaged by `arch0_sum_expected_eq` / `arch1_sum_expected_eq`. I isolate the total-rewriting step and the expected-sum step as two small `arch2_` lemmas, then `req_conservation` is just their composition.

```lean
theorem arch2_total_step_eq_sum_expected (s : State) (r : Request)
    (hok : (step s r).1 = .ok) :
    total (step s r).2 = sumOver s.accounts (fun a => expectedBalance s r a) := by sorry

theorem arch2_sum_expected_eq_total (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = total s := by sorry

theorem req_conservation   : Conserves step := by
  intro s r hok
  have hv : ValidPayout s r := arch0_valid_of_ok s r hok
  rw [arch2_total_step_eq_sum_expected s r hok, arch2_sum_expected_eq_total s r hv]
```