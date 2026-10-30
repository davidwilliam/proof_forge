(1) **Plan.** The shared reduction is: an `.ok` outcome must come from a valid payout (`arch0_valid_of_ok`), so the already-proved `req_effects` determines the next accounts and every balance as `expectedBalance`. For conservation, `arch0_sum_expected_eq` shows summing `expectedBalance` over the account universe returns the original total; it is decomposed into a debit sum (the source is charged exactly `amount`, via the nodup indicator sum), a fair-share range sum (`n * (amount/n) + amount%n = amount`), transfer of that recipient sum to the whole account universe (shares vanish off the recipient list, which is a duplicate-free sublist of the duplicate-free accounts), and recombination with `sumOver_add`/`sumOver_sub`. For nonnegativity, `arch0_expected_nonneg` checks `expectedBalance` pointwise: the source is not a recipient so it receives no share and is charged at most its balance, while every other account keeps its nonnegative balance plus a nonnegative cast share. Invalid payouts are handled by `req_invalid_noop`, valid ones by `req_valid_succeeds` plus `req_effects`.

(2)

```lean
theorem arch0_valid_of_ok (s : State) (r : Request) :
    (step s r).1 = .ok → ValidPayout s r := by sorry

theorem arch0_share_eq_zero_of_not_mem (r : Request) (a : AccountId) :
    a ∉ r.recipients → shareOf r a = 0 := by sorry

theorem arch0_expected_nonneg (s : State) (r : Request) (hv : ValidPayout s r)
    (hnon : ∀ a ∈ s.accounts, 0 ≤ s.balance a) :
    ∀ a ∈ s.accounts, 0 ≤ expectedBalance s r a := by sorry

theorem arch0_sum_debit_eq (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by sorry

theorem arch0_sum_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by sorry

theorem arch0_sum_range_indicator (n m : Nat) (hm : m ≤ n) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0)
      = (m : Int) := by sorry

theorem arch0_sum_fair_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (amount : Int) := by sorry

theorem arch0_sum_share_recipients (r : Request) (hnd : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by sorry

theorem arch0_sum_credit_recipients (r : Request) (hv : ValidPayout s r) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = (r.amount : Int) := by sorry

theorem arch0_sum_eq_of_subset_zero (l1 l2 : List AccountId) (f : AccountId → Int)
    (h1 : l1.Nodup) (h2 : l2.Nodup)
    (hsub : ∀ x ∈ l2, x ∈ l1)
    (hzero : ∀ x, x ∉ l2 → f x = 0) :
    sumOver l1 f = sumOver l2 f := by sorry

theorem arch0_sum_credit_eq (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int))
      = (r.amount : Int) := by sorry

theorem arch0_sum_expected_eq (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance := by sorry

theorem req_nonnegative : NonNegative step := by
  intro s r hnon a ha
  by_cases hv : ValidPayout s r
  · have hok : (step s r).1 = .ok := req_valid_succeeds s r hv
    have heff := req_effects s r hok
    have ha' : a ∈ s.accounts := by
      rw [← heff.1]
      exact ha
    have hb : (step s r).2.balance a = expectedBalance s r a := heff.2.2 a
    rw [hb]
    exact arch0_expected_nonneg s r hv hnon a ha'
  · have hstep := req_invalid_noop s r hv
    rw [hstep] at ha
    rw [hstep]
    exact hnon a ha

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv := arch0_valid_of_ok s r hok
  have heff := req_effects s r hok
  have hcong : sumOver s.accounts (step s r).2.balance
      = sumOver s.accounts (fun a => expectedBalance s r a) :=
    sumOver_congr s.accounts (step s r).2.balance
      (fun a => expectedBalance s r a) (fun a _ => heff.2.2 a)
  unfold total
  rw [heff.1]
  rw [hcong]
  exact arch0_sum_expected_eq s r hv
```