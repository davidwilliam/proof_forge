(1) **Plan.** All three requirements are single-call properties, so they follow from one computing lemma for `step`: success is equivalent to `ValidPayout`, and on validity `step` returns `.ok` with balances replaced by `expectedBalance`, `applied` extended by `r.txId`, and `accounts`/`auth` untouched. `req_effects` is then a direct read-off of that state equality. `req_nonnegative` is already exactly the banked `req_nonnegative_aux3`. For `req_conservation`, split the money calculation into small pieces: the `fairShare` values over `List.range n` sum to `amount` (for `0 < n`); reindexing along a duplicate-free recipient list turns the recipient sum into that range sum; because a valid request has recipients inside the duplicate-free account universe and `shareOf` is `0` outside the recipients, the share sum over all accounts is also `amount`; symmetrically the source indicator over the accounts sums to `amount` (by the provided `sumOver_ite_eq`). Hence in `total (step s r).2` the debit and the credited shares cancel, giving `total s`.

(2)

```lean
theorem arch0_valid_of_ok (s : State) (r : Request)
    (h : (step s r).1 = .ok) : ValidPayout s r := by sorry

theorem arch0_step_eq_of_valid (s : State) (r : Request) (hv : ValidPayout s r) :
    step s r = (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied }) := by sorry

theorem arch0_sum_fairShare_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by
  sorry

theorem arch0_sum_shareOf_recipients_range (r : Request) (hn : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by sorry

theorem arch0_sum_shareOf_recipients_amount (r : Request)
    (hn : r.recipients.Nodup) (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem arch0_sum_shareOf_accounts (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem arch0_sum_source_indicator (s : State) (r : Request)
    (hnd : s.accounts.Nodup) (hmem : r.source ∈ s.accounts) :
    sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by sorry

theorem arch0_total_eq_of_valid (s : State) (r : Request) (hv : ValidPayout s r) :
    total (step s r).2 = total s := by sorry

theorem req_effects : Effects step := by
  intro s r h
  have hv := arch0_valid_of_ok s r h
  have hstep := arch0_step_eq_of_valid s r hv
  have h2 : (step s r).2 = { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied } := by rw [hstep]
  refine ⟨?_, ?_, ?_⟩
  · simp [h2]
  · simp [h2]
  · intro a
    simp [h2]

theorem req_nonnegative : NonNegative step := by
  exact req_nonnegative_aux3

theorem req_conservation : Conserves step := by
  intro s r h
  have hv := arch0_valid_of_ok s r h
  exact arch0_total_eq_of_valid s r hv
```