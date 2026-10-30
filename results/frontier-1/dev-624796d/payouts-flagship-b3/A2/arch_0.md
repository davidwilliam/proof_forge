(1) **Plan.** Both remaining requirements are single-call consequences of facts already banked. For idempotency, a successful call must have been valid (`valid_of_ok_aux`); its applied list is then `r.txId :: s.applied` (`req_idempotency_aux_applied`), giving the membership characterization, and the resubmission is invalid because `r.txId` is now applied (`idem_notvalid_test`), so `req_invalid_noop` makes the replay a rejected no-op. For conservation, on success `req_effects` fixes all balances to `expectedBalance`; summing over the (unchanged) account universe, the source debit contributes exactly `amount` (source is in the duplicate-free universe, via `sumOver_ite_eq`) and the shares contribute exactly `amount`: the share at position `i` is `fairShare amount n i`, those shares summed over `List.range n` total `amount` since `n * (amount / n) + amount % n = amount`, the recipients' shares transfer from `r.recipients` to `s.accounts` because recipients are a duplicate-free subset and non-recipients receive `0`. The debit and shares cancel, leaving `total` unchanged.

(2)

```lean
theorem arch0_idem_applied_mem (s : State) (r : Request) (hok : (step s r).1 = .ok)
    (x : TxId) :
    x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by sorry

theorem arch0_idem_replay (s : State) (r : Request) (hok : (step s r).1 = .ok) :
    step (step s r).2 r = (.rejected, (step s r).2) := by sorry

theorem arch0_shareOf_getElem (r : Request) (hnd : r.recipients.Nodup)
    (i : Nat) (hi : i < r.recipients.length) :
    shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by sorry

theorem arch0_shareOf_eq_zero_of_not_mem (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) :
    shareOf r a = 0 := by sorry

theorem arch0_sumOver_eq_range {α : Type} (l : List α) (f : α → Int) (g : Nat → Int)
    (h : ∀ (i : Nat) (hi : i < l.length), f l[i] = g i) :
    sumOver l f = sumOver (List.range l.length) g := by sorry

theorem arch0_fairShare_range_sum (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by sorry

theorem arch0_sumOver_recipients_share (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem arch0_sumOver_subset_eq (big small : List AccountId) (f : AccountId → Int)
    (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hzero : ∀ x, x ∈ big → x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry

theorem arch0_sumOver_accounts_share (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem arch0_sumOver_accounts_expected (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (expectedBalance s r) = total s := by sorry

theorem req_idempotency : Idempotent step := by
  unfold Idempotent
  intro s r hok
  exact ⟨arch0_idem_applied_mem s r hok, arch0_idem_replay s r hok⟩

theorem req_conservation : Conserves step := by
  unfold Conserves
  intro s r hok
  have hV : ValidPayout s r := valid_of_ok_aux s r hok
  have hEff := req_effects s r hok
  have hsum : total (step s r).2 = sumOver s.accounts (expectedBalance s r) := by
    unfold total
    rw [hEff.1]
    exact sumOver_congr s.accounts _ _ (fun a _ => hEff.2.2 a)
  rw [hsum, arch0_sumOver_accounts_expected s r hV]
```