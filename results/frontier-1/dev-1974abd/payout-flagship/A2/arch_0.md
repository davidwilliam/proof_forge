(1) **Plan.** Conservation is a single-step computation, so the proof is organized around computing the post-state total exactly, rather than around an invariant over sequences. Shared facts: `arch0_valid_of_ok` extracts `ValidPayout` from `(step s r).1 = .ok` (the step branches on this predicate). The fair-split bookkeeping is isolated in range lemmas: `arch0_fairShare_int` pushes the cast through `fairShare`, `arch0_sumOver_range_const` and `arch0_sumOver_range_ite_mod` sum the constant and bonus parts, and `arch0_amount_eq_div_add_mod` is the integer form of `Nat.div_add_mod`; together they give `arch0_sum_range_fairShare`, i.e. the shares over all positions sum to `amount`. A reindexing chain (`arch0_indexOf_cons_ne`, `arch0_sumOver_range_succ_head`, `arch0_sumOver_indexOf_range`) converts the sum of `shareOf` over the recipient list into that positional sum, yielding `arch0_sum_recipients_share`. Since shares vanish off the recipient list (`arch0_shareOf_eq_zero_of_not_mem`), a subset-sum lemma (`arch0_sumOver_eq_of_subset`) lifts this to the whole account universe (`arch0_sum_accounts_share`). Finally `arch0_sum_expectedBalance` expands `expectedBalance` over the accounts with the supplied `sumOver_add`/`sumOver_sub`/`sumOver_ite_eq` lemmas: the source deduction contributes exactly `amount` (source ∈ accounts, accounts nodup) and the shares contribute exactly `amount`, so the total is unchanged. `req_conservation` then follows in a few lines from the already-proved `req_effects` (accounts and balances of the successor state) plus `arch0_sum_expectedBalance`.

(2)

```lean
theorem arch0_valid_of_ok (s : State) (r : Request) :
    (step s r).1 = .ok → ValidPayout s r := by sorry

theorem arch0_fairShare_int (amount n i : Nat) :
    (fairShare amount n i : Int)
      = (amount / n : Int) + (if i < amount % n then (1 : Int) else 0) := by sorry

theorem arch0_sumOver_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by sorry

theorem arch0_sumOver_range_ite_mod (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => if i < amount % n then (1 : Int) else 0)
      = ((amount % n : Nat) : Int) := by sorry

theorem arch0_amount_eq_div_add_mod (amount n : Nat) (hn : 0 < n) :
    (amount : Int) = (n : Int) * (amount / n : Int) + ((amount % n : Nat) : Int) := by sorry

theorem arch0_sum_range_fairShare (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by sorry

theorem arch0_indexOf_cons_ne (x a : AccountId) (xs : List AccountId) (h : a ≠ x) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by sorry

theorem arch0_sumOver_range_succ_head (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by sorry

theorem arch0_sumOver_indexOf_range (l : List AccountId) (f : Nat → Int) (hl : l.Nodup) :
    sumOver l (fun a => match indexOf? l a with
                         | some i => f i
                         | none => 0)
      = sumOver (List.range l.length) (fun i => f i) := by sorry

theorem arch0_shareOf_eq_zero_of_not_mem (r : Request) (a : AccountId) (h : a ∉ r.recipients) :
    shareOf r a = 0 := by sorry

theorem arch0_sum_recipients_share (r : Request) (hnd : r.recipients.Nodup)
    (hne : r.recipients ≠ []) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem arch0_sumOver_eq_of_subset (L l : List AccountId) (f : AccountId → Int)
    (hL : L.Nodup) (hl : l.Nodup) (hsub : ∀ x ∈ l, x ∈ L)
    (hzero : ∀ x, x ∉ l → f x = 0) :
    sumOver L f = sumOver l f := by sorry

theorem arch0_sum_accounts_share (s : State) (r : Request) (hs : s.accounts.Nodup)
    (hr : r.recipients.Nodup) (hne : r.recipients ≠ [])
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem arch0_sum_expectedBalance (s : State) (r : Request) (h : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a) = total s := by sorry

theorem req_conservation   : Conserves step := by
  intro s r hOk
  have hValid : ValidPayout s r := arch0_valid_of_ok s r hOk
  have hEff := req_effects s r hOk
  have hSum : total (step s r).2
      = sumOver s.accounts (fun a => expectedBalance s r a) := by
    show sumOver (step s r).2.accounts (step s r).2.balance = _
    rw [hEff.1]
    exact sumOver_congr s.accounts _ _ (fun a _ => hEff.2.2 a)
  rw [hSum, arch0_sum_expectedBalance s r hValid]
```