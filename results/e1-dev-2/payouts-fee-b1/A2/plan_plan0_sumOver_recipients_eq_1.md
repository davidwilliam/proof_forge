Short proof plan: Prove the target by induction on `recipients`. The empty case is a sum of zeros. For `b :: t`, use `b ∉ t` to split the indicator for membership in `b :: t` into a singleton indicator for `b` plus the indicator for `t`; sum the singleton over the duplicate-free `accounts` using `b ∈ accounts`, apply the induction hypothesis to `t`, and finish with the length calculation for a cons list.

```lean
theorem plan1_sumOver_zero (l : List AccountId) :
    sumOver l (fun _ => (0 : Int)) = 0 := by
  sorry

theorem plan1_indicator_cons (b : AccountId) (t : List AccountId) (c : Int)
    (hb : b ∉ t) (a : AccountId) :
    (if a ∈ b :: t then c else (0 : Int))
      = (if a = b then c else 0) + (if a ∈ t then c else 0) := by
  sorry

theorem plan1_sumOver_single (accounts : List AccountId) (b : AccountId) (c : Int)
    (hnd : accounts.Nodup) (hb : b ∈ accounts) :
    sumOver accounts (fun a => if a = b then c else (0 : Int)) = c := by
  sorry

theorem plan1_sumOver_mem_cons (accounts recipients : List AccountId)
    (b : AccountId) (c : Int)
    (hnd : accounts.Nodup) (hb_notin : b ∉ recipients) (hb_mem : b ∈ accounts) :
    sumOver accounts (fun a => if a ∈ b :: recipients then c else (0 : Int))
      = c + sumOver accounts (fun a => if a ∈ recipients then c else 0) := by
  sorry

theorem plan1_cons_length_mul (b : AccountId) (t : List AccountId) (c : Int) :
    ((b :: t).length : Int) * c = c + (t.length : Int) * c := by
  sorry
```