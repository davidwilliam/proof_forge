Induct on `recipients`. The empty case is a zero sum. For a head `x :: recipients`, nodup gives `x ∉ recipients`, the subset hypothesis gives `x ∈ accounts` and the subset property for the tail, and the membership indicator for the cons splits into a singleton indicator plus the tail indicator. The singleton contributes exactly `c`, while the tail contributes `recipients.length * c` by the induction hypothesis.

```lean
theorem plan1_sumOver_zero (l : List AccountId) : sumOver l (fun _ : AccountId => (0 : Int)) = 0 := by sorry

theorem plan1_indicator_cons_add (x : AccountId) (recipients : List AccountId) (a : AccountId) (c : Int) (hx : x ∉ recipients) : (if a ∈ (x :: recipients) then c else 0) = (if a = x then c else 0) + (if a ∈ recipients then c else 0) := by sorry

theorem plan1_sumOver_indicator_single (accounts : List AccountId) (hacc : accounts.Nodup) (x : AccountId) (c : Int) : sumOver accounts (fun a => if a = x then c else 0) = if x ∈ accounts then c else 0 := by sorry

theorem plan1_sumOver_indicator_cons (accounts recipients : List AccountId) (x : AccountId) (c : Int) (hacc : accounts.Nodup) (hx : x ∉ recipients) : sumOver accounts (fun a => if a ∈ (x :: recipients) then c else 0) = (if x ∈ accounts then c else 0) + sumOver accounts (fun a => if a ∈ recipients then c else 0) := by sorry

theorem plan1_sum_recipients_cons (accounts recipients : List AccountId) (x : AccountId) (c : Int) (hacc : accounts.Nodup) (hxnot : x ∉ recipients) (hxmem : x ∈ accounts) (ih : sumOver accounts (fun a => if a ∈ recipients then c else 0) = (recipients.length : Int) * c) : sumOver accounts (fun a => if a ∈ (x :: recipients) then c else 0) = ((x :: recipients).length : Int) * c := by sorry
```