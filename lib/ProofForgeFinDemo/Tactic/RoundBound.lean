import ProofForgeFin
/-!
# Tactic tests: `fin_simp`, `div_norm` and `round_bound`

The first section states the rounding facts that task proofs keep re-deriving and closes each
with one call. The second copies goals from the error messages of the failed attempts on
`rw-compound-comp` (`results/compound-1/*/events.jsonl`), with the hypotheses they had, and
gives the proof without the automation next to each. The third checks that `round_bound`
fails, and leaves the goal unchanged, when the goal does not follow from the facts it knows.

`doubleScale` and `creditFor` are copied without change from
`realworld/tasks/rw-compound-comp/spec/CompRewards/Spec.lean`; the share-value goals restate
the arithmetic of `exec_value` in `realworld/tasks/rw-hundred-vault/reference/SolutionA.lean`
(`mintTo`, `burnFrom` and `sharesUp` expanded).
-/

namespace ProofForgeFinDemo.Tactic.RoundBound

open ProofForgeFin

/-- `doubleScale` (ExponentialNoError.sol): the scale of reward index mantissas. -/
def doubleScale : Nat := 10 ^ 36

/-- COMP credited for `units` held from index `start` to index `index`:
`mul_(units, Double(index - start))`, rounded down. -/
def creditFor (units start index : Nat) : Nat := units * (index - start) / doubleScale

/-- An 18-decimal fixed-point scale. -/
def WAD : Nat := 10 ^ 18

/-! ## Rounding facts, one call each -/

example (x d : Nat) : x / d * d ≤ x := by round_bound
example (x d : Nat) (h : 0 < d) : x < x / d * d + d := by round_bound
example (x d : Nat) (h : 0 < d) : x ≤ ceilDiv x d * d := by round_bound
example (x d : Nat) (h : 0 < d) : ceilDiv x d * d < x + d := by round_bound
example (x d : Nat) : x / d ≤ ceilDiv x d := by round_bound
example (one a b : Nat) : mulDown one a b ≤ mulUp one a b := by round_bound
example (one a b : Nat) : mulUp one a b ≤ mulDown one a b + 1 := by round_bound
example (one a b : Nat) (h : 0 < one) : a * b ≤ mulUp one a b * one := by round_bound
example (one a b : Nat) : divDown one (mulDown one a b) b ≤ a := by round_bound
example (one a b : Nat) (h : 0 < one) (hb : 0 < b) : a ≤ divUp one (mulUp one a b) b := by round_bound
example (t a s : Nat) (h : t ≤ s) : t * a / s ≤ a := by round_bound
example (a b c : Nat) : a / c + b / c ≤ (a + b) / c := by round_bound
example (a b c : Nat) (hc : 0 < c) : (a * c + b) / c = a + b / c := by round_bound
example (x d q : Nat) (hd : 0 < d) (h : x < q * d) : x / d < q := by round_bound
example (x d q : Nat) (hd : 0 < d) (h : q * d ≤ x) : q ≤ x / d := by round_bound
example (a a' d : Nat) (h : a ≤ a') : a / d ≤ a' / d := by round_bound
example (x y : Nat) (h : x ≤ y) : ceilDiv x 1000 ≤ ceilDiv y 1000 := by round_bound
example (x y : Nat) : x / 3 + y / 3 ≤ (x + y) / 3 := by round_bound
example (a : Nat) : mulDown (10 ^ 18) a (10 ^ 18) = a := by round_bound
example (x : Nat) : x * WAD / WAD = x := by round_bound with [WAD]
example (u s i : Nat) : creditFor u s i * doubleScale ≤ u * (i - s) := by
  round_bound with [creditFor, doubleScale]
example (p : Shares.Pool) (t : Nat) (h : t ≤ p.supply) : Shares.previewRedeem p t ≤ p.assets := by
  round_bound
example (p : Shares.Pool) (x : Nat) : Shares.previewDeposit p x * p.assets ≤ x * p.supply := by
  round_bound

example (a x : Nat) (h : x ≤ mulDown 1000 a 1) : x ≤ a := by round_bound
example (x d : Nat) : x ≥ x / d * d := by round_bound

/-- `fin_simp` and `div_norm` leave a goal that `omega` closes. -/
example (a : Nat) : mulDown (10 ^ 18) a 1 * 10 ^ 18 ≤ a := by
  div_norm
  omega

example (a b : Nat) (h : 0 < b) : mulDiv (a * b) 1 b = a := by
  fin_simp [h]

/-! ## Share value, the arithmetic of `exec_value` in `rw-hundred-vault`

A deposit rounded down, a redemption rounded down and a withdrawal rounded up keep
`assets / supply` from falling, cross-multiplied. The reference proves each with a calc block
of about eight steps over its own floor and ceiling lemmas. -/

example (A S x : Nat) : A * (S + x * S / A) ≤ (A + x) * S := by round_bound

example (A S t : Nat) : A * (S - t) ≤ (A - t * A / S) * S := by round_bound

example (A S x : Nat) (hA : 0 < A) : A * (S - (x * S + A - 1) / A) ≤ (A - x) * S := by round_bound

/-! ## Goals copied from failed attempts on `rw-compound-comp` -/

/-- `results/compound-1/implement-1/events.jsonl`, line 267: the model reached this goal after a case split
on `t = 0` and a `calc` whose steps it could not close. -/
example (K t s : Nat) : K / t * s ≤ K * s / t := by round_bound

example (K t s : Nat) : K / t * s ≤ K * s / t := by
  by_cases ht : t = 0
  · simp [ht]
  · apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero ht)).2
    have h1 : K / t * t ≤ K := Nat.div_mul_le_self K t
    calc K / t * s * t = K / t * t * s := Nat.mul_right_comm _ _ _
      _ ≤ K * s := Nat.mul_le_mul_right s h1

/-- The same line, the two unsolved steps of the `calc`. -/
example (K t s : Nat) (_ht : ¬t = 0) (_h1 : K / t * t ≤ K) : K / t * s * t = K / t * t * s := by
  round_bound

example (K t s : Nat) (_ht : ¬t = 0) (_h1 : K / t * t ≤ K) : K / t * t * s ≤ K * s := by
  round_bound

example (K t s : Nat) (_ht : ¬t = 0) (h1 : K / t * t ≤ K) : K / t * t * s ≤ K * s :=
  Nat.mul_le_mul_right s h1

/-- `results/compound-1/repair-A2-1/events.jsonl`, line 233: the sum of two rounded-down parts (an
unknown tactic was tried first). -/
example (x y K : Nat) : x / K + y / K ≤ (x + y) / K := by round_bound

example (x y K : Nat) : x / K + y / K ≤ (x + y) / K := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  · apply (Nat.le_div_iff_mul_le hK).2
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self x K) (Nat.div_mul_le_self y K)

/-- The same line: the lemma the model stated next, with a subtraction. -/
example (S b K : Nat) (h : b ≤ S) : (S - b) / K + b / K ≤ S / K := by round_bound

example (S b K : Nat) (h : b ≤ S) : (S - b) / K + b / K ≤ S / K := by
  have := div_add_div_le (S - b) b K
  rwa [Nat.sub_add_cancel h] at this

/-- The same line: the type mismatch between `tot * (em * K / tot)` and `em * K / tot * tot`. -/
example (tot em K : Nat) : tot * (em * K / tot) ≤ em * K := by round_bound

example (tot em K : Nat) : tot * (em * K / tot) ≤ em * K := Nat.mul_div_le (em * K) tot

/-- `results/compound-1/implement-1/events.jsonl`, line 204, in the sum over accounts:
distributing a product over a sum. -/
example (hd : Nat) (tl : List Nat) (c : Nat) : hd * c + tl.sum * c = (hd + tl.sum) * c := by
  round_bound

example (hd : Nat) (tl : List Nat) (c : Nat) : hd * c + tl.sum * c = (hd + tl.sum) * c :=
  (Nat.add_mul hd tl.sum c).symm

/-! ## Clean failure -/

/-- A goal that needs a fact `round_bound` does not have: it fails with a message and the goal
is left as it was, for the next tactic. -/
example (a b : Nat) (h : a = b) : a * a = b * b := by
  fail_if_success round_bound
  subst h
  rfl

/-- The missing fact, given as an argument. -/
example (x d q : Nat) (h : x < q * d) : x / d < q := by
  fail_if_success round_bound
  round_bound [Nat.pos_of_ne_zero (fun hd : d = 0 => by subst hd; simp at h)]

end ProofForgeFinDemo.Tactic.RoundBound
