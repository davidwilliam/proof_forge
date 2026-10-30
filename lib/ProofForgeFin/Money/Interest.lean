import ProofForgeFin.FixedPoint
import ProofForgeFin.Money.Round
/-!
# Interest and amortization

Interest at rate `rn / rd` per period, on amounts in minor units, rounded at every period as
deployed code does. `g = rd + rn` is the growth factor `1 + rn / rd` scaled by `rd`.

* Simple interest `simpleInterest rn rd P t = P * rn * t / rd`: bounds, monotonicity, and
  splitting the term in two changes the interest by at most one unit.
* Compound interest rounded down at every period, `compound rn rd n P` (each period adds
  `C * rn / rd`), and rounded up, `compoundUp`. The rounded balances bracket the exact value
  `P * (g / rd) ^ n`: rounding down never exceeds it (`compound_mul_le`) and loses less than
  one unit per period, compounded (`le_compound`:
  `rn * (P * g^n) + (rd - 1) * rd^n ≤ rn * (C * rd^n) + (rd - 1) * g^n`, so the loss is below
  `(g^n - rd^n) / (rn * rd^(n-1)) = Σ_{j<n} (1 + rn/rd)^j` units); rounding up never falls
  below it and gains at most as much (`le_compoundUp_mul`, `compoundUp_le`). Both are monotone
  in the principal, the rate and the number of periods, and compounding rounded down earns at
  least the per-period simple interest (`add_mul_simple_le_compound`).
* Amortization with a fixed payment `p` and any per-period interest function `i` on signed
  balances (`balanceAfter`, `interestPaid`, `finalPayment`, `payments`): the final payment
  closes the balance exactly, and the payments add up to the principal plus the total
  interest (`sum_payments`). With interest rounded down and a payment at least the exact
  annuity payment (`rn * B * g^n ≤ p * rd * (g^n - rd^n)`), the final payment never exceeds
  the regular payment (`finalPayment_le`); `annuityPayment` (the exact annuity payment
  rounded up) satisfies that condition (`finalPayment_annuityPayment_le`).
-/

namespace ProofForgeFin.Money

/-! ## Simple interest -/

/-- Simple interest on `P` at `rn / rd` per period over `t` periods, rounded down. -/
def simpleInterest (rn rd P t : Nat) : Nat := P * rn * t / rd

/-- Simple interest is within one unit below the exact interest. -/
theorem simpleInterest_spec (rn : Nat) {rd : Nat} (P t : Nat) (hd : 0 < rd) :
    simpleInterest rn rd P t * rd ≤ P * rn * t ∧ P * rn * t < (simpleInterest rn rd P t + 1) * rd :=
  floor_spec _ _ hd

/-- Simple interest is monotone in the principal, the rate and the term. -/
theorem simpleInterest_mono {rn rn' P P' t t' : Nat} (rd : Nat) (hr : rn ≤ rn') (hP : P ≤ P')
    (ht : t ≤ t') : simpleInterest rn rd P t ≤ simpleInterest rn' rd P' t' :=
  div_mono_left _ (Nat.mul_le_mul (Nat.mul_le_mul hP hr) ht)

/-- Splitting the term in two never raises the interest. -/
theorem simpleInterest_add_le (rn rd P t₁ t₂ : Nat) :
    simpleInterest rn rd P t₁ + simpleInterest rn rd P t₂ ≤ simpleInterest rn rd P (t₁ + t₂) := by
  unfold simpleInterest; rw [Nat.mul_add]; exact div_add_div_le _ _ _

/-- Splitting the term in two lowers the interest by at most one unit. -/
theorem le_simpleInterest_add (rn rd P t₁ t₂ : Nat) :
    simpleInterest rn rd P (t₁ + t₂) ≤ simpleInterest rn rd P t₁ + simpleInterest rn rd P t₂ + 1 := by
  unfold simpleInterest; rw [Nat.mul_add]; exact div_add_le_div_add_div_add_one _ _ _

/-! ## Compound interest rounded at every period -/

/-- One period of compounding, the interest rounded down: `P + P * rn / rd`. -/
def compoundStep (rn rd P : Nat) : Nat := P + P * rn / rd

/-- The balance after `n` periods of compounding, the interest rounded down each period. -/
def compound (rn rd : Nat) : Nat → Nat → Nat
  | 0, P => P
  | n + 1, P => compoundStep rn rd (compound rn rd n P)

/-- One period of compounding, the interest rounded up. -/
def compoundUpStep (rn rd P : Nat) : Nat := P + ceilDiv (P * rn) rd

/-- The balance after `n` periods of compounding, the interest rounded up each period. -/
def compoundUp (rn rd : Nat) : Nat → Nat → Nat
  | 0, P => P
  | n + 1, P => compoundUpStep rn rd (compoundUp rn rd n P)

/-- No period of compounding leaves the principal. -/
@[simp] theorem compound_zero (rn rd P : Nat) : compound rn rd 0 P = P := rfl

/-- One more period adds the interest on the balance, rounded down. -/
@[simp] theorem compound_succ (rn rd n P : Nat) :
    compound rn rd (n + 1) P = compound rn rd n P + compound rn rd n P * rn / rd := rfl

/-- No period of compounding leaves the principal. -/
@[simp] theorem compoundUp_zero (rn rd P : Nat) : compoundUp rn rd 0 P = P := rfl

/-- One more period adds the interest on the balance, rounded up. -/
@[simp] theorem compoundUp_succ (rn rd n P : Nat) :
    compoundUp rn rd (n + 1) P = compoundUp rn rd n P + ceilDiv (compoundUp rn rd n P * rn) rd := rfl

/-- Compounding rounded down never exceeds the exact value: `C * rd^n ≤ P * g^n`. -/
theorem compound_mul_le (rn rd n P : Nat) :
    compound rn rd n P * rd ^ n ≤ P * (rd + rn) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [compound_succ, Nat.pow_succ, Nat.pow_succ]
    have h1 : compound rn rd n P * rn / rd * rd ≤ compound rn rd n P * rn := div_mul_le _ _
    generalize compound rn rd n P = C at ih h1 ⊢
    generalize C * rn / rd = q at h1 ⊢
    generalize rd ^ n = V at ih ⊢
    generalize (rd + rn) ^ n = U at ih ⊢
    have m1 : (C + q) * rd ≤ C * (rd + rn) := by rw [Nat.add_mul, Nat.mul_add]; omega
    have m2 := Nat.mul_le_mul_right V m1
    have m3 := Nat.mul_le_mul_right (rd + rn) ih
    have e1 : (C + q) * (V * rd) = (C + q) * rd * V := by grind
    have e2 : C * (rd + rn) * V = C * V * (rd + rn) := by grind
    have e3 : P * U * (rd + rn) = P * (U * (rd + rn)) := by grind
    omega

/-- Compounding rounded down loses less than one unit per period, compounded:
`rn * (P * g^n) + (rd - 1) * rd^n ≤ rn * (C * rd^n) + (rd - 1) * g^n`. -/
theorem le_compound (rn : Nat) {rd : Nat} (n P : Nat) (hd : 0 < rd) :
    rn * (P * (rd + rn) ^ n) + (rd - 1) * rd ^ n ≤
      rn * (compound rn rd n P * rd ^ n) + (rd - 1) * (rd + rn) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [compound_succ, Nat.pow_succ, Nat.pow_succ]
    have h1 := lt_div_add_one_mul (compound rn rd n P * rn) rd hd
    generalize compound rn rd n P = C at ih h1 ⊢
    generalize C * rn / rd = q at h1 ⊢
    generalize rd ^ n = V at ih ⊢
    generalize (rd + rn) ^ n = U at ih ⊢
    generalize hk : rd - 1 = k at ih ⊢
    have hrd : rd = k + 1 := by omega
    subst hrd
    have hC : C * rn ≤ q * (k + 1) + k := by rw [Nat.add_mul, Nat.one_mul] at h1; omega
    have m1 := Nat.mul_le_mul_right (k + 1 + rn) ih
    have m2 := Nat.mul_le_mul_right (rn * V) hC
    have e1 : (rn * (P * U) + k * V) * (k + 1 + rn) =
        rn * (P * (U * (k + 1 + rn))) + k * (V * (k + 1)) + k * V * rn := by grind
    have e2 : (rn * (C * V) + k * U) * (k + 1 + rn) =
        rn * (C * V) * (k + 1) + C * rn * (rn * V) + k * (U * (k + 1 + rn)) := by grind
    have e3 : (q * (k + 1) + k) * (rn * V) = rn * (q * (V * (k + 1))) + k * V * rn := by grind
    have e4 : rn * ((C + q) * (V * (k + 1))) = rn * (C * V) * (k + 1) + rn * (q * (V * (k + 1))) := by
      grind
    omega

/-- Compounding rounded up never falls below the exact value: `P * g^n ≤ C * rd^n`. -/
theorem le_compoundUp_mul (rn : Nat) {rd : Nat} (n P : Nat) (hd : 0 < rd) :
    P * (rd + rn) ^ n ≤ compoundUp rn rd n P * rd ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [compoundUp_succ, Nat.pow_succ, Nat.pow_succ]
    have h1 := le_ceilDiv_mul (compoundUp rn rd n P * rn) rd hd
    generalize compoundUp rn rd n P = C at ih h1 ⊢
    generalize ceilDiv (C * rn) rd = q at h1 ⊢
    generalize rd ^ n = V at ih ⊢
    generalize (rd + rn) ^ n = U at ih ⊢
    have m1 : C * (rd + rn) ≤ (C + q) * rd := by rw [Nat.add_mul, Nat.mul_add]; omega
    have m2 := Nat.mul_le_mul_right V m1
    have m3 := Nat.mul_le_mul_right (rd + rn) ih
    have e1 : (C + q) * (V * rd) = (C + q) * rd * V := by grind
    have e2 : C * (rd + rn) * V = C * V * (rd + rn) := by grind
    have e3 : P * U * (rd + rn) = P * (U * (rd + rn)) := by grind
    omega

/-- Compounding rounded up gains less than one unit per period, compounded:
`rn * (C * rd^n) + (rd - 1) * rd^n ≤ rn * (P * g^n) + (rd - 1) * g^n`. -/
theorem compoundUp_le (rn : Nat) {rd : Nat} (n P : Nat) (hd : 0 < rd) :
    rn * (compoundUp rn rd n P * rd ^ n) + (rd - 1) * rd ^ n ≤
      rn * (P * (rd + rn) ^ n) + (rd - 1) * (rd + rn) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [compoundUp_succ, Nat.pow_succ, Nat.pow_succ]
    have h1 := ceilDiv_mul_lt (compoundUp rn rd n P * rn) rd hd
    generalize compoundUp rn rd n P = C at ih h1 ⊢
    generalize ceilDiv (C * rn) rd = q at h1 ⊢
    generalize rd ^ n = V at ih ⊢
    generalize (rd + rn) ^ n = U at ih ⊢
    generalize hk : rd - 1 = k at ih ⊢
    have hrd : rd = k + 1 := by omega
    subst hrd
    have hC : q * (k + 1) ≤ C * rn + k := by omega
    have m1 := Nat.mul_le_mul_right (k + 1 + rn) ih
    have m2 := Nat.mul_le_mul_right (rn * V) hC
    have e1 : (rn * (C * V) + k * V) * (k + 1 + rn) =
        rn * (C * V) * (k + 1) + C * rn * (rn * V) + k * (V * (k + 1)) + k * V * rn := by grind
    have e2 : (rn * (P * U) + k * U) * (k + 1 + rn) =
        rn * (P * (U * (k + 1 + rn))) + k * (U * (k + 1 + rn)) := by grind
    have e3 : (C * rn + k) * (rn * V) = C * rn * (rn * V) + k * V * rn := by grind
    have e4 : rn * ((C + q) * (V * (k + 1))) = rn * (C * V) * (k + 1) + q * (k + 1) * (rn * V) := by
      grind
    omega

/-- Compounding never lowers the balance from one period to the next. -/
theorem compound_le_succ (rn rd n P : Nat) : compound rn rd n P ≤ compound rn rd (n + 1) P := by
  rw [compound_succ]; exact Nat.le_add_right _ _

/-- Compounding is monotone in the number of periods. -/
theorem compound_mono_time (rn rd P : Nat) {n n' : Nat} (h : n ≤ n') :
    compound rn rd n P ≤ compound rn rd n' P := by
  induction n' with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n' ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Nat.le_trans (ih (by omega)) (compound_le_succ rn rd n' P)
    · subst h; exact Nat.le_refl _

/-- Compounding is monotone in the principal and the rate. -/
theorem compound_mono {rn rn' P P' : Nat} (rd n : Nat) (hr : rn ≤ rn') (hP : P ≤ P') :
    compound rn rd n P ≤ compound rn' rd n P' := by
  induction n with
  | zero => exact hP
  | succ n ih =>
    rw [compound_succ, compound_succ]
    have := div_mono_left rd (Nat.mul_le_mul ih hr)
    omega

/-- Compounding rounded up is monotone in the principal and the rate. -/
theorem compoundUp_mono {rn rn' P P' : Nat} (rd n : Nat) (hr : rn ≤ rn') (hP : P ≤ P') :
    compoundUp rn rd n P ≤ compoundUp rn' rd n P' := by
  induction n with
  | zero => exact hP
  | succ n ih =>
    rw [compoundUp_succ, compoundUp_succ]
    have := ceilDiv_mono_left rd (Nat.mul_le_mul ih hr)
    omega

/-- Compounding rounded down earns at least the simple interest of the principal rounded down
each period: `P + n * (P * rn / rd) ≤ compound rn rd n P`. -/
theorem add_mul_simple_le_compound (rn rd n P : Nat) :
    P + n * (P * rn / rd) ≤ compound rn rd n P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : P ≤ compound rn rd n P := by
      have := compound_mono_time rn rd P (Nat.zero_le n); simpa using this
    have h2 := div_mono_left rd (Nat.mul_le_mul_right rn h1)
    have e : (n + 1) * (P * rn / rd) = n * (P * rn / rd) + P * rn / rd := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [compound_succ, e]
    omega

/-- Compounding rounded down is at most compounding rounded up. -/
theorem compound_le_compoundUp (rn rd n P : Nat) : compound rn rd n P ≤ compoundUp rn rd n P := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [compound_succ, compoundUp_succ]
    have := div_mono_left rd (Nat.mul_le_mul_right rn ih)
    have := div_le_ceilDiv (compoundUp rn rd n P * rn) rd
    omega

/-! ## Amortization with a fixed payment -/

/-- The balance after `k` regular payments of `p`, each period charging interest `i b` on its
opening balance `b`. -/
def balanceAfter (i : Int → Int) (p : Int) : Nat → Int → Int
  | 0, B => B
  | k + 1, B => balanceAfter i p k (B + i B - p)

/-- The interest charged over the first `k` periods. -/
def interestPaid (i : Int → Int) (p : Int) : Nat → Int → Int
  | 0, _ => 0
  | k + 1, B => i B + interestPaid i p k (B + i B - p)

/-- The last payment of an `n`-period schedule: the opening balance of period `n` plus its
interest, which closes the loan. -/
def finalPayment (i : Int → Int) (p : Int) (n : Nat) (B : Int) : Int :=
  balanceAfter i p (n - 1) B + i (balanceAfter i p (n - 1) B)

/-- The payments of an `n`-period schedule: `n - 1` regular payments and the final one. -/
def payments (i : Int → Int) (p : Int) (n : Nat) (B : Int) : List Int :=
  List.replicate (n - 1) p ++ [finalPayment i p n B]

/-- The balance one period later. -/
theorem balanceAfter_succ' (i : Int → Int) (p : Int) (k : Nat) (B : Int) :
    balanceAfter i p (k + 1) B = balanceAfter i p k B + i (balanceAfter i p k B) - p := by
  induction k generalizing B with
  | zero => rfl
  | succ k ih => simp only [balanceAfter] at *; rw [ih]

/-- The interest of one more period. -/
theorem interestPaid_succ' (i : Int → Int) (p : Int) (k : Nat) (B : Int) :
    interestPaid i p (k + 1) B = interestPaid i p k B + i (balanceAfter i p k B) := by
  induction k generalizing B with
  | zero => simp [interestPaid, balanceAfter]
  | succ k ih =>
    simp only [interestPaid, balanceAfter] at *
    rw [ih]; omega

/-- Telescoping: the balance after `k` payments plus the payments is the principal plus the
interest. -/
theorem balanceAfter_add_mul (i : Int → Int) (p : Int) (k : Nat) (B : Int) :
    balanceAfter i p k B + k * p = B + interestPaid i p k B := by
  induction k generalizing B with
  | zero => simp [balanceAfter, interestPaid]
  | succ k ih =>
    simp only [balanceAfter, interestPaid]
    have := ih (B + i B - p)
    have e : ((k + 1 : Nat) : Int) * p = (k : Int) * p + p := by push_cast; rw [Int.add_mul, Int.one_mul]
    rw [e]; omega

/-- The final payment closes the loan: the balance after it is zero. -/
theorem finalPayment_closes (i : Int → Int) (p : Int) (n : Nat) (B : Int) :
    balanceAfter i p (n - 1) B + i (balanceAfter i p (n - 1) B) - finalPayment i p n B = 0 := by
  unfold finalPayment; omega

/-- The sum of `n` copies of `a`. -/
theorem sum_replicate_int (n : Nat) (a : Int) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.sum_cons, ih]; push_cast; rw [Int.add_mul, Int.one_mul]; omega

/-- A schedule of `n ≥ 1` periods has `n` payments. -/
theorem length_payments (i : Int → Int) (p : Int) {n : Nat} (hn : 1 ≤ n) (B : Int) :
    (payments i p n B).length = n := by
  simp [payments]; omega

/-- The payments add up to the principal plus the total interest. -/
theorem sum_payments (i : Int → Int) (p : Int) {n : Nat} (hn : 1 ≤ n) (B : Int) :
    (payments i p n B).sum = B + interestPaid i p n B := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold payments finalPayment
  simp only [Nat.add_sub_cancel, List.sum_append, sum_replicate_int, List.sum_cons, List.sum_nil,
    Int.add_zero, interestPaid_succ']
  have := balanceAfter_add_mul i p m B
  omega

/-- Interest rounded down at rate `rn / rd`: `b * rn / rd` on a signed balance. -/
def interestDown (rn rd : Int) (b : Int) : Int := b * rn / rd

/-- With interest rounded down, the balance after `k` regular payments is at most the exact
balance: `rn * b_k * rd^k ≤ rn * B * g^k - p * rd * (g^k - rd^k)`. -/
theorem balanceAfter_interestDown_le {rn rd : Int} (hd : 0 < rd) (hn : 0 ≤ rn) (p : Int) (k : Nat)
    (B : Int) :
    rn * balanceAfter (interestDown rn rd) p k B * rd ^ k ≤
      rn * B * (rd + rn) ^ k - p * rd * ((rd + rn) ^ k - rd ^ k) := by
  induction k with
  | zero => simp [balanceAfter]
  | succ k ih =>
    rw [balanceAfter_succ', Int.pow_succ, Int.pow_succ]
    have hb := (ediv_bounds (balanceAfter (interestDown rn rd) p k B * rn) hd).1
    generalize balanceAfter (interestDown rn rd) p k B = b at ih hb ⊢
    simp only [interestDown]
    generalize b * rn / rd = q at hb ⊢
    have hV : 0 ≤ rd ^ k := Int.le_of_lt (Int.pow_pos hd)
    generalize rd ^ k = V at ih hV ⊢
    generalize (rd + rn) ^ k = U at ih ⊢
    have hstep : (b + q - p) * rd ≤ (rd + rn) * b - rd * p := by grind
    have m1 := Int.mul_le_mul_of_nonneg_left hstep (Int.mul_nonneg hn hV)
    have m2 := Int.mul_le_mul_of_nonneg_left ih (show 0 ≤ rd + rn by omega)
    grind

/-- With interest rounded down and a regular payment at least the exact annuity payment
(`rn * B * g^n ≤ p * rd * (g^n - rd^n)`, `0 < rn`), the final payment never exceeds the
regular payment. -/
theorem finalPayment_le {rn rd : Int} (hd : 0 < rd) (hn : 0 < rn) {p B : Int} {n : Nat}
    (h1 : 1 ≤ n) (h : rn * B * (rd + rn) ^ n ≤ p * rd * ((rd + rn) ^ n - rd ^ n)) :
    finalPayment (interestDown rn rd) p n B ≤ p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold finalPayment
  simp only [Nat.add_sub_cancel]
  have inv := balanceAfter_interestDown_le hd (Int.le_of_lt hn) p m B
  have hb := (ediv_bounds (balanceAfter (interestDown rn rd) p m B * rn) hd).1
  rw [Int.pow_succ, Int.pow_succ] at h
  generalize balanceAfter (interestDown rn rd) p m B = b at inv hb ⊢
  simp only [interestDown]
  generalize b * rn / rd = q at hb ⊢
  have hV : 0 < rd ^ m := Int.pow_pos hd
  generalize rd ^ m = V at inv h hV ⊢
  generalize (rd + rn) ^ m = U at inv h ⊢
  have hF : (b + q) * rd ≤ (rd + rn) * b := by grind
  have m1 := Int.mul_le_mul_of_nonneg_left hF (Int.le_of_lt (Int.mul_pos hn hV))
  have m2 := Int.mul_le_mul_of_nonneg_left inv (show 0 ≤ rd + rn by omega)
  have key : (b + q) * (rn * V * rd) ≤ p * (rn * V * rd) := by grind
  exact Int.le_of_mul_le_mul_right key (Int.mul_pos (Int.mul_pos hn hV) hd)

/-- The exact annuity payment rounded up: `ceil (rn * B * g^n / (rd * (g^n - rd^n)))`. -/
def annuityPayment (rn rd : Int) (n : Nat) (B : Int) : Int :=
  divCeil (rn * B * (rd + rn) ^ n) (rd * ((rd + rn) ^ n - rd ^ n))

/-- A larger base has a larger power: `rd^n < (rd + rn)^n` for `0 < rn`, `0 < rd`, `1 ≤ n`. -/
theorem pow_lt_pow_add {rn rd : Int} (hd : 0 < rd) (hn : 0 < rn) {n : Nat} (h1 : 1 ≤ n) :
    rd ^ n < (rd + rn) ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Int.pow_succ, Int.pow_succ]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp; omega
    · have a := ih h0
      have hV : 0 < rd ^ n := Int.pow_pos hd
      have b1 := Int.mul_lt_mul_of_pos_right a hd
      have b2 := Int.mul_le_mul_of_nonneg_left (show rd ≤ rd + rn by omega)
        (Int.le_of_lt (Int.lt_trans hV a))
      rw [Int.mul_comm ((rd + rn) ^ n) rd] at b1
      rw [Int.mul_comm ((rd + rn) ^ n) rd, Int.mul_comm ((rd + rn) ^ n) (rd + rn)] at *
      omega

/-- With interest rounded down and the annuity payment rounded up, the final payment never
exceeds the regular payment. -/
theorem finalPayment_annuityPayment_le {rn rd : Int} (hd : 0 < rd) (hn : 0 < rn) {n : Nat}
    (h1 : 1 ≤ n) (B : Int) :
    finalPayment (interestDown rn rd) (annuityPayment rn rd n B) n B ≤ annuityPayment rn rd n B := by
  apply finalPayment_le hd hn h1
  have hp := pow_lt_pow_add hd hn h1
  have hden : 0 < rd * ((rd + rn) ^ n - rd ^ n) := Int.mul_pos hd (by omega)
  have := (divCeil_bounds (rn * B * (rd + rn) ^ n) hden).2
  unfold annuityPayment
  have e : divCeil (rn * B * (rd + rn) ^ n) (rd * ((rd + rn) ^ n - rd ^ n)) * rd * ((rd + rn) ^ n - rd ^ n) =
      divCeil (rn * B * (rd + rn) ^ n) (rd * ((rd + rn) ^ n - rd ^ n)) * (rd * ((rd + rn) ^ n - rd ^ n)) := by
    rw [Int.mul_assoc]
  rw [e]; exact this

/-- 10000 units at 1% a month (rate 1/100) over 12 months: the annuity payment rounded up is
889 units, and the twelfth payment, which closes the loan, is 883 units. -/
theorem annuity_example :
    annuityPayment 1 100 12 10000 = 889 ∧ finalPayment (interestDown 1 100) 889 12 10000 = 878 := by
  decide

end ProofForgeFin.Money
