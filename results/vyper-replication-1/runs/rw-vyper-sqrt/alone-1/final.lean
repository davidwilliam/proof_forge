import VyperSqrt.Spec
import VyperSqrt.Lemmas

namespace VyperSqrt

/-- The corrected routine: the deployed loop followed by the choice from PR 4486
(the minimum of the last two iterates), which rounds the root down. -/
def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

namespace Newton

/-- Square monotonicity on naturals. -/
theorem sq_mono {a b : Nat} (h : a ≤ b) : a * a ≤ b * b :=
  Nat.mul_le_mul h h

/-- Strict square monotonicity, reversed. -/
theorem lt_of_sq_lt {a b : Nat} (h : a * a < b * b) : a < b := by
  rcases Nat.le_total a b with hle | hle
  · by_cases heq : a = b
    · subst heq
      omega
    · exact Nat.lt_of_le_of_ne hle heq
  · have h2 := sq_mono hle
    omega

/-- If `m * m ≤ X` then `m ≤ √X`. -/
theorem le_sqrt_of_sq {m X : Nat} (h : m * m ≤ X) : m ≤ Nat.sqrt X := by
  rcases Nat.le_total m (Nat.sqrt X) with hle | hge
  · exact hle
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
    rw [hd]
    have hlt2 := Nat.lt_succ_sqrt X
    rw [Nat.succ_eq_add_one] at hlt2
    rw [hd] at h
    have hlt3 : (Nat.sqrt X + d) * (Nat.sqrt X + d)
        < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := by omega
    have hlt4 := lt_of_sq_lt hlt3
    omega

/-- Uniqueness of the floor root. -/
theorem sqrt_eq_of_sq {z X : Nat} (h1 : z * z ≤ X)
    (h2 : X < (z + 1) * (z + 1)) : z = Nat.sqrt X := by
  have g1 := le_sqrt_of_sq h1
  have g2 : Nat.sqrt X ≤ z := by
    by_cases heq : z = Nat.sqrt X
    · omega
    · have hlt : z < Nat.sqrt X := Nat.lt_of_le_of_ne g1 heq
      have hz : z + 1 ≤ Nat.sqrt X := by omega
      have h5 := Nat.mul_le_mul hz hz
      have h4 := Nat.sqrt_le X
      omega
  omega

/-- The scaled radicand `a * 10^10`. -/
def Xc (a : Nat) : Nat := a * 10 ^ 10

/-- The seed `a / 2 + 5 * 10^9`. -/
def Sd (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- One Newton step (total variant; `0` maps to `0` and never occurs). -/
def Nf (X z : Nat) : Nat := (X / z + z) / 2

/-- The Newton iterates from the seed. -/
def NSeq (a : Nat) : Nat → Nat
  | 0 => Sd a
  | n + 1 => Nf (Xc a) (NSeq a n)

/-- The floor root of the scaled radicand. -/
def Rt (a : Nat) : Nat := Nat.sqrt (Xc a)

theorem nseq_succ (a n : Nat) : NSeq a (n + 1) = Nf (Xc a) (NSeq a n) := rfl

theorem rt_sq (a : Nat) : Rt a * Rt a ≤ Xc a := Nat.sqrt_le (Xc a)

theorem rt_succ (a : Nat) : Xc a < (Rt a + 1) * (Rt a + 1) := by
  have h := Nat.lt_succ_sqrt (Xc a)
  rw [Nat.succ_eq_add_one] at h
  exact h

/-- Expansion of a square of a sum (stated in rewrite-normal form). -/
theorem add_sq (x y : Nat) :
    (x + y) * (x + y) = (x * x + x * y) + (y * x + y * y) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]

/-- The scaled radicand is below `2^201`. -/
theorem Xc_lt {a : Nat} (hM : a ≤ 2 ^ 167 - 1) : Xc a < 2 ^ 201 := by
  have e34 : (10 : Nat) ^ 10 < 2 ^ 34 := by decide
  have h1 : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 10 ^ 10 :=
    Nat.mul_le_mul_right _ hM
  have h10 : (0 : Nat) < 10 ^ 10 := by decide
  have g1 : (2 ^ 167 - 1) * 10 ^ 10 < 2 ^ 167 * 10 ^ 10 :=
    Nat.mul_lt_mul_of_pos_right (by omega) h10
  have g2 : 2 ^ 167 * 10 ^ 10 ≤ 2 ^ 167 * 2 ^ 34 :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : (2 : Nat) ^ 167 * 2 ^ 34 = 2 ^ (167 + 34) := (Nat.pow_add _ _ _).symm
  have h4 : (167 + 34 : Nat) = 201 := by decide
  rw [h4] at h3
  unfold Xc
  calc a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 10 ^ 10 := h1
    _ < 2 ^ 167 * 10 ^ 10 := g1
    _ ≤ 2 ^ 167 * 2 ^ 34 := g2
    _ = 2 ^ 201 := h3

/-- The floor root is at least `10^5` for `a ≥ 1`. -/
theorem rt_ge {a : Nat} (ha : 1 ≤ a) : 100000 ≤ Rt a := by
  apply le_sqrt_of_sq
  have h1 : (100000 : Nat) * 100000 = 10000000000 := by decide
  have h2 : 1 * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha
  unfold Xc
  omega

/-- The floor root is below `2^101`. -/
theorem rt_lt {a : Nat} (hM : a ≤ 2 ^ 167 - 1) : Rt a < 2 ^ 101 := by
  have hX := Xc_lt hM
  have hr := rt_sq a
  have e202 : (2 : Nat) ^ 101 * 2 ^ 101 = 2 ^ 202 := by
    have h3 : (2 : Nat) ^ 101 * 2 ^ 101 = 2 ^ (101 + 101) :=
      (Nat.pow_add _ _ _).symm
    have h4 : (101 + 101 : Nat) = 202 := by decide
    rw [h4] at h3
  have e201 : (2 : Nat) ^ 202 > 2 ^ 201 := by decide
  have hchain : (2 : Nat) ^ 202 ≤ Xc a → (2 : Nat) ^ 202 < 2 ^ 202 := by
    intro hcon
    calc (2 : Nat) ^ 202 ≤ Xc a := hcon
      _ < 2 ^ 201 := hX
      _ < 2 ^ 202 := e201
  rcases Nat.le_total (Rt a) (2 ^ 101) with hle | hge
  · by_cases heq : Rt a = 2 ^ 101
    · rw [heq] at hr
      have hcon : (2 : Nat) ^ 202 ≤ Xc a :=
        calc (2 : Nat) ^ 202 = 2 ^ 101 * 2 ^ 101 := e202.symm
          _ ≤ Xc a := hr
      exact absurd (hchain hcon) (Nat.lt_irrefl _)
    · exact Nat.lt_of_le_of_ne hle heq
  · have h2 := sq_mono hge
    have hcon : (2 : Nat) ^ 202 ≤ Xc a :=
      calc (2 : Nat) ^ 202 = 2 ^ 101 * 2 ^ 101 := e202.symm
        _ ≤ Rt a * Rt a := h2
        _ ≤ Xc a := hr
    exact absurd (hchain hcon) (Nat.lt_irrefl _)

/-- The seed is a decimal. -/
theorem sd_le {a : Nat} (hM : a ≤ 2 ^ 167 - 1) : Sd a ≤ 2 ^ 167 - 1 := by
  have h1 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hM
  have h2 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
  have h5 : (2 : Nat) ^ 167 = 2 ^ 166 + 2 ^ 166 := by decide
  have h6 : 5 * 10 ^ 9 ≤ (2 : Nat) ^ 166 := by decide
  unfold Sd
  omega

/-- The seed is positive. -/
theorem sd_pos (a : Nat) : 1 ≤ Sd a := by
  unfold Sd
  omega

/-- Completing the square: `4 * ((u-1) * c + 1) ≤ ((u-1) + c + 1)^2`. -/
theorem csq_le {u c : Nat} (hu : 1 ≤ u) (hc : 1 ≤ c) :
    4 * ((u - 1) * c + 1) ≤ ((u - 1) + c + 1) * ((u - 1) + c + 1) := by
  rcases Nat.le_total u c with hcase | hcase
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hcase
    rw [hd]
    have hbase : (u - 1) + (u + d) + 1 = u + (u + d) := by omega
    rw [hbase, add_sq]
    have e1 : u * (u + d) = u * u + u * d := Nat.mul_add _ _ _
    have e2 : (u + d) * u = u * u + u * d := by
      rw [Nat.add_mul, Nat.mul_comm d u]
    have e3 : (u + d) * (u + d) = (u * u + u * d) + (u * d + d * d) := by
      rw [add_sq, Nat.mul_comm d u]
    have e4 : (u - 1) * (u + d) = (u * u + u * d) - (u + d) := by
      rw [Nat.sub_mul, Nat.one_mul, e1]
    rw [e1, e2, e3, e4]
    have hAu : u ≤ u * u := by
      have h : u * 1 ≤ u * u := Nat.mul_le_mul_left u (by omega : 1 ≤ u)
      rwa [Nat.mul_one] at h
    have hBd : d ≤ u * d := by
      have h : 1 * d ≤ u * d := Nat.mul_le_mul_right d (by omega : 1 ≤ u)
      rwa [Nat.one_mul] at h
    generalize u * u = A at *
    generalize u * d = B at *
    generalize d * d = C at *
    clear e1 e2 e3 e4 hbase
    omega
  · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hcase
    rw [he]
    have hsub2 : c + e - 1 = (c - 1) + e := by omega
    rw [hsub2]
    have e4 : (c - 1) * c = c * c - c := by
      rw [Nat.sub_mul, Nat.one_mul]
    have g1 : ((c - 1) + e) * c = ((c * c - c) + c * e) := by
      rw [Nat.add_mul, e4, Nat.mul_comm e c]
    have hbase : ((c - 1) + e) + c + 1 = (c + c) + e := by omega
    rw [hbase, add_sq, g1]
    have f1 : (c + c) * (c + c) = (c * c + c * c) + (c * c + c * c) := by
      rw [add_sq]
    have f2 : (c + c) * e = c * e + c * e := Nat.add_mul _ _ _
    have f3 : e * (c + c) = c * e + c * e := by
      rw [Nat.mul_add, Nat.mul_comm e c]
    rw [f1, f2, f3]
    have hCc : c ≤ c * c := by
      have h : c * 1 ≤ c * c := Nat.mul_le_mul_left c (by omega : 1 ≤ c)
      rwa [Nat.mul_one] at h
    generalize c * c = D at *
    generalize c * e = E at *
    generalize e * e = F at *
    clear e4 g1 f1 f2 f3 hbase hsub2
    omega

/-- The seed sits above the floor root. -/
theorem sd_ge_rt {a : Nat} (ha : 1 ≤ a) : Rt a ≤ Sd a := by
  have h10 : (1 : Nat) ≤ 10 ^ 10 := by decide
  have hcore := csq_le (u := a + 1) (c := 10 ^ 10) (by omega) h10
  have ha1 : a + 1 - 1 = a := by omega
  rw [ha1] at hcore
  have h2 : a + 10 ^ 10 + 1 ≤ 2 * (Sd a + 1) := by
    unfold Sd
    omega
  have hsq := sq_mono h2
  have hexp : (2 * (Sd a + 1)) * (2 * (Sd a + 1))
      = 4 * ((Sd a + 1) * (Sd a + 1)) := by
    have h2t : (2 : Nat) * (Sd a + 1) = (Sd a + 1) + (Sd a + 1) := by omega
    rw [h2t, add_sq]
    omega
  have h4 : 4 * (a * 10 ^ 10 + 1) ≤ 4 * ((Sd a + 1) * (Sd a + 1)) :=
    calc 4 * (a * 10 ^ 10 + 1)
          ≤ (a + 10 ^ 10 + 1) * (a + 10 ^ 10 + 1) := hcore
      _ ≤ (2 * (Sd a + 1)) * (2 * (Sd a + 1)) := hsq
      _ = 4 * ((Sd a + 1) * (Sd a + 1)) := hexp
  have hfin : a * 10 ^ 10 < (Sd a + 1) * (Sd a + 1) := by omega
  have hrt := rt_sq a
  have hXc2 : Xc a = a * 10 ^ 10 := rfl
  have hlt : Rt a < Sd a + 1 :=
    lt_of_sq_lt (by omega : Rt a * Rt a < (Sd a + 1) * (Sd a + 1))
  omega

/-- A positive fixed point of the Newton step is the floor root. -/
theorem f_fix {a w : Nat} (hw1 : 1 ≤ w) (hfix : Nf (Xc a) w = w) :
    w = Rt a := by
  have hfix2 : (Xc a / w + w) / 2 = w := by
    unfold Nf at hfix
    exact hfix
  have hmod := Nat.div_add_mod (Xc a / w + w) 2
  have hm2 : (Xc a / w + w) % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [hfix2] at hmod
  apply sqrt_eq_of_sq
  · have hge : w ≤ Xc a / w := by omega
    exact (Nat.le_div_iff_mul_le hw1).mp hge
  · have hle : Xc a / w ≤ w + 1 := by omega
    have hlt : Xc a / w < w + 2 := by omega
    have hXlt := (Nat.div_lt_iff_lt_mul hw1).mp hlt
    have e1 : (w + 2) * w = w * w + (w + w) := by
      rw [Nat.add_mul]
      omega
    have e2 : (w + 1) * (w + 1) = w * w + (w + (w + 1)) := by
      rw [add_sq, Nat.mul_one, Nat.one_mul, Nat.mul_one]
      omega
    rw [e1] at hXlt
    rw [e2]
    omega

/-- The quotient at `r + 1` is at most `r + 1`. -/
theorem q_le {a z : Nat} (hz : Rt a + 1 ≤ z) : Xc a / z ≤ Rt a + 1 := by
  have hX := rt_succ a
  have hz2 : (Rt a + 1) * (Rt a + 1) ≤ (Rt a + 1) * z :=
    Nat.mul_le_mul_left _ hz
  have hzpos : (0 : Nat) < z := by omega
  rcases Nat.le_total (Xc a / z) (Rt a + 1) with hle | hge
  · exact hle
  · have hle2 := (Nat.le_div_iff_mul_le hzpos).mp hge
    have hcon : (Rt a + 1) * z < (Rt a + 1) * z := by
      calc (Rt a + 1) * z ≤ Xc a := hle2
        _ < (Rt a + 1) * (Rt a + 1) := hX
        _ ≤ (Rt a + 1) * z := hz2
    exact absurd hcon (Nat.lt_irrefl _)

/-- The Newton step maps `r + 1` exactly to `r`. -/
theorem f_top {a : Nat} (hr1 : 1 ≤ Rt a) : Nf (Xc a) (Rt a + 1) = Rt a := by
  have hpos : (0 : Nat) < Rt a + 1 := by omega
  have hqlt : Xc a / (Rt a + 1) < Rt a + 1 :=
    (Nat.div_lt_iff_lt_mul hpos).mpr (rt_succ a)
  have hq1 : Xc a / (Rt a + 1) ≤ Rt a := by omega
  have hq2 : Rt a - 1 ≤ Xc a / (Rt a + 1) := by
    rw [Nat.le_div_iff_mul_le hpos]
    have e : (Rt a - 1) * (Rt a + 1) + 1 = Rt a * Rt a := by
      cases h : Rt a with
      | zero => omega
      | succ n =>
        rw [Nat.add_sub_cancel]
        have g1 : n * ((n + 1) + 1) = n * n + (n + n) := by
          have hnn : ((n + 1) + 1) = n + 2 := by omega
          rw [hnn, Nat.mul_add]
          omega
        have g2 : (n + 1) * (n + 1) = n * n + (n + (n + 1)) := by
          rw [add_sq, Nat.mul_one, Nat.one_mul, Nat.mul_one]
          omega
        rw [g1, g2]
        omega
    have hle := rt_sq a
    omega
  unfold Nf
  omega

/-- `X < (r+1)^2` as a non-strict bound. -/
theorem Xc_le_succ (a : Nat) : Xc a + 1 ≤ (Rt a + 1) * (Rt a + 1) := by
  have h := rt_succ a
  omega

/-- `(r-1) * (r+1) + 1 = r * r` for `r ≥ 1`. -/
theorem sq_sub_add {r : Nat} (hr1 : 1 ≤ r) :
    (r - 1) * (r + 1) + 1 = r * r := by
  cases h : r with
  | zero => omega
  | succ n =>
    rw [Nat.add_sub_cancel]
    have g1 : n * ((n + 1) + 1) = n * n + (n + n) := by
      have hnn : ((n + 1) + 1) = n + 2 := by omega
      rw [hnn, Nat.mul_add]
      omega
    have g2 : (n + 1) * (n + 1) = n * n + (n + (n + 1)) := by
      rw [add_sq, Nat.mul_one, Nat.one_mul, Nat.mul_one]
      omega
    rw [g1, g2]
    omega

/-- The quotient at `r` is at least `r`. -/
theorem q2_ge {a : Nat} (hr1 : 1 ≤ Rt a) : Rt a ≤ Xc a / Rt a :=
  (Nat.le_div_iff_mul_le hr1).mpr (rt_sq a)

/-- The quotient at `r` is at most `r + 2`. -/
theorem q2_le {a : Nat} (hr1 : 1 ≤ Rt a) : Xc a / Rt a ≤ Rt a + 2 := by
  rcases Nat.le_total (Xc a / Rt a) (Rt a + 2) with hle | hge
  · exact hle
  · by_cases heq : Xc a / Rt a = Rt a + 2
    · omega
    · have hge3 : Rt a + 3 ≤ Xc a / Rt a := by omega
      have hle2 := (Nat.le_div_iff_mul_le hr1).mp hge3
      have hX : Xc a + 1 ≤ (Rt a + 1) * (Rt a + 1) := Xc_le_succ a
      have bridge : (Rt a + 1) * (Rt a + 1) ≤ (Rt a + 3) * Rt a := by
        have h3 : Rt a + 3 = (Rt a + 1) + 2 := by omega
        rw [h3, Nat.add_mul (Rt a + 1) 2 (Rt a)]
        have e : (Rt a + 1) * (Rt a + 1)
            = (Rt a + 1) * Rt a + (Rt a + 1) * 1 := Nat.mul_add _ _ _
        rw [e, Nat.mul_one]
        have h1r : Rt a + 1 ≤ 2 * Rt a := by omega
        omega
      have hcon : (Rt a + 3) * Rt a < (Rt a + 3) * Rt a := by
        calc (Rt a + 3) * Rt a ≤ Xc a := hle2
          _ < (Rt a + 1) * (Rt a + 1) := by omega
          _ ≤ (Rt a + 3) * Rt a := bridge
      exact absurd hcon (Nat.lt_irrefl _)

/-- The Newton step at `r` stays in `{r, r+1}`. -/
theorem f_r {a : Nat} (hr1 : 1 ≤ Rt a) :
    Nf (Xc a) (Rt a) = Rt a ∨ Nf (Xc a) (Rt a) = Rt a + 1 := by
  have hq2 := q2_ge hr1
  have hq2' := q2_le hr1
  have hq : Xc a / Rt a = Rt a ∨ Xc a / Rt a = Rt a + 1
      ∨ Xc a / Rt a = Rt a + 2 := by omega
  unfold Nf
  rcases hq with h | h | h
  · rw [h]
    exact Or.inl (by omega)
  · rw [h]
    exact Or.inl (by omega)
  · rw [h]
    exact Or.inr (by omega)

/-- The quotient at `r - 1` is at least `r + 1`. -/
theorem q3_ge {a : Nat} (ha : 1 ≤ a) : Rt a + 1 ≤ Xc a / (Rt a - 1) := by
  have hr100k := rt_ge ha
  have hzpos : (0 : Nat) < Rt a - 1 := by omega
  rw [Nat.le_div_iff_mul_le hzpos]
  have e := sq_sub_add (by omega : 1 ≤ Rt a)
  have hle := rt_sq a
  have hc : (Rt a + 1) * (Rt a - 1) = (Rt a - 1) * (Rt a + 1) :=
    Nat.mul_comm _ _
  omega

/-- The quotient at `r - 1` is at most `r + 3`. -/
theorem q3_le {a : Nat} (ha : 1 ≤ a) : Xc a / (Rt a - 1) ≤ Rt a + 3 := by
  have hr100k := rt_ge ha
  have hzpos : (0 : Nat) < Rt a - 1 := by omega
  rcases Nat.le_total (Xc a / (Rt a - 1)) (Rt a + 3) with hle | hge
  · exact hle
  · by_cases heq : Xc a / (Rt a - 1) = Rt a + 3
    · omega
    · have hge4 : Rt a + 4 ≤ Xc a / (Rt a - 1) := by omega
      have hle2 := (Nat.le_div_iff_mul_le hzpos).mp hge4
      have hX : Xc a + 1 ≤ (Rt a + 1) * (Rt a + 1) := Xc_le_succ a
      have bridge : (Rt a + 1) * (Rt a + 1) ≤ (Rt a + 4) * (Rt a - 1) := by
        have h4 : Rt a + 4 = (Rt a + 1) + 3 := by omega
        rw [h4, Nat.add_mul (Rt a + 1) 3 (Rt a - 1)]
        have e : (Rt a - 1) * (Rt a + 1) + 1 = Rt a * Rt a :=
          sq_sub_add (by omega)
        have e2 : (Rt a + 1) * (Rt a + 1)
            = Rt a * Rt a + (Rt a + (Rt a + 1)) := by
          rw [add_sq, Nat.mul_one, Nat.one_mul, Nat.mul_one]
          omega
        have c1 : (Rt a + 1) * (Rt a - 1) = (Rt a - 1) * (Rt a + 1) :=
          Nat.mul_comm _ _
        rw [e2, c1]
        clear e2 c1 h4
        omega
      have hcon : (Rt a + 4) * (Rt a - 1) < (Rt a + 4) * (Rt a - 1) := by
        calc (Rt a + 4) * (Rt a - 1) ≤ Xc a := hle2
          _ < (Rt a + 1) * (Rt a + 1) := by omega
          _ ≤ (Rt a + 4) * (Rt a - 1) := bridge
      exact absurd hcon (Nat.lt_irrefl _)

/-- The Newton step at `r - 1` lands in `{r, r+1}`. -/
theorem f_rm1 {a : Nat} (ha : 1 ≤ a) :
    Nf (Xc a) (Rt a - 1) = Rt a ∨ Nf (Xc a) (Rt a - 1) = Rt a + 1 := by
  have hr100k := rt_ge ha
  have hq3 := q3_ge ha
  have hq3' := q3_le ha
  have hq : Xc a / (Rt a - 1) = Rt a + 1 ∨ Xc a / (Rt a - 1) = Rt a + 2
      ∨ Xc a / (Rt a - 1) = Rt a + 3 := by omega
  unfold Nf
  rcases hq with h | h | h
  · rw [h]
    exact Or.inl (by omega)
  · rw [h]
    exact Or.inl (by omega)
  · rw [h]
    exact Or.inr (by omega)

/-- Key arithmetic: `(2m - z) * z ≤ m * m` for `z ≤ 2m`. -/
theorem mul_le_sq {m z : Nat} (hz : z ≤ 2 * m) : (2 * m - z) * z ≤ m * m := by
  rcases Nat.le_total z m with hcase | hcase
  · have h1 : 2 * m - z = m + (m - z) := by omega
    have h2 : z + (m - z) = m := by omega
    have g1 : (m - z) * z ≤ (m - z) * m := Nat.mul_le_mul_left _ hcase
    have g2 : m * z + (m - z) * m = m * m := by
      rw [Nat.mul_comm (m - z) m, ← Nat.mul_add, h2]
    rw [h1, Nat.add_mul]
    generalize m * z = A at g1 g2 ⊢
    generalize (m - z) * z = B at g1 ⊢
    generalize (m - z) * m = C at g1 g2
    generalize m * m = D at g2 ⊢
    omega
  · obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hcase
    have hvm : v ≤ m := by omega
    have h2m : 2 * m - (m + v) = m - v := by omega
    have key : (m - v) * (m + v) + v * v = m * m := by
      have s1 : (m - v) * (m + v) = m * (m + v) - v * (m + v) := Nat.sub_mul _ _ _
      have s2 : m * (m + v) = m * m + m * v := Nat.mul_add _ _ _
      have s3 : v * (m + v) = v * m + v * v := Nat.mul_add _ _ _
      have c : v * m = m * v := Nat.mul_comm _ _
      rw [s1, s2, s3, c]
      have hCA : v * v ≤ m * m := sq_mono hvm
      generalize m * m = A at *
      generalize m * v = B at *
      generalize v * v = C at *
      clear s1 s2 s3 c
      omega
    rw [hv, h2m]
    calc (m - v) * (m + v) ≤ (m - v) * (m + v) + v * v := Nat.le_add_right _ _
      _ = m * m := key

/-- The Newton step never drops below `r - 1`. -/
theorem f_ge {a z : Nat} (hr1 : 1 ≤ Rt a) (hz1 : 1 ≤ z) :
    Rt a - 1 ≤ Nf (Xc a) z := by
  have h2 : 2 * (Rt a - 1) ≤ Xc a / z + z := by
    rcases Nat.le_total z (2 * (Rt a - 1)) with hcase | hcase
    · have hq : 2 * (Rt a - 1) - z ≤ Xc a / z := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < z)]
        have hml := mul_le_sq hcase
        have hmr : (Rt a - 1) * (Rt a - 1) ≤ Rt a * Rt a :=
          sq_mono (Nat.sub_le _ _)
        have hrx := rt_sq a
        calc (2 * (Rt a - 1) - z) * z ≤ (Rt a - 1) * (Rt a - 1) := hml
          _ ≤ Rt a * Rt a := hmr
          _ ≤ Xc a := hrx
      omega
    · exact Nat.le_trans hcase (Nat.le_add_left _ _)
  unfold Nf
  omega

/-- Above `r + 1`, the gap to `r + 1` at least halves. -/
theorem halve {a z : Nat} (hz : Rt a + 2 ≤ z) :
    2 * Nf (Xc a) z ≤ z + (Rt a + 1) := by
  have hq := q_le (by omega : Rt a + 1 ≤ z)
  have hmod := Nat.div_add_mod (Xc a / z + z) 2
  have hm2 : (Xc a / z + z) % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold Nf
  omega

/-- Every iterate stays above `r - 1`. -/
theorem nseq_ge {a : Nat} (ha : 1 ≤ a) : ∀ k, Rt a - 1 ≤ NSeq a k := by
  have hr100k := rt_ge ha
  intro k
  induction k with
  | zero =>
    have h0 : NSeq a 0 = Sd a := rfl
    have hsd := sd_ge_rt ha
    omega
  | succ k ih =>
    have hk1 : 1 ≤ NSeq a k := by omega
    have hstep : NSeq a (k + 1) = Nf (Xc a) (NSeq a k) := rfl
    rw [hstep]
    exact f_ge (by omega) hk1

/-- The quotient at `r - 1` is at most `r + 4`. -/
theorem q4_le {a : Nat} (ha : 1 ≤ a) : Xc a / (Rt a - 1) ≤ Rt a + 4 := by
  have hr100k := rt_ge ha
  have hzpos : (0 : Nat) < Rt a - 1 := by omega
  rcases Nat.le_total (Xc a / (Rt a - 1)) (Rt a + 4) with hle | hge
  · exact hle
  · by_cases heq : Xc a / (Rt a - 1) = Rt a + 4
    · omega
    · have hge5 : Rt a + 5 ≤ Xc a / (Rt a - 1) := by omega
      have hle2 := (Nat.le_div_iff_mul_le hzpos).mp hge5
      have hX : Xc a + 1 ≤ (Rt a + 1) * (Rt a + 1) := Xc_le_succ a
      have bridge : (Rt a + 1) * (Rt a + 1) ≤ (Rt a + 5) * (Rt a - 1) := by
        have h5 : Rt a + 5 = (Rt a + 1) + 4 := by omega
        rw [h5, Nat.add_mul (Rt a + 1) 4 (Rt a - 1)]
        have e : (Rt a - 1) * (Rt a + 1) + 1 = Rt a * Rt a :=
          sq_sub_add (by omega)
        have e2 : (Rt a + 1) * (Rt a + 1)
            = Rt a * Rt a + (Rt a + (Rt a + 1)) := by
          rw [add_sq, Nat.mul_one, Nat.one_mul, Nat.mul_one]
          omega
        have c1 : (Rt a + 1) * (Rt a - 1) = (Rt a - 1) * (Rt a + 1) :=
          Nat.mul_comm _ _
        rw [e2, c1]
        clear e2 c1 h5
        omega
      have hcon : (Rt a + 5) * (Rt a - 1) < (Rt a + 5) * (Rt a - 1) := by
        calc (Rt a + 5) * (Rt a - 1) ≤ Xc a := hle2
          _ < (Rt a + 1) * (Rt a + 1) := by omega
          _ ≤ (Rt a + 5) * (Rt a - 1) := bridge
      exact absurd hcon (Nat.lt_irrefl _)

/-- Once within one of the root, the next iterate is in `{r, r+1}`. -/
theorem step_close {a z : Nat} (ha : 1 ≤ a)
    (hlo : Rt a - 1 ≤ z) (hhi : z ≤ Rt a + 1) :
    Nf (Xc a) z = Rt a ∨ Nf (Xc a) z = Rt a + 1 := by
  have hr100k := rt_ge ha
  have hr1 : 1 ≤ Rt a := by omega
  have h3 : z = Rt a - 1 ∨ z = Rt a ∨ z = Rt a + 1 := by omega
  rcases h3 with h | h | h
  · rw [h]; exact f_rm1 ha
  · rw [h]; exact f_r hr1
  · rw [h]; exact Or.inl (f_top hr1)

/-- Every iterate stays at most one above the seed. -/
theorem nseq_le1 {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    ∀ k, NSeq a k ≤ Sd a + 1 := by
  have hr100k := rt_ge ha
  intro k
  induction k with
  | zero =>
    have h0 : NSeq a 0 = Sd a := rfl
    omega
  | succ k ih =>
    have hlo := nseq_ge ha k
    rcases Nat.le_total (NSeq a k) (Rt a + 1) with hcase | hcase
    · have hF := step_close ha hlo hcase
      have hstep : NSeq a (k + 1) = Nf (Xc a) (NSeq a k) := rfl
      rw [hstep]
      have hrs := sd_ge_rt ha
      omega
    · by_cases hz2 : Rt a + 2 ≤ NSeq a k
      · have hhalf := halve hz2
        have hstep : NSeq a (k + 1) = Nf (Xc a) (NSeq a k) := rfl
        rw [hstep]
        have hrs := sd_ge_rt ha
        omega
      · have hzeq : NSeq a k = Rt a + 1 := by omega
        have hstep : NSeq a (k + 1) = Nf (Xc a) (NSeq a k) := rfl
        rw [hstep, hzeq]
        have hF := f_top (by omega : 1 ≤ Rt a)
        have hrs := sd_ge_rt ha
        omega

/-- The Newton step arguments always stay in range. -/
theorem range_ok {a z : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1)
    (hlo : Rt a - 1 ≤ z) (hhi : z ≤ Sd a + 1) :
    Xc a / z + z ≤ 2 ^ 167 - 1 := by
  have hr100k := rt_ge ha
  have hq4 := q4_le ha
  have hzpos : (0 : Nat) < Rt a - 1 := by omega
  have hqdiv : Xc a / z ≤ Xc a / (Rt a - 1) :=
    Nat.div_le_div_left hlo hzpos
  have hq : Xc a / z ≤ Rt a + 4 := Nat.le_trans hqdiv hq4
  have hrt := rt_lt hM
  have hrB : Rt a ≤ 2 ^ 101 - 1 := by omega
  have h1 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hM
  have h2 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
  have hSdB : Sd a ≤ (2 ^ 166 - 1) + 5 * 10 ^ 9 := by
    unfold Sd
    omega
  have h4 : Xc a / z + z ≤ (Rt a + 4) + (Sd a + 1) :=
    Nat.add_le_add hq hhi
  have p1 : (2 : Nat) ^ 101 ≤ 2 ^ 160 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  have p2 : 5 * 10 ^ 9 + 4 ≤ (2 : Nat) ^ 160 := by decide
  have p3 : (2 : Nat) ^ 160 + 2 ^ 160 = 2 ^ 161 := by decide
  have p4 : (2 : Nat) ^ 161 < 2 ^ 166 :=
    Nat.pow_lt_pow_right (by decide) (by decide)
  have p5 : (2 : Nat) ^ 166 + 2 ^ 166 = 2 ^ 167 := by decide
  generalize Rt a = R at h4 hrB
  generalize Xc a / z = Q at h4 ⊢
  omega

/-- The gap to `r + 1` halves at each step above `r + 1`. -/
theorem reach_bound {a : Nat} :
    ∀ k, (∀ j, j < k → Rt a + 2 ≤ NSeq a j) →
      NSeq a k - (Rt a + 1) ≤ (Sd a - (Rt a + 1)) / 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : NSeq a 0 = Sd a := rfl
    rw [h0, Nat.pow_zero, Nat.div_one]
    exact Nat.le_refl _
  | succ k ih =>
    intro hall
    have hk : ∀ j, j < k → Rt a + 2 ≤ NSeq a j :=
      fun j hj => hall j (by omega)
    have hih := ih hk
    have hkk := hall k (by omega)
    have hhalf : 2 * NSeq a (k + 1) ≤ NSeq a k + (Rt a + 1) := by
      rw [nseq_succ]
      exact halve hkk
    have hdiv : (Sd a - (Rt a + 1)) / 2 ^ k / 2
        = (Sd a - (Rt a + 1)) / 2 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.succ_eq_add_one, Nat.pow_succ]
    have step1 : NSeq a (k + 1) - (Rt a + 1)
        ≤ (NSeq a k - (Rt a + 1)) / 2 := by
      generalize Rt a = R at hhalf ⊢
      omega
    have step2 : (NSeq a k - (Rt a + 1)) / 2
        ≤ ((Sd a - (Rt a + 1)) / 2 ^ k) / 2 :=
      Nat.div_le_div_right hih
    rw [← hdiv]
    generalize Rt a = R at step1 step2 ⊢
    omega

/-- The iterates reach `r + 1` within 167 steps. -/
theorem reached {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    ∃ K, K ≤ 167 ∧ NSeq a K ≤ Rt a + 1 := by
  rcases Classical.em (∃ K, K ≤ 167 ∧ NSeq a K ≤ Rt a + 1) with h | h
  · exact h
  · have hall : ∀ j, j < 168 → Rt a + 2 ≤ NSeq a j := by
      intro j hj
      by_cases hj' : NSeq a j ≤ Rt a + 1
      · exact absurd ⟨j, by omega, hj'⟩ h
      · omega
    have hb := @reach_bound a 167 (fun j hj => hall j (by omega))
    have hSd : Sd a - (Rt a + 1) < 2 ^ 167 := by
      have hle := sd_le hM
      omega
    have hD : (Sd a - (Rt a + 1)) / 2 ^ 167 = 0 := by
      have hn : (0 : Nat) < 2 ^ 167 := by decide
      have h1 : Sd a - (Rt a + 1) < 1 * 2 ^ 167 := by
        rw [Nat.one_mul]
        exact hSd
      have h2 := (Nat.div_lt_iff_lt_mul hn).mpr h1
      omega
    rw [hD] at hb
    have h167 := hall 167 (by omega)
    omega

/-- Once in `{r, r+1}`, all later iterates stay there. -/
theorem stay_closed {a : Nat} (ha : 1 ≤ a) {K : Nat}
    (hK : NSeq a (K + 1) = Rt a ∨ NSeq a (K + 1) = Rt a + 1) :
    ∀ n, NSeq a (K + 1 + n) = Rt a ∨ NSeq a (K + 1 + n) = Rt a + 1 := by
  have hr100k := rt_ge ha
  have hr1 : 1 ≤ Rt a := by omega
  intro n
  induction n with
  | zero =>
    have h0 : K + 1 + 0 = K + 1 := by omega
    rw [h0]
    exact hK
  | succ n ih =>
    have e : K + 1 + (n + 1) = (K + 1 + n) + 1 := by omega
    rw [e, nseq_succ]
    rcases ih with h | h
    · rw [h]; exact f_r hr1
    · rw [h]; exact Or.inl (f_top hr1)

/-- Previous iterate (`a` at step zero). -/
def Yq (a : Nat) : Nat → Nat
  | 0 => a
  | n + 1 => NSeq a n

theorem Yq_succ (a n : Nat) : Yq a (n + 1) = NSeq a n := rfl

/-- One loop step from explicit states follows the Newton sequence. -/
theorem loop_step_ok {a y z : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1)
    {f : Nat} (hz : 0 < z) (hne : z ≠ y)
    (hrange : a * 10 ^ 10 / z + z ≤ 2 ^ 167 - 1) :
    loop (a : Int) (f + 1) ((y : Nat) : Int) ((z : Nat) : Int)
    = loop (a : Int) f (((z : Nat)) : Int)
      ((((Nf (Xc a) z : Nat))) : Int) := by
  have h := loop_step (f) (a := a) (y := y) (z := z) hz hne hrange
  have hN : Nf (Xc a) z = (a * 10 ^ 10 / z + z) / 2 := rfl
  rw [← hN] at h
  exact h

/-- The first loop step from the seed. -/
theorem loop_step_zero {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1)
    {f : Nat} (hne : Sd a ≠ a) :
    loop (a : Int) (f + 1) ((a : Nat) : Int) (((Sd a : Nat)) : Int)
    = loop (a : Int) f (((Sd a : Nat)) : Int) (((NSeq a 1 : Nat)) : Int) := by
  have hz : 0 < Sd a := sd_pos a
  have hlo : Rt a - 1 ≤ Sd a := by
    have h0 := nseq_ge ha 0
    have h00 : NSeq a 0 = Sd a := rfl
    rwa [h00] at h0
  have hrange2 : a * 10 ^ 10 / Sd a + Sd a ≤ 2 ^ 167 - 1 :=
    range_ok ha hM hlo (by omega : Sd a ≤ Sd a + 1)
  have h := loop_step (f) (a := a) (y := a) (z := Sd a) hz hne hrange2
  have hN : NSeq a 1 = (a * 10 ^ 10 / Sd a + Sd a) / 2 := rfl
  rw [← hN] at h
  exact h

/-- The minimum of two casts in `{r, r+1}` (not both `r+1`) is `r`. -/
theorem final_min {a : Nat} {u v : Nat}
    (hu : u = Rt a ∨ u = Rt a + 1) (hv : v = Rt a ∨ v = Rt a + 1)
    (hne : ¬ (u = Rt a + 1 ∧ v = Rt a + 1)) :
    (fun y z => if y < z then y else z) (((u : Nat)) : Int) (((v : Nat)) : Int)
    = (((Rt a : Nat)) : Int) := by
  rcases hu with h | h <;> rcases hv with h' | h'
  · rw [h, h']
    show (if ((((Rt a : Nat))) : Int) < ((((Rt a : Nat))) : Int) then _ else _) = _
    rw [if_neg (by omega)]
  · rw [h, h']
    show (if ((((Rt a : Nat))) : Int) < ((((Rt a + 1 : Nat))) : Int) then _ else _) = _
    rw [if_pos (Int.ofNat_lt.mpr (by omega))]
  · rw [h, h']
    show (if ((((Rt a + 1 : Nat))) : Int) < ((((Rt a : Nat))) : Int) then _ else _) = _
    rw [if_neg (by omega)]
  · exact absurd ⟨h, h'⟩ hne

theorem self_seed {a : Nat} (ha : 1 ≤ a) (h : Sd a = a) : a = Rt a := by
  have ha10 : a = 10 ^ 10 - 1 ∨ a = 10 ^ 10 := by
    unfold Sd at h
    omega
  rcases ha10 with h9 | h10
  · subst h9
    apply sqrt_eq_of_sq
    · have eX : Xc (10 ^ 10 - 1) = 99999999990000000000 := by decide
      rw [eX]
      decide
    · have eX : Xc (10 ^ 10 - 1) = 99999999990000000000 := by decide
      rw [eX]
      decide
  · subst h10
    apply sqrt_eq_of_sq
    · have eX : Xc (10 ^ 10) = 100000000000000000000 := by decide
      rw [eX]
      decide
    · have eX : Xc (10 ^ 10) = 100000000000000000000 := by decide
      rw [eX]
      decide

/-- The loop from any reachable state maps to the floor root. -/
theorem loop_min {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    ∀ m k, k + m = 256 →
    ((loop (a : Int) m (((Yq a k : Nat)) : Int) (((NSeq a k : Nat)) : Int)).map
      (fun p : Int × Int => (fun y z => if y < z then y else z) p.1 p.2))
    = some (((Rt a : Nat)) : Int) := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hk256 : k = 256 := by omega
    subst hk256
    have hY : Yq a 256 = NSeq a 255 := Yq_succ a 255
    have hloop : loop (a : Int) 0 (((Yq a 256 : Nat)) : Int) (((NSeq a 256 : Nat)) : Int)
        = some (((((Yq a 256 : Nat)) : Int), (((NSeq a 256 : Nat)) : Int))) := rfl
    rw [hloop, Option.map_some, hY]
    obtain ⟨K, hKle, hKle2⟩ := reached ha hM
    have hr100k := rt_ge ha
    have hKmem : NSeq a (K + 1) = Rt a ∨ NSeq a (K + 1) = Rt a + 1 := by
      have h := step_close ha (nseq_ge ha K) hKle2
      rw [nseq_succ]
      exact h
    have e255 : (255 : Nat) = K + 1 + (254 - K) := by omega
    have e256 : (256 : Nat) = K + 1 + (255 - K) := by omega
    have h255 : NSeq a 255 = Rt a ∨ NSeq a 255 = Rt a + 1 := by
      rw [e255]; exact stay_closed ha hKmem _
    have h256 : NSeq a 256 = Rt a ∨ NSeq a 256 = Rt a + 1 := by
      rw [e256]; exact stay_closed ha hKmem _
    have hne : ¬ (NSeq a 255 = Rt a + 1 ∧ NSeq a 256 = Rt a + 1) := by
      intro hc
      have h1 : NSeq a 256 = Nf (Xc a) (NSeq a 255) := nseq_succ a 255
      have hr1 : 1 ≤ Rt a := by omega
      rw [hc.1, hc.2, f_top hr1] at h1
      omega
    have hfin := final_min h255 h256 hne
    exact congrArg some hfin
  | succ m ih =>
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      have hY0 : Yq a 0 = a := rfl
      have hN0 : NSeq a 0 = Sd a := rfl
      rw [hY0, hN0]
      by_cases hstop : Sd a = a
      · have hrw : a = Rt a := self_seed ha hstop
        have hSd : Sd a = Rt a := by rw [hstop]; exact hrw
        have hloop : loop (a : Int) (m + 1) (((a : Nat)) : Int) (((Sd a : Nat)) : Int)
            = some (((((a : Nat)) : Int), (((Sd a : Nat)) : Int))) := by
          rw [hstop]; exact loop_stop _ _ _
        rw [hloop, Option.map_some]
        have hu : a = Rt a ∨ a = Rt a + 1 := Or.inl hrw
        have hv : Sd a = Rt a ∨ Sd a = Rt a + 1 := Or.inl hSd
        have hne : ¬ (a = Rt a + 1 ∧ Sd a = Rt a + 1) := by
          intro hc
          omega
        have hfin := final_min hu hv hne
        exact congrArg some hfin
      · have hstep := loop_step_zero ha hM (f := m) hstop
        rw [hstep]
        have hkm : 1 + m = 256 := by omega
        have hYq1 : Yq a 1 = Sd a := rfl
        rw [← hYq1]
        exact ih 1 hkm
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one.mpr (by omega : 0 < k)
      by_cases hstop : NSeq a (j + 1) = Yq a (j + 1)
      · have hYq : Yq a (j + 1) = NSeq a j := rfl
        rw [hYq] at hstop
        have hF : Nf (Xc a) (NSeq a j) = NSeq a j := by
          rw [← nseq_succ]; exact hstop
        have hw1 : 1 ≤ NSeq a j := by
          have hlo := nseq_ge ha j; have hr := rt_ge ha; omega
        have hw : NSeq a j = Rt a := f_fix hw1 hF
        have hNz : NSeq a (j + 1) = Rt a := by rw [hstop]; exact hw
        rw [hYq, hw, hNz, loop_stop, Option.map_some]
        congr 1
        show (if ((((Rt a : Nat))) : Int) < ((((Rt a : Nat))) : Int) then _ else _) = _
        rw [if_neg (by omega)]
      · have hYq : Yq a (j + 1) = NSeq a j := rfl
        have hz : 0 < NSeq a (j + 1) := by
          have hlo := nseq_ge ha (j + 1); have hr := rt_ge ha; omega
        have hrange : Xc a / NSeq a (j + 1) + NSeq a (j + 1) ≤ 2 ^ 167 - 1 :=
          range_ok ha hM (nseq_ge ha (j + 1)) (nseq_le1 ha hM (j + 1))
        have hstep := loop_step_ok ha hM (y := Yq a (j + 1)) (z := NSeq a (j + 1))
          (f := m) hz hstop hrange
        rw [hstep]
        have hkm : (j + 1 + 1) + m = 256 := by omega
        exact ih (j + 1 + 1) hkm

end Newton

open Newton

/-- Value of the routine on a positive decimal: the floor root. -/
theorem sqrt_pos_val {a : Nat} (ha : 0 < a) (hM : a ≤ 2 ^ 167 - 1) :
    sqrt (a : Int) = some (((Rt a : Nat)) : Int) := by
  show vyperSqrtWith (fun y z => if y < z then y else z) (a : Int) = _
  rw [vyperSqrtWith_pos _ ha hM]
  exact loop_min (by omega) hM 256 0 (by omega)

/-- Value of the routine at zero. -/
theorem sqrt_zero : sqrt 0 = some 0 := by
  show vyperSqrtWith (fun y z => if y < z then y else z) 0 = _
  unfold vyperSqrtWith
  rw [if_neg (by omega), if_pos rfl]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hxr
  by_cases hneg : x < 0
  · have hnn : sqrt x = none := by
      show vyperSqrtWith (fun y z => if y < z then y else z) x = _
      unfold vyperSqrtWith
      rw [if_pos hneg]
    rw [hnn] at hxr
    cases hxr
  · have h0 : 0 ≤ x := by omega
    by_cases heq : x = 0
    · subst heq
      rw [sqrt_zero] at hxr
      have hr : (0 : Int) = r := Option.some.inj hxr
      subst hr
      decide
    · have hex : ∃ a : Nat, x = (a : Int) := ⟨x.toNat, (Int.toNat_of_nonneg h0).symm⟩
      obtain ⟨a, hx_eq⟩ := hex
      have hapos : 0 < a := by omega
      have hM : a ≤ 2 ^ 167 - 1 := by
        have h1 := hx.2
        rw [max_decimal_eq, hx_eq] at h1
        omega
      have hval := sqrt_pos_val hapos hM
      rw [hx_eq] at hxr
      rw [hval] at hxr
      have hr : (((Rt a : Nat)) : Int) = r := Option.some.inj hxr
      rw [hx_eq, ← hr]
      have hR : Rt a * Rt a ≤ Xc a := Nat.sqrt_le (Xc a)
      have hRc : ((((Rt a * Rt a : Nat))) : Int) ≤ (((Xc a : Nat)) : Int) :=
        Int.ofNat_le.mpr hR
      rw [divisor_eq, ← Int.natCast_mul, ← Int.natCast_mul]
      exact hRc

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hxr
  by_cases hneg : x < 0
  · have hnn : sqrt x = none := by
      show vyperSqrtWith (fun y z => if y < z then y else z) x = _
      unfold vyperSqrtWith
      rw [if_pos hneg]
    rw [hnn] at hxr
    cases hxr
  · have h0 : 0 ≤ x := by omega
    by_cases heq : x = 0
    · subst heq
      rw [sqrt_zero] at hxr
      have hr : (0 : Int) = r := Option.some.inj hxr
      subst hr
      decide
    · have hex : ∃ a : Nat, x = (a : Int) := ⟨x.toNat, (Int.toNat_of_nonneg h0).symm⟩
      obtain ⟨a, hx_eq⟩ := hex
      have hapos : 0 < a := by omega
      have hM : a ≤ 2 ^ 167 - 1 := by
        have h1 := hx.2
        rw [max_decimal_eq, hx_eq] at h1
        omega
      have hval := sqrt_pos_val hapos hM
      rw [hx_eq] at hxr
      rw [hval] at hxr
      have hr : (((Rt a : Nat)) : Int) = r := Option.some.inj hxr
      rw [hx_eq, ← hr]
      have hU : a * 10 ^ 10 < (Rt a + 1) * (Rt a + 1) := Nat.lt_succ_sqrt (Xc a)
      have hUc : ((((a * 10 ^ 10 : Nat))) : Int)
          < ((((Rt a + 1) * (Rt a + 1) : Nat)) : Int) :=
        Int.ofNat_lt.mpr hU
      rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_add, Int.ofNat_one,
        ← divisor_eq] at hUc
      exact hUc

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx h0
  by_cases heq : x = 0
  · subst heq
    rw [sqrt_zero]
    rfl
  · have hpos : 0 < x := by omega
    have hex : ∃ a : Nat, x = (a : Int) := ⟨x.toNat, (Int.toNat_of_nonneg h0).symm⟩
    obtain ⟨a, hx_eq⟩ := hex
    have hapos : 0 < a := by omega
    have hM : a ≤ 2 ^ 167 - 1 := by
      have h1 := hx.2
      rw [max_decimal_eq, hx_eq] at h1
      omega
    rw [hx_eq, sqrt_pos_val hapos hM]
    rfl

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith (fun y z => if y < z then y else z) x = _
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨(fun y z => if y < z then y else z), fun x => rfl⟩

end VyperSqrt
