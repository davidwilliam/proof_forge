import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.Rounding
/-!
Fixed `VyperSqrt.sqrt`: the deployed Babylonian loop followed by the minimum of the last two
iterates (pull request 4486), so the result is the root rounded down.
-/
namespace VyperSqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  rw [ite_eq_left (by omega : x < 0)]

theorem req_deployed_loop : DeployedLoop sqrt := ⟨_, fun x => rfl⟩

/-! ## Natural-number mirror of the iteration -/

/-- `A = x * 10^10`: the scaled radicand. -/
def floorA (a : Nat) : Nat := a * 10 ^ 10

/-- The seed `x / 2 + 5 * 10^9`. -/
def seedN (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- The true floor root of the scaled radicand. -/
def rootN (a : Nat) : Nat := Nat.sqrt (floorA a)

/-- One Newton step on naturals. -/
def stepN (a x : Nat) : Nat := ProofForgeFin.Sqrt.newton (floorA a) x

/-- The Newton sequence from the seed. -/
def seqN (a : Nat) : Nat → Nat
  | 0 => seedN a
  | n + 1 => stepN a (seqN a n)

/-- The loop trajectory: `seqP 0 = a`, `seqP (n+1) = seqN n`. -/
def seqP (a : Nat) : Nat → Nat
  | 0 => a
  | n + 1 => seqN a n

theorem rootN_le_seed (a : Nat) : rootN a ≤ seedN a := by
  have hAM := ProofForgeFin.Sqrt.four_mul_le_sq (a / 2) (5 * 10 ^ 9)
  have hmod : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
  have hmod2 : a % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt a (by decide))
  have hle : rootN a < seedN a + 1 := by
    have h := ProofForgeFin.Sqrt.sqrt_lt_of_lt_mul_self (m := seedN a + 1) (a := floorA a)
    have h2 : floorA a < (seedN a + 1) * (seedN a + 1) := by
      unfold floorA seedN
      grind
    exact h h2
  omega

theorem rootN_ge (a : Nat) (ha : 1 ≤ a) : 10 ^ 5 ≤ rootN a := by
  have h1 : (10 ^ 5) * (10 ^ 5) ≤ floorA a := by
    unfold floorA
    grind
  exact ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le h1

theorem rootN_lt (a : Nat) (h : a ≤ 2 ^ 167 - 1) : rootN a < 2 ^ 101 := by
  apply ProofForgeFin.Sqrt.sqrt_lt_of_lt_mul_self (m := 2 ^ 101)
  have h10 : (10 : Nat) ^ 10 < 2 ^ 34 := by decide
  have hpos : (0 : Nat) < 2 ^ 167 - 1 := by decide
  have h1 : floorA a ≤ (2 ^ 167 - 1) * 10 ^ 10 := by
    unfold floorA
    exact Nat.mul_le_mul_right _ h
  have h2 : (2 ^ 167 - 1) * 10 ^ 10 < 2 ^ 167 * 2 ^ 34 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left h10 hpos)
      (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  have h3 : (2 : Nat) ^ 167 * 2 ^ 34 ≤ 2 ^ (2 * 101) := by
    have e : (2 : Nat) ^ 167 * 2 ^ 34 = 2 ^ 201 := by
      have hpa := Nat.pow_add 2 167 34
      omega
    have l : (2 : Nat) ^ 201 ≤ 2 ^ (2 * 101) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h4 : floorA a < 2 ^ (2 * 101) := Nat.lt_of_le_of_lt h1 (Nat.lt_of_lt_of_le h2 h3)
  have h5 : floorA a < (2 ^ 101) * (2 ^ 101) := by
    have e : (2 : Nat) ^ (2 * 101) = (2 ^ 101) * (2 ^ 101) := by
      have hpa := Nat.pow_add 2 101 101
      omega
    rw [e] at h4
    exact h4
  exact h5

theorem seedN_le (a : Nat) (h : a ≤ 2 ^ 167 - 1) : seedN a ≤ 2 ^ 167 - 1 := by
  have e : 5 * 10 ^ 9 + (2 ^ 167 - 1) / 2 ≤ 2 ^ 167 - 1 := by decide
  have h2 := Nat.div_le_div_right (c := 2) h
  unfold seedN
  generalize 2 ^ 167 - 1 = M at *
  omega

theorem unifB (a : Nat) (h : a ≤ 2 ^ 167 - 1) :
    rootN a + seedN a + 3 ≤ 2 ^ 167 - 1 := by
  have hs : rootN a < 2 ^ 101 := rootN_lt a h
  have hz : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right (c := 2) h
  have c : 2 ^ 101 + (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 + 2 ≤ 2 ^ 167 - 1 := by decide
  have hs2 : seedN a = a / 2 + 5 * 10 ^ 9 := rfl
  generalize 2 ^ 167 - 1 = M at *
  generalize (2 ^ 101 : Nat) = P at *
  omega

theorem quot_le (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) {z : Nat}
    (hz : 0 < z) (hzs : rootN a ≤ z) : floorA a / z ≤ rootN a + 2 := by
  have hs : 0 < rootN a := Nat.lt_of_lt_of_le (by decide : 0 < 10 ^ 5) (rootN_ge a ha)
  have hup : floorA a < (rootN a + 1) * (rootN a + 1) := Nat.lt_succ_sqrt _
  have heq : (rootN a + 1) * (rootN a + 1) = rootN a * (rootN a + 2) + 1 := by grind
  have hA : floorA a ≤ rootN a * (rootN a + 2) := by omega
  have hB : floorA a ≤ (rootN a + 2) * z := by
    have hm : rootN a * (rootN a + 2) ≤ z * (rootN a + 2) := Nat.mul_le_mul_right _ hzs
    have hc : z * (rootN a + 2) = (rootN a + 2) * z := Nat.mul_comm _ _
    omega
  exact ProofForgeFin.div_le_of_le_mul' hB

theorem seq_ge (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) (n : Nat) :
    rootN a ≤ seqN a n := by
  induction n with
  | zero => exact rootN_le_seed a
  | succ n ih =>
    have hp : 0 < seqN a n :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide : 0 < 10 ^ 5) (rootN_ge a ha)) ih
    exact ProofForgeFin.Sqrt.sqrt_le_newton hp

theorem seq_pos (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) (n : Nat) :
    0 < seqN a n :=
  Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide : 0 < 10 ^ 5) (rootN_ge a ha)) (seq_ge a ha h n)

theorem seq_le (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) (n : Nat) :
    seqN a n ≤ seedN a + 1 := by
  induction n with
  | zero => exact Nat.le_succ _
  | succ n ih =>
    have hq : floorA a / seqN a n ≤ rootN a + 2 :=
      quot_le a ha h (seq_pos a ha h n) (seq_ge a ha h n)
    have hs : rootN a ≤ seedN a := rootN_le_seed a
    have hstep : stepN a (seqN a n) = (seqN a n + floorA a / seqN a n) / 2 := rfl
    show stepN a (seqN a n) ≤ seedN a + 1
    omega

theorem seq_sum (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) (n : Nat) :
    floorA a / seqN a n + seqN a n ≤ 2 ^ 167 - 1 := by
  have hq : floorA a / seqN a n ≤ rootN a + 2 :=
    quot_le a ha h (seq_pos a ha h n) (seq_ge a ha h n)
  have hl : seqN a n ≤ seedN a + 1 := seq_le a ha h n
  have hu := unifB a h
  omega

theorem err_half (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) (n : Nat) :
    seqN a (n + 1) - rootN a ≤ (seqN a n - rootN a) / 2 + 1 :=
  ProofForgeFin.Sqrt.newton_sub_sqrt_le_half
    (seq_pos a ha h n) (seq_ge a ha h n)

theorem err_bound (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) (n : Nat) :
    seqN a n - rootN a ≤ (seedN a - rootN a) / 2 ^ n + 2 := by
  induction n with
  | zero =>
    have h0 : seqN a 0 = seedN a := rfl
    have hp : (2 : Nat) ^ 0 = 1 := by decide
    rw [h0, hp, Nat.div_one]
    omega
  | succ n ih =>
    have hs := err_half a ha h n
    have h2 : ((seedN a - rootN a) / 2 ^ n + 2) / 2
        = (seedN a - rootN a) / 2 ^ n / 2 + 1 := by omega
    have h3 : (seedN a - rootN a) / 2 ^ n / 2 = (seedN a - rootN a) / 2 ^ (n + 1) := by
      have e2 : (2 : Nat) ^ n * 2 = 2 ^ (n + 1) := by
        have hpa := Nat.pow_add 2 n 1
        rw [Nat.pow_one] at hpa
        exact hpa
      rw [Nat.div_div_eq_div_mul, e2]
    omega

theorem reach167 (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) :
    seqN a 167 - rootN a ≤ 2 := by
  have he := err_bound a ha h 167
  have hlt : seedN a - rootN a < 2 ^ 167 := by
    have hs := seedN_le a h
    have hr : rootN a ≤ seedN a := rootN_le_seed a
    have h167 : (2 : Nat) ^ 167 - 1 < 2 ^ 167 := by omega
    omega
  have hz : (seedN a - rootN a) / 2 ^ 167 = 0 := Nat.div_eq_of_lt hlt
  omega

theorem enter168 (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) :
    rootN a ≤ seqN a 168 ∧ seqN a 168 ≤ rootN a + 1 := by
  refine ⟨seq_ge a ha h 168, ?_⟩
  have h167 := reach167 a ha h
  have hs : 10 ^ 5 ≤ rootN a := rootN_ge a ha
  have hd : (seqN a 167 - rootN a) * (seqN a 167 - rootN a) ≤ 2 * rootN a := by
    have h4 : (seqN a 167 - rootN a) * (seqN a 167 - rootN a) ≤ 2 * 2 :=
      Nat.mul_le_mul h167 h167
    omega
  have hle := ProofForgeFin.Sqrt.newton_le_sqrt_add_one
    (seq_pos a ha h 167) (seq_ge a ha h 167) hd
  have hle2 : seqN a 168 ≤ rootN a + 1 := hle
  exact hle2

theorem stay (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) (n : Nat) :
    rootN a ≤ seqN a (168 + n) ∧ seqN a (168 + n) ≤ rootN a + 1 := by
  induction n with
  | zero =>
    have hz : 168 + 0 = 168 := by omega
    rw [hz]
    exact enter168 a ha h
  | succ n ih =>
    have hsucc : 168 + (n + 1) = (168 + n) + 1 := by omega
    rw [hsucc]
    have hx : 0 < seqN a (168 + n) := seq_pos a ha h _
    have hm := ProofForgeFin.Sqrt.newton_of_mem hx ih.1 ih.2
    rcases hm with hmem | ⟨heqx, hmem, hcond⟩
    · have h0 : stepN a (seqN a (168 + n)) = rootN a := hmem
      show rootN a ≤ stepN a (seqN a (168 + n)) ∧ stepN a (seqN a (168 + n)) ≤ rootN a + 1
      omega
    · have h1 : seqN a (168 + n) = rootN a := heqx
      have h2 : stepN a (seqN a (168 + n)) = rootN a + 1 := hmem
      show rootN a ≤ stepN a (seqN a (168 + n)) ∧ stepN a (seqN a (168 + n)) ≤ rootN a + 1
      omega

theorem edge_eq (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) (he : a = seedN a) :
    a = rootN a := by
  have hmod : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
  have hrng : a % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt a (by decide))
  have hseed : seedN a = a / 2 + 5 * 10 ^ 9 := rfl
  have hqr : a / 2 + a % 2 = 5 * 10 ^ 9 := by omega
  have ha10 : a = 10 ^ 10 - a % 2 := by omega
  rcases Nat.lt_or_ge (a % 2) 1 with hr0 | hr1
  · have hr0' : a % 2 = 0 := by omega
    have haa : a = 10 ^ 10 := by omega
    rw [haa]
    have hrw : floorA (10 ^ 10) = (10 ^ 10) * (10 ^ 10) := rfl
    have hs : Nat.sqrt (floorA (10 ^ 10)) = 10 ^ 10 := by
      rw [hrw]
      exact ProofForgeFin.Sqrt.sqrt_mul_self _
    exact hs.symm
  · have hr1' : a % 2 = 1 := by omega
    have haa : a = 10 ^ 10 - 1 := by omega
    rw [haa]
    have h1 : (10 ^ 10 - 1) * (10 ^ 10 - 1) ≤ (10 ^ 10 - 1) * 10 ^ 10 := by grind
    have h2 : (10 ^ 10 - 1) * 10 ^ 10 < ((10 ^ 10 - 1) + 1) * ((10 ^ 10 - 1) + 1) := by grind
    exact (ProofForgeFin.Sqrt.sqrt_eq_of_bounds h1 h2).symm

theorem seqP_zero (a : Nat) : seqP a 0 = a := rfl
theorem seqP_succ (a j : Nat) : seqP a (j + 1) = seqN a j := rfl
theorem seqN_zero (a : Nat) : seqN a 0 = seedN a := rfl
theorem seqN_succ (a j : Nat) : seqN a (j + 1) = stepN a (seqN a j) := rfl

theorem seqP_adv (a i : Nat) :
    (a * 10 ^ 10 / seqP a (i + 1) + seqP a (i + 1)) / 2 = seqP a ((i + 1) + 1) := by
  have e0 : seqP a (i + 1) = seqN a i := seqP_succ a i
  have e1 : seqP a ((i + 1) + 1) = seqN a (i + 1) := seqP_succ a (i + 1)
  have e2 : seqN a (i + 1) = stepN a (seqN a i) := seqN_succ a i
  have e3 : stepN a (seqN a i) = (seqN a i + a * 10 ^ 10 / seqN a i) / 2 := rfl
  rw [e0, e1, e2, e3, Nat.add_comm (a * 10 ^ 10 / seqN a i) (seqN a i)]

theorem loop_some_aux (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) :
    ∀ (r i : Nat),
      (loop (a : Int) r ((seqP a i : Nat) : Int) ((seqP a (i + 1) : Nat) : Int)).isSome := by
  intro r
  induction r with
  | zero =>
    intro i
    rfl
  | succ r ih =>
    intro i
    by_cases heq : seqP a (i + 1) = seqP a i
    · have hcc : ((seqP a (i + 1) : Nat) : Int) = ((seqP a i : Nat) : Int) := by rw [heq]
      rw [hcc]
      have hs := loop_stop (a : Int) r ((seqP a i : Nat) : Int)
      rw [hs]
      rfl
    · have hstep := VyperSqrt.loop_step (a := a) (y := seqP a i) (z := seqP a (i + 1)) r
        (show 0 < seqP a (i + 1) from seq_pos a ha h i)
        heq
        (show a * 10 ^ 10 / seqP a (i + 1) + seqP a (i + 1) ≤ 2 ^ 167 - 1 from
          seq_sum a ha h i)
      have hz2 : (((a * 10 ^ 10 / seqP a (i + 1) + seqP a (i + 1)) / 2 : Nat) : Int)
          = ((seqP a ((i + 1) + 1) : Nat) : Int) := congrArg _ (seqP_adv a i)
      rw [hstep, hz2]
      exact ih (i + 1)

theorem loop_min (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) :
    ∀ (r i : Nat), 256 ≤ r + i → ∀ (p : Int × Int),
      loop (a : Int) r ((seqP a i : Nat) : Int) ((seqP a (i + 1) : Nat) : Int) = some p →
      (if p.1 < p.2 then p.1 else p.2) = ((rootN a : Nat) : Int) := by
  intro r
  induction r with
  | zero =>
    intro i hri p e
    have hloop0 : loop (a : Int) 0 ((seqP a i : Nat) : Int) ((seqP a (i + 1) : Nat) : Int)
        = some ((((seqP a i : Nat)) : Int), (((seqP a (i + 1) : Nat)) : Int)) := rfl
    rw [hloop0] at e
    have hp : p = ((((seqP a i : Nat)) : Int), (((seqP a (i + 1) : Nat)) : Int)) :=
      Option.some_inj.mp e.symm
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    subst hp
    show (if ((seqP a (j + 1) : Nat) : Int) < ((seqP a (j + 1 + 1) : Nat) : Int)
      then ((seqP a (j + 1) : Nat) : Int) else ((seqP a (j + 1 + 1) : Nat) : Int))
      = ((rootN a : Nat) : Int)
    rw [seqP_succ, seqP_succ, seqN_succ]
    have hj : 168 ≤ j := by omega
    have hjj : 168 + (j - 168) = j := by omega
    have hstay := stay a ha h (j - 168)
    rw [hjj] at hstay
    have hmin := ProofForgeFin.Sqrt.min_newton_eq_sqrt (a := floorA a) (x := seqN a j)
      (seq_pos a ha h j) hstay.1 hstay.2
    have hmin' : min (seqN a j) (stepN a (seqN a j)) = rootN a := hmin
    by_cases hlt : seqN a j < stepN a (seqN a j)
    · have hltI : ((seqN a j : Nat) : Int) < ((stepN a (seqN a j) : Nat) : Int) :=
        (Int.ofNat_lt).mpr hlt
      rw [if_pos hltI]
      have hmj : seqN a j = rootN a := by omega
      rw [hmj]
    · have hle : stepN a (seqN a j) ≤ seqN a j := by omega
      have hnge : ¬ ((seqN a j : Nat) : Int) < ((stepN a (seqN a j) : Nat) : Int) := by
        intro c
        exact hlt ((Int.ofNat_lt).mp c)
      rw [if_neg hnge]
      have hmj : stepN a (seqN a j) = rootN a := by omega
      rw [hmj]
  | succ r ih =>
    intro i hri p e
    by_cases heq : seqP a (i + 1) = seqP a i
    · have hcc : ((seqP a (i + 1) : Nat) : Int) = ((seqP a i : Nat) : Int) := by rw [heq]
      rw [hcc] at e
      have hstop := loop_stop (a : Int) r ((seqP a i : Nat) : Int)
      rw [hstop] at e
      have hp : p = ((((seqP a i : Nat)) : Int), (((seqP a i : Nat)) : Int)) :=
        Option.some_inj.mp e.symm
      subst hp
      show (if ((seqP a i : Nat) : Int) < ((seqP a i : Nat) : Int)
        then ((seqP a i : Nat) : Int) else ((seqP a i : Nat) : Int))
        = ((rootN a : Nat) : Int)
      have hnn : ¬ ((seqP a i : Nat) : Int) < ((seqP a i : Nat) : Int) := by omega
      rw [if_neg hnn]
      by_cases hi : i = 0
      · subst hi
        have heq0 : seqP a (0 + 1) = seqP a 0 := heq
        rw [seqP_succ, seqP_zero] at heq0
        have h20 : seqN a 0 = seedN a := seqN_zero a
        have hea : a = seedN a := by omega
        have hedge : a = rootN a := edge_eq a ha h hea
        have hW : ((seqP a 0 : Nat) : Int) = ((a : Nat) : Int) := by rw [seqP_zero]
        rw [hW]
        exact congrArg _ hedge
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have heq1 : seqP a (j + 1 + 1) = seqP a (j + 1) := heq
        rw [seqP_succ, seqP_succ] at heq1
        have heq2 : seqN a (j + 1) = seqN a j := heq1
        have hfp : ProofForgeFin.Sqrt.newton (floorA a) (seqN a j) = seqN a j := by
          show stepN a (seqN a j) = seqN a j
          rw [← seqN_succ a j]
          exact heq2
        have hfix := ProofForgeFin.Sqrt.eq_sqrt_of_newton_eq_self
          (seq_pos a ha h j) hfp
        have hfix2 : seqN a j = rootN a := hfix
        rw [seqP_succ, hfix2]
    · have hstep := VyperSqrt.loop_step (a := a) (y := seqP a i) (z := seqP a (i + 1)) r
        (show 0 < seqP a (i + 1) from seq_pos a ha h i)
        heq
        (show a * 10 ^ 10 / seqP a (i + 1) + seqP a (i + 1) ≤ 2 ^ 167 - 1 from
          seq_sum a ha h i)
      rw [hstep] at e
      have hz2 : (((a * 10 ^ 10 / seqP a (i + 1) + seqP a (i + 1)) / 2 : Nat) : Int)
          = ((seqP a ((i + 1) + 1) : Nat) : Int) := congrArg _ (seqP_adv a i)
      rw [hz2] at e
      have hri' : 256 ≤ r + (i + 1) := by omega
      exact ih (i + 1) hri' p e

theorem sqrt_zero : sqrt ((0 : Nat) : Int) = some 0 := by
  unfold sqrt vyperSqrtWith
  rw [if_neg (by decide), if_pos (by decide)]

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hdec hnn
  obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) := ⟨x.toNat, (Int.toNat_of_nonneg hnn).symm⟩
  have haM : a ≤ 2 ^ 167 - 1 := by
    have h2 : (a : Int) ≤ MAX_DECIMAL := by
      unfold IsDecimal at hdec
      exact hdec.2
    rw [max_decimal_eq] at h2
    exact (Int.ofNat_le).mp h2
  by_cases ha0 : a = 0
  · subst ha0
    show (sqrt ((0 : Nat) : Int)).isSome
    rw [sqrt_zero]
    rfl
  · have ha1 : 1 ≤ a := by omega
    have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z)
      (show 0 < a by omega) haM
    have hsq : sqrt (a : Int)
        = vyperSqrtWith (fun y z => if y < z then y else z) (a : Int) := rfl
    rw [hsq, hpos]
    have hL0 : ((seqP a 0 : Nat) : Int) = ((a : Nat) : Int) := by rw [seqP_zero]
    have hL1 : ((seqP a (0 + 1) : Nat) : Int) = (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int) := by
      rw [seqP_succ, seqN_zero]
      rfl
    have hL := loop_some_aux a ha1 haM 256 0
    rw [hL0, hL1] at hL
    rw [Option.isSome_map]
    exact hL

/-- The value returned on a positive input is the floor root. -/
theorem sqrt_eq_rootN (a : Nat) (ha : 1 ≤ a) (h : a ≤ 2 ^ 167 - 1) (r : Int)
    (hxr : sqrt (a : Int) = some r) : r = ((rootN a : Nat) : Int) := by
  have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z)
    (show 0 < a by omega) h
  have hsq : sqrt (a : Int)
      = vyperSqrtWith (fun y z => if y < z then y else z) (a : Int) := rfl
  rw [hsq, hpos] at hxr
  have hL0 : ((seqP a 0 : Nat) : Int) = ((a : Nat) : Int) := by rw [seqP_zero]
  have hL1 : ((seqP a (0 + 1) : Nat) : Int) = (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int) := by
    rw [seqP_succ, seqN_zero]
    rfl
  have hsome := loop_some_aux a ha h 256 0
  rw [hL0, hL1] at hsome
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  have hfin : (if p.1 < p.2 then p.1 else p.2) = r := by
    have hmap : (loop (a : Int) 256 (a : Int) (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)).map
        (fun q => if q.1 < q.2 then q.1 else q.2) = some r := hxr
    rw [hp] at hmap
    exact Option.some_inj.mp hmap
  have hroot := loop_min a ha h 256 0 (by omega) p (by rw [hL0, hL1]; exact hp)
  exact hfin.symm.trans hroot

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hdec hxr
  by_cases hneg : x < 0
  · unfold sqrt vyperSqrtWith at hxr
    rw [ite_eq_left hneg] at hxr
    cases hxr
  · have hnn : 0 ≤ x := by omega
    obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) := ⟨x.toNat, (Int.toNat_of_nonneg hnn).symm⟩
    by_cases ha0 : a = 0
    · subst ha0
      have h00 : sqrt ((0 : Nat) : Int) = some 0 := sqrt_zero
      rw [h00] at hxr
      have hr0 : r = 0 := Option.some_inj.mp hxr.symm
      subst hr0
      decide
    · have ha1 : 1 ≤ a := by omega
      have haM : a ≤ 2 ^ 167 - 1 := by
        have h2 : (a : Int) ≤ MAX_DECIMAL := by
          unfold IsDecimal at hdec
          exact hdec.2
        rw [max_decimal_eq] at h2
        exact (Int.ofNat_le).mp h2
      have hr := sqrt_eq_rootN a ha1 haM r hxr
      have hN : rootN a * rootN a ≤ floorA a := Nat.sqrt_le (floorA a)
      have castA : (((floorA a : Nat)) : Int) = (a : Int) * DIVISOR := by
        unfold floorA
        rw [divisor_eq]
        simp
      have castS : ((((rootN a) * (rootN a) : Nat)) : Int)
          = ((rootN a : Nat) : Int) * ((rootN a : Nat) : Int) := by simp
      have hI : ((((rootN a) * (rootN a) : Nat)) : Int)
          ≤ (((floorA a : Nat)) : Int) := (Int.ofNat_le).mpr hN
      rw [castS, castA] at hI
      rw [hr]
      exact hI

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hdec hxr
  by_cases hneg : x < 0
  · unfold sqrt vyperSqrtWith at hxr
    rw [ite_eq_left hneg] at hxr
    cases hxr
  · have hnn : 0 ≤ x := by omega
    obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) := ⟨x.toNat, (Int.toNat_of_nonneg hnn).symm⟩
    by_cases ha0 : a = 0
    · subst ha0
      have h00 : sqrt ((0 : Nat) : Int) = some 0 := sqrt_zero
      rw [h00] at hxr
      have hr0 : r = 0 := Option.some_inj.mp hxr.symm
      subst hr0
      decide
    · have ha1 : 1 ≤ a := by omega
      have haM : a ≤ 2 ^ 167 - 1 := by
        have h2 : (a : Int) ≤ MAX_DECIMAL := by
          unfold IsDecimal at hdec
          exact hdec.2
        rw [max_decimal_eq] at h2
        exact (Int.ofNat_le).mp h2
      have hr := sqrt_eq_rootN a ha1 haM r hxr
      have hN : floorA a < (rootN a + 1) * (rootN a + 1) := Nat.lt_succ_sqrt (floorA a)
      have castA : (((floorA a : Nat)) : Int) = (a : Int) * DIVISOR := by
        unfold floorA
        rw [divisor_eq]
        simp
      have castS1 : (((rootN a + 1) * (rootN a + 1) : Nat) : Int)
          = (((rootN a : Nat) : Int) + 1) * ((((rootN a : Nat)) : Int) + 1) := by simp
      have hI : (((floorA a : Nat)) : Int)
          < (((rootN a + 1) * (rootN a + 1) : Nat) : Int) := (Int.ofNat_lt).mpr hN
      rw [castA, castS1] at hI
      rw [hr]
      exact hI

