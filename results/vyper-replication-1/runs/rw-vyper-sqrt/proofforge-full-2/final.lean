import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
namespace VyperSqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

open ProofForgeFin.Sqrt in
/-- Scaled radicand on naturals. -/
def AN (a : Nat) : Nat := a * 10 ^ 10

/-- Integer square root of the scaled radicand. -/
def sN (a : Nat) : Nat := Nat.sqrt (AN a)

/-- Seed on naturals. -/
def z0N (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- Newton iterates on naturals. -/
def seqN (a : Nat) : Nat → Nat
  | 0 => z0N a
  | n + 1 => ProofForgeFin.Sqrt.newton (AN a) (seqN a n)

theorem z0N_pos (a : Nat) : 0 < z0N a := by
  have h5 : (5 : Nat) * 10 ^ 9 = 5000000000 := by decide
  unfold z0N
  omega

theorem z0N_le {a : Nat} (h : a ≤ 2 ^ 167 - 1) : z0N a ≤ 2 ^ 167 - 1 := by
  unfold z0N
  have e : 5 * 10 ^ 9 + (2 ^ 167 - 1) / 2 ≤ 2 ^ 167 - 1 := by decide
  have := Nat.div_le_div_right (c := 2) h
  generalize 2 ^ 167 - 1 = M at *
  omega

theorem sN_lt_pow {a : Nat} (h : a ≤ 2 ^ 167 - 1) : sN a < 2 ^ 101 := by
  unfold sN AN
  apply ProofForgeFin.Sqrt.sqrt_lt_two_pow (k := 101)
  have h10 : (10 : Nat) ^ 10 ≤ 2 ^ 34 := by decide
  have hsub : 2 ^ 167 - 1 < 2 ^ 167 := Nat.sub_lt (Nat.pow_pos (by decide : 0 < 2)) (by decide : 0 < 1)
  have h1 : a * 10 ^ 10 < 2 ^ 167 * 2 ^ 34 :=
    calc a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 2 ^ 34 := Nat.mul_le_mul h h10
    _ < 2 ^ 167 * 2 ^ 34 := Nat.mul_lt_mul_of_pos_right hsub (by decide : 0 < 2 ^ 34)
  have h2 : 2 ^ 167 * 2 ^ 34 ≤ 2 ^ (2 * 101) := by
    rw [← Nat.pow_add]
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    decide
  omega

theorem sN_ge_1e5 {a : Nat} (h : 1 ≤ a) : 100000 ≤ sN a := by
  unfold sN AN
  have e10 : (10 : Nat) ^ 10 = 10000000000 := by decide
  rw [e10]
  apply ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le (m := 100000)
  have e100 : (100000 : Nat) * 100000 = 1 * 10000000000 := by decide
  rw [e100]
  exact Nat.mul_le_mul h (Nat.le_refl _)

theorem sN_pos {a : Nat} (ha : 0 < a) : 0 < sN a := by
  have hA : 0 < AN a := by
    unfold AN
    exact Nat.mul_pos ha (Nat.pow_pos (by decide : 0 < 10))
  exact ProofForgeFin.Sqrt.sqrt_pos hA

theorem sN_le_z0N {a : Nat} : sN a ≤ z0N a := by
  unfold sN z0N AN
  have e10 : (10 : Nat) ^ 10 = 10000000000 := by decide
  have h5 : (5 : Nat) * 10 ^ 9 = 5000000000 := by decide
  rw [e10, h5]
  have hb : a * 10000000000 < (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1) := by
    have hmod : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
    have hr : a % 2 < 2 := Nat.mod_lt _ (by decide)
    rcases Nat.le_total (a / 2) 5000000000 with hle | hle
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have hqq : a / 2 * (a / 2) + 10000000000 * d
          = 25000000000000000000 + d * d := by grind
      have hexp : (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1)
          = a / 2 * (a / 2) + (10000000002 * (a / 2) + 5000000001 * 5000000001) := by
        grind
      rw [hexp]
      grind
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd] at hmod ⊢
      have amgm := ProofForgeFin.Sqrt.four_mul_le_sq (5000000000 + d) (5000000000 + 1)
      have hassoc : (5000000000 + d + 5000000000 + 1)
          = (5000000000 + d) + (5000000000 + 1) := by omega
      rw [hassoc]
      omega
  have hs : Nat.sqrt (a * 10000000000) < a / 2 + 5000000000 + 1 :=
    ProofForgeFin.Sqrt.sqrt_lt_of_lt_mul_self hb
  omega

theorem AN_div_le {a z : Nat} (hs : 0 < sN a) (hle : sN a ≤ z) :
    AN a / z ≤ sN a + 2 := by
  have hlt := Nat.lt_succ_sqrt (AN a)
  have hfold : Nat.sqrt (AN a) = sN a := rfl
  rw [hfold] at hlt
  have hexp : (sN a).succ * (sN a).succ = sN a * sN a + 2 * sN a + 1 := by
    grind
  rw [hexp] at hlt
  have hA : AN a ≤ sN a * sN a + 2 * sN a := by omega
  have h1 : AN a / z ≤ (sN a * sN a + 2 * sN a) / z := Nat.div_le_div_right hA
  have hfac : sN a * sN a + 2 * sN a = (sN a + 2) * sN a := by grind
  rw [hfac] at h1
  have h2 : (sN a + 2) * sN a / z ≤ (sN a + 2) * sN a / sN a :=
    Nat.div_le_div_left hle hs
  have h3 : (sN a + 2) * sN a / sN a = sN a + 2 :=
    Nat.mul_div_cancel _ hs
  omega

theorem sN_z0_sum_le {a : Nat} (h : a ≤ 2 ^ 167 - 1) :
    sN a + (z0N a + 4) ≤ 2 ^ 167 := by
  have hs101 : sN a < 2 ^ 101 := sN_lt_pow h
  have hz : z0N a ≤ 2 ^ 166 + 5000000000 := by
    unfold z0N
    have ha2 : a ≤ 2 ^ 167 := Nat.le_trans h (Nat.sub_le _ _)
    have e167 : (2 : Nat) ^ 167 = 2 ^ 166 * 2 := by
      rw [show 167 = 166 + 1 by decide, Nat.pow_succ]
    have h1 : a / 2 ≤ 2 ^ 167 / 2 := Nat.div_le_div_right ha2
    rw [e167] at h1
    have h2 : 2 ^ 166 * 2 / 2 = 2 ^ 166 := Nat.mul_div_cancel _ (by decide)
    omega
  have h1 : (2 : Nat) ^ 101 ≤ 2 ^ 165 := Nat.pow_le_pow_right (by decide) (by decide)
  have h2 : (2 : Nat) ^ 33 ≤ 2 ^ 165 := Nat.pow_le_pow_right (by decide) (by decide)
  have h3 : (5000000003 : Nat) ≤ 2 ^ 33 := by decide
  have e166 : (2 : Nat) ^ 166 = 2 ^ 165 + 2 ^ 165 := by
    have e : (2 : Nat) ^ 166 = 2 ^ 165 * 2 := by
      rw [show 166 = 165 + 1 by decide, Nat.pow_succ]
    omega
  have e167 : (2 : Nat) ^ 167 = 2 ^ 166 + 2 ^ 166 := by
    have e : (2 : Nat) ^ 167 = 2 ^ 166 * 2 := by
      rw [show 167 = 166 + 1 by decide, Nat.pow_succ]
    omega
  omega

theorem hover {a z : Nat} (ha : a ≤ 2 ^ 167 - 1) (hs : 0 < sN a)
    (hle : sN a ≤ z) (hzb : z ≤ z0N a + 1) : AN a / z + z ≤ 2 ^ 167 - 1 := by
  have hdiv : AN a / z ≤ sN a + 2 := AN_div_le hs hle
  have hsum : sN a + (z0N a + 4) ≤ 2 ^ 167 := sN_z0_sum_le ha
  omega

theorem hseq_pos {a : Nat} (ha : 0 < a) (k : Nat) : 0 < seqN a k := by
  induction k with
  | zero => exact Nat.lt_of_le_of_lt (Nat.zero_le _) (z0N_pos a)
  | succ k ih =>
    have hs : 0 < sN a := sN_pos ha
    have hle : sN a ≤ ProofForgeFin.Sqrt.newton (AN a) (seqN a k) :=
      ProofForgeFin.Sqrt.sqrt_le_newton ih
    have : seqN a (k + 1) = ProofForgeFin.Sqrt.newton (AN a) (seqN a k) := rfl
    omega

theorem hseq_ge {a : Nat} (ha : 0 < a) (k : Nat) : sN a ≤ seqN a k := by
  induction k with
  | zero => exact sN_le_z0N
  | succ k ih =>
    have hpos : 0 < seqN a k := hseq_pos ha k
    have hle : sN a ≤ ProofForgeFin.Sqrt.newton (AN a) (seqN a k) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hpos
    have : seqN a (k + 1) = ProofForgeFin.Sqrt.newton (AN a) (seqN a k) := rfl
    omega

theorem hseq_le {a : Nat} (ha : 0 < a) (k : Nat) : seqN a k ≤ z0N a + 1 := by
  induction k with
  | zero => exact Nat.le_succ _
  | succ k ih =>
    have hpos : 0 < seqN a k := hseq_pos ha k
    have hge : sN a ≤ seqN a k := hseq_ge ha k
    have hsz : sN a ≤ z0N a := sN_le_z0N
    have hstep : seqN a (k + 1) = ProofForgeFin.Sqrt.newton (AN a) (seqN a k) := rfl
    rw [hstep]
    rcases Nat.lt_or_ge (sN a) (seqN a k) with hlt | hge'
    · have hdec : ProofForgeFin.Sqrt.newton (AN a) (seqN a k) < seqN a k :=
        ProofForgeFin.Sqrt.newton_lt_self hlt
      omega
    · have heq : seqN a k = sN a := by omega
      rw [heq]
      have hpos_s : 0 < sN a := sN_pos ha
      have hm := ProofForgeFin.Sqrt.newton_of_mem (a := AN a) (x := sN a)
        hpos_s (Nat.le_refl _) (Nat.le_succ _)
      rcases hm with h | ⟨_, h2, _⟩
      · have hnw : ProofForgeFin.Sqrt.newton (AN a) (sN a) = sN a := h
        omega
      · have hnw : ProofForgeFin.Sqrt.newton (AN a) (sN a) = sN a + 1 := h2
        omega

theorem herr_bound {a : Nat} (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1) (k : Nat) :
    seqN a k - sN a ≤ 2 ^ (167 - k) + 2 := by
  induction k with
  | zero =>
    have hz := z0N_le haM
    have h0 : seqN a 0 = z0N a := rfl
    have p0 : (167 : Nat) - 0 = 167 := rfl
    rw [p0]
    omega
  | succ k ih =>
    have hpos : 0 < seqN a k := hseq_pos ha k
    have hge : sN a ≤ seqN a k := hseq_ge ha k
    have hhalf : ProofForgeFin.Sqrt.newton (AN a) (seqN a k) - sN a
        ≤ (seqN a k - sN a) / 2 + 1 :=
      ProofForgeFin.Sqrt.newton_sub_sqrt_le_half hpos hge
    have hstep : seqN a (k + 1) = ProofForgeFin.Sqrt.newton (AN a) (seqN a k) := rfl
    rw [hstep]
    by_cases hk : k < 167
    · have hm : 167 - k = (167 - (k + 1)) + 1 := by omega
      have h2 : 2 ^ (167 - k) = 2 ^ (167 - (k + 1)) * 2 := by
        rw [hm, Nat.pow_succ]
      rw [h2] at ih
      omega
    · have e1 : 167 - k = 0 := by omega
      have e2 : 167 - (k + 1) = 0 := by omega
      have p0 : (2 : Nat) ^ 0 = 1 := rfl
      rw [e1, p0] at ih
      rw [e2, p0]
      omega

theorem hstay {a : Nat} (ha : 0 < a) {x : Nat} (hx1 : sN a ≤ x) (hx2 : x ≤ sN a + 1) :
    ProofForgeFin.Sqrt.newton (AN a) x = sN a ∨
      ProofForgeFin.Sqrt.newton (AN a) x = sN a + 1 := by
  have hpos : 0 < x := Nat.lt_of_lt_of_le (sN_pos ha) hx1
  have hm := ProofForgeFin.Sqrt.newton_of_mem (a := AN a) (x := x) hpos hx1 hx2
  rcases hm with h | ⟨_, h2, _⟩
  · exact Or.inl h
  · exact Or.inr h2

theorem hseq168_mem {a : Nat} (ha : 0 < a) (haM : a ≤ 2 ^ 167 - 1) (ha1 : 1 ≤ a) :
    (seqN a 168 = sN a ∨ seqN a 168 = sN a + 1) ∧
      (seqN a 169 = sN a ∨ seqN a 169 = sN a + 1) := by
  have herr167 : seqN a 167 - sN a ≤ 3 := by
    have h := herr_bound ha haM 167
    have e167 : 167 - 167 = 0 := by omega
    have p0 : (2 : Nat) ^ 0 = 1 := rfl
    rw [e167, p0] at h
    omega
  have hsq : (seqN a 167 - sN a) * (seqN a 167 - sN a) ≤ sN a := by
    have h1 : (seqN a 167 - sN a) * (seqN a 167 - sN a) ≤ 3 * 3 :=
      Nat.mul_le_mul herr167 herr167
    have h2 : (100000 : Nat) ≤ sN a := sN_ge_1e5 ha1
    omega
  have hpos167 : 0 < seqN a 167 := hseq_pos ha 167
  have hge167 : sN a ≤ seqN a 167 := hseq_ge ha 167
  have hmem := ProofForgeFin.Sqrt.newton_eq_or_succ (a := AN a) (x := seqN a 167)
    hpos167 hge167 hsq
  have hstep168 : seqN a 168 = ProofForgeFin.Sqrt.newton (AN a) (seqN a 167) := rfl
  have h168 : seqN a 168 = sN a ∨ seqN a 168 = sN a + 1 := by
    rw [hstep168]
    rcases hmem with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨h168, ?_⟩
  have hstep169 : seqN a 169 = ProofForgeFin.Sqrt.newton (AN a) (seqN a 168) := rfl
  rw [hstep169]
  rcases h168 with h | h
  · rw [h] at hstep169 ⊢
    exact hstay ha (Nat.le_refl _) (Nat.le_succ _)
  · rw [h] at hstep169 ⊢
    have hx1 : sN a ≤ sN a + 1 := Nat.le_succ _
    exact hstay ha hx1 (Nat.le_refl _)

/-- Previous iterate: `prev 0 = a`, `prev (k+1) = seq k`. -/
def prevN (a : Nat) : Nat → Nat
  | 0 => a
  | n + 1 => seqN a n

theorem heq0 {a0 : Nat} (ha_eq : a0 = z0N a0) : a0 = sN a0 := by
  have h5 : (5 : Nat) * 10 ^ 9 = 5000000000 := by decide
  have e10 : (10 : Nat) ^ 10 = 10000000000 := by decide
  have hz : z0N a0 = a0 / 2 + 5 * 10 ^ 9 := rfl
  rw [hz, h5] at ha_eq
  have hmod : 2 * (a0 / 2) + a0 % 2 = a0 := Nat.div_add_mod a0 2
  have hr : a0 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hqr : a0 / 2 + a0 % 2 = 5000000000 := by omega
  have hr01 : a0 % 2 = 0 ∨ a0 % 2 = 1 := by omega
  rcases hr01 with hr0 | hr0
  · have hq : a0 / 2 = 5000000000 := by omega
    have ha0 : a0 = 10000000000 := by omega
    rw [ha0]
    have hsqrt : Nat.sqrt (AN 10000000000) = 10000000000 :=
      ProofForgeFin.Sqrt.sqrt_eq_of_bounds (by decide) (by decide)
    exact hsqrt.symm
  · have hq : a0 / 2 = 4999999999 := by omega
    have ha0 : a0 = 9999999999 := by omega
    rw [ha0]
    have hsqrt : Nat.sqrt (AN 9999999999) = 9999999999 :=
      ProofForgeFin.Sqrt.sqrt_eq_of_bounds (by decide) (by decide)
    exact hsqrt.symm

theorem hloop_stays {a0 : Nat} (ha : 0 < a0) (haM : a0 ≤ 2 ^ 167 - 1) (n : Nat) :
    ∀ {y z : Nat}, sN a0 ≤ y → y ≤ sN a0 + 1 → sN a0 ≤ z → z ≤ sN a0 + 1 →
    (y = z → y = sN a0) →
    ∃ y' z' : Nat, loop (↑a0) n (↑y) (↑z) = some ((↑y'), (↑z')) ∧ min y' z' = sN a0 := by
  induction n with
  | zero =>
    intro y z hy1 hy2 hz1 hz2 heq
    refine ⟨y, z, rfl, ?_⟩
    by_cases hyz : y = z
    · have hys : y = sN a0 := heq hyz
      subst hys
      have hz2' : z = sN a0 := by omega
      rw [hz2']
      omega
    · omega
  | succ n ih =>
    intro y z hy1 hy2 hz1 hz2 heq
    by_cases heqI : ((z : Nat) : Int) = ((y : Nat) : Int)
    · have heqN : z = y := Int.ofNat.inj heqI
      have hstop : loop (↑a0) (n + 1) (↑y) (↑z) = some ((↑y), (↑y)) := by
        rw [heqI]
        exact loop_stop _ _ _
      have hys : y = sN a0 := heq heqN.symm
      refine ⟨y, y, hstop, ?_⟩
      rw [hys]
      omega
    · have hneN : z ≠ y := fun c => heqI (by exact_mod_cast c)
      have hpos : 0 < z := Nat.lt_of_lt_of_le (sN_pos ha) hz1
      have hsz : sN a0 ≤ z0N a0 := sN_le_z0N
      have hhov : AN a0 / z + z ≤ 2 ^ 167 - 1 :=
        hover haM (sN_pos ha) hz1 (by omega)
      have hstep := loop_step (a := a0) (y := y) (z := z) n hpos hneN hhov
      have hmem : ProofForgeFin.Sqrt.newton (AN a0) z = sN a0 ∨
          ProofForgeFin.Sqrt.newton (AN a0) z = sN a0 + 1 :=
        hstay ha hz1 hz2
      have hbridge : ((a0 * 10 ^ 10 / z + z) / 2 : Nat)
          = ProofForgeFin.Sqrt.newton (AN a0) z := by
        have h1 : a0 * 10 ^ 10 = AN a0 := rfl
        rw [h1]
        have h3 : ProofForgeFin.Sqrt.newton (AN a0) z = (z + AN a0 / z) / 2 := rfl
        rw [h3]
        exact congrArg (· / 2) (Nat.add_comm _ _)
      rw [hbridge] at hstep
      rcases hmem with hm | hm
      · obtain ⟨y', z', hloop, hmin⟩ :=
          ih (y := z) (z := sN a0) hz1 hz2 (Nat.le_refl _) (Nat.le_succ _) (fun h => h)
        rw [← hm] at hloop
        exact ⟨y', z', by rw [hstep]; exact hloop, hmin⟩
      · have heq_new : z = sN a0 + 1 → z = sN a0 := by
          intro hzz
          have hzz' : ProofForgeFin.Sqrt.newton (AN a0) z = z := by
            rw [hm, ← hzz]
          have hlt : Nat.sqrt (AN a0) < z := by
            rw [hzz]
            exact Nat.lt_succ_self _
          have hlt2 := ProofForgeFin.Sqrt.newton_lt_self hlt
          omega
        obtain ⟨y', z', hloop, hmin⟩ :=
          ih (y := z) (z := sN a0 + 1) hz1 hz2 (Nat.le_succ _) (Nat.le_refl _) heq_new
        rw [← hm] at hloop
        exact ⟨y', z', by rw [hstep]; exact hloop, hmin⟩

theorem hreach_eq {a0 k : Nat} (ha : 0 < a0)
    (heq : seqN a0 k = prevN a0 k) : prevN a0 k = sN a0 := by
  cases k with
  | zero =>
    have h0p : prevN a0 Nat.zero = a0 := rfl
    have h0s : seqN a0 Nat.zero = z0N a0 := rfl
    rw [h0p, h0s] at heq
    rw [h0p]
    exact heq0 heq.symm
  | succ k' =>
    have hp : prevN a0 (k' + 1) = seqN a0 k' := rfl
    have hs2 : seqN a0 (k' + 1)
        = ProofForgeFin.Sqrt.newton (AN a0) (seqN a0 k') := rfl
    rw [hp, hs2] at heq
    have hfix := ProofForgeFin.Sqrt.eq_sqrt_of_newton_eq_self
      (hseq_pos ha k') heq
    rw [hp]
    exact hfix

theorem hreaches {a0 : Nat} (ha : 0 < a0) (haM : a0 ≤ 2 ^ 167 - 1) :
    ∀ (k : Nat), k ≤ 169 →
    loop (↑a0) 256 (↑a0) (↑(z0N a0)) =
      loop (↑a0) (256 - k) (↑(prevN a0 k)) (↑(seqN a0 k)) ∨
    loop (↑a0) 256 (↑a0) (↑(z0N a0)) = some ((↑(sN a0)), (↑(sN a0))) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact Or.inl rfl
  | succ k ih =>
    intro hk1
    have hk' : k ≤ 169 := by omega
    have hk256 : k ≤ 168 := by omega
    have hfuel : 256 - k = (256 - (k + 1)) + 1 := by omega
    rcases ih hk' with h | hDone
    · rw [hfuel] at h
      by_cases heqI : ((seqN a0 k : Nat) : Int) = ((prevN a0 k : Nat) : Int)
      case pos =>
        have heqN : seqN a0 k = prevN a0 k := Int.ofNat.inj heqI
        have hstop : loop (↑a0) ((256 - (k + 1)) + 1) (↑(prevN a0 k)) (↑(seqN a0 k))
            = some ((↑(prevN a0 k)), (↑(prevN a0 k))) := by
          rw [heqI]
          exact loop_stop _ _ _
        rw [hstop] at h
        have hps : prevN a0 k = sN a0 := hreach_eq ha heqN
        have hcast : ((prevN a0 k : Nat) : Int) = ((sN a0 : Nat) : Int) := by
          exact_mod_cast hps
        rw [hcast] at h
        exact Or.inr h
      case neg =>
        have hneN : seqN a0 k ≠ prevN a0 k := fun c => heqI (by exact_mod_cast c)
        have hhov : AN a0 / seqN a0 k + seqN a0 k ≤ 2 ^ 167 - 1 :=
          hover haM (sN_pos ha) (hseq_ge ha k) (hseq_le ha k)
        have hstep := loop_step (a := a0) (y := prevN a0 k) (z := seqN a0 k)
          (256 - (k + 1)) (hseq_pos ha k) hneN hhov
        rw [hstep] at h
        have hnz : ((a0 * 10 ^ 10 / seqN a0 k + seqN a0 k) / 2 : Nat)
            = seqN a0 (k + 1) := by
          have h1 : a0 * 10 ^ 10 = AN a0 := rfl
          rw [h1]
          have h2 : seqN a0 (k + 1)
              = ProofForgeFin.Sqrt.newton (AN a0) (seqN a0 k) := rfl
          rw [h2]
          have h3 : ProofForgeFin.Sqrt.newton (AN a0) (seqN a0 k)
              = (seqN a0 k + AN a0 / seqN a0 k) / 2 := rfl
          rw [h3]
          exact congrArg (· / 2) (Nat.add_comm _ _)
        rw [hnz] at h
        have hprev : prevN a0 (k + 1) = seqN a0 k := rfl
        rw [hprev]
        exact Or.inl h
    · exact Or.inr hDone

theorem hloop_correct {a0 : Nat} (ha : 0 < a0) (haM : a0 ≤ 2 ^ 167 - 1)
    (ha1 : 1 ≤ a0) :
    ∃ y' z' : Nat, loop (↑a0) 256 (↑a0) (↑(z0N a0))
      = some ((↑y'), (↑z')) ∧ min y' z' = sN a0 := by
  have h169 := hreaches ha haM 169 (Nat.le_refl _)
  rcases h169 with h | h
  · have h87 : 256 - 169 = 87 := rfl
    rw [h87] at h
    have hprev : prevN a0 169 = seqN a0 168 := rfl
    rw [hprev] at h
    have hmem := hseq168_mem ha haM ha1
    obtain ⟨h168, h169m⟩ := hmem
    have hy1 : sN a0 ≤ seqN a0 168 := hseq_ge ha 168
    have hy2 : seqN a0 168 ≤ sN a0 + 1 := by
      rcases h168 with h' | h' <;> omega
    have hz1 : sN a0 ≤ seqN a0 169 := hseq_ge ha 169
    have hz2 : seqN a0 169 ≤ sN a0 + 1 := by
      rcases h169m with h' | h' <;> omega
    have heq : seqN a0 168 = seqN a0 169 → seqN a0 168 = sN a0 := by
      intro heq
      have hs169 : seqN a0 169
          = ProofForgeFin.Sqrt.newton (AN a0) (seqN a0 168) := rfl
      rw [hs169] at heq
      have hmem2 := hstay ha hy1 hy2
      rcases hmem2 with hm | hm
      · exact heq.trans hm
      · exfalso
        have hfold : Nat.sqrt (AN a0) = sN a0 := rfl
        have h168eq : seqN a0 168 = sN a0 + 1 := heq.trans hm
        have hlt' : Nat.sqrt (AN a0) < seqN a0 168 := by omega
        have hlt := ProofForgeFin.Sqrt.newton_lt_self hlt'
        omega
    obtain ⟨y', z', hloop, hmin⟩ := hloop_stays ha haM 87 hy1 hy2 hz1 hz2 heq
    rw [← h] at hloop
    exact ⟨y', z', hloop, hmin⟩
  · exact ⟨sN a0, sN a0, h, by omega⟩

theorem hsqrt_some {a0 : Nat} (ha : 0 < a0) (haM : a0 ≤ 2 ^ 167 - 1)
    (ha1 : 1 ≤ a0) : sqrt (↑a0) = some (↑(sN a0)) := by
  obtain ⟨y', z', hloop, hmin⟩ := hloop_correct ha haM ha1
  have hfin : (fun y z => if y < z then y else z) ((y' : Nat) : Int) ((z' : Nat) : Int)
      = ((sN a0 : Nat) : Int) := by
    show (if ((y' : Nat) : Int) < ((z' : Nat) : Int) then ((y' : Nat) : Int)
      else ((z' : Nat) : Int)) = ((sN a0 : Nat) : Int)
    by_cases h : y' < z'
    · have hI : ((y' : Nat) : Int) < ((z' : Nat) : Int) := by exact_mod_cast h
      rw [if_pos hI, ← hmin, Nat.min_eq_left (Nat.le_of_lt h)]
    · have hle : z' ≤ y' := by omega
      have hI : ¬ ((y' : Nat) : Int) < ((z' : Nat) : Int) := by exact_mod_cast h
      rw [if_neg hI, ← hmin, Nat.min_eq_right hle]
  have h1 : sqrt (↑a0)
      = vyperSqrtWith (fun y z => if y < z then y else z) (↑a0) := rfl
  rw [h1, vyperSqrtWith_pos (fun y z => if y < z then y else z) ha haM]
  have hseed : ((a0 / 2 + 5 * 10 ^ 9 : Nat) : Int) = ((z0N a0 : Nat) : Int) := rfl
  rw [hseed, hloop, Option.map_some]
  show some ((fun y z => if y < z then y else z) ((y' : Nat) : Int) ((z' : Nat) : Int))
    = some ((sN a0 : Nat) : Int)
  rw [hfin]

theorem hsqrt_zero : sqrt ((0 : Nat) : Int) = some 0 := rfl

theorem hX_eq {a0 : Nat} : ((AN a0 : Nat) : Int) = (↑a0) * DIVISOR := by
  have e1 : AN a0 = a0 * 10 ^ 10 := rfl
  rw [e1, Int.natCast_mul, divisor_eq.symm]

theorem hx_nonneg {x r : Int} (hsqrt : sqrt x = some r) : 0 ≤ x := by
  by_cases hle : 0 ≤ x
  · exact hle
  · have hlt' : x < 0 := by omega
    have hnone : sqrt x = none := by
      unfold sqrt vyperSqrtWith
      simp [hlt']
    rw [hsqrt] at hnone
    cases hnone

theorem haM_of {x : Int} (hxD : IsDecimal x) (a0 : Nat) (hxa : x = ((a0 : Nat) : Int)) :
    a0 ≤ 2 ^ 167 - 1 := by
  have hmax : x ≤ MAX_DECIMAL := hxD.2
  rw [hxa, max_decimal_eq] at hmax
  exact_mod_cast hmax

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hxD hsqrt
  have hx0 := hx_nonneg hsqrt
  obtain ⟨a0, rfl⟩ : ∃ a : Nat, x = ((a : Nat) : Int) :=
    ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
  have haM : a0 ≤ 2 ^ 167 - 1 := haM_of hxD a0 rfl
  rcases Nat.eq_zero_or_pos a0 with rfl | hpos
  · have h0 : sqrt ((0 : Nat) : Int) = some 0 := hsqrt_zero
    rw [h0] at hsqrt
    have hr : r = 0 := (Option.some_inj.mp hsqrt).symm
    rw [hr]
    simp
  · have ha1 : 1 ≤ a0 := hpos
    have hs := hsqrt_some hpos haM ha1
    rw [hs] at hsqrt
    have hr : r = ((sN a0 : Nat) : Int) := (Option.some_inj.mp hsqrt).symm
    have hleN : sN a0 * sN a0 ≤ AN a0 := Nat.sqrt_le (AN a0)
    have hNr : ((sN a0 : Nat) : Int) * ((sN a0 : Nat) : Int)
        ≤ ((AN a0 : Nat) : Int) := by exact_mod_cast hleN
    rw [hr, ← hX_eq]
    exact hNr

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hxD hsqrt
  have hx0 := hx_nonneg hsqrt
  obtain ⟨a0, rfl⟩ : ∃ a : Nat, x = ((a : Nat) : Int) :=
    ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
  have haM : a0 ≤ 2 ^ 167 - 1 := haM_of hxD a0 rfl
  rcases Nat.eq_zero_or_pos a0 with rfl | hpos
  · have h0 : sqrt ((0 : Nat) : Int) = some 0 := hsqrt_zero
    rw [h0] at hsqrt
    have hr : r = 0 := (Option.some_inj.mp hsqrt).symm
    rw [hr]
    simp
  · have ha1 : 1 ≤ a0 := hpos
    have hs := hsqrt_some hpos haM ha1
    rw [hs] at hsqrt
    have hr : r = ((sN a0 : Nat) : Int) := (Option.some_inj.mp hsqrt).symm
    have hltN : AN a0 < (sN a0 + 1) * (sN a0 + 1) := Nat.lt_succ_sqrt (AN a0)
    have hNu : ((AN a0 : Nat) : Int) < (((sN a0 + 1) * (sN a0 + 1) : Nat) : Int) := by
      exact_mod_cast hltN
    have hpush : (((sN a0 + 1) * (sN a0 + 1) : Nat) : Int)
        = (((sN a0 : Nat) : Int) + 1) * (((sN a0 : Nat) : Int) + 1) := by
      rw [Int.natCast_mul, Int.natCast_add, Int.natCast_one]
    rw [hr, ← hX_eq, ← hpush]
    exact hNu

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hxD hx0
  obtain ⟨a0, rfl⟩ : ∃ a : Nat, x = ((a : Nat) : Int) :=
    ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
  have haM : a0 ≤ 2 ^ 167 - 1 := haM_of hxD a0 rfl
  rcases Nat.eq_zero_or_pos a0 with rfl | hpos
  · rw [hsqrt_zero]; rfl
  · have ha1 : 1 ≤ a0 := hpos
    rw [hsqrt_some hpos haM ha1]; rfl
theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  simp [hx]
theorem req_deployed_loop    : DeployedLoop sqrt := ⟨_, fun _ => rfl⟩

end VyperSqrt
