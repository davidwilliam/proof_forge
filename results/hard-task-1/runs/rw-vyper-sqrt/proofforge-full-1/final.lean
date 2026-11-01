import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
namespace VyperSqrt

open ProofForgeFin.Sqrt

def sqrt : SqrtFn := vyperSqrtWith fun y z => if y < z then y else z

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  simp only [hx, ite_eq_left]

theorem req_deployed_loop : DeployedLoop sqrt := by
  exact ⟨_, fun _ => rfl⟩

/-- Raw product whose floor root is wanted. -/
def Aval (a : Nat) : Nat := a * 10 ^ 10

/-- Babylonian seed. -/
def Seed (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- Newton iterate. -/
def Iter (a : Nat) : Nat → Nat
  | 0 => Seed a
  | n + 1 => newton (Aval a) (Iter a n)

theorem seed_succ_sq_gt (a : Nat) :
    a * 10 ^ 10 < (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1) := by
  have hpow1 : 5 * 10 ^ 9 = 5000000000 := by decide
  have hpow2 : 10 ^ 10 = 10000000000 := by decide
  rw [hpow1, hpow2]
  generalize h : a / 2 = k
  have h1 : 2 * k ≤ a := by omega
  have h2 : a ≤ 2 * k + 1 := by omega
  have hle : a * 10000000000 ≤ (2 * k + 1) * 10000000000 := Nat.mul_le_mul_right _ h2
  have hmul2 : (2 * k + 1) * 10000000000 = 20000000000 * k + 10000000000 := by grind
  rw [hmul2] at hle
  have hamgm := four_mul_le_sq k 5000000000
  have hexpand : (k + 5000000000 + 1) * (k + 5000000000 + 1)
      = (k + 5000000000) * (k + 5000000000) + 2 * (k + 5000000000) + 1 := by grind
  rw [hexpand]
  have h4 : 4 * k * 5000000000 = 20000000000 * k := by grind
  omega

theorem seed_ge_sqrt (a : Nat) : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := by
  have hlt := seed_succ_sq_gt a
  have h2 : Nat.sqrt (a * 10 ^ 10) < a / 2 + 5 * 10 ^ 9 + 1 :=
    sqrt_lt_of_lt_mul_self (a := a * 10 ^ 10) (m := a / 2 + 5 * 10 ^ 9 + 1) hlt
  omega

theorem sqrt_lt_pow101 (a : Nat) (h : a ≤ 2 ^ 167 - 1) :
    Nat.sqrt (a * 10 ^ 10) < 2 ^ 101 := by
  have h10 : (10 : Nat) ^ 10 ≤ 2 ^ 34 := by decide
  have e1 : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 2 ^ 34 :=
    calc a * 10 ^ 10 ≤ a * 2 ^ 34 := Nat.mul_le_mul_left _ h10
      _ ≤ (2 ^ 167 - 1) * 2 ^ 34 := Nat.mul_le_mul_right _ h
  have e2 : (2 ^ 167 - 1) * 2 ^ 34 < 2 ^ 167 * 2 ^ 34 :=
    Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by decide : 0 < 2))
  have e3 : (2 : Nat) ^ 167 * 2 ^ 34 = 2 ^ 201 := by rw [← Nat.pow_add]
  have e4 : (2 : Nat) ^ 201 < 2 ^ (2 * 101) := by
    have hh : 2 * 101 = 202 := by decide
    rw [hh]
    have h202 : (2 : Nat) ^ 202 = 2 ^ 201 * 2 := by rw [← Nat.pow_succ]
    have hpos : 0 < (2 : Nat) ^ 201 := Nat.pow_pos (by decide : 0 < 2)
    omega
  have hA : a * 10 ^ 10 < 2 ^ (2 * 101) := by
    calc a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 2 ^ 34 := e1
      _ < 2 ^ 167 * 2 ^ 34 := e2
      _ = 2 ^ 201 := e3
      _ < 2 ^ (2 * 101) := e4
  exact sqrt_lt_two_pow hA

theorem div_le_add_two {A s z : Nat} (hs : 0 < s) (hle : s ≤ z)
    (hA : A < (s + 1) * (s + 1)) : A / z ≤ s + 2 := by
  have h1 : A ≤ s * s + 2 * s := by grind
  have h2 : A / z ≤ A / s := Nat.div_le_div_left hle hs
  have h3 : A / s ≤ (s * s + 2 * s) / s := Nat.div_le_div_right h1
  have h4 : (s * s + 2 * s) / s = s + 2 := by
    have e : s * s + 2 * s = (s + 2) * s := by grind
    rw [e]
    exact Nat.mul_div_cancel _ hs
  omega

theorem seed_le_max (a : Nat) (h : a ≤ 2 ^ 167 - 1) :
    a / 2 + 5 * 10 ^ 9 ≤ 2 ^ 167 - 1 := by
  have h5 : 5 * 10 ^ 9 = 5000000000 := by decide
  rw [h5]
  have h166 : (2 : Nat) ^ 166 ≤ 2 ^ 167 - 1 := by decide
  omega

theorem sqrt_ge_100k {a : Nat} (ha : 0 < a) : 100000 ≤ Nat.sqrt (a * 10 ^ 10) := by
  apply le_sqrt_of_mul_self_le (m := 100000)
  have h10 : (100000 : Nat) * 100000 = 10 ^ 10 := by decide
  rw [h10]
  calc 10 ^ 10 = 1 * 10 ^ 10 := by grind
    _ ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha

theorem sq_le_two_sqrt {a n : Nat} (hspos : 0 < Nat.sqrt (Aval a))
    (hlo : Nat.sqrt (Aval a) ≤ Iter a n)
    (hle : Iter a n ≤ Nat.sqrt (Aval a) + 1) :
    (Iter a n - Nat.sqrt (Aval a)) * (Iter a n - Nat.sqrt (Aval a))
      ≤ 2 * Nat.sqrt (Aval a) := by
  have e : Iter a n - Nat.sqrt (Aval a) ≤ 1 := by omega
  have hmul : (Iter a n - Nat.sqrt (Aval a)) * (Iter a n - Nat.sqrt (Aval a)) ≤ 1 * 1 :=
    Nat.mul_le_mul e e
  have h11 : (1 : Nat) * 1 ≤ 2 * Nat.sqrt (Aval a) := by omega
  exact Nat.le_trans hmul h11

theorem iter_mem (a : Nat) (ha : 0 < a) (n : Nat) :
    Nat.sqrt (Aval a) ≤ Iter a n ∧ Iter a n ≤ Seed a + 1 := by
  induction n with
  | zero =>
    have h1 : Nat.sqrt (Aval a) ≤ Seed a := by
      have : Aval a = a * 10 ^ 10 := rfl
      rw [this]
      exact seed_ge_sqrt a
    exact ⟨h1, Nat.le_succ _⟩
  | succ n ih =>
    obtain ⟨hlo, hhi⟩ := ih
    have hspos : 0 < Nat.sqrt (Aval a) := by
      have h100 : 100000 ≤ Nat.sqrt (Aval a) := by
        have : Aval a = a * 10 ^ 10 := rfl
        rw [this]
        exact sqrt_ge_100k ha
      omega
    have hxpos : 0 < Iter a n := by omega
    have hNlo : Nat.sqrt (Aval a) ≤ newton (Aval a) (Iter a n) :=
      sqrt_le_newton hxpos
    have hIter : Iter a (n + 1) = newton (Aval a) (Iter a n) := rfl
    rw [hIter]
    refine ⟨hNlo, ?_⟩
    by_cases hle : Iter a n ≤ Nat.sqrt (Aval a) + 1
    · have hsq := sq_le_two_sqrt hspos hlo hle
      have hNle := newton_le_sqrt_add_one hxpos hlo hsq
      have hsle : Nat.sqrt (Aval a) + 1 ≤ Seed a + 1 := by
        have h1 : Nat.sqrt (Aval a) ≤ Seed a := by
          have : Aval a = a * 10 ^ 10 := rfl
          rw [this]
          exact seed_ge_sqrt a
        omega
      exact Nat.le_trans hNle hsle
    · have hlt : Nat.sqrt (Aval a) < Iter a n := by omega
      have hdec : newton (Aval a) (Iter a n) < Iter a n := newton_lt_self hlt
      exact Nat.le_trans (Nat.le_of_lt hdec) hhi

theorem pow_half (t : Nat) : (2 ^ (t + 1) + 1) / 2 = 2 ^ t := by
  have h : (2 : Nat) ^ (t + 1) = 2 ^ t * 2 := by rw [Nat.pow_succ]
  omega

theorem err_half (a n : Nat) (ha : 0 < a) :
    Iter a (n + 1) - Nat.sqrt (Aval a)
      ≤ (Iter a n - Nat.sqrt (Aval a)) / 2 + 1 := by
  have hmem := iter_mem a ha n
  have hxpos : 0 < Iter a n := by
    have h100 : 100000 ≤ Nat.sqrt (Aval a) := by
      have : Aval a = a * 10 ^ 10 := rfl
      rw [this]
      exact sqrt_ge_100k ha
    omega
  have hIter : Iter a (n + 1) = newton (Aval a) (Iter a n) := rfl
  rw [hIter]
  exact newton_sub_sqrt_le_half hxpos hmem.1

theorem err_bound (a : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) (n : Nat)
    (hn : n ≤ 167) : Iter a n - Nat.sqrt (Aval a) ≤ 2 ^ (167 - n) + 1 := by
  induction n with
  | zero =>
    have hseed : Seed a ≤ 2 ^ 167 - 1 := seed_le_max a hle
    have hmem := iter_mem a ha 0
    have hIter0 : Iter a 0 = Seed a := rfl
    have h0 : 167 - 0 = 167 := by decide
    rw [h0, hIter0]
    omega
  | succ n ih =>
    have hnle : n ≤ 167 := by omega
    have ih' := ih hnle
    have hhalf := err_half a n ha
    have hn1 : n + 1 ≤ 167 := hn
    have ht : 167 - n = (167 - (n + 1)) + 1 := by omega
    have hp : (2 : Nat) ^ (167 - n) = 2 ^ (167 - (n + 1)) * 2 := by
      rw [ht, Nat.pow_succ]
    have hdiv : (Iter a n - Nat.sqrt (Aval a)) / 2 ≤ (2 ^ (167 - n) + 1) / 2 :=
      Nat.div_le_div_right ih'
    have hpow : (2 ^ (167 - n) + 1) / 2 = 2 ^ (167 - (n + 1)) := by
      rw [hp]
      have h2 : (2 ^ (167 - (n + 1)) * 2 + 1) / 2 = 2 ^ (167 - (n + 1)) := by omega
      exact h2
    omega

theorem err_167_le_two (a : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) :
    Iter a 167 - Nat.sqrt (Aval a) ≤ 2 := by
  have h := err_bound a ha hle 167 (by decide)
  have h0 : 167 - 167 = 0 := by decide
  rw [h0] at h
  simpa using h

theorem err_168_le_one (a : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) :
    Iter a 168 - Nat.sqrt (Aval a) ≤ 1 := by
  have h167mem := iter_mem a ha 167
  have h167le := err_167_le_two a ha hle
  have h100k : 100000 ≤ Nat.sqrt (Aval a) := by
    have : Aval a = a * 10 ^ 10 := rfl
    rw [this]
    exact sqrt_ge_100k ha
  have hspos : 0 < Nat.sqrt (Aval a) := by omega
  have hxpos : 0 < Iter a 167 := by omega
  have e167 : Iter a 167 - Nat.sqrt (Aval a) ≤ 2 := h167le
  have hsq : (Iter a 167 - Nat.sqrt (Aval a)) * (Iter a 167 - Nat.sqrt (Aval a))
      ≤ Nat.sqrt (Aval a) := by
    have e : Iter a 167 - Nat.sqrt (Aval a) ≤ 2 := e167
    have hmul : (Iter a 167 - Nat.sqrt (Aval a)) * (Iter a 167 - Nat.sqrt (Aval a))
        ≤ 2 * 2 := Nat.mul_le_mul e e
    have h4 : (2 : Nat) * 2 ≤ Nat.sqrt (Aval a) := by omega
    exact Nat.le_trans hmul h4
  have h168eq : Iter a 168 = newton (Aval a) (Iter a 167) := rfl
  have hmem167 : Nat.sqrt (Aval a) ≤ Iter a 167 := h167mem.1
  rcases newton_eq_or_succ hxpos hmem167 hsq with h | ⟨h, _⟩
  · have : Iter a 168 = Nat.sqrt (Aval a) := by rw [h168eq, h]
    omega
  · have : Iter a 168 = Nat.sqrt (Aval a) + 1 := by rw [h168eq, h]
    omega

theorem err_stay_one (a : Nat) (ha : 0 < a) (n : Nat) (hn : 168 ≤ n)
    (h : Iter a n - Nat.sqrt (Aval a) ≤ 1) :
    Iter a (n + 1) - Nat.sqrt (Aval a) ≤ 1 := by
  have hmem := iter_mem a ha n
  have hle : Iter a n ≤ Nat.sqrt (Aval a) + 1 := by omega
  have hxpos : 0 < Iter a n := by
    have h100 : 100000 ≤ Nat.sqrt (Aval a) := by
      have : Aval a = a * 10 ^ 10 := rfl
      rw [this]
      exact sqrt_ge_100k ha
    omega
  have hIter : Iter a (n + 1) = newton (Aval a) (Iter a n) := rfl
  have hNmem := newton_of_mem hxpos hmem.1 hle
  rcases hNmem with hN | ⟨_, hN, _⟩
  · rw [hIter, hN]
    omega
  · rw [hIter, hN]
    omega

theorem err_ge_168_le_one_aux (a : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) (m : Nat) :
    Iter a (168 + m) - Nat.sqrt (Aval a) ≤ 1 := by
  induction m with
  | zero => simpa using err_168_le_one a ha hle
  | succ m ih =>
    have hle' : 168 ≤ 168 + m := by omega
    have hstep := err_stay_one a ha (168 + m) hle' ih
    have heq : 168 + (m + 1) = (168 + m) + 1 := by omega
    rw [heq]
    exact hstep

theorem err_ge_168_le_one (a : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) (n : Nat)
    (hn : 168 ≤ n) : Iter a n - Nat.sqrt (Aval a) ≤ 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact err_ge_168_le_one_aux a ha hle m

theorem final_min (a : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) :
    min (Iter a 255) (Iter a 256) = Nat.sqrt (Aval a) := by
  have h255 : Iter a 255 - Nat.sqrt (Aval a) ≤ 1 :=
    err_ge_168_le_one a ha hle 255 (by decide)
  have hmem255 := iter_mem a ha 255
  have hxpos : 0 < Iter a 255 := by
    have h100 : 100000 ≤ Nat.sqrt (Aval a) := by
      have : Aval a = a * 10 ^ 10 := rfl
      rw [this]
      exact sqrt_ge_100k ha
    omega
  have hle255 : Iter a 255 ≤ Nat.sqrt (Aval a) + 1 := by omega
  have h256eq : Iter a 256 = newton (Aval a) (Iter a 255) := rfl
  have hmin : min (Iter a 255) (newton (Aval a) (Iter a 255)) = Nat.sqrt (Aval a) :=
    min_newton_eq_sqrt hxpos hmem255.1 hle255
  rw [← h256eq] at hmin
  exact hmin

theorem seed_le_166 (a : Nat) (hle : a ≤ 2 ^ 167 - 1) :
    Seed a ≤ 2 ^ 166 + 5000000000 := by
  have h5 : 5 * 10 ^ 9 = 5000000000 := by decide
  have hseed : Seed a = a / 2 + 5000000000 := by
    unfold Seed
    rw [h5]
  rw [hseed]
  have hdiv : a / 2 ≤ 2 ^ 166 := by
    have hle2 : a ≤ 2 ^ 167 := by omega
    have h2 : (2 : Nat) ^ 167 = 2 ^ 166 * 2 := by rw [← Nat.pow_succ]
    omega
  omega

theorem div_le_add_two' (a n : Nat) (ha : 0 < a)
    (hle : a ≤ 2 ^ 167 - 1) :
    Aval a / Iter a n ≤ Nat.sqrt (Aval a) + 2 := by
  have hmem := iter_mem a ha n
  have hspos : 0 < Nat.sqrt (Aval a) := by
    have h100 : 100000 ≤ Nat.sqrt (Aval a) := by
      have : Aval a = a * 10 ^ 10 := rfl
      rw [this]
      exact sqrt_ge_100k ha
    omega
  have hA : Aval a < (Nat.sqrt (Aval a) + 1) * (Nat.sqrt (Aval a) + 1) :=
    Nat.lt_succ_sqrt _
  exact div_le_add_two hspos hmem.1 hA

theorem iter_sum_le_max (a : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) (n : Nat) :
    Aval a / Iter a n + Iter a n ≤ 2 ^ 167 - 1 := by
  have hmem := iter_mem a ha n
  have hq := div_le_add_two' a n ha hle
  have hslt : Nat.sqrt (Aval a) < 2 ^ 101 := by
    have hA : Aval a = a * 10 ^ 10 := rfl
    rw [hA]
    exact sqrt_lt_pow101 a hle
  have hseed166 := seed_le_166 a hle
  have hIterLe : Iter a n ≤ 2 ^ 166 + 5000000000 + 1 := by omega
  have hqLe : Aval a / Iter a n ≤ 2 ^ 101 + 1 := by omega
  have hbound : 2 ^ 166 + 5000000000 + 1 + (2 ^ 101 + 1) ≤ 2 ^ 167 - 1 := by decide
  omega

theorem iter_pos (a n : Nat) (ha : 0 < a) : 0 < Iter a n := by
  have hmem := iter_mem a ha n
  have h100 : 100000 ≤ Nat.sqrt (Aval a) := by
    have : Aval a = a * 10 ^ 10 := rfl
    rw [this]
    exact sqrt_ge_100k ha
  omega

theorem iter_fixed_stay (a k m : Nat) (hfix : Iter a (k + 1) = Iter a k) :
    Iter a (k + m) = Iter a k := by
  induction m with
  | zero =>
    have h0 : k + 0 = k := by omega
    rw [h0]
  | succ m ih =>
    have heq : k + (m + 1) = (k + m) + 1 := by omega
    rw [heq]
    have hIter : Iter a ((k + m) + 1) = newton (Aval a) (Iter a (k + m)) := rfl
    rw [hIter, ih]
    have hk1 : Iter a (k + 1) = newton (Aval a) (Iter a k) := rfl
    have hN : newton (Aval a) (Iter a k) = Iter a k := by omega
    exact hN

theorem loop_nat_eq (a k n : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) :
    loop (a : Int) n ((Iter a k : Nat) : Int) ((Iter a (k + 1) : Nat) : Int)
      = some (((Iter a (k + n) : Nat) : Int), ((Iter a (k + n + 1) : Nat) : Int)) := by
  induction n generalizing k with
  | zero =>
    have h0 : k + 0 = k := by omega
    have h01 : k + 0 + 1 = k + 1 := by omega
    rw [h0, h01]
    rfl
  | succ n ih =>
    by_cases heq : ((Iter a (k + 1) : Nat) : Int) = ((Iter a k : Nat) : Int)
    · have hNatEq : Iter a (k + 1) = Iter a k := by omega
      have hstop : loop (a : Int) (n + 1) ((Iter a k : Nat) : Int)
          ((Iter a (k + 1) : Nat) : Int)
          = some (((Iter a k : Nat) : Int), ((Iter a (k + 1) : Nat) : Int)) := by
        rw [heq]
        exact loop_stop (a : Int) n ((Iter a k : Nat) : Int)
      rw [hstop]
      have hstay1 : Iter a (k + (n + 1)) = Iter a k :=
        iter_fixed_stay a k (n + 1) hNatEq
      have hstay2 : Iter a (k + (n + 1) + 1) = Iter a k := by
        have h1 : k + (n + 1) + 1 = k + (n + 2) := by omega
        rw [h1]
        exact iter_fixed_stay a k (n + 2) hNatEq
      rw [hstay1, hstay2, hNatEq]
    · have hneNat : Iter a (k + 1) ≠ Iter a k := fun h => heq (by rw [h])
      have hzpos : 0 < Iter a (k + 1) := iter_pos a (k + 1) ha
      have hsum := iter_sum_le_max a ha hle (k + 1)
      have hAval : Aval a = a * 10 ^ 10 := rfl
      have hstep := loop_step (a := a) (y := Iter a k) (z := Iter a (k + 1)) n hzpos hneNat (by
        have : a * 10 ^ 10 / Iter a (k + 1) + Iter a (k + 1) ≤ 2 ^ 167 - 1 := by
          have : Aval a / Iter a (k + 1) + Iter a (k + 1) ≤ 2 ^ 167 - 1 := hsum
          rwa [hAval] at this
        exact this)
      have hNewtonEq : ((a * 10 ^ 10 / Iter a (k + 1) + Iter a (k + 1)) / 2 : Nat)
          = Iter a (k + 1 + 1) := by
        have hIter2 : Iter a (k + 1 + 1) = newton (Aval a) (Iter a (k + 1)) := rfl
        rw [hIter2]
        unfold newton Aval
        have hcomm : a * 10 ^ 10 / Iter a (k + 1) + Iter a (k + 1)
            = Iter a (k + 1) + a * 10 ^ 10 / Iter a (k + 1) := by omega
        rw [hcomm]
      rw [hstep, hNewtonEq]
      have ih' := ih (k + 1)
      have heq1 : k + 1 + n = k + (n + 1) := by omega
      have heq2 : k + 1 + n + 1 = k + (n + 1) + 1 := by omega
      rw [heq2, heq1] at ih'
      exact ih'

theorem seed_eq_sqrt (a : Nat) (h : a = Seed a) : Nat.sqrt (Aval a) = a := by
  have hSeedEq : Seed a = a / 2 + 5 * 10 ^ 9 := rfl
  have h5 : 5 * 10 ^ 9 = 5000000000 := by decide
  rw [h5] at hSeedEq
  have ha_eq : a = a / 2 + 5000000000 := by omega
  have hdisj : a = 9999999999 ∨ a = 10000000000 := by omega
  rcases hdisj with rfl | rfl
  · have h1 : (9999999999 : Nat) * 9999999999 ≤ 9999999999 * 10 ^ 10 := by decide
    have h2 : 9999999999 * 10 ^ 10 < (9999999999 + 1) * (9999999999 + 1) := by decide
    have hA : Aval 9999999999 = 9999999999 * 10 ^ 10 := rfl
    rw [hA]
    exact sqrt_eq_of_bounds h1 h2
  · have h1 : (10000000000 : Nat) * 10000000000 ≤ 10000000000 * 10 ^ 10 := by decide
    have h2 : 10000000000 * 10 ^ 10 < (10000000000 + 1) * (10000000000 + 1) := by decide
    have hA : Aval 10000000000 = 10000000000 * 10 ^ 10 := rfl
    rw [hA]
    exact sqrt_eq_of_bounds h1 h2

theorem loop_eq_seed_eq (a : Nat) (h : Seed a = a) :
    loop (a : Int) 256 ((a : Nat) : Int) (((Seed a : Nat)) : Int)
      = some (((a : Nat) : Int), (((a : Nat)) : Int)) := by
  have hcast : (((Seed a : Nat)) : Int) = ((a : Nat) : Int) := by omega
  have h256 : (256 : Nat) = 255 + 1 := by decide
  rw [h256, hcast]
  exact loop_stop (a : Int) 255 (((a : Nat) : Int))

theorem loop_eq_seed_ne (a : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1)
    (hne : Seed a ≠ a) :
    loop (a : Int) 256 ((a : Nat) : Int) (((Seed a : Nat)) : Int)
      = some ((((Iter a 255 : Nat)) : Int), ((((Iter a 256 : Nat))) : Int)) := by
  have hSeedPos : 0 < Seed a := by
    have h5 : 5 * 10 ^ 9 = 5000000000 := by decide
    have hSeedEq : Seed a = a / 2 + 5 * 10 ^ 9 := rfl
    omega
  have hsum0 := iter_sum_le_max a ha hle 0
  have hIter0 : Iter a 0 = Seed a := rfl
  have hIter1 : Iter a 1 = newton (Aval a) (Seed a) := rfl
  have hAval : Aval a = a * 10 ^ 10 := rfl
  have hneInt : (((Seed a : Nat)) : Int) ≠ (((a : Nat)) : Int) := by omega
  have hstep := loop_step (a := a) (y := a) (z := Seed a) 255 hSeedPos hne (by
    have : a * 10 ^ 10 / Seed a + Seed a ≤ 2 ^ 167 - 1 := by
      have h0 : Aval a / Iter a 0 + Iter a 0 ≤ 2 ^ 167 - 1 := hsum0
      rw [hIter0] at h0
      rwa [hAval] at h0
    exact this)
  have hNewtonEq : ((a * 10 ^ 10 / Seed a + Seed a) / 2 : Nat) = Iter a 1 := by
    have hIter1' : Iter a 1 = newton (Aval a) (Seed a) := rfl
    rw [hIter1']
    unfold newton Aval
    have hcomm : a * 10 ^ 10 / Seed a + Seed a
        = Seed a + a * 10 ^ 10 / Seed a := by omega
    rw [hcomm]
  have h256 : (256 : Nat) = 255 + 1 := by decide
  rw [h256]
  rw [hstep]
  have hLoop := loop_nat_eq a 0 255 ha hle
  have h0 : 0 + 255 = 255 := by decide
  have h01 : 0 + 255 + 1 = 256 := by decide
  have h01' : (0 : Nat) + 1 = 1 := by decide
  rw [h0, h01, h01'] at hLoop
  have hCast0 : ((Seed a : Nat) : Int) = ((Iter a 0 : Nat) : Int) := by rw [hIter0]
  have hCast1 : (((a * 10 ^ 10 / Seed a + Seed a) / 2 : Nat) : Int)
      = ((Iter a 1 : Nat) : Int) := by rw [hNewtonEq]
  rw [hCast0, hCast1]
  exact hLoop

theorem sqrt_zero_eq : sqrt 0 = some 0 := rfl

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx hx0
  obtain ⟨a, rfl⟩ : ∃ a : Nat, (x : Int) = ((a : Nat) : Int) := ⟨x.toNat, by omega⟩
  have hle : a ≤ 2 ^ 167 - 1 := by
    have hmax : MAX_DECIMAL = (((2 ^ 167 - 1 : Nat)) : Int) := max_decimal_eq
    unfold IsDecimal at hx
    omega
  by_cases ha : a = 0
  · subst ha
    have h0 : (((0 : Nat)) : Int) = 0 := rfl
    rw [h0, sqrt_zero_eq]
    rfl
  · have haPos : 0 < a := by omega
    have hpos : vyperSqrtWith (fun y z => if y < z then y else z) ((a : Nat) : Int)
        = (loop ((a : Nat) : Int) 256 ((a : Nat) : Int) (((Seed a : Nat)) : Int)).map
          (fun p => if p.1 < p.2 then p.1 else p.2) := vyperSqrtWith_pos _ haPos hle
    have hsqrt : sqrt ((a : Nat) : Int)
        = (loop ((a : Nat) : Int) 256 ((a : Nat) : Int) (((Seed a : Nat)) : Int)).map
          (fun p => if p.1 < p.2 then p.1 else p.2) := by
      unfold sqrt
      exact hpos
    rw [hsqrt]
    by_cases hseed : Seed a = a
    · have hloop := loop_eq_seed_eq a hseed
      rw [hloop]
      rfl
    · have hloop := loop_eq_seed_ne a haPos hle hseed
      rw [hloop]
      rfl

theorem if_min_cast (m n : Nat) :
    (if ((m : Nat) : Int) < ((n : Nat) : Int) then ((m : Nat) : Int) else ((n : Nat) : Int))
      = (↑(min m n) : Int) := by
  by_cases h : m < n
  · have hInt : ((m : Nat) : Int) < ((n : Nat) : Int) := by omega
    have hmin : min m n = m := Nat.min_eq_left (by omega)
    rw [if_pos hInt]
    rw [hmin]
  · have hInt : ¬ ((m : Nat) : Int) < ((n : Nat) : Int) := by omega
    have hmin : min m n = n := Nat.min_eq_right (by omega)
    rw [if_neg hInt]
    rw [hmin]

theorem sqrt_eq_sqrt_cast (a : Nat) (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1)
    (r : Int) (hsqrt : sqrt ((a : Nat) : Int) = some r) :
    r = (↑(Nat.sqrt (Aval a)) : Int) := by
  have hpos : vyperSqrtWith (fun y z => if y < z then y else z) ((a : Nat) : Int)
      = (loop ((a : Nat) : Int) 256 ((a : Nat) : Int) (((Seed a : Nat)) : Int)).map
        (fun p => if p.1 < p.2 then p.1 else p.2) := vyperSqrtWith_pos _ ha hle
  have hsqrtEq : sqrt ((a : Nat) : Int)
      = (loop ((a : Nat) : Int) 256 ((a : Nat) : Int) (((Seed a : Nat)) : Int)).map
        (fun p => if p.1 < p.2 then p.1 else p.2) := by
    unfold sqrt
    exact hpos
  by_cases hseed : Seed a = a
  · have hloop := loop_eq_seed_eq a hseed
    have hval : sqrt ((a : Nat) : Int)
        = some (if ((a : Nat) : Int) < ((a : Nat) : Int) then ((a : Nat) : Int) else ((a : Nat) : Int)) := by
      rw [hsqrtEq, hloop]
      rfl
    have hfr : (if ((a : Nat) : Int) < ((a : Nat) : Int) then ((a : Nat) : Int) else ((a : Nat) : Int)) = r := by
      have : some (if ((a : Nat) : Int) < ((a : Nat) : Int) then ((a : Nat) : Int) else ((a : Nat) : Int)) = some r := by
        rw [← hval, hsqrt]
      exact Option.some_inj.mp this
    have hif : (if ((a : Nat) : Int) < ((a : Nat) : Int) then ((a : Nat) : Int) else ((a : Nat) : Int)) = ((a : Nat) : Int) := by
      have hneg : ¬ ((a : Nat) : Int) < ((a : Nat) : Int) := by omega
      rw [if_neg hneg]
    have hs : Nat.sqrt (Aval a) = a := seed_eq_sqrt a hseed.symm
    omega
  · have hloop := loop_eq_seed_ne a ha hle hseed
    have hval : sqrt ((a : Nat) : Int)
        = some (if (((Iter a 255 : Nat)) : Int) < (((Iter a 256 : Nat)) : Int) then (((Iter a 255 : Nat)) : Int) else (((Iter a 256 : Nat)) : Int)) := by
      rw [hsqrtEq, hloop]
      rfl
    have hfr : (if (((Iter a 255 : Nat)) : Int) < (((Iter a 256 : Nat)) : Int) then (((Iter a 255 : Nat)) : Int) else (((Iter a 256 : Nat)) : Int)) = r := by
      have : some (if (((Iter a 255 : Nat)) : Int) < (((Iter a 256 : Nat)) : Int) then (((Iter a 255 : Nat)) : Int) else (((Iter a 256 : Nat)) : Int)) = some r := by
        rw [← hval, hsqrt]
      exact Option.some_inj.mp this
    have hif : (if (((Iter a 255 : Nat)) : Int) < (((Iter a 256 : Nat)) : Int) then (((Iter a 255 : Nat)) : Int) else (((Iter a 256 : Nat)) : Int))
        = ((Nat.sqrt (Aval a) : Int)) := by
      rw [if_min_cast]
      have hmin := final_min a ha hle
      rw [hmin]
    omega

theorem aval_int_eq (a : Nat) : ((Aval a : Nat) : Int) = ((a : Nat) : Int) * DIVISOR := by
  unfold Aval DIVISOR
  have h10 : ((10 ^ 10 : Nat) : Int) = 10000000000 := by decide
  have e : ((a * 10 ^ 10 : Nat) : Int) = ((a : Nat) : Int) * (((10 ^ 10 : Nat)) : Int) := by
    exact_mod_cast rfl
  omega

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hsqrt
  by_cases hx0 : 0 ≤ x
  · obtain ⟨a, rfl⟩ : ∃ a : Nat, (x : Int) = ((a : Nat) : Int) := ⟨x.toNat, by omega⟩
    have hle : a ≤ 2 ^ 167 - 1 := by
      have hmax : MAX_DECIMAL = (((2 ^ 167 - 1 : Nat)) : Int) := max_decimal_eq
      unfold IsDecimal at hx
      omega
    by_cases ha0 : a = 0
    · subst ha0
      have h0 : (((0 : Nat)) : Int) = 0 := rfl
      rw [h0] at hsqrt ⊢
      have hr0 : r = 0 := by
        have h00 : sqrt 0 = some 0 := sqrt_zero_eq
        have : some (0 : Int) = some r := by rw [← h00, hsqrt]
        have h01 : (0 : Int) = r := Option.some_inj.mp this
        omega
      rw [hr0]
      simp
    · have haPos : 0 < a := by omega
      have hrEq := sqrt_eq_sqrt_cast a haPos hle r hsqrt
      have hNat : Nat.sqrt (Aval a) * Nat.sqrt (Aval a) ≤ Aval a := Nat.sqrt_le _
      have hNatInt : (↑(Nat.sqrt (Aval a) * Nat.sqrt (Aval a)) : Int)
          ≤ (↑(Aval a) : Int) := by exact_mod_cast hNat
      have hmul : (↑(Nat.sqrt (Aval a) * Nat.sqrt (Aval a)) : Int)
          = (↑(Nat.sqrt (Aval a)) : Int) * (↑(Nat.sqrt (Aval a)) : Int) := by exact_mod_cast rfl
      have hAval := aval_int_eq a
      rw [hmul, hAval] at hNatInt
      rw [hrEq] at ⊢
      exact hNatInt
  · have hlt : x < 0 := by omega
    have hnone := req_sqrt_neg_reverts x hlt
    have hcontra : (some r : Option Int) = none := by rw [← hsqrt, hnone]
    cases hcontra

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hsqrt
  by_cases hx0 : 0 ≤ x
  · obtain ⟨a, rfl⟩ : ∃ a : Nat, (x : Int) = ((a : Nat) : Int) := ⟨x.toNat, by omega⟩
    have hle : a ≤ 2 ^ 167 - 1 := by
      have hmax : MAX_DECIMAL = (((2 ^ 167 - 1 : Nat)) : Int) := max_decimal_eq
      unfold IsDecimal at hx
      omega
    by_cases ha0 : a = 0
    · subst ha0
      have h0 : (((0 : Nat)) : Int) = 0 := rfl
      rw [h0] at hsqrt ⊢
      have hr0 : r = 0 := by
        have h00 : sqrt 0 = some 0 := sqrt_zero_eq
        have : some (0 : Int) = some r := by rw [← h00, hsqrt]
        have h01 : (0 : Int) = r := Option.some_inj.mp this
        omega
      rw [hr0]
      simp
    · have haPos : 0 < a := by omega
      have hrEq := sqrt_eq_sqrt_cast a haPos hle r hsqrt
      have hNat : Aval a < (Nat.sqrt (Aval a) + 1) * (Nat.sqrt (Aval a) + 1) := Nat.lt_succ_sqrt _
      have hNatInt : (↑(Aval a) : Int)
          < (↑((Nat.sqrt (Aval a) + 1) * (Nat.sqrt (Aval a) + 1)) : Int) := by exact_mod_cast hNat
      have hmul1 : (↑((Nat.sqrt (Aval a) + 1) * (Nat.sqrt (Aval a) + 1)) : Int)
          = ((↑(Nat.sqrt (Aval a)) : Int) + 1) * ((↑(Nat.sqrt (Aval a)) : Int) + 1) := by
        have e1 : (↑(Nat.sqrt (Aval a) + 1) : Int) = (↑(Nat.sqrt (Aval a)) : Int) + 1 := by exact_mod_cast rfl
        have e2 : (↑((Nat.sqrt (Aval a) + 1) * (Nat.sqrt (Aval a) + 1)) : Int)
            = (↑(Nat.sqrt (Aval a) + 1) : Int) * (↑(Nat.sqrt (Aval a) + 1) : Int) := by exact_mod_cast rfl
        rw [e1] at e2
        exact e2
      have hAval := aval_int_eq a
      rw [hAval] at hNatInt
      rw [hmul1] at hNatInt
      rw [hrEq] at ⊢
      exact hNatInt
  · have hlt : x < 0 := by omega
    have hnone := req_sqrt_neg_reverts x hlt
    have hcontra : (some r : Option Int) = none := by rw [← hsqrt, hnone]
    cases hcontra

end VyperSqrt
