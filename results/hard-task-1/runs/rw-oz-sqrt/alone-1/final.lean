import OzSqrt.Spec
import OzSqrt.Lemmas
import Std.Tactic

/-!
Fixed square root: 7 Newton steps (deployed OpenZeppelin algorithm).
-/
namespace OzSqrt

theorem sq_add_sq_ge_two_mul (s u : Nat) : s * s + u * u ≥ 2 * s * u := by
  by_cases h : s ≤ u
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 : (s + k) * (s + k) = s * s + s * k + (k * s + k * k) := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
      ac_rfl
    have hc : k * s = s * k := Nat.mul_comm k s
    have e1 : (s + k) * (s + k) = s * s + 2 * (s * k) + k * k := by omega
    have h2 : (2 * s) * (s + k) = (2 * s) * s + (2 * s) * k := Nat.mul_add _ _ _
    have h3 : (2 * s) * s = 2 * (s * s) := by rw [Nat.mul_assoc]
    have h4 : (2 * s) * k = 2 * (s * k) := by rw [Nat.mul_assoc]
    have e2 : 2 * s * (s + k) = 2 * (s * s) + 2 * (s * k) := by omega
    omega
  · have h' : u ≤ s := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h'
    have h1 : (u + k) * (u + k) = u * u + u * k + (k * u + k * k) := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
      ac_rfl
    have hc : k * u = u * k := Nat.mul_comm k u
    have e1 : (u + k) * (u + k) = u * u + 2 * (u * k) + k * k := by omega
    have h0 : 2 * (u + k) * u = 2 * ((u + k) * u) := by rw [Nat.mul_assoc]
    have h2 : (u + k) * u = u * u + k * u := Nat.add_mul _ _ _
    have e2 : 2 * (u + k) * u = 2 * (u * u) + 2 * (u * k) := by omega
    omega

theorem am_gm (s u : Nat) (hu : 0 < u) : u + s * s / u ≥ 2 * s := by
  by_cases hs : s = 0
  · subst hs
    simp
  · have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs
    have hs2 : 1 ≤ 2 * s := by omega
    by_cases h : u + s * s / u ≥ 2 * s
    · exact h
    · have hlt : u + s * s / u < 2 * s := Nat.not_le.mp h
      have hmod := Nat.div_add_mod (s * s) u
      have hlt_u : s * s % u < u := Nat.mod_lt _ hu
      have hle : s * s / u + u ≤ 2 * s - 1 := by omega
      have hmul : (s * s / u + u) * u ≤ (2 * s - 1) * u :=
        Nat.mul_le_mul_right u hle
      have hexpand : (s * s / u + u) * u = s * s / u * u + u * u := Nat.add_mul _ _ _
      have hcomm : u * (s * s / u) = s * s / u * u := Nat.mul_comm _ _
      have hsucc : s * s % u + 1 ≤ u := Nat.succ_le_of_lt hlt_u
      have hsub : (2 * s - 1) + 1 = 2 * s := Nat.sub_add_cancel hs2
      have hmul2 : ((2 * s - 1) * u) + u = (2 * s) * u := by
        have htmp : ((2 * s - 1) + 1) * u = (2 * s) * u := by rw [Nat.sub_add_cancel hs2]
        rw [Nat.add_mul, Nat.one_mul] at htmp
        omega
      have hcontra : s * s + u * u < 2 * s * u := by omega
      have hge := sq_add_sq_ge_two_mul s u
      omega

theorem sqrt_le_iff (a n : Nat) : a ≤ Nat.sqrt n ↔ a * a ≤ n := by
  constructor
  · intro h
    have h1 : a * a ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul h h
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    omega
  · intro h
    by_cases hle : a ≤ Nat.sqrt n
    · exact hle
    · have hlt : Nat.sqrt n < a := Nat.lt_of_not_le hle
      have h1 : Nat.sqrt n + 1 ≤ a := by omega
      have h2 : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ a * a :=
        Nat.mul_le_mul h1 h1
      have h3 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
      omega

def natStep (N x : Nat) : Nat := (x + N / x) / 2
def natInit (N : Nat) : Nat := 2 ^ (Nat.log2 N / 2)
def natIter : Nat → Nat → Nat
  | N, 0 => natInit N
  | N, k + 1 => natStep N (natIter N k)

theorem two_pow_lt_256 {k : Nat} (hk : k < 256) : 2 ^ k < 2 ^ 256 := by
  have h1 : k + 1 ≤ 256 := Nat.succ_le_of_lt hk
  have h2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_succ (by decide : 1 < 2)
  have h3 : 2 ^ (k + 1) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide : 0 < 2) h1
  exact Nat.lt_of_lt_of_le h2 h3

theorem sqrt_pos_of_pos {N : Nat} (hN : 0 < N) : 0 < Nat.sqrt N := by
  have h1 : 1 * 1 ≤ N := by omega
  have h2 : 1 ≤ Nat.sqrt N := (sqrt_le_iff 1 N).mpr h1
  omega

theorem sqrt_lt_128 {N : Nat} (hN : N < 2 ^ 256) : Nat.sqrt N < 2 ^ 128 := by
  by_cases h : Nat.sqrt N < 2 ^ 128
  case pos => exact h
  case neg =>
    have hge : 2 ^ 128 ≤ Nat.sqrt N := Nat.le_of_not_lt h
    have h1 : (2 ^ 128) * (2 ^ 128) ≤ Nat.sqrt N * Nat.sqrt N :=
      Nat.mul_le_mul hge hge
    have h2 : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
    have h3 : (2 ^ 128) * (2 ^ 128) ≤ N := Nat.le_trans h1 h2
    have h4 : (2 ^ 128) * (2 ^ 128) = 2 ^ 256 := by
      rw [← Nat.pow_add]
    omega

theorem mul_div_half_le (s y : Nat) : s * (y / 2) ≤ (s * y) / 2 := by
  have hy : y = 2 * (y / 2) + y % 2 := by omega
  have hs : s * y = s * (2 * (y / 2) + y % 2) := congrArg (s * ·) hy
  have e : s * y = 2 * (s * (y / 2)) + s * (y % 2) := by
    rw [hs, Nat.mul_add]
    have h2 : s * (2 * (y / 2)) = 2 * (s * (y / 2)) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm s 2]
    omega
  omega

theorem x0_pos (N : Nat) : 0 < natInit N := by
  unfold natInit
  exact Nat.two_pow_pos _

theorem x0_sq_le {N : Nat} (hN : 0 < N) : (natInit N) * (natInit N) ≤ N := by
  have h0 : N ≠ 0 := Nat.ne_of_gt hN
  have hlog := (Nat.log2_eq_iff h0).mp rfl
  obtain ⟨hlo, _⟩ := hlog
  unfold natInit
  have hq : 2 * (Nat.log2 N / 2) ≤ Nat.log2 N := by omega
  have h1 : 2 ^ (2 * (Nat.log2 N / 2)) ≤ 2 ^ (Nat.log2 N) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hq
  have h2 : (2 ^ (Nat.log2 N / 2)) * (2 ^ (Nat.log2 N / 2)) = 2 ^ (2 * (Nat.log2 N / 2)) := by
    rw [← Nat.pow_add]
  omega

theorem x0_lt_4 {N : Nat} (hN : 0 < N) : N < 4 * ((natInit N) * (natInit N)) := by
  have h0 : N ≠ 0 := Nat.ne_of_gt hN
  have hlog := (Nat.log2_eq_iff h0).mp rfl
  obtain ⟨_, hhi⟩ := hlog
  have hmod : Nat.log2 N % 2 < 2 := Nat.mod_lt _ (by decide : 0 < 2)
  have hdiv := Nat.div_add_mod (Nat.log2 N) 2
  unfold natInit
  have hsq : (2 ^ (Nat.log2 N / 2)) * (2 ^ (Nat.log2 N / 2)) = 2 ^ (2 * (Nat.log2 N / 2)) := by
    rw [← Nat.pow_add]
  have hexp : Nat.log2 N + 1 ≤ 2 * (Nat.log2 N / 2) + 2 := by omega
  have h1 : 2 ^ (Nat.log2 N + 1) ≤ 2 ^ (2 * (Nat.log2 N / 2) + 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  have h2 : 2 ^ (2 * (Nat.log2 N / 2) + 2) = 4 * (2 ^ (2 * (Nat.log2 N / 2))) := by
    rw [Nat.pow_add]
    decide
  omega

theorem newton_preserve {N x : Nat} (hN : 0 < N)
    (hx : 0 < x) (hle : Nat.sqrt N ≤ x) (hub : Nat.sqrt N * x ≤ N) :
    Nat.sqrt N ≤ natStep N x ∧ Nat.sqrt N * natStep N x ≤ N := by
  have hs : 0 < Nat.sqrt N := sqrt_pos_of_pos hN
  have hq : Nat.sqrt N ≤ N / x := (Nat.le_div_iff_mul_le hx).mpr hub
  have hsum : 2 * Nat.sqrt N ≤ x + N / x := by omega
  have hstep : natStep N x = (x + N / x) / 2 := rfl
  have hge : Nat.sqrt N ≤ (x + N / x) / 2 := by
    have h1 : (2 * Nat.sqrt N) / 2 ≤ (x + N / x) / 2 :=
      Nat.div_le_div_right hsum
    have h2 : (2 * Nat.sqrt N) / 2 = Nat.sqrt N := by omega
    omega
  have hq_le : N / x ≤ N / Nat.sqrt N := Nat.div_le_div_left hle hs
  have hNs : Nat.sqrt N * (N / Nat.sqrt N) ≤ N := by
    have h1 : N / Nat.sqrt N * Nat.sqrt N ≤ N := Nat.div_mul_le_self N (Nat.sqrt N)
    have h2 : Nat.sqrt N * (N / Nat.sqrt N) = N / Nat.sqrt N * Nat.sqrt N :=
      Nat.mul_comm _ _
    omega
  have hsq : Nat.sqrt N * (N / x) ≤ N := by
    have h1 : Nat.sqrt N * (N / x) ≤ Nat.sqrt N * (N / Nat.sqrt N) :=
      Nat.mul_le_mul_left _ hq_le
    omega
  have hsum2 : Nat.sqrt N * (x + N / x) ≤ 2 * N := by
    have h1 : Nat.sqrt N * (x + N / x) = Nat.sqrt N * x + Nat.sqrt N * (N / x) :=
      Nat.mul_add _ _ _
    omega
  have hdiv : (Nat.sqrt N * (x + N / x)) / 2 ≤ N := by
    have h1 : (Nat.sqrt N * (x + N / x)) / 2 ≤ (2 * N) / 2 :=
      Nat.div_le_div_right hsum2
    have h2 : (2 * N) / 2 = N := by omega
    omega
  have hmul : Nat.sqrt N * ((x + N / x) / 2) ≤ (Nat.sqrt N * (x + N / x)) / 2 :=
    mul_div_half_le _ _
  rw [hstep]
  exact ⟨hge, Nat.le_trans hmul hdiv⟩

theorem init_eq (a : U256) : ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have hlog : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
  have hshr : ((log2 a >>> (1 : Nat))).toNat = (log2 a).toNat >>> 1 := BitVec.toNat_ushiftRight _ _
  have hshr2 : ((log2 a >>> (1 : Nat))).toNat = (log2 a).toNat / 2 := by
    rw [hshr, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hlog2 : ((log2 a >>> (1 : Nat))).toNat = Nat.log2 a.toNat / 2 := by
    rw [hshr2, hlog]
  have hshift_eq : ((1 : U256) <<< (log2 a >>> (1 : Nat))) = ((1 : U256).shiftLeft ((log2 a >>> (1 : Nat))).toNat) := rfl
  have hshift : (((1 : U256).shiftLeft ((log2 a >>> (1 : Nat))).toNat)).toNat = (1 : U256).toNat <<< ((log2 a >>> (1 : Nat))).toNat % 2 ^ 256 := BitVec.toNat_shiftLeft
  have hone : ((1 : U256)).toNat = 1 := BitVec.toNat_one (by decide : 0 < 256)
  have hinit : (((1 : U256) <<< (log2 a >>> (1 : Nat)))).toNat = (1 : Nat) <<< ((log2 a >>> (1 : Nat))).toNat % 2 ^ 256 := by
    rw [hshift_eq, hshift, hone]
  rw [hinit, hlog2, Nat.shiftLeft_eq, Nat.one_mul]
  have hk2 : Nat.log2 a.toNat / 2 < 256 := by
    by_cases h0 : a.toNat = 0
    · rw [h0, Nat.log2_zero]
      decide
    · have ha : a.toNat < 2 ^ 256 := a.isLt
      have hL : Nat.log2 a.toNat < 256 := (Nat.log2_lt h0).mpr ha
      omega
  have hlt : 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256 := two_pow_lt_256 hk2
  rw [Nat.mod_eq_of_lt hlt]

def sqrt : SqrtFn := newtonSqrt 7

theorem req_newton_budget : NewtonBudget sqrt := by
  exact ⟨7, by omega, fun a => rfl⟩

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  unfold sqrt newtonSqrt
  by_cases h0 : a = 0
  · subst h0
    simp
  · have hif : (if a = 0 then (0 : U256) else min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))) = min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) := by
      rw [if_neg h0]
    rw [hif]
    have hmin : (min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat = Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat ((a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat := toNat_min _ _
    rw [hmin]
    have hdiv : ((a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat = a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat := BitVec.toNat_udiv
    rw [hdiv]
    have h1 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat := Nat.min_le_left _ _
    have h2 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat := Nat.min_le_right _ _
    have h3 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
      Nat.mul_le_mul (Nat.le_refl _) h1
    have h4 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat ≤ (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
      Nat.mul_le_mul_right _ h2
    have h5 : (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat ≤ a.toNat :=
      Nat.div_mul_le_self _ _
    omega
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight : SqrtUpTight sqrt := sorry
theorem req_mint_backed : MintBacked sqrt := sorry
theorem req_mint_full : MintFull sqrt := sorry
theorem req_mint_live : MintLive sqrt := sorry

end OzSqrt
