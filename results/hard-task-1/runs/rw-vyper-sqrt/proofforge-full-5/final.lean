import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
/-!
Fix of the Vyper `sqrt()` builtin on decimals (pull request 4486): take the smaller of the
last two Babylonian iterates, so the result is the root rounded down.
-/
namespace VyperSqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  rw [ite_eq_left (by omega : x < 0)]

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨_, fun _ => rfl⟩

/-! ### Trajectory on natural numbers -/

/-- `A = a * 10^10`: the scaled radicand whose floor root we want. -/
def Aval (a : Nat) : Nat := a * 10^10

/-- The seed `x / 2.0 + 0.5` on raw values. -/
def seedOf (a : Nat) : Nat := a / 2 + 5 * 10^9

/-- The pure Newton trajectory from the seed. -/
def wtraj (a : Nat) : Nat → Nat
  | 0 => seedOf a
  | n + 1 => ProofForgeFin.Sqrt.newton (Aval a) (wtraj a n)

/-- The Newton loop with early stop, on natural numbers. -/
def nloop (A : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, y, z => (y, z)
  | n + 1, y, z =>
    if z = y then (y, z) else nloop A n z (ProofForgeFin.Sqrt.newton A z)

/-- Successive pairs of the trajectory: `upair 0 = (a, seed)`, then shift. -/
def upair (a : Nat) : Nat → Nat × Nat
  | 0 => (a, seedOf a)
  | n + 1 => ((upair a n).2, ProofForgeFin.Sqrt.newton (Aval a) (upair a n).2)

theorem wtraj_zero (a : Nat) : wtraj a 0 = seedOf a := rfl

theorem wtraj_succ (a n : Nat) :
    wtraj a (n + 1) = ProofForgeFin.Sqrt.newton (Aval a) (wtraj a n) := rfl

theorem nloop_zero (A y z : Nat) : nloop A 0 y z = (y, z) := rfl

theorem nloop_succ (A n y z : Nat) : nloop A (n + 1) y z =
    if z = y then (y, z) else nloop A n z (ProofForgeFin.Sqrt.newton A z) := rfl

theorem upair_zero (a : Nat) : upair a 0 = (a, seedOf a) := rfl

theorem upair_fst_succ (a n : Nat) : (upair a (n + 1)).1 = (upair a n).2 := rfl

theorem upair_snd_succ (a n : Nat) : (upair a (n + 1)).2 =
    ProofForgeFin.Sqrt.newton (Aval a) (upair a n).2 := rfl

/-- Division bounded by a multiple: `x ≤ z * y` gives `x / y ≤ z`. -/
theorem div_le_of_le_mul' (x y z : Nat) (h : x ≤ z * y) (hy : 0 < y) :
    x / y ≤ z := by
  have e := Nat.div_add_mod x y
  have hc : x / y * y = y * (x / y) := Nat.mul_comm _ _
  have hq : x / y * y ≤ z * y := by omega
  exact Nat.le_of_mul_le_mul_right hq hy

/-- The deployed loop with the min-choice computes the floor root on positive decimals. -/
theorem master (a : Nat) (ha0 : 0 < a) (haM : a ≤ 2^167 - 1) :
    vyperSqrtWith (fun y z => if y < z then y else z) (a : Int)
      = some ((Nat.sqrt (a * 10^10) : Nat) : Int) := by
  have F1 : 5*10^9 + (2^167-1)/2 ≤ 2^167-1 := by decide
  have F2 : (2:Nat)^101 ≤ (2^167-1)/2 + 5*10^9 := by decide
  have F3 : 2*10^10 + ((2^167-1)/2 + 5*10^9) ≤ 2^167-1 := by decide
  have F4 : (2^101+1) + ((2^167-1)/2 + 5*10^9) ≤ 2^167-1 := by decide
  have F5 : ((2^167-1)/2 + 5*10^9 + 2*10^10)/2 ≤ (2^167-1)/2 + 5*10^9 := by
    decide
  have F6 : (10^10:Nat) ≤ 2^34 := by decide
  have F8 : (10^10:Nat) ≤ 2*10^10*(5*10^9) := by decide
  have F10 : (100000*100000 : Nat) = 10^10 := by decide
  have hApos : 0 < Aval a := by
    unfold Aval
    exact Nat.mul_pos ha0 (by decide)
  have hseedpos : 0 < seedOf a := by unfold seedOf; omega
  have hs_lo : 100000 ≤ Nat.sqrt (Aval a) := by
    apply ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le
    rw [F10]
    unfold Aval
    have ha1 : 1 ≤ a := ha0
    have h := Nat.mul_le_mul_left (10^10) ha1
    rwa [Nat.mul_one, Nat.mul_comm] at h
  have hs_pos : 0 < Nat.sqrt (Aval a) := by omega
  have hs_ub : Nat.sqrt (Aval a) < 2^101 := by
    apply ProofForgeFin.Sqrt.sqrt_lt_two_pow (k := 101)
    have h202 : (2:Nat)*101 = 202 := rfl
    rw [h202]
    have hD : (10^10:Nat) ≤ 2^34 := F6
    have hM : a * 10^10 ≤ (2^167-1) * 2^34 := Nat.mul_le_mul haM hD
    have hlt : (2^167-1) * 2^34 < 2^167 * 2^34 :=
      Nat.mul_lt_mul_of_pos_right (by decide) (by decide)
    have heq : (2:Nat)^167 * 2^34 = 2^201 := (Nat.pow_add 2 167 34).symm
    have hle : (2:Nat)^201 ≤ 2^202 := Nat.pow_le_pow_right (by decide) (by decide)
    calc Aval a = a * 10^10 := rfl
      _ ≤ (2^167-1) * 2^34 := hM
      _ < 2^167 * 2^34 := hlt
      _ = 2^201 := heq
      _ ≤ 2^202 := hle
  have wpos : ∀ k, 0 < wtraj a k := by
    intro k
    induction k with
    | zero => exact hseedpos
    | succ k ih =>
      rw [wtraj_succ]
      by_cases hle : wtraj a k ≤ Aval a
      · have hd : 0 < Aval a / wtraj a k := Nat.div_pos hle ih
        unfold ProofForgeFin.Sqrt.newton
        omega
      · have hg : 0 ≤ Aval a / wtraj a k := Nat.zero_le _
        have h2 : 2 ≤ wtraj a k + Aval a / wtraj a k := by omega
        unfold ProofForgeFin.Sqrt.newton
        omega
  have wge : ∀ k, Nat.sqrt (Aval a) ≤ wtraj a (k+1) := by
    intro k
    induction k with
    | zero => rw [wtraj_succ]; exact ProofForgeFin.Sqrt.sqrt_le_newton (wpos 0)
    | succ k _ => rw [wtraj_succ]; exact ProofForgeFin.Sqrt.sqrt_le_newton (wpos _)
  have hAdiv0 : Aval a / seedOf a ≤ 2*10^10 := by
    have e2 := Nat.div_add_mod a 2
    have hm2 : a % 2 ≤ 1 := by
      have h2 : a % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have ha2 : a ≤ 2*(a/2) + 1 := by omega
    have hAle : Aval a ≤ 2*10^10 * seedOf a := by
      unfold Aval seedOf
      have h := Nat.mul_le_mul_right (10^10) ha2
      have eL : (2*(a/2)+1)*10^10 = 2*10^10*(a/2) + 10^10 := by
        rw [Nat.add_mul, Nat.mul_comm 2 (a/2), Nat.mul_assoc,
          Nat.mul_comm (a/2) (2*10^10), Nat.one_mul]
      rw [eL] at h
      rw [Nat.mul_add]
      exact Nat.le_trans h (Nat.add_le_add_left F8 _)
    have eA := Nat.div_add_mod (Aval a) (seedOf a)
    have hc : Aval a / seedOf a * seedOf a = seedOf a * (Aval a / seedOf a) :=
      Nat.mul_comm _ _
    have hm0 : 0 ≤ Aval a % seedOf a := Nat.zero_le _
    have hq : Aval a / seedOf a * seedOf a ≤ 2*10^10 * seedOf a := by omega
    exact Nat.le_of_mul_le_mul_right hq hseedpos
  have wle : ∀ k, wtraj a k ≤ (2^167-1)/2 + 5*10^9 := by
    intro k
    induction k with
    | zero =>
      have h := Nat.div_le_div_right (c := 2) haM
      exact Nat.add_le_add_right h _
    | succ k ih =>
      rw [wtraj_succ]
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · have hw0 : wtraj a 0 ≤ (2^167-1)/2 + 5*10^9 := by
          have h := Nat.div_le_div_right (c := 2) haM
          exact Nat.add_le_add_right h _
        have h1 : ProofForgeFin.Sqrt.newton (Aval a) (wtraj a 0)
            = (wtraj a 0 + Aval a / wtraj a 0) / 2 := rfl
        rw [h1]
        have h2 : (wtraj a 0 + Aval a / wtraj a 0) / 2
            ≤ ((2^167-1)/2 + 5*10^9 + 2*10^10)/2 := by
          apply Nat.div_le_div_right (c := 2)
          exact Nat.add_le_add hw0 hAdiv0
        exact Nat.le_trans h2 F5
      · have hk1 : k = (k-1) + 1 := by omega
        have hge : Nat.sqrt (Aval a) ≤ wtraj a k := by
          rw [hk1]; exact wge (k-1)
        by_cases heq : wtraj a k = Nat.sqrt (Aval a)
        · have hle1 := ProofForgeFin.Sqrt.newton_le_sqrt_add_one (a := Aval a)
            (wpos k) hge (by rw [heq]; simp)
          exact Nat.le_trans hle1 (by omega)
        · have hlt := ProofForgeFin.Sqrt.newton_lt_self
            (a := Aval a) (by omega : Nat.sqrt (Aval a) < wtraj a k)
          exact Nat.le_trans (Nat.le_of_lt hlt) ih
  have hAdivS : ∀ k, Aval a / wtraj a (k+1) ≤ Nat.sqrt (Aval a) + 2 := by
    intro k
    have hge : Nat.sqrt (Aval a) ≤ wtraj a (k+1) := wge k
    have hpos : 0 < wtraj a (k+1) := wpos _
    have e : Nat.sqrt (Aval a) * (Nat.sqrt (Aval a) + 2) + 1
        = (Nat.sqrt (Aval a)+1)*(Nat.sqrt (Aval a)+1) := by
      rw [Nat.mul_add, Nat.add_mul, Nat.mul_add, Nat.mul_add]
      simp only [Nat.mul_one, Nat.one_mul]
      omega
    have hAlt : Aval a < (Nat.sqrt (Aval a) + 1) * (Nat.sqrt (Aval a) + 1) :=
      Nat.lt_succ_sqrt _
    have hAs : Aval a ≤ Nat.sqrt (Aval a) * (Nat.sqrt (Aval a) + 2) := by omega
    have hXw : Aval a ≤ (Nat.sqrt (Aval a) + 2) * wtraj a (k+1) := by
      have h := Nat.mul_le_mul_right (Nat.sqrt (Aval a) + 2) hge
      rw [Nat.mul_comm (wtraj a (k+1)) (Nat.sqrt (Aval a)+2)] at h
      exact Nat.le_trans hAs h
    exact div_le_of_le_mul' _ _ _ hXw hpos
  have halve : ∀ j, wtraj a (j+1) - Nat.sqrt (Aval a)
      ≤ ((2^167-1) + 2*2^j) / 2^j := by
    intro j
    induction j with
    | zero =>
      have he1 : wtraj a 1 - Nat.sqrt (Aval a) ≤ 2^167-1 := by
        have h1 := wle 1
        omega
      have e0 : ((2^167-1) + 2*2^(0:Nat)) / 2^(0:Nat) = (2^167-1) + 2 := by
        rw [Nat.pow_zero, Nat.mul_one, Nat.div_one]
      rw [e0]
      show wtraj a 1 - Nat.sqrt (Aval a) ≤ (2^167-1) + 2
      omega
    | succ j ih =>
      have hge : Nat.sqrt (Aval a) ≤ wtraj a (j+1) := wge j
      have hpos : 0 < wtraj a (j+1) := wpos _
      have hstep := ProofForgeFin.Sqrt.newton_sub_sqrt_le_half (a := Aval a)
        hpos hge
      have hw : wtraj a (j+2) =
          ProofForgeFin.Sqrt.newton (Aval a) (wtraj a (j+1)) :=
        wtraj_succ a (j+1)
      have hU : (wtraj a (j+1) - Nat.sqrt (Aval a))/2 + 1
          ≤ (((2^167-1) + 2*2^j) / 2^j)/2 + 1 :=
        Nat.add_le_add_right (Nat.div_le_div_right (c := 2) ih) _
      have hp : 2^j * 2 = 2^(j+1) := by
        have e := (Nat.pow_add 2 j 1).symm
        rwa [Nat.pow_one] at e
      have hpos2 : 0 < 2^(j+1) := by
        have h := Nat.one_le_pow (j+1) 2 (by decide)
        omega
      have hUU : (((2^167-1) + 2*2^j) / 2^j)/2 + 1
          = ((2^167-1) + 2*2^(j+1)) / 2^(j+1) := by
        calc (((2^167-1) + 2*2^j) / 2^j)/2 + 1
            = ((2^167-1) + 2*2^j) / 2^(j+1) + 1 := by
              rw [Nat.div_div_eq_div_mul, hp]
          _ = (((2^167-1) + 2*2^j) + 1 * 2^(j+1)) / 2^(j+1) := by
              rw [Nat.add_mul_div_right _ _ hpos2]
          _ = ((2^167-1) + 2*2^(j+1)) / 2^(j+1) := by
              have h2 : ((2^167-1) + 2*2^j) + 1 * 2^(j+1)
                  = (2^167-1) + 2*2^(j+1) := by
                rw [Nat.mul_comm 2 (2^j), hp, Nat.one_mul]
                omega
              rw [h2]
      rw [hw]
      calc ProofForgeFin.Sqrt.newton (Aval a) (wtraj a (j+1))
            - Nat.sqrt (Aval a)
          ≤ (wtraj a (j+1) - Nat.sqrt (Aval a))/2 + 1 := hstep
        _ ≤ (((2^167-1) + 2*2^j) / 2^j)/2 + 1 := hU
        _ = ((2^167-1) + 2*2^(j+1)) / 2^(j+1) := hUU
  have hpow168 : (2:Nat)^168 = 2^167 * 2 := by decide
  have e168 : wtraj a 168 - Nat.sqrt (Aval a) ≤ 2 := by
    have h : wtraj a 168 - Nat.sqrt (Aval a)
        ≤ ((2^167-1) + 2*2^167) / 2^167 := halve 167
    have h2 : ((2^167-1) + 2*2^167) / 2^167
        = ((2^167-1) + 2^168) / 2^167 := by
      rw [Nat.mul_comm 2 (2^167), hpow168]
    have hUle : ((2^167-1) + 2^168) / 2^167 ≤ 2 := by
      have hUlt : ((2^167-1) + 2^168) / 2^167 < 3 := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2^167)]
        rw [hpow168]
        have hX : (1:Nat) ≤ 2^167 := by decide
        omega
      omega
    rw [h2] at h
    exact Nat.le_trans h hUle
  have w169 : Nat.sqrt (Aval a) ≤ wtraj a 169
      ∧ wtraj a 169 ≤ Nat.sqrt (Aval a) + 1 := by
    have hw : wtraj a 169 =
        ProofForgeFin.Sqrt.newton (Aval a) (wtraj a 168) :=
      wtraj_succ a 168
    constructor
    · rw [hw]; exact ProofForgeFin.Sqrt.sqrt_le_newton (wpos _)
    · rw [hw]
      have hge : Nat.sqrt (Aval a) ≤ wtraj a 168 := wge 167
      have hd : (wtraj a 168 - Nat.sqrt (Aval a))
          * (wtraj a 168 - Nat.sqrt (Aval a)) ≤ Nat.sqrt (Aval a) := by
        have h4 : (wtraj a 168 - Nat.sqrt (Aval a))
            * (wtraj a 168 - Nat.sqrt (Aval a)) ≤ 2*2 :=
          Nat.mul_le_mul e168 e168
        omega
      have hcase := ProofForgeFin.Sqrt.newton_eq_or_succ (a := Aval a)
        (wpos 168) hge hd
      rcases hcase with h | ⟨h, _⟩
      · rw [h]; omega
      · rw [h]; exact Nat.le_refl _
  have stay_plus : ∀ t, Nat.sqrt (Aval a) ≤ wtraj a (169+t)
      ∧ wtraj a (169+t) ≤ Nat.sqrt (Aval a)+1 := by
    intro t
    induction t with
    | zero => exact w169
    | succ t ih =>
      have hstep : wtraj a (169+(t+1)) =
          ProofForgeFin.Sqrt.newton (Aval a) (wtraj a (169+t)) := by
        have e : 169+(t+1) = (169+t)+1 := by omega
        rw [e]
        exact wtraj_succ a (169+t)
      rw [hstep]
      have hmem := ProofForgeFin.Sqrt.newton_of_mem (a := Aval a)
        (wpos _) ih.1 ih.2
      rcases hmem with h | ⟨_, h, _⟩
      · rw [h]; exact ⟨Nat.le_refl _, by omega⟩
      · rw [h]; exact ⟨by omega, Nat.le_refl _⟩
  have stay : ∀ k, 169 ≤ k → Nat.sqrt (Aval a) ≤ wtraj a k
      ∧ wtraj a k ≤ Nat.sqrt (Aval a)+1 := by
    intro k hk
    have h := stay_plus (k - 169)
    rwa [show 169 + (k - 169) = k from by omega] at h
  have upair_snd_eq : ∀ j, (upair a j).2 = wtraj a j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [upair_snd_succ, ih, wtraj_succ]
  have edge : seedOf a = a → a = Nat.sqrt (Aval a) := by
    intro h
    have e2 := Nat.div_add_mod a 2
    have hm2 : a % 2 ≤ 1 := by
      have h2 : a % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    unfold seedOf at h
    have hqr : a / 2 + a % 2 = 5 * 10^9 := by omega
    have har : a = 10^10 - a % 2 := by omega
    rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with hr | hr
    · have ha10 : a = 10^10 := by omega
      subst ha10
      exact (ProofForgeFin.Sqrt.sqrt_mul_self _).symm
    · have ha10 : a = 10^10 - 1 := by omega
      subst ha10
      have h1 : (10^10-1)*(10^10-1) ≤ Aval (10^10-1) := by
        unfold Aval
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have h2 : Aval (10^10-1) < ((10^10-1)+1)*((10^10-1)+1) := by
        unfold Aval
        have hd : (10^10-1) + 1 = 10^10 := by omega
        rw [hd]
        have hlt : (10^10-1) < 10^10 := by omega
        exact Nat.mul_lt_mul_of_pos_right hlt (by decide)
      exact (ProofForgeFin.Sqrt.sqrt_eq_of_bounds h1 h2).symm
  have fbound : ∀ j, j ≤ 256 → Aval a / wtraj a j + wtraj a j ≤ 2^167-1 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hposj
    · have h1' : Aval a / wtraj a 0 ≤ 2*10^10 := hAdiv0
      have h2' : wtraj a 0 ≤ (2^167-1)/2 + 5*10^9 := wle 0
      omega
    · have hjm : j = (j-1) + 1 := by omega
      have h1 : Aval a / wtraj a j ≤ Nat.sqrt (Aval a) + 2 := by
        rw [hjm]; exact hAdivS (j-1)
      have h2 : wtraj a j ≤ (2^167-1)/2 + 5*10^9 := wle j
      have hs : Nat.sqrt (Aval a) + 1 ≤ 2^101 := by omega
      omega
  have hstop_all : ∀ k, k + 1 ≤ 256 → (upair a k).2 = (upair a k).1 →
      nloop (Aval a) (256-k) (upair a k).1 (upair a k).2
        = (Nat.sqrt (Aval a), Nat.sqrt (Aval a)) := by
    intro k hk hzy
    have h256 : 256 - k = (256 - (k+1)) + 1 := by omega
    rw [h256, nloop_succ, if_pos hzy]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0] at hzy ⊢
      have hea : seedOf a = a := hzy
      have haS := edge hea
      show (a, seedOf a) = (Nat.sqrt (Aval a), Nat.sqrt (Aval a))
      rw [Prod.mk.injEq]
      exact ⟨haS, hea.trans haS⟩
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hj' : k = j + 1 := hj
      rw [hj'] at hzy ⊢
      have h2eq : (upair a (j+1)).2 = wtraj a (j+1) := upair_snd_eq _
      have h1eq : (upair a (j+1)).1 = wtraj a j :=
        (upair_fst_succ a j).trans (upair_snd_eq j)
      have hfixed : wtraj a (j+1) = wtraj a j := by omega
      have hnewt : ProofForgeFin.Sqrt.newton (Aval a) (wtraj a j)
          = wtraj a j := by
        have hwstep : wtraj a (j+1) =
            ProofForgeFin.Sqrt.newton (Aval a) (wtraj a j) :=
          wtraj_succ a j
        omega
      have hsfix : wtraj a j = Nat.sqrt (Aval a) :=
        ProofForgeFin.Sqrt.eq_sqrt_of_newton_eq_self (wpos _) hnewt
      have e1 : (upair a (j+1)).1 = Nat.sqrt (Aval a) := by omega
      have e2 : (upair a (j+1)).2 = Nat.sqrt (Aval a) := by omega
      rw [e1, e2]
  have hstep_all : ∀ k, k + 1 ≤ 256 → (upair a k).2 ≠ (upair a k).1 →
      nloop (Aval a) (256-k) (upair a k).1 (upair a k).2
        = nloop (Aval a) (256-(k+1)) (upair a (k+1)).1
          (upair a (k+1)).2 := by
    intro k hk hzy
    have h256 : 256 - k = (256 - (k+1)) + 1 := by omega
    rw [h256, nloop_succ, if_neg hzy, upair_fst_succ, upair_snd_succ]
  have R : ∀ k, k ≤ 256 → nloop (Aval a) 256 a (seedOf a)
      = nloop (Aval a) (256-k) (upair a k).1 (upair a k).2
      ∨ nloop (Aval a) 256 a (seedOf a)
        = (Nat.sqrt (Aval a), Nat.sqrt (Aval a)) := by
    intro k
    induction k with
    | zero =>
      intro _
      left
      rfl
    | succ k ih =>
      intro hk
      have hk' : k ≤ 256 := by omega
      by_cases hzy : (upair a k).2 = (upair a k).1
      · rcases ih hk' with h | h
        · exact Or.inr (h.trans (hstop_all k hk hzy))
        · exact Or.inr h
      · rcases ih hk' with h | h
        · exact Or.inl (h.trans (hstep_all k hk hzy))
        · exact Or.inr h
  have nloop_min : min (nloop (Aval a) 256 a (seedOf a)).1
      (nloop (Aval a) 256 a (seedOf a)).2 = Nat.sqrt (Aval a) := by
    have hR := R 255 (by decide)
    rcases hR with h | h
    · rw [h]
      have h255 : 256 - 255 = 1 := by decide
      rw [h255, nloop_succ]
      by_cases hzy : (upair a 255).2 = (upair a 255).1
      · rw [if_pos hzy]
        have h2eq : (upair a 255).2 = wtraj a 255 := upair_snd_eq 255
        have h1eq : (upair a 255).1 = wtraj a 254 :=
          (upair_fst_succ a 254).trans (upair_snd_eq 254)
        have hfixed : wtraj a 255 = wtraj a 254 := by omega
        have hnewt : ProofForgeFin.Sqrt.newton (Aval a) (wtraj a 254)
            = wtraj a 254 := by
          have hwstep : wtraj a 255 =
              ProofForgeFin.Sqrt.newton (Aval a) (wtraj a 254) :=
            wtraj_succ a 254
          omega
        have hsfix : wtraj a 254 = Nat.sqrt (Aval a) :=
          ProofForgeFin.Sqrt.eq_sqrt_of_newton_eq_self (wpos _) hnewt
        have e1 : (upair a 255).1 = Nat.sqrt (Aval a) := by omega
        have e2 : (upair a 255).2 = Nat.sqrt (Aval a) := by omega
        rw [e1, e2]
        exact Nat.min_self _
      · rw [if_neg hzy]
        have h0 : nloop (Aval a) 0 (upair a 255).2
            (ProofForgeFin.Sqrt.newton (Aval a) (upair a 255).2)
            = ((upair a 255).2,
              ProofForgeFin.Sqrt.newton (Aval a) (upair a 255).2) :=
          nloop_zero _ _ _
        rw [h0]
        have hmem := stay 255 (by decide)
        have h2eq : (upair a 255).2 = wtraj a 255 := upair_snd_eq 255
        rw [h2eq]
        show min (wtraj a 255)
          (ProofForgeFin.Sqrt.newton (Aval a) (wtraj a 255))
          = Nat.sqrt (Aval a)
        exact ProofForgeFin.Sqrt.min_newton_eq_sqrt (wpos _) hmem.1 hmem.2
    · rw [h]; exact Nat.min_self _
  have Q : ∀ m, m ≤ 256 → loop (a:Int) m ((upair a (256-m)).1 : Int)
        ((upair a (256-m)).2 : Int)
      = some (((nloop (Aval a) m (upair a (256-m)).1
        (upair a (256-m)).2).1 : Int),
        ((nloop (Aval a) m (upair a (256-m)).1
          (upair a (256-m)).2).2 : Int)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rfl
    | succ m ih =>
      intro hm
      have hm' : m ≤ 256 := by omega
      have ih' := ih hm'
      have hup : 256-(m+1) ≤ 256 := by omega
      by_cases hzy : (upair a (256-(m+1))).2 = (upair a (256-(m+1))).1
      · have hI : ((upair a (256-(m+1))).2 : Int)
            = ((upair a (256-(m+1))).1 : Int) := by rw [hzy]
        rw [nloop_succ, if_pos hzy, hI, loop_stop]
      · have hz : 0 < (upair a (256-(m+1))).2 := by
          rw [upair_snd_eq]
          exact wpos _
        have hfb : a*10^10/(upair a (256-(m+1))).2 + (upair a (256-(m+1))).2
            ≤ 2^167-1 := by
          have h := fbound (256-(m+1)) hup
          rw [upair_snd_eq]
          exact h
        have hbr : ((a*10^10/(upair a (256-(m+1))).2
            + (upair a (256-(m+1))).2)/2 : Nat)
            = ProofForgeFin.Sqrt.newton (Aval a) (upair a (256-(m+1))).2 := by
          unfold Aval ProofForgeFin.Sqrt.newton
          rw [Nat.add_comm]
        have hstepI := loop_step (a := a) (y := (upair a (256-(m+1))).1)
          (z := (upair a (256-(m+1))).2) m hz hzy hfb
        rw [hstepI, hbr, nloop_succ, if_neg hzy]
        have hjm : 256 - m = (256-(m+1)) + 1 := by omega
        rw [hjm, upair_fst_succ, upair_snd_succ] at ih'
        exact ih'
  have loop_some : loop (a:Int) 256 (a:Int) ((a/2+5*10^9 : Nat) : Int)
      = some (((nloop (Aval a) 256 a (seedOf a)).1 : Int),
        (((nloop (Aval a) 256 a (seedOf a)).2 : Int))) := Q 256 (Nat.le_refl _)
  have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha0 haM
  have hfin : ∀ m1 m2 : Nat, min m1 m2 = Nat.sqrt (Aval a) →
      (some (if (m1:Int) < (m2:Int) then (m1:Int) else (m2:Int))
        = some ((Nat.sqrt (a*10^10)) : Int)) := by
    intro m1 m2 hN
    by_cases hlt : m1 < m2
    · rw [if_pos (Int.ofNat_lt.mpr hlt)]
      have hm1 : m1 = Nat.sqrt (Aval a) := by omega
      exact congrArg (fun n : Nat => some ((n : Int))) hm1
    · rw [if_neg (fun hc => hlt (Int.ofNat_lt.mp hc))]
      have hm2 : m2 = Nat.sqrt (Aval a) := by omega
      exact congrArg (fun n : Nat => some ((n : Int))) hm2
  rw [hpos, loop_some]
  exact hfin _ _ nloop_min

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hdec hx0
  show (vyperSqrtWith (fun y z => if y < z then y else z) x).isSome
  by_cases hx : x = 0
  · subst hx
    unfold vyperSqrtWith
    rw [ite_eq_right (by omega : ¬ (0:Int) < 0), ite_eq_left rfl]
    rfl
  · have hxpos : 0 < x := by omega
    obtain ⟨a, rfl⟩ : ∃ a : Nat, (a:Int) = x := ⟨x.toNat, by omega⟩
    have haM : a ≤ 2^167 - 1 := by
      have hle : (a:Int) ≤ MAX_DECIMAL := hdec.2
      rw [max_decimal_eq] at hle
      exact Int.ofNat_le.mp hle
    have ha0 : 0 < a := by omega
    rw [master a ha0 haM]
    rfl

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hdec hsqrt
  have hsqrt' : vyperSqrtWith (fun y z => if y < z then y else z) x
      = some r := hsqrt
  by_cases hx0 : x < 0
  · have hnone : vyperSqrtWith (fun y z => if y < z then y else z) x
        = none := by
      unfold vyperSqrtWith
      rw [if_pos hx0]
    rw [hnone] at hsqrt'
    cases hsqrt'
  · by_cases hx00 : x = 0
    · subst hx00
      have hzero : vyperSqrtWith (fun y z => if y < z then y else z) 0
          = some 0 := by
        unfold vyperSqrtWith
        rw [ite_eq_right (by omega : ¬ (0:Int) < 0), ite_eq_left rfl]
      have hr : r = 0 := Option.some_inj.mp (hsqrt'.symm.trans hzero)
      subst hr
      decide
    · have hxpos : 0 < x := by omega
      obtain ⟨a, rfl⟩ : ∃ a : Nat, (a:Int) = x := ⟨x.toNat, by omega⟩
      have haM : a ≤ 2^167 - 1 := by
        have hle : (a:Int) ≤ MAX_DECIMAL := hdec.2
        rw [max_decimal_eq] at hle
        exact Int.ofNat_le.mp hle
      have ha0 : 0 < a := by omega
      have hm := master a ha0 haM
      have hr : ((Nat.sqrt (a*10^10) : Nat):Int) = r :=
        Option.some_inj.mp (hm.symm.trans hsqrt')
      rw [← hr, divisor_eq]
      exact_mod_cast Nat.sqrt_le (a*10^10)

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hdec hsqrt
  have hsqrt' : vyperSqrtWith (fun y z => if y < z then y else z) x
      = some r := hsqrt
  by_cases hx0 : x < 0
  · have hnone : vyperSqrtWith (fun y z => if y < z then y else z) x
        = none := by
      unfold vyperSqrtWith
      rw [if_pos hx0]
    rw [hnone] at hsqrt'
    cases hsqrt'
  · by_cases hx00 : x = 0
    · subst hx00
      have hzero : vyperSqrtWith (fun y z => if y < z then y else z) 0
          = some 0 := by
        unfold vyperSqrtWith
        rw [ite_eq_right (by omega : ¬ (0:Int) < 0), ite_eq_left rfl]
      have hr : r = 0 := Option.some_inj.mp (hsqrt'.symm.trans hzero)
      subst hr
      decide
    · have hxpos : 0 < x := by omega
      obtain ⟨a, rfl⟩ : ∃ a : Nat, (a:Int) = x := ⟨x.toNat, by omega⟩
      have haM : a ≤ 2^167 - 1 := by
        have hle : (a:Int) ≤ MAX_DECIMAL := hdec.2
        rw [max_decimal_eq] at hle
        exact Int.ofNat_le.mp hle
      have ha0 : 0 < a := by omega
      have hm := master a ha0 haM
      have hr : ((Nat.sqrt (a*10^10) : Nat):Int) = r :=
        Option.some_inj.mp (hm.symm.trans hsqrt')
      rw [← hr, divisor_eq]
      exact_mod_cast Nat.lt_succ_sqrt (a*10^10)

end VyperSqrt
