import WeightedPayout.Spec
import WeightedPayout.Lemmas
namespace WeightedPayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_idempotency_aux2 : Idempotent step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have h2 : (step s r).2 = ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) := by simp [step, hv]
    have hNot : ¬ ValidPayout ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) r := by
      intro hc
      unfold ValidPayout at hc
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hmem⟩ := hc
      simp at hmem
    have heq' : step ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) r = (.rejected, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := by
      simp [step, hNot]
    constructor
    · intro x
      rw [h2]
      simp
    · calc step (step s r).2 r
          = step ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State) r := by rw [h2]
        _ = (.rejected, ({ s with balance := expectedBalance s r, applied := r.txId :: s.applied } : State)) := heq'
        _ = (.rejected, (step s r).2) := by rw [h2]
  · simp [step, hv] at h

theorem rounding_nat_check2 (M W q d : Nat) (hW : 0 < W)
    (hqW : q * W ≤ M) (hmod : M < q * W + W) (hd : d = q ∨ d = q + 1) :
    d * W ≤ M + W ∧ M < d * W + W := by
  rcases hd with rfl | rfl
  · constructor
    · omega
    · omega
  · have hexpand : (q + 1) * W = q * W + W := by rw [Nat.add_mul, Nat.one_mul]
    rw [hexpand]
    constructor <;> omega

theorem natSum_pos_of_all_pos (ws : List Nat) (hpos : ∀ w ∈ ws, 0 < w)
    (hne : ws ≠ []) : 0 < natSum ws := by
  cases ws with
  | nil => contradiction
  | cons y ys =>
    have hy : 0 < y := hpos y (by simp)
    simp only [natSum]
    omega

theorem nat_div_bounds (M W : Nat) (hW : 0 < W) :
    M / W * W ≤ M ∧ M < M / W * W + W := by
  have h1 := Nat.div_add_mod M W
  have h2 := Nat.mod_lt M hW
  have hcomm : W * (M / W) = M / W * W := Nat.mul_comm _ _
  omega

theorem natSum_ge_length_aux (ws : List Nat) (hpos : ∀ w ∈ ws, 0 < w) : ws.length ≤ natSum ws := by
  induction ws with
  | nil => simp [natSum]
  | cons y ys ih =>
    have hy : 0 < y := hpos y (by simp)
    have htail : ∀ w ∈ ys, 0 < w := fun w hw => hpos w (by simp [hw])
    have iht := ih htail
    simp only [natSum, List.length_cons]
    omega

theorem sumOver_append_aux (l1 l2 : List Nat) (f : Nat → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons y ys ih => simp [ih]; omega

theorem sumOver_zero_aux (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem sumOver_add_symm_aux (l : List Nat) (f g : Nat → Int) :
    sumOver l f + sumOver l g = sumOver l (fun a => f a + g a) := by
  rw [sumOver_add]

theorem natSum_map_mul_aux (l : List Nat) (c : Nat) (f : Nat → Nat) :
    natSum (l.map (fun x => f x * c)) = natSum (l.map f) * c := by
  induction l with
  | nil => simp [natSum]
  | cons y ys ih => simp [natSum, ih, Nat.add_mul]

theorem sumOver_map_aux {α β : Type} (l : List α) (g : α → β) (F : β → Int) :
    sumOver (l.map g) F = sumOver l (fun a => F (g a)) := by
  induction l with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem tmp_check_tac : True := by
  trivial

theorem tmp_a1 (a b : Nat) (h : a = b) : a = b := h

theorem tmp_cast1 (a b : Nat) (h : a ≤ b) : (a : Int) ≤ (b : Int) := Int.ofNat_le.mpr h

theorem tmp_cast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp

theorem tmp_mul_cast (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by
  simp

theorem tmp_omega_test (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by
  omega

theorem cons_test_aux : True := trivial

theorem cons_sum_helper_test (ws : List Nat) : natSum ws = natSum ws := rfl
#check @Nat.div_mul_le_self
#check @Nat.mul_div_cancel
#check @Nat.le_div_iff_mul_le
#check @List.range
#check @List.erase

theorem range_check1 : List.range 3 = [0,1,2] := rfl
#check @List.range_succ
#check @List.nodup_range
#check @List.mem_range

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  show (step s r).1 = .ok
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · unfold ValidPayout at hv
    obtain ⟨_, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · simp [step, hv] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · simp [step, hv]
  · simp [step, hv] at h

theorem req_idempotency : Idempotent step := req_idempotency_aux2

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hacc : (step s r).2.accounts = s.accounts := by simp [step, hv]
    rw [hacc] at ha
    have hbal : (step s r).2.balance a = expectedBalance s r a := by simp [step, hv]
    rw [hbal]
    have ha0 : 0 ≤ s.balance a := hnn a ha
    unfold ValidPayout at hv
    obtain ⟨hnodup, hamtpos, hne, hlen, hpos, hrnodup, hsrcNot, hsrcIn, hrecIn, hauth, hle, htxNot⟩ := hv
    unfold expectedBalance
    by_cases heq : a = r.source
    · subst heq
      have hshare0 : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrcNot]
      rw [hshare0]
      simp
      omega
    · simp [heq]
      have hge : (0 : Int) ≤ (shareOf r a : Int) := Int.natCast_nonneg _
      omega
  · have hst : step s r = (.rejected, s) := by simp [step, hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hst]
    have hbal : (step s r).2.balance a = s.balance a := by rw [hst]
    rw [hacc] at ha
    rw [hbal]
    exact hnn a ha

theorem req_pro_rata : ProRataShares step := by
  intro s r h i hi
  by_cases hv : ValidPayout s r
  · have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by simp [step, hv]
    rw [hbal]
    obtain ⟨hnodup, hamtpos, hne, hlen, hpos, hrnodup, hsrcNot, hsrcIn, hrecIn, hauth, hle, htxNot⟩ := hv
    have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_src : r.recipients[i] ≠ r.source := fun heq => hsrcNot (heq ▸ hmem)
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hrnodup i hi
    have hshare : shareOf r r.recipients[i] = weightedShare r.amount r.weights i := by
      unfold shareOf
      rw [hidx]
    unfold expectedBalance
    have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by simp [hne_src]
    rw [hif, hshare]
    simp
    omega
  · simp [step, hv] at h

theorem req_rounding_bound : RoundingBound step := sorry

theorem req_conservation   : Conserves step := sorry

end WeightedPayout
