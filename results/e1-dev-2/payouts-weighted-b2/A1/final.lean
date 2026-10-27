import WeightedPayout.Spec
import WeightedPayout.Lemmas
namespace WeightedPayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_nonnegative_aux_mem3 {l : List AccountId} {x : AccountId} {i : Nat}
    (h : indexOf? l x = some i) : x ∈ l := by
  induction l generalizing i with
  | nil => simp [indexOf?] at h
  | cons y ys ih =>
    simp only [indexOf?] at h
    by_cases hy : y = x
    · subst hy; simp
    · simp only [hy, ite_false] at h
      cases hc : indexOf? ys x with
      | none => simp [hc] at h
      | some j =>
        simp [hc] at h
        have hmem := ih (i := j) hc
        simp [hmem]

theorem tmp_cast_test (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp

theorem tmp_omega_test (a b : Nat) (h : a ≤ b) : (a : Int) ≤ (b : Int) := by
  omega

theorem t1 : ∀ (a b : Nat), a * b = b * a := Nat.mul_comm

theorem t2 : ∀ (a b c : Nat), (a + b) * c = a * c + b * c := Nat.add_mul

theorem t3 (f W : Nat) : (f + 1) * W = f * W + W := by rw [Nat.add_mul, Nat.one_mul]

theorem t4 (a W : Nat) : W * (a / W) + a % W = a := Nat.div_add_mod a W

theorem probe2 : True := trivial
#check Nat.lt_of_mul_lt_mul_right
#check Nat.le_of_mul_le_mul_left
#check Nat.lt_of_mul_lt_mul_left
#check Nat.mul_lt_mul_right
#check Nat.mul_le_mul
#check List.length_map
#check List.getD
#check List.range
#check Nat.div_mul_le_self

theorem natSum_pos_of_mem (ws : List Nat) (hne : ws ≠ []) (hall : ∀ w ∈ ws, 0 < w) : 0 < natSum ws := by
  cases ws with
  | nil => simp at hne
  | cons w ws =>
    simp only [natSum]
    have hw : 0 < w := hall w (by simp)
    omega

theorem natSum_eq_zero_iff (ws : List Nat) : natSum ws = 0 ↔ ∀ w ∈ ws, w = 0 := by
  induction ws with
  | nil => simp [natSum]
  | cons w ws ih =>
    simp only [natSum]
    constructor
    · intro h w' hm
      simp at hm
      cases hm with
      | inl heq => subst heq; omega
      | inr hmem =>
        have := ih.mp (by omega : natSum ws = 0)
        exact this w' hmem
    · intro h
      have hw : w = 0 := h w (by simp)
      have ht : natSum ws = 0 := ih.mpr (fun w' hm => h w' (by simp [hm]))
      omega

theorem probe_nat_lemmas : True := trivial
#check Nat.div_mul_le_self
#check Nat.le_of_mul_le_mul_right
#check Nat.le_of_mul_le_mul_left
#check Nat.mul_le_mul_right
#check Nat.mul_le_mul_left
#check Nat.div_add_mod
#check Nat.mod_lt
#check Nat.add_sub_cancel
#check Nat.sub_add_cancel
#check Nat.mul_add
#check Nat.add_mul

theorem req_rounding_bound_aux_test : True := trivial

theorem probe_div_lt (P W : Nat) (hW : 0 < W) : P < (P / W + 1) * W := by
  have hmod : P % W < W := Nat.mod_lt P hW
  have hdm : W * (P / W) + P % W = P := Nat.div_add_mod P W
  have hcomm : W * (P / W) = (P / W) * W := Nat.mul_comm _ _
  have hexp : (P / W + 1) * W = (P / W) * W + W := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem probe_lift_le (d W P : Nat) (h : d * W ≤ P + W) : ((d * W : Nat) : Int) ≤ ((P + W : Nat) : Int) := by omega

theorem probe_lift_lt (d W P : Nat) (h : P < d * W + W) : ((P : Nat) : Int) < ((d * W + W : Nat) : Int) := by omega

theorem probe_rw1 (d W : Nat) : ((d * W : Nat) : Int) = (d : Int) * (W : Int) := by simp

theorem probe_rw2 (P W : Nat) : ((P + W : Nat) : Int) = (P : Int) + (W : Int) := by simp

theorem probe_set_test (a : Nat) : a = a := by rfl

theorem round_int_of_nat (d W P : Nat) (h1 : d * W ≤ P + W) (h2 : P < d * W + W)
    (dI Wl PI : Int) (hd : (d : Int) = dI) (hW : (W : Int) = Wl) (hP : (P : Int) = PI) :
    dI * Wl ≤ PI + Wl ∧ PI < dI * Wl + Wl := by
  have g1 : ((d * W : Nat) : Int) ≤ ((P + W : Nat) : Int) := by omega
  have g2 : ((P : Nat) : Int) < ((d * W + W : Nat) : Int) := by omega
  have e1 : ((d * W : Nat) : Int) = dI * Wl := by simp [hd, hW]
  have e2 : ((P + W : Nat) : Int) = PI + Wl := by simp [hP, hW]
  have e3 : ((P : Nat) : Int) = PI := hP
  have e4 : ((d * W + W : Nat) : Int) = dI * Wl + Wl := by simp [hd, hW]
  rw [e1, e2] at g1
  rw [e3, e4] at g2
  exact ⟨g1, g2⟩

theorem round_helper_nat (P W f : Nat) (hW : 0 < W) (hf : f = P / W) :
    f * W ≤ P ∧ P < (f + 1) * W := by
  have h1 : f * W ≤ P := by rw [hf]; exact Nat.div_mul_le_self P W
  have hmod : P % W < W := Nat.mod_lt P hW
  have hdm : W * (P / W) + P % W = P := Nat.div_add_mod P W
  have hcomm : W * (P / W) = (P / W) * W := Nat.mul_comm _ _
  have hexp : (f + 1) * W = f * W + W := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : P < (f + 1) * W := by rw [hf] at hexp ⊢; omega
  exact ⟨h1, h2⟩

theorem probe_cancel1 : ∀ (a b k : Nat), 0 < k → a * k ≤ b * k → a ≤ b := by
  intro a b k hk h
  exact Nat.le_of_mul_le_mul_right h hk
#check Nat.le_of_mul_le_mul_right
#check Nat.le_of_mul_le_mul_left
#check Nat.mul_lt_mul_right
#check Nat.div_mul_le_self

theorem probe_swap_check : True := trivial

theorem natSum_cons2 (x : Nat) (xs : List Nat) : natSum (x :: xs) = x + natSum xs := rfl

theorem natSum_append_test (l1 l2 : List Nat) : natSum (l1 ++ l2) = natSum l1 + natSum l2 := by
  induction l1 with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc]

theorem natSum_map_mul_test (l : List Nat) (k : Nat) : natSum (l.map (· * k)) = natSum l * k := by
  induction l with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_mul]
#check Nat.div_mul_le_self
#check Nat.div_add_mod
#check Nat.mod_lt
#check Nat.le_of_mul_le_mul_right

theorem natSum_map_le_test (ws : List Nat) (f g : Nat → Nat)
    (h : ∀ w ∈ ws, f w ≤ g w) : natSum (ws.map f) ≤ natSum (ws.map g) := by
  induction ws with
  | nil => simp [natSum]
  | cons w ws ih =>
    simp only [List.map_cons, natSum]
    have hw : f w ≤ g w := h w (by simp)
    have ht : natSum (ws.map f) ≤ natSum (ws.map g) :=
      ih (fun w' hm => h w' (by simp [hm]))
    omega

theorem natSum_map_le_ok : True := trivial

theorem t_tmp : True := trivial

theorem sig_probe_aux : True := trivial

theorem sig_probe2 : True := trivial
#check Nat.div_add_mod
#check Nat.mod_lt
#check Nat.div_mul_le_self
#check Nat.le_of_mul_le_mul_right
#check Nat.mul_add_div

theorem natSum_mul_map (ws : List Nat) (amount : Nat) :
    natSum (ws.map (fun w => amount * w)) = amount * natSum ws := by
  induction ws with
  | nil => simp [natSum]
  | cons w ws ih => simp [natSum, ih, Nat.mul_add]

theorem natSum_mul_map_ok : True := trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hv : ValidPayout s r
  · exact hv.2.2.2.2.2.2.2.2.2.1
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have e : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; simp [hv]
    rw [e]
    exact ⟨rfl, rfl, fun a => rfl⟩
  · have e1 : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [e1] at h
    contradiction

theorem req_idempotency    : Idempotent step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have e : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; simp [hv]
    have h2 : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
      rw [e]
    rw [h2]
    constructor
    · intro x
      simp only
      constructor
      · intro hx
        simp at hx
        exact hx
      · intro hx
        simp
        exact hx
    · have hNot : ¬ ValidPayout { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r := by
        intro hc
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hmem⟩ := hc
        simp at hmem
      have e2 : step { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r
          = (.rejected, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
        unfold step; simp [hNot]
      exact e2
  · have e1 : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [e1] at h
    contradiction

theorem req_nonnegative : NonNegative step := by
  intro s r hpos a ha
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    rw [hacc] at ha
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [hstep]
    rw [hbal]
    have hsrcNot : r.source ∉ r.recipients := hv.2.2.2.2.2.2.1
    have hle : (r.amount : Int) ≤ s.balance r.source := hv.2.2.2.2.2.2.2.2.2.2.1
    have hnonneg_a : 0 ≤ s.balance a := hpos a ha
    have hexp : expectedBalance s r a = s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int) := rfl
    rw [hexp]
    cases hidx : indexOf? r.recipients a with
    | none =>
      have hsh : shareOf r a = 0 := by unfold shareOf; rw [hidx]
      rw [hsh]
      by_cases heq : a = r.source
      · subst heq; simp; omega
      · simp [heq]; omega
    | some i =>
      have hmem : a ∈ r.recipients := req_nonnegative_aux_mem3 hidx
      have hsh : shareOf r a = weightedShare r.amount r.weights i := by unfold shareOf; rw [hidx]
      rw [hsh]
      by_cases heq : a = r.source
      · subst heq; exact absurd hmem hsrcNot
      · simp [heq]; omega
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have hbal : (step s r).2.balance a = s.balance a := by rw [hstep]
    rw [hacc] at ha
    rw [hbal]
    exact hpos a ha

theorem req_pro_rata : ProRataShares step := by
  intro s r h i hi
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hv]
    have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by rw [hstep]
    rw [hbal]
    obtain ⟨hnodup_acc, hpos_amt, hne_nil, hlen, hpos_w, hnodup_rec, hsrcNot, hsrcMem, hmem_acc, hauth, hle, htx⟩ := hv
    have hidx : indexOf? r.recipients r.recipients[i] = some i := indexOf?_getElem hnodup_rec i hi
    have hshare : shareOf r r.recipients[i] = weightedShare r.amount r.weights i := by
      unfold shareOf; rw [hidx]
    have hne_src : r.recipients[i] ≠ r.source := fun heq => hsrcNot (heq ▸ List.getElem_mem hi)
    unfold expectedBalance
    simp only [hne_src, ite_false]
    simp only [hshare]
    omega
  · have e1 : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [e1] at h
    contradiction

theorem req_rounding_bound : RoundingBound step := sorry

theorem req_conservation   : Conserves step := sorry

end WeightedPayout
