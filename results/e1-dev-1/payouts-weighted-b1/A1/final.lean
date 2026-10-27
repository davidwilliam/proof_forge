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

theorem tmp_omega_test (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by omega

theorem tmp_probe9 (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem tmp_probe10 (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by simp

theorem tmp_probe11 (a b : Nat) (h : a ≤ b) : (a : Int) ≤ (b : Int) := by simp [h]

theorem tmp_probe10b (f W : Nat) : (((f * W : Nat)) : Int) = ((f : Nat) : Int) * (W : Int) := by simp

theorem tmp_lt_probe (a b : Nat) (h : a < b) : (a : Int) < (b : Int) := by simp [h]

theorem tmp_le_trans_test (f W amt : Nat) (h : (f + 1) * W ≤ amt + W) :
    (((f + 1 : Nat) : Int) * (W : Int) ≤ ((amt : Nat) : Int) + (W : Int)) := by
  have e : ((((f + 1) * W : Nat)) : Int) ≤ (((amt + W : Nat)) : Int) := tmp_probe11 _ _ h
  simpa using e

theorem tmp_distrib (f W : Nat) : (f + 1) * W = f * W + W := by
  rw [Nat.add_mul, Nat.one_mul]
#check Nat.add_mul
#check Nat.one_mul
#check Nat.mul_comm
#check Nat.div_mul_le_self
#check Nat.div_add_mod
#check Nat.mod_lt

theorem tmp_range1 : List.range 0 = ([] : List Nat) := rfl

theorem tmp_range2 : List.range 1 = [0] := rfl

theorem tmp_range3 : List.range 2 = [0,1] := rfl
#check List.range
#check List.range_succ
#check List.nodup_range
#check List.mem_range

theorem tmp_natSum_append (l1 l2 : List Nat) : natSum (l1 ++ l2) = natSum l1 + natSum l2 := by
  induction l1 with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc]

theorem tmp_Wpos_helper (ws : List Nat) (h : ∀ w ∈ ws, 0 < w) (hne : ws ≠ []) : 0 < natSum ws := by
  match ws with
  | [] => simp at hne
  | w :: ws => simp [natSum]; have := h w (by simp); omega

theorem tmp_natSum_map_add_fix (l : List Nat) (f g : Nat → Nat) :
    natSum (l.map (fun x => f x + g x)) = natSum (l.map f) + natSum (l.map g) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc, Nat.add_left_comm]

theorem tmp_natSum_map_mul_fix (l : List Nat) (W : Nat) :
    natSum (l.map (fun x => x * W)) = natSum l * W := by
  induction l with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_mul]

theorem tmp_floor_mul_le (a w W : Nat) : floorShare a W w * W ≤ a * w := by
  unfold floorShare
  exact Nat.div_mul_le_self _ _

theorem tmp_test_unfold (x : Nat) (xs : List Nat) (f : Nat → Nat) :
  (x :: xs).map f = f x :: xs.map f := rfl

theorem tmp_test_natSum (x : Nat) (xs : List Nat) : natSum (x :: xs) = x + natSum xs := rfl

theorem tmp_sumOver_append2 {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem probe_div1 (a b : Nat) : a / b * b ≤ a := Nat.div_mul_le_self a b

theorem probe_div2 (a b : Nat) (h : 0 < b) : a % b < b := Nat.mod_lt a h
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @Nat.div_mul_le_self

theorem helper_floor_le (n W : Nat) : n / W * W ≤ n := Nat.div_mul_le_self n W

theorem helper_floor_lt (n W : Nat) (hW : 0 < W) : n < (n / W + 1) * W := by
  have hmod : n % W < W := Nat.mod_lt n hW
  have hdm : W * (n / W) + n % W = n := Nat.div_add_mod n W
  have hrew : (n / W + 1) * W = W * (n / W) + W := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / W) W]
  omega

theorem helper_round_core (n W f d : Nat) (hW : 0 < W)
    (hf : f = n / W) (hd : d = f ∨ d = f + 1) : d * W ≤ n + W ∧ n < d * W + W := by
  have hle : f * W ≤ n := hf ▸ helper_floor_le n W
  have hlt : n < (f + 1) * W := by
    have h := helper_floor_lt n W hW
    rw [← hf] at h; exact h
  have hexpand : (f + 1) * W = f * W + W := by rw [Nat.add_mul, Nat.one_mul]
  rcases hd with rfl | rfl
  · constructor <;> omega
  · rw [hexpand]; constructor <;> omega

theorem helper_cast_probe2 (a b : Nat) (h : a ≤ b) : (a : Int) ≤ (b : Int) := by simp [h]

theorem helper_cast_probe3 (a b : Nat) (h : a < b) : (a : Int) < (b : Int) := by simp [h]

theorem helper_cast_add_probe (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem helper_cast_mul_probe (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by simp

theorem helper_nat_cast_le (a b : Nat) (h : a ≤ b) : (a : Int) ≤ (b : Int) := by simp [h]

theorem helper_nat_cast_lt (a b : Nat) (h : a < b) : (a : Int) < (b : Int) := by simp [h]

theorem helper_nat_cast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem helper_nat_cast_mul (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by simp

theorem probe_cast_goal2 (d W n : Nat) (h1 : d * W ≤ n + W) :
    (d : Int) * (W : Int) ≤ (n : Int) + (W : Int) := by
  have c1 := helper_nat_cast_le _ _ h1
  simp at c1
  exact c1

theorem probe_cast_goal3 (d W n : Nat) (h2 : n < d * W + W) :
    (n : Int) < (d : Int) * (W : Int) + (W : Int) := by
  have c2 := helper_nat_cast_lt _ _ h2
  simp at c2
  exact c2

theorem helper_natSum_le_natSum (l1 l2 : List Nat) (h : ∀ i (hi1 : i < l1.length) (hi2 : i < l2.length), l1[i] ≤ l2[i]) (hlen : l1.length = l2.length) : natSum l1 ≤ natSum l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [natSum]
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      simp at hlen
      simp [natSum]
      have hx : x ≤ y := by
        have := h 0 (by simp) (by simp)
        simpa using this
      have ht : natSum xs ≤ natSum ys := by
        apply ih
        · intro i hi1 hi2
          have := h (i+1) (by simpa using Nat.succ_lt_succ hi1) (by simpa using Nat.succ_lt_succ hi2)
          simpa using this
        · simpa using hlen
      omega

theorem helper_S_mul_le (amount W : Nat) (ws : List Nat) :
    natSum ((ws.map (floorShare amount W)).map (fun q => q * W)) ≤ natSum (ws.map (fun w => amount * w)) := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih =>
    simp only [List.map_cons, natSum]
    have h1 : floorShare amount W w * W ≤ amount * w := tmp_floor_mul_le amount w W
    omega

theorem helper_Wpos_of_valid (ws : List Nat) (hpos : ∀ w ∈ ws, 0 < w) (hne : ws ≠ []) : 0 < natSum ws := by
  match ws with
  | [] => simp at hne
  | w :: ws2 =>
    simp only [natSum]
    have hw : 0 < w := hpos w (by simp)
    omega

theorem helper_S_mul_eq (ws : List Nat) (amt W : Nat) :
    natSum ((ws.map (floorShare amt W)).map (fun q => q * W)) = natSum (ws.map (floorShare amt W)) * W := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih =>
    simp only [List.map_cons, natSum] at *
    rw [ih]
    rw [Nat.add_mul]

theorem helper_sum_amt_mul (ws : List Nat) (amt : Nat) :
    natSum (ws.map (fun w => amt * w)) = amt * natSum ws := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih => simp [natSum, ih, Nat.mul_add]

theorem helper_S_mul_le2 (amt W : Nat) (ws : List Nat) :
    natSum (ws.map (floorShare amt W)) * W ≤ amt * natSum ws := by
  have h1 : natSum ((ws.map (floorShare amt W)).map (fun q => q * W)) ≤ natSum (ws.map (fun w => amt * w)) := helper_S_mul_le amt W ws
  rw [helper_S_mul_eq] at h1
  rw [helper_sum_amt_mul] at h1
  exact h1

theorem tmp_cancel_test (S amt W : Nat) (hW : 0 < W) (h : S * W ≤ amt * W) : S ≤ amt := by
  exact Nat.le_of_mul_le_mul_right h hW

theorem helper_len_le_sum (ws : List Nat) (h : ∀ w ∈ ws, 0 < w) : ws.length ≤ natSum ws := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih =>
    simp only [natSum, List.length_cons]
    have hw : 0 < w := h w (by simp)
    have ih' : rest.length ≤ natSum rest := ih (fun x hx => h x (by simp [hx]))
    omega

theorem helper_range_bonus1 (n k : Nat) :
    sumOver (List.range n) (fun i => if i < k then (1 : Int) else 0) = (min k n : Nat) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    have hrw : List.range (n+1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [hrw, tmp_sumOver_append2]
    simp
    rw [ih]
    omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · obtain ⟨_,_,_,_,_,_,_,_,_,hauth,_,_⟩ := hv
    exact hauth
  · simp [step, hv] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · simp [step, hv]
  · simp [step, hv] at h

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · simp [step, h] at hok
  have hstep2 : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    simp [step, hv]
  constructor
  · intro x
    rw [hstep2]
    simp
  · have hnot : ¬ ValidPayout { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } r := by
      intro hvalid
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_, hmem⟩ := hvalid
      simp at hmem
    have hrr : step ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) r = (.rejected, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      simp [step, hnot]
    rw [← hstep2] at hrr
    exact hrr

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hacc : (step s r).2.accounts = s.accounts := by simp [step, hv]
    rw [hacc] at ha
    have hbal : (step s r).2.balance a = expectedBalance s r a := by simp [step, hv]
    rw [hbal]
    unfold expectedBalance
    have ha0 : 0 ≤ s.balance a := hnn a ha
    by_cases hsrc : a = r.source
    · subst hsrc
      have hnotin : r.source ∉ r.recipients := hv.2.2.2.2.2.2.1
      have hidx : indexOf? r.recipients r.source = none :=
        indexOf?_eq_none hnotin
      have hshare0 : shareOf r r.source = 0 := by simp [shareOf, hidx]
      rw [if_pos rfl, hshare0]
      simp
      have hle : (r.amount : Int) ≤ s.balance r.source := hv.2.2.2.2.2.2.2.2.2.2.1
      omega
    · rw [if_neg hsrc]
      simp
      omega
  · have hst : (step s r).2 = s := by simp [step, hv]
    have ha' : a ∈ s.accounts := by rw [← hst] at ha; simpa [hst] using ha
    have hb : (step s r).2.balance a = s.balance a := by simp [step, hv]
    rw [hb]
    exact hnn a ha'

theorem req_pro_rata : ProRataShares step := by
  intro s r hok i hi
  have hv : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · simp [step, h] at hok
  have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
    simp [step, hv]
  have hsrc_ne : r.recipients[i] ≠ r.source := by
    intro heq
    have hmem : r.source ∈ r.recipients := heq ▸ List.getElem_mem hi
    exact hv.2.2.2.2.2.2.1 hmem
  have hnodup : r.recipients.Nodup := hv.2.2.2.2.2.1
  -- careful: ValidPayout tuple order: check
  have hidx : indexOf? r.recipients r.recipients[i] = some i :=
    indexOf?_getElem hnodup i hi
  have hshare : shareOf r r.recipients[i] = weightedShare r.amount r.weights i := by
    simp [shareOf, hidx]
  unfold expectedBalance at hbal
  have hif : (r.recipients[i] = r.source) = False := by
    simp [hsrc_ne]
  -- hbal : new = old - (if ... ) + share
  rw [hbal]
  have hif2 : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by
    simp [hsrc_ne]
  rw [hif2]
  simp [hshare]
  omega

theorem req_rounding_bound : RoundingBound step := sorry

theorem req_conservation : Conserves step := sorry

end WeightedPayout
