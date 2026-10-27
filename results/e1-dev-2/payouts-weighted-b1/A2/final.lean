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

theorem req_rounding_bound_aux : True := trivial

theorem t_set2 (a : Nat) : a = a := by
  rfl

theorem t_calc2 (a b : Nat) (h : a = b) : a = b := by
  calc a = b := h
    _ = b := rfl

theorem t_cast_check (a b : Nat) (h : a ≤ b) : (a : Int) ≤ (b : Int) := by
  exact Int.ofNat_le.mpr h

theorem t_cast_add_check (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp

theorem t_cast_mul_check (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by
  simp

theorem t_div_mul_le (x W : Nat) : x / W * W ≤ x := Nat.div_mul_le_self x W

theorem t_cases_colon (ws : List Nat) (h : ws ≠ []) : 0 < 1 := by
  cases hws : ws with
  | nil => contradiction
  | cons w ws => trivial

theorem helper_natSum_pos_test (ws : List Nat) (h1 : ∀ w ∈ ws, 0 < w) (h2 : ws ≠ []) : 0 < natSum ws := by
  cases ws with
  | nil => contradiction
  | cons w ws =>
    simp [natSum]
    have hw : 0 < w := h1 w (by simp)
    omega

theorem helper_natSum_map_mul (l : List Nat) (k : Nat) : natSum (l.map (· * k)) = natSum l * k := by
  induction l with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_mul]

theorem helper_natSum_le_of_forall_le (l1 l2 : List Nat) (h : l1.length = l2.length)
    (hle : ∀ i (hi1 : i < l1.length) (hi2 : i < l2.length), l1[i] ≤ l2[i]) :
    natSum l1 ≤ natSum l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [natSum]
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp at h
      simp [natSum]
      have hx : x ≤ y := hle 0 (by simp) (by simp)
      have ht : natSum xs ≤ natSum ys := by
        apply ih
        · simpa using h
        · intro i hi1 hi2
          have := hle (i+1) (by simpa using hi1) (by simpa using hi2)
          simpa using this
      omega

theorem helper_natSum_map_mul2 (l : List Nat) (k : Nat) : natSum (l.map (fun x => k * x)) = k * natSum l := by
  induction l with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.mul_add]

theorem helper_div_add_le (x y W : Nat) : x / W + y / W ≤ (x + y) / W := by
  by_cases hW : W = 0
  · simp [hW]
  · have hWpos : 0 < W := Nat.pos_of_ne_zero hW
    have hx : x / W * W ≤ x := Nat.div_mul_le_self x W
    have hy : y / W * W ≤ y := Nat.div_mul_le_self y W
    have hsum : (x / W + y / W) * W ≤ x + y := by
      rw [Nat.add_mul]
      exact Nat.add_le_add hx hy
    have h := (Nat.le_div_iff_mul_le hWpos).mpr hsum
    exact h

theorem helper_natSum_append (l1 l2 : List Nat) : natSum (l1 ++ l2) = natSum l1 + natSum l2 := by
  induction l1 with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc]

theorem helper_lt_div_mul_add (x W : Nat) (hW : 0 < W) : x < x / W * W + W := by
  have h1 : W * (x / W) + x % W = x := Nat.div_add_mod x W
  have h1' : x / W * W + x % W = x := by rw [Nat.mul_comm] at h1; exact h1
  have h2 : x % W < W := Nat.mod_lt x hW
  omega

theorem helper_natSum_map_div_le (xs : List Nat) (W : Nat) :
    natSum ((xs.map (· / W))) ≤ (natSum xs) / W := by
  induction xs with
  | nil => simp [natSum]
  | cons x xs ih =>
    simp [natSum]
    have h := helper_div_add_le x (natSum xs) W
    have h2 : x / W + natSum (xs.map (· / W)) ≤ x / W + natSum xs / W := by
      have := Nat.add_le_add_left ih (x / W)
      simpa using this
    omega

theorem helper_W_pos (ws : List Nat) (hlen : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    0 < natSum ws := by
  cases ws with
  | nil => simp at hlen
  | cons w ws =>
    simp only [natSum]
    have hw : 0 < w := hpos w (by simp)
    omega

theorem helper_F_le_amount2 (amount : Nat) (ws : List Nat)
    (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    natSum (ws.map (floorShare amount (natSum ws))) ≤ amount := by
  have hWpos : 0 < natSum ws := helper_W_pos ws hne hpos
  have hmap : ws.map (floorShare amount (natSum ws)) = (ws.map (fun w => amount * w)).map (· / natSum ws) := by
    simp [floorShare]
  rw [hmap]
  have hle := helper_natSum_map_div_le (ws.map (fun w => amount * w)) (natSum ws)
  have heq : natSum (ws.map (fun w => amount * w)) = amount * natSum ws := helper_natSum_map_mul2 ws amount
  rw [heq] at hle
  have hdiv : (amount * natSum ws) / natSum ws = amount := Nat.mul_div_cancel _ hWpos
  rw [hdiv] at hle
  exact hle

theorem tmp_neg_test (s : State) (r : Request) (hok : (step s r).1 = .ok) (hv : ¬ ValidPayout s r) : False := by
  have hrej : (step s r).1 = .rejected := by unfold step; simp [hv]
  rw [hrej] at hok
  contradiction

theorem helper_cast_mul_test (F W : Nat) : (((F * W : Nat)) : Int) = ((F : Nat) : Int) * ((W : Nat) : Int) := by
  simp

theorem helper_expand_test (F W : Nat) : (F + 1) * W = F * W + W := by
  simp [Nat.add_mul, Nat.one_mul]





theorem plan0_natSum_pos (ws : List Nat) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) : 0 < natSum ws := helper_W_pos ws hne hpos


theorem plan0_weighted_share_nat_bounds (amount : Nat) (ws : List Nat) (i : Nat) (hW : 0 < natSum ws) :
    weightedShare amount ws i * natSum ws ≤ amount * ws.getD i 0 + natSum ws ∧
    amount * ws.getD i 0 < weightedShare amount ws i * natSum ws + natSum ws := by
  have h1 : (amount * ws.getD i 0 / natSum ws) * natSum ws ≤ amount * ws.getD i 0 :=
    Nat.div_mul_le_self _ _
  have h2 : amount * ws.getD i 0 < amount * ws.getD i 0 / natSum ws * natSum ws + natSum ws :=
    helper_lt_div_mul_add _ _ hW
  unfold weightedShare floorShare
  by_cases hb : i < leftover amount ws
  · simp only [hb, ↓reduceIte]
    have hexpand : (amount * ws.getD i 0 / natSum ws + 1) * natSum ws
        = amount * ws.getD i 0 / natSum ws * natSum ws + natSum ws := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hexpand]
    constructor <;> omega
  · simp only [hb, ↓reduceIte, Nat.add_zero]
    constructor <;> omega


theorem plan0_weighted_share_int_bounds (amount : Nat) (ws : List Nat) (i : Nat) (hW : 0 < natSum ws) :
    (weightedShare amount ws i : Int) * (natSum ws : Int) ≤ ((amount * ws.getD i 0 : Nat) : Int) + (natSum ws : Int) ∧
    ((amount * ws.getD i 0 : Nat) : Int) < (weightedShare amount ws i : Int) * (natSum ws : Int) + (natSum ws : Int) := by
  have hnat := plan0_weighted_share_nat_bounds amount ws i hW
  obtain ⟨h1, h2⟩ := hnat
  constructor
  · have h1c : ((weightedShare amount ws i * natSum ws : Nat) : Int) ≤ (((amount * ws.getD i 0 + natSum ws) : Nat) : Int) :=
      Int.ofNat_le.mpr h1
    simpa using h1c
  · have h2c : (((amount * ws.getD i 0 : Nat)) : Int) < (((weightedShare amount ws i * natSum ws + natSum ws) : Nat) : Int) :=
      Int.ofNat_lt.mpr h2
    simpa using h2c


theorem plan0_div_mul_le (x W : Nat) : x / W * W ≤ x := Nat.div_mul_le_self x W

theorem plan0_lt_div_mul_add_aux_unique123 (x W : Nat) (hW : 0 < W) : x < x / W * W + W := helper_lt_div_mul_add x W hW

theorem plan0_lt_div_mul_add (x W : Nat) (hW : 0 < W) : x < x / W * W + W := helper_lt_div_mul_add x W hW

theorem plan0_natSum_pos_fixed (ws : List Nat) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) : 0 < natSum ws := helper_W_pos ws hne hpos

theorem plan0_weighted_share_nat_bounds_aux_check2 (amount : Nat) (ws : List Nat) (i : Nat) (hW : 0 < natSum ws) :
    weightedShare amount ws i * natSum ws ≤ amount * ws.getD i 0 + natSum ws ∧
    amount * ws.getD i 0 < weightedShare amount ws i * natSum ws + natSum ws := by
  have h1 : (amount * ws.getD i 0 / natSum ws) * natSum ws ≤ amount * ws.getD i 0 :=
    Nat.div_mul_le_self _ _
  have h2 : amount * ws.getD i 0 < amount * ws.getD i 0 / natSum ws * natSum ws + natSum ws :=
    helper_lt_div_mul_add _ _ hW
  unfold weightedShare floorShare
  by_cases hb : i < leftover amount ws
  · simp only [hb, ↓reduceIte]
    have hexpand : (amount * ws.getD i 0 / natSum ws + 1) * natSum ws
        = amount * ws.getD i 0 / natSum ws * natSum ws + natSum ws := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hexpand]
    constructor <;> omega
  · simp only [hb, ↓reduceIte, Nat.add_zero]
    constructor <;> omega

theorem plan0_weighted_share_int_bounds_proofcheck (amount : Nat) (ws : List Nat) (i : Nat) (hW : 0 < natSum ws) :
    (weightedShare amount ws i : Int) * (natSum ws : Int) ≤ ((amount * ws.getD i 0 : Nat) : Int) + (natSum ws : Int) ∧
    ((amount * ws.getD i 0 : Nat) : Int) < (weightedShare amount ws i : Int) * (natSum ws : Int) + (natSum ws : Int) := by
  have hnat := plan0_weighted_share_nat_bounds amount ws i hW
  obtain ⟨h1, h2⟩ := hnat
  constructor
  · have h1c : ((weightedShare amount ws i * natSum ws : Nat) : Int) ≤ (((amount * ws.getD i 0 + natSum ws) : Nat) : Int) :=
      Int.ofNat_le.mpr h1
    simpa using h1c
  · have h2c : (((amount * ws.getD i 0 : Nat)) : Int) < (((weightedShare amount ws i * natSum ws + natSum ws) : Nat) : Int) :=
      Int.ofNat_lt.mpr h2
    simpa using h2c

theorem cons_sum_test (a : Nat) (l : List Nat) (F : Nat → Nat) :
    natSum ((a :: l).map F) = F a + natSum (l.map F) := by simp [natSum]

theorem tmp_range_test : List.range 3 = [0,1,2] := by rfl

theorem tmp_natSum_range : natSum [0,1,2] = 3 := by rfl

theorem tmp_range_succ (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  simp [List.range_succ]

theorem div_add_mod_test (x W : Nat) : W * (x / W) + x % W = x := Nat.div_add_mod x W

theorem mod_lt_test (x W : Nat) (hW : 0 < W) : x % W < W := Nat.mod_lt x hW

theorem mul_div_cancel_test (a : Nat) {b : Nat} (hb : 0 < b) : (a * b) / b = a := Nat.mul_div_cancel a hb

theorem sumOver_indicator_single (l : List Nat) (hl : l.Nodup) (x : Nat) (c : Int) :
    sumOver l (fun a => if a = x then c else 0) = if x ∈ l then c else 0 :=
  sumOver_ite_eq hl x c

theorem sumOver_zero_list (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem plan1_leftover_le_length (amount : Nat) (ws : List Nat)
    (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    leftover amount ws ≤ ws.length := by sorry

theorem plan1_natSum_weightedShare_range (amount : Nat) (ws : List Nat)
    (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) = amount := by sorry

theorem plan1_sumOver_eq_of_subset_zero {L M : List Nat} {f : Nat → Int}
    (hL : L.Nodup) (hM : M.Nodup)
    (hsub : ∀ x ∈ M, x ∈ L) (hzero : ∀ x, x ∉ M → f x = 0) :
    sumOver L f = sumOver M f := by sorry

theorem plan1_sumOver_recipients_shareOf (s : State) (r : Request)
    (h : ValidPayout s r) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry

theorem plan1_sumOver_expectedBalance_eq (s : State) (r : Request)
    (h : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance := by sorry

theorem plan1_leftover_le_length_test_aux : True := trivial
#check @Nat.mul_le_mul
#check @Nat.mul_lt_mul_of_pos_right
#check @Nat.le_of_mul_le_mul_right
#check @Nat.sub_add_cancel
#check @Nat.add_sub_cancel

theorem check_names_aux1 : True := trivial
#check @Nat.div_add_mod
#check @Nat.sub_add_cancel
#check @Nat.add_mul
#check @Nat.le_of_mul_le_mul_right
#check @Nat.mul_le_mul_right
#check @Nat.sub_mul
#check @Nat.mul_sub

theorem aux_decomp_ok3 (amount : Nat) : ∀ (l : List Nat) (W : Nat),
      natSum (l.map (fun w => amount * w))
        = W * natSum (l.map (fun w => amount * w / W))
          + natSum (l.map (fun w => (amount * w) % W)) := by
  intro l W
  induction l with
  | nil => simp [natSum]
  | cons x xs ih =>
    have h := Nat.div_add_mod (amount * x) W
    simp only [List.map_cons, natSum]
    rw [ih, Nat.mul_add]
    omega

theorem aux_sub_mul_test (a b c : Nat) : (a - b) * c = a * c - b * c := Nat.sub_mul a b c

theorem aux_bound_test (amount : Nat) (l : List Nat) (W : Nat) (hW : 0 < W) :
    natSum (l.map (fun w => (amount * w) % W)) ≤ l.length * W := by
  induction l with
  | nil => simp [natSum]
  | cons x xs ih =>
    simp only [List.map_cons, natSum, List.length_cons]
    have hlt : (amount * x) % W < W := Nat.mod_lt _ hW
    have h2 : (xs.length + 1) * W = xs.length * W + W := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [h2]
    omega

theorem plan2_natSum_map_amount_mul (amount : Nat) (l : List Nat) :
    natSum (l.map (fun w => amount * w)) = amount * natSum l := by sorry

theorem plan2_div_mod_decomp (amount : Nat) (l : List Nat) (W : Nat) :
    natSum (l.map (fun w => amount * w)) =
      W * natSum (l.map (fun w => amount * w / W)) +
        natSum (l.map (fun w => (amount * w) % W)) := by sorry

theorem plan2_remainder_sum_le (amount : Nat) (l : List Nat) (W : Nat) (hW : 0 < W) :
    natSum (l.map (fun w => (amount * w) % W)) ≤ l.length * W := by sorry

theorem plan2_mul_sub_add (W amount F : Nat) (hF : F ≤ amount) :
    W * (amount - F) + W * F = amount * W := by sorry

theorem plan2_key_eq (amount : Nat) (ws : List Nat) :
    natSum ws * natSum (ws.map (floorShare amount (natSum ws))) +
        natSum (ws.map (fun w => (amount * w) % natSum ws)) =
      amount * natSum ws := by sorry

theorem plan2_mul_leftover_le (amount : Nat) (ws : List Nat)
    (hW : 0 < natSum ws)
    (hF : natSum (ws.map (floorShare amount (natSum ws))) ≤ amount) :
    natSum ws * leftover amount ws ≤ ws.length * natSum ws := by sorry

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  unfold step at hok
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · simp [hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      unfold step
      simp [hv]
    rw [h2]
    exact ⟨rfl, rfl, fun a => rfl⟩
  · have hrej : (step s r).1 = .rejected := by
      unfold step
      simp [hv]
    rw [hrej] at hok
    contradiction

theorem req_idempotency    : Idempotent step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hv]
    have h1 : (step s r).1 = Outcome.ok := by rw [hstep]
    have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by rw [hstep]
    rw [h2]
    constructor
    · intro x; simp
    · have hnot : ¬ ValidPayout ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
        intro hcon
        unfold ValidPayout at hcon
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hnotin⟩ := hcon
        simp at hnotin
      have hstep2 : step ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r = (.rejected, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
        unfold step; simp [hnot]
      exact hstep2
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hrej] at hok
    contradiction

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  unfold step at ha ⊢
  by_cases hv : ValidPayout s r
  · simp only [hv, ↓reduceIte] at ha ⊢
    have ha_mem : a ∈ s.accounts := ha
    have hbal_nn : 0 ≤ s.balance a := hnn a ha_mem
    obtain ⟨hnodup, hpos, hne, hlen, hposw, hrnodup, hsrc_not, hsrc_mem, hrec_mem, hauth, hle, htx⟩ := hv
    show 0 ≤ expectedBalance s r a
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · have hnone : indexOf? r.recipients a = none := by
        subst hsrc; exact indexOf?_eq_none hsrc_not
      have hshare : shareOf r a = 0 := by unfold shareOf; rw [hnone]
      rw [hshare]
      simp [hsrc]
      omega
    · simp [hsrc]
      have hshare_nn : (0 : Int) ≤ (shareOf r a : Int) := Int.natCast_nonneg _
      omega
  · simp only [hv, ↓reduceIte] at ha ⊢
    exact hnn a ha

theorem req_pro_rata : ProRataShares step := by
  intro s r hok i hi
  by_cases hv : ValidPayout s r
  · have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      unfold step
      simp [hv]
    rw [h2]
    show expectedBalance s r r.recipients[i] - s.balance r.recipients[i] = _
    obtain ⟨_, _, _, _, _, hrnodup, hsrc_not, _, _, _, _, _⟩ := hv
    have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne : r.recipients[i] ≠ r.source := fun h => hsrc_not (h ▸ hmem)
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hrnodup i hi
    have hshare : shareOf r r.recipients[i] = weightedShare r.amount r.weights i := by
      unfold shareOf; rw [hidx]
    unfold expectedBalance
    have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by
      simp [hne]
    rw [hif, hshare]
    omega
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hrej] at hok
    contradiction

theorem req_rounding_bound : RoundingBound step := by
  intro s r hok i hi
  by_cases hv : ValidPayout s r
  · have hpr : (step s r).2.balance r.recipients[i] - s.balance r.recipients[i]
        = (weightedShare r.amount r.weights i : Int) := req_pro_rata s r hok i hi
    obtain ⟨hnodup, hpos, hne, hlen, hposw, hrnodup, hsrc_not, hsrc_mem, hrec_mem, hauth, hle, htx⟩ := hv
    have hws_ne : r.weights ≠ [] := by
      intro hcon
      have hlen0 : r.weights.length = 0 := by rw [hcon]; rfl
      have hrec0 : r.recipients.length = 0 := by omega
      have : r.recipients = [] := List.length_eq_zero_iff.mp hrec0
      exact hne this
    have hWpos : 0 < natSum r.weights := helper_W_pos r.weights hws_ne hposw
    have hb := plan0_weighted_share_int_bounds r.amount r.weights i hWpos
    rw [hpr]
    exact hb
  · have hrej : (step s r).1 = .rejected := by unfold step; simp [hv]
    rw [hrej] at hok
    contradiction

theorem req_conservation   : Conserves step := sorry

end WeightedPayout
