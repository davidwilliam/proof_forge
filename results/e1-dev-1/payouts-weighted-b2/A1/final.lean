import WeightedPayout.Spec
import WeightedPayout.Lemmas
namespace WeightedPayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if _ : ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_effects_aux_test : True := trivial
#check (step)

theorem req_effects2 : Effects step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · unfold step at hok ⊢
    simp [hv] at hok ⊢
  · unfold step at hok
    simp [hv] at hok

theorem natSum_pos_of_mem3 {ws : List Nat} (hpos : ∀ w ∈ ws, 0 < w) (hne : ws ≠ []) : 0 < natSum ws := by
  cases ws with
  | nil => simp at hne
  | cons w rest =>
    simp only [natSum]
    have hw : 0 < w := hpos w (by simp)
    omega

#check Nat.div_add_mod
#check Nat.mod_lt
#check Nat.div_mul_le_self
#check @Int.ofNat_le
#check @Int.ofNat_lt
#check Nat.lt_add_one_of_le
example (a b W : Nat) (h : a < (b+1)*W) : a < b*W + W := by
  have : (b+1)*W = b*W+W := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem rounding_helper1 (A W : Nat) : (A / W) * W ≤ A := Nat.div_mul_le_self A W

theorem rounding_helper2 (A W : Nat) (hW : 0 < W) : A < (A / W) * W + W := by
  have hmod : A % W < W := Nat.mod_lt A hW
  have hdm : W * (A / W) + A % W = A := Nat.div_add_mod A W
  have hcomm : W * (A / W) = (A / W) * W := Nat.mul_comm _ _
  omega

theorem cons_test_aux1 : ∀ (ws : List Nat) (amount W : Nat),
  natSum (ws.map (floorShare amount W)) * W ≤ natSum (ws.map (fun w => amount * w)) := by
  intro ws amount W
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih =>
    simp only [List.map_cons, natSum]
    have h1 : floorShare amount W w * W ≤ amount * w := Nat.div_mul_le_self _ _
    have h2 : natSum (List.map (floorShare amount W) rest) * W ≤ natSum (List.map (fun w => amount * w) rest) := ih
    have h3 : (floorShare amount W w + natSum (List.map (floorShare amount W) rest)) * W
      = floorShare amount W w * W + natSum (List.map (floorShare amount W) rest) * W := Nat.add_mul _ _ _
    have h4 : (amount * w + natSum (List.map (fun w => amount * w) rest)) = natSum ((w :: rest).map (fun w => amount * w)) := by simp [natSum]
    omega

def genShare (amount W L : Nat) (rs : List Nat) (ws : List Nat) (k : Nat) (a : Nat) : Nat :=
  match indexOf? rs a with
  | some j => floorShare amount W (ws.getD j 0) + (if k + j < L then 1 else 0)
  | none => 0

def bonusSum : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | _ :: ws', k, L => (if k < L then 1 else 0) + bonusSum ws' (k+1) L

theorem bonusSum_zero : bonusSum [] k L = 0 := rfl

theorem natSum_map_mul (ws : List Nat) (c W : Nat) : natSum (List.map (fun w => c * w / W) ws) * W ≤ c * natSum ws := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih =>
    simp only [List.map_cons, natSum]
    have h1 : (c * w / W) * W ≤ c * w := Nat.div_mul_le_self _ _
    have hmul : ((c * w / W) + natSum (List.map (fun w => c * w / W) rest)) * W
      = (c * w / W) * W + natSum (List.map (fun w => c * w / W) rest) * W := Nat.add_mul _ _ _
    have hmul2 : c * (w + natSum rest) = c * w + c * natSum rest := Nat.mul_add _ _ _
    omega

theorem natSum_map_distrib (ws : List Nat) (c : Nat) : natSum (List.map (fun w => c * w) ws) = c * natSum ws := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih => simp only [List.map_cons, natSum, ih, Nat.mul_add]

theorem natSum_mul_distrib (ws : List Nat) (W : Nat) : natSum (List.map (fun x => x * W) ws) = natSum ws * W := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih => simp only [List.map_cons, natSum, ih, Nat.add_mul]

theorem natSum_map_add (ws : List Nat) (f g : Nat → Nat) :
  natSum (List.map (fun w => f w + g w) ws) = natSum (List.map f ws) + natSum (List.map g ws) := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih => simp only [List.map_cons, natSum, ih]; omega

theorem t1 (a b W : Nat) (hW : 0 < W) (h : a * W ≤ b * W) : a ≤ b := Nat.le_of_mul_le_mul_right h hW
#check Nat.mul_lt_mul_of_pos_right

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization  : AuthorizedOnly step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · unfold step at hok
    simp [hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · unfold step at hok ⊢
    simp [hv] at hok ⊢
  · unfold step at hok
    simp [hv] at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hv]
    have hok' : (step s r).1 = .ok := hok
    rw [hstep] at hok ⊢
    simp only at hok ⊢
    constructor
    · intro x
      simp only [List.mem_cons]
    · have hnot : ¬ ValidPayout ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
        intro hcon
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hmem⟩ := hcon
        simp at hmem
      have hstep2 : step ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r
          = (.rejected, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
        unfold step; simp [hnot]
      exact hstep2
  · unfold step at hok
    simp [hv] at hok

theorem req_nonnegative : NonNegative step := by
  intro s r hnonneg a ha
  by_cases hv : ValidPayout s r
  · have hok : (step s r).1 = .ok := req_valid_succeeds s r hv
    obtain ⟨hacc, hauth, hbal⟩ := req_effects s r hok
    have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
    have ha0 : 0 ≤ s.balance a := hnonneg a ha'
    have hbal_a : (step s r).2.balance a = expectedBalance s r a := hbal a
    rw [hbal_a]
    obtain ⟨_, _, _, _, _, _, hsrc_notin, _, _, _, hle, _⟩ := hv
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hshare0 : shareOf r r.source = 0 := by
        simp only [shareOf, indexOf?_eq_none hsrc_notin]
      rw [if_pos rfl, hshare0]
      simp
      omega
    · rw [if_neg hsrc]
      simp
      omega
  · have hstep : step s r = (.rejected, s) := req_invalid_noop s r hv
    have h2 : (step s r).2 = s := by rw [hstep]
    rw [h2] at ha ⊢
    exact hnonneg a ha

theorem req_pro_rata : ProRataShares step := by
  intro s r hok i hi
  have hv : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · have h2 := req_invalid_noop s r h
      rw [h2] at hok
      simp at hok
  obtain ⟨hacc_nodup, hpos, hne, hlen, hposW, hnodup, hsrc_notin, hsrc_mem, hmem_rec, hauth, hle, htx⟩ := hv
  have heff := req_effects s r hok
  obtain ⟨hacc_eq, hauth_eq, hbal⟩ := heff
  have hbal_i : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := hbal _
  rw [hbal_i]
  unfold expectedBalance
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne_src : r.recipients[i] ≠ r.source := fun h => hsrc_notin (h ▸ hmem)
  rw [if_neg hne_src]
  have hidx : indexOf? r.recipients r.recipients[i] = some i := indexOf?_getElem hnodup i hi
  have hshare : shareOf r r.recipients[i] = weightedShare r.amount r.weights i := by
    unfold shareOf
    rw [hidx]
  rw [hshare]
  omega

theorem req_rounding_bound : RoundingBound step := by
  intro s r hok i hi
  have hv : ValidPayout s r := by
    by_cases h : ValidPayout s r
    · exact h
    · have h2 := req_invalid_noop s r h
      rw [h2] at hok
      simp at hok
  obtain ⟨hacc_nodup, hpos, hne, hlen, hposW, hnodup, hsrc_notin, hsrc_mem, hmem_rec, hauth, hle, htx⟩ := hv
  have hpr := req_pro_rata s r hok i hi
  have hWpos : 0 < natSum r.weights := by
    apply natSum_pos_of_mem3 hposW
    intro hnil
    have hllen : r.recipients.length = 0 := by rw [← hlen, hnil]; simp
    omega
  have hle1 : floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights ≤ r.amount * r.weights.getD i 0 :=
    rounding_helper1 _ _
  have hlt1 : r.amount * r.weights.getD i 0 < floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights + natSum r.weights := by
    have h2 := rounding_helper2 (r.amount * r.weights.getD i 0) (natSum r.weights) hWpos
    have heq : r.amount * r.weights.getD i 0 / natSum r.weights = floorShare r.amount (natSum r.weights) (r.weights.getD i 0) := rfl
    rw [heq] at h2
    exact h2
  have hd_eq : weightedShare r.amount r.weights i = floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + (if i < leftover r.amount r.weights then 1 else 0) := rfl
  rw [hpr, hd_eq]
  by_cases hlt : i < leftover r.amount r.weights
  · rw [if_pos hlt]
    have hmul : (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights = floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights + natSum r.weights := by
      rw [Nat.add_mul, Nat.one_mul]
    have h1N : (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights ≤ r.amount * r.weights.getD i 0 + natSum r.weights := by omega
    have h2N : r.amount * r.weights.getD i 0 < (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights + natSum r.weights := by omega
    exact ⟨Int.ofNat_le.mpr h1N, Int.ofNat_lt.mpr h2N⟩
  · rw [if_neg hlt]
    simp only [Nat.add_zero]
    have h1N : floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights ≤ r.amount * r.weights.getD i 0 + natSum r.weights := by omega
    exact ⟨Int.ofNat_le.mpr h1N, Int.ofNat_lt.mpr hlt1⟩

theorem req_conservation   : Conserves step := sorry

end WeightedPayout
