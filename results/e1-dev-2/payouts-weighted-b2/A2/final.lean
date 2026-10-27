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

theorem snippet_nonneg_probe (s : State) (r : Request) (a : AccountId)
    (hvp : ValidPayout s r) (ha : a ∈ (step s r).2.accounts) : a ∈ s.accounts := by
  unfold step at ha
  simp [hvp] at ha
  exact ha

theorem snippet_int_test (n : Nat) : (0 : Int) ≤ (n : Int) := Int.ofNat_nonneg n

theorem snippet_valid_unpack (s : State) (r : Request) (hvp : ValidPayout s r) :
    (r.amount : Int) ≤ s.balance r.source := by
  unfold ValidPayout at hvp
  -- test destructuring
  exact hvp.2.2.2.2.2.2.2.2.2.2.1

theorem snippet_nat_probe1 (a W : Nat) : a / W * W ≤ a := Nat.div_mul_le_self a W

theorem snippet_nat_probe2 (a W : Nat) (hW : 0 < W) : a % W < W := Nat.mod_lt a hW
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @Nat.div_mul_le_self

theorem snippet_round_pure2 (a W : Nat) (hW : 0 < W) :
    (a / W) * W ≤ a ∧ a < (a / W) * W + W := by
  constructor
  · exact Nat.div_mul_le_self a W
  · have hmod : a % W < W := Nat.mod_lt a hW
    have hdm : W * (a / W) + a % W = a := Nat.div_add_mod a W
    have hcomm : W * (a / W) = (a / W) * W := Nat.mul_comm _ _
    omega

theorem snippet_natSum_pos_aux (ws : List Nat) (hpos : ∀ w ∈ ws, 0 < w) (hne : ws ≠ []) :
    0 < natSum ws := by
  cases ws with
  | nil => simp at hne
  | cons w rest =>
    simp only [natSum]
    have hw : 0 < w := hpos w (by simp)
    omega

theorem snippet_cast_probeA (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp

theorem snippet_cast_probeB (a b : Nat) : (((a * b : Nat)) : Int) = (a : Int) * (b : Int) := by
  simp

theorem probe_le_mul {a b W : Nat} (hW : 0 < W) (h : a * W ≤ b * W) : a ≤ b := by
  exact Nat.le_of_mul_le_mul_right h hW
#check @Nat.le_of_mul_le_mul_right
#check @Nat.lt_of_mul_lt_mul_right
#check @Nat.le_of_mul_le_mul_left
#check @Nat.mul_lt_mul_right

theorem natSum_add_distrib2 (l1 l2 : List Nat) (h : l1.length = l2.length) :
    natSum (List.zipWith (· + ·) l1 l2) = natSum l1 + natSum l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zipWith_cons_cons, natSum]
      simp at h
      have htail := ih ys h
      omega

theorem natSum_mul_right (l : List Nat) (W : Nat) :
    natSum (l.map (· * W)) = natSum l * W := by
  induction l with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_mul]

theorem natSum_map_le (l1 l2 : List Nat) (h : l1.length = l2.length)
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
      simp only [natSum]
      have hx : x ≤ y := by
        have hh := hle 0 (by simp) (by simp)
        simpa using hh
      have htail : natSum xs ≤ natSum ys := by
        apply ih ys h
        intro i hi1 hi2
        have h1 : (i+1) < (x :: xs).length := by simpa using Nat.succ_lt_succ hi1
        have h2 : (i+1) < (y :: ys).length := by simpa using Nat.succ_lt_succ hi2
        have hh := hle (i+1) h1 h2
        simpa using hh
      omega

theorem rounding_nat_aux (amount W w : Nat) (hW : 0 < W) (extra : Nat) (hextra : extra ≤ 1) :
    let a := amount * w
    let f := a / W
    let d := f + extra
    d * W ≤ a + W ∧ a < d * W + W := by
  simp only
  have h1 : (amount * w / W) * W ≤ amount * w := Nat.div_mul_le_self _ _
  have hmod : (amount * w) % W < W := Nat.mod_lt _ hW
  have hdm : W * (amount * w / W) + (amount * w) % W = amount * w := Nat.div_add_mod _ _
  have hcomm : W * (amount * w / W) = (amount * w / W) * W := Nat.mul_comm _ _
  constructor
  · have h2 : extra * W ≤ W := by
      cases extra with
      | zero => simp
      | succ e =>
        have : e = 0 := by omega
        subst this; simp
    have hdW : ((amount * w / W) + extra) * W = (amount * w / W) * W + extra * W := Nat.add_mul _ _ _
    omega
  · have hdW : ((amount * w / W) + extra) * W = (amount * w / W) * W + extra * W := Nat.add_mul _ _ _
    omega

theorem snippet_set_test (a b : Nat) (h : a ≤ b) : a ≤ b := by
  exact h

theorem probe_range1 (n : Nat) : List.range (n+1) = List.range n ++ [n] := by simp [List.range_succ]

theorem probe_sumOver_map_nat2 (l : List Nat) (f : Nat → Nat) :
    sumOver l (fun a => (f a : Int)) = ((natSum (l.map f) : Nat) : Int) := by
  induction l with
  | nil => simp [sumOver, natSum]
  | cons x xs ih => simp [ih, natSum]

theorem floors_mul_le_general2 (amount W : Nat) (ws : List Nat) :
    natSum (((ws.map (floorShare amount W)).map (· * W))) ≤ amount * natSum ws := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih =>
    simp only [List.map_cons, natSum]
    have h1 : floorShare amount W w * W ≤ amount * w := by unfold floorShare; exact Nat.div_mul_le_self _ _
    have h2 : natSum ((List.map (· * W)) (List.map (floorShare amount W) rest)) ≤ amount * natSum rest := ih
    have hrw : amount * (w + natSum rest) = amount * w + amount * natSum rest := Nat.mul_add _ _ _
    omega

theorem floor_lt_succ_mul2 (amount W w : Nat) (hW : 0 < W) :
    amount * w < (floorShare amount W w + 1) * W := by
  unfold floorShare
  have hdm : W * (amount * w / W) + (amount * w) % W = amount * w := Nat.div_add_mod _ _
  have hmod : (amount * w) % W < W := Nat.mod_lt _ hW
  have hcomm : W * (amount * w / W) = (amount * w / W) * W := Nat.mul_comm _ _
  have hexpand : (amount * w / W + 1) * W = (amount * w / W) * W + W := by
    rw [Nat.add_mul]; simp
  omega

theorem key_ineq_aux (amount W : Nat) (hW : 0 < W) (ws : List Nat) :
    amount * natSum ws + ws.length ≤ (natSum (ws.map (floorShare amount W)) + ws.length) * W := by
  induction ws with
  | nil => simp [natSum]
  | cons w rest ih =>
    simp only [List.map_cons, natSum, List.length_cons]
    have hlt : amount * w + 1 ≤ (floorShare amount W w + 1) * W := by
      have hlt2 : amount * w < (floorShare amount W w + 1) * W := floor_lt_succ_mul2 amount W w hW
      omega
    have hrw1 : amount * (w + natSum rest) = amount * w + amount * natSum rest := Nat.mul_add _ _ _
    have hrw2 : (floorShare amount W w + natSum (List.map (floorShare amount W) rest) + (List.length rest + 1)) * W
        = (floorShare amount W w + 1) * W + (natSum (List.map (floorShare amount W) rest) + List.length rest) * W := by
      rw [← Nat.add_mul]; congr 1; omega
    omega



theorem plan0_floor_sum_mul_le (amount W : Nat) (ws : List Nat) :
    natSum (ws.map (floorShare amount W)) * W ≤ amount * natSum ws := by
  have h := floors_mul_le_general2 amount W ws
  have h2 := natSum_mul_right (ws.map (floorShare amount W)) W
  omega








theorem plan0_weighted_range_sum_placeholder : True := trivial


theorem plan0_range_succ_map (n : Nat) (g : Nat → Nat) :
    (List.range (n + 1)).map g = g 0 :: (List.range n).map (fun i => g (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by
      rw [List.range_succ]
    have h2 : List.range (n + 1) = List.range n ++ [n] := by
      rw [List.range_succ]
    calc (List.range (n + 1 + 1)).map g
        = (List.range (n + 1)).map g ++ [g (n + 1)] := by rw [h1, List.map_append]; simp
      _ = (g 0 :: (List.range n).map (fun i => g (i + 1))) ++ [g (n + 1)] := by rw [ih]
      _ = g 0 :: ((List.range n).map (fun i => g (i + 1)) ++ [g (n + 1)]) := by simp
      _ = g 0 :: ((List.range n).map (fun i => g (i + 1)) ++ [(fun i => g (i + 1)) n]) := by simp
      _ = g 0 :: (List.range n ++ [n]).map (fun i => g (i + 1)) := by rw [List.map_append]; simp
      _ = g 0 :: (List.range (n + 1)).map (fun i => g (i + 1)) := by rw [h2]

theorem plan0_floor_sum_mul_le_proof : ∀ (amount W : Nat) (ws : List Nat),
    natSum (ws.map (floorShare amount W)) * W ≤ amount * natSum ws := by
  intro amount W ws
  have h := floors_mul_le_general2 amount W ws
  have h2 := natSum_mul_right (ws.map (floorShare amount W)) W
  omega

theorem plan0_amount_mul_le_floor_sum_add_length (amount W : Nat) (ws : List Nat) (hW : 0 < W) :
    amount * natSum ws ≤ (natSum (ws.map (floorShare amount W)) + ws.length) * W := by
  have h := key_ineq_aux amount W hW ws
  omega

theorem plan0_probe_natsum : natSum ([] : List Nat) = 0 := by simp [natSum]

theorem plan0_probe_natsum2 (x : Nat) (xs : List Nat) : natSum (x :: xs) = x + natSum xs := by simp [natSum]
#check @natSum.eq_1
#check @natSum.eq_2

theorem plan0_min0 (L : Nat) : Nat.min L 0 = 0 := Nat.min_zero L

theorem plan0_natSum_append3 (l1 l2 : List Nat) :
    natSum (l1 ++ l2) = natSum l1 + natSum l2 := by
  induction l1 with
  | nil => simp only [natSum, List.nil_append, Nat.zero_add]
  | cons x xs ih => simp only [natSum, List.cons_append, ih, Nat.add_assoc]

theorem plan0_indicator_sum3 (n L : Nat) :
    natSum ((List.range n).map (fun i => if i < L then 1 else 0)) = Nat.min L n := by
  induction n generalizing L with
  | zero => simp only [List.range_zero, List.map_nil, natSum, Nat.min_zero]
  | succ n ih =>
    have hr : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [hr, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [plan0_natSum_append3]
    simp only [natSum, Nat.add_zero]
    rw [ih]
    cases L with
    | zero => simp
    | succ L' =>
      simp only [Nat.succ_min_succ]
      by_cases h : n < L' + 1
      · simp [h]
        have hmin : Nat.min L' n = n := Nat.min_eq_right (by omega)
        have hmin2 : Nat.min (L' + 1) n = n := Nat.min_eq_right (by omega)
        omega
      · simp [h]
        have hmin : Nat.min L' n = L' := Nat.min_eq_left (by omega)
        have hmin2 : Nat.min (L' + 1) n = L' + 1 := Nat.min_eq_left (by omega)
        omega

theorem plan0_range_floor_map_eq4 (amount W : Nat) (ws : List Nat) :
    ((List.range ws.length).map (fun i => floorShare amount W (ws.getD i 0))) = ws.map (floorShare amount W) := by
  induction ws with
  | nil => simp
  | cons w rest ih =>
    have hlen : (w :: rest).length = rest.length + 1 := by simp
    rw [hlen]
    have h := plan0_range_succ_map rest.length (fun i => floorShare amount W ((w :: rest).getD i 0))
    rw [h]
    simp only [List.getD_cons_zero]
    have hcongr : (List.range rest.length).map (fun i => floorShare amount W ((w :: rest).getD (i + 1) 0)) = (List.range rest.length).map (fun i => floorShare amount W (rest.getD i 0)) := by
      apply List.map_congr_left
      intro i _
      simp
    rw [hcongr, ih]
    simp





theorem plan1_natSum_map_add (l : List Nat) (f g : Nat → Nat) :
    natSum (l.map (fun i => f i + g i)) = natSum (l.map f) + natSum (l.map g) := by
  induction l with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc, Nat.add_left_comm]






theorem plan1_range_succ_map_shift (n : Nat) (g : Nat → Nat) :
    (List.range (n + 1)).map g = g 0 :: (List.range n).map (fun i => g (i + 1)) :=
  plan0_range_succ_map n g

theorem plan1_range_getD_map (ws : List Nat) (f : Nat → Nat) :
    (List.range ws.length).map (fun i => f (ws.getD i 0)) = ws.map f := by
  induction ws with
  | nil => simp
  | cons w rest ih =>
    have hlen : (w :: rest).length = rest.length + 1 := by simp
    rw [hlen]
    rw [plan0_range_succ_map _ (fun i => f ((w :: rest).getD i 0))]
    simp only [List.getD_cons_zero]
    have hfun : (fun i => f ((w :: rest).getD (i + 1) 0)) = (fun i => f (rest.getD i 0)) := by
      funext i
      simp
    rw [hfun, ih]
    simp

theorem plan1_natSum_append (l1 l2 : List Nat) :
    natSum (l1 ++ l2) = natSum l1 + natSum l2 := by
  induction l1 with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc]

theorem plan1_natSum_range_indicator (n L : Nat) :
    natSum ((List.range n).map (fun i => if i < L then 1 else 0)) = Nat.min L n :=
  plan0_indicator_sum3 n L

theorem plan0_range_floor_add_indicator_sum (amount W L : Nat) (ws : List Nat) :
    natSum ((List.range ws.length).map (fun i => floorShare amount W (ws.getD i 0) + if i < L then 1 else 0))
      = natSum (ws.map (floorShare amount W)) + Nat.min L ws.length := by
  have hsplit := plan1_natSum_map_add (List.range ws.length)
    (fun i => floorShare amount W (ws.getD i 0)) (fun i => if i < L then 1 else 0)
  have hfirst : ((List.range ws.length).map (fun i => floorShare amount W (ws.getD i 0))) = ws.map (floorShare amount W) :=
    plan1_range_getD_map ws (floorShare amount W)
  have hsecond : natSum ((List.range ws.length).map (fun i => if i < L then 1 else 0)) = Nat.min L ws.length :=
    plan1_natSum_range_indicator ws.length L
  -- rewrite using hsplit
  have heq : ((List.range ws.length).map (fun i => floorShare amount W (ws.getD i 0) + if i < L then 1 else 0))
      = ((List.range ws.length).map (fun i => (fun i => floorShare amount W (ws.getD i 0)) i + (fun i => if i < L then 1 else 0) i)) := rfl
  rw [heq, hsplit, hfirst, hsecond]

theorem plan0_floor_sum_add_leftover (amount : Nat) (ws : List Nat) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    natSum (ws.map (floorShare amount (natSum ws))) + leftover amount ws = amount ∧ leftover amount ws ≤ ws.length := by
  have hWpos : 0 < natSum ws := snippet_natSum_pos_aux ws hpos hne
  have hmul_le : natSum (ws.map (floorShare amount (natSum ws))) * natSum ws ≤ amount * natSum ws :=
    plan0_floor_sum_mul_le_proof amount (natSum ws) ws
  have hle1 : natSum (ws.map (floorShare amount (natSum ws))) ≤ amount :=
    probe_le_mul hWpos hmul_le
  have hmul_ge : amount * natSum ws ≤ (natSum (ws.map (floorShare amount (natSum ws))) + ws.length) * natSum ws :=
    plan0_amount_mul_le_floor_sum_add_length amount (natSum ws) ws hWpos
  have hle2 : amount ≤ natSum (ws.map (floorShare amount (natSum ws))) + ws.length :=
    probe_le_mul hWpos hmul_ge
  unfold leftover
  constructor
  · omega
  · omega

theorem plan0_weighted_range_sum_aux (amount : Nat) (ws : List Nat) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) = amount := by
  have h1 := plan0_range_floor_add_indicator_sum amount (natSum ws) (leftover amount ws) ws
  have h2 := plan0_floor_sum_add_leftover amount ws hne hpos
  obtain ⟨h_eq, h_le⟩ := h2
  have hmin : Nat.min (leftover amount ws) ws.length = leftover amount ws := Nat.min_eq_left h_le
  have heq_map : ((List.range ws.length).map (weightedShare amount ws))
      = ((List.range ws.length).map (fun i => floorShare amount (natSum ws) (ws.getD i 0) + if i < leftover amount ws then 1 else 0)) := by
    apply List.map_congr_left
    intro i _
    unfold weightedShare
    rfl
  rw [heq_map, h1, hmin] at *
  omega

theorem plan0_weighted_range_sum (amount : Nat) (ws : List Nat) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) = amount :=
  plan0_weighted_range_sum_aux amount ws hne hpos

theorem sumOver_zero_aux (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem sumOver_swap_aux2 (l1 l2 : List Nat) (F : Nat → Nat → Int) :
    sumOver l1 (fun a => sumOver l2 (fun b => F a b)) =
    sumOver l2 (fun b => sumOver l1 (fun a => F a b)) := by
  induction l1 with
  | nil =>
    simp only [sumOver_nil]
    have h2 : sumOver l2 (fun b => sumOver ([] : List Nat) (fun a => F a b)) = 0 := by
      have hcongr : sumOver l2 (fun b => sumOver ([] : List Nat) (fun a => F a b)) = sumOver l2 (fun _ => (0 : Int)) := by
        apply sumOver_congr
        intro b _
        rfl
      rw [hcongr]
      exact sumOver_zero_aux l2
    exact h2.symm
  | cons x xs ih =>
    have hL : sumOver (x :: xs) (fun a => sumOver l2 (fun b => F a b))
        = sumOver l2 (fun b => F x b) + sumOver xs (fun a => sumOver l2 (fun b => F a b)) := rfl
    rw [hL, ih]
    have hR : sumOver l2 (fun b => sumOver (x :: xs) (fun a => F a b))
        = sumOver l2 (fun b => (F x b + sumOver xs (fun a => F a b))) := by
      apply sumOver_congr
      intro b _
      rfl
    rw [hR, ← sumOver_add]

theorem sumOver_map_aux {α β : Type} (l : List α) (f : α → β) (g : β → Int) :
    sumOver (l.map f) g = sumOver l (fun x => g (f x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem sumOver_ite_var_aux4 (l : List Nat) (hl : l.Nodup) (a : Nat) (g : Nat → Int) :
    sumOver l (fun x => if x = a then g x else 0) = if a ∈ l then g a else 0 := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    have hnd : y ∉ ys ∧ ys.Nodup := by
      have h := (List.nodup_cons.mp hl)
      exact h
    have ih' := ih hnd.2
    simp only [sumOver_cons]
    by_cases hya : y = a
    · rw [if_pos hya]
      have hnot : a ∉ ys := by rw [← hya]; exact hnd.1
      rw [ih']
      rw [if_neg hnot]
      have hmem : a ∈ y :: ys := by simp [hya]
      rw [if_pos hmem]
      subst hya
      simp
    · rw [if_neg hya]
      rw [ih']
      have hne : a ≠ y := fun h => hya h.symm
      have hiff : a ∈ y :: ys ↔ a ∈ ys := by simp [hne]
      by_cases hmem2 : a ∈ ys
      · rw [if_pos hmem2, if_pos (hiff.mpr hmem2)]
        simp
      · rw [if_neg hmem2, if_neg (fun h => hmem2 (hiff.mp h))]
        simp

theorem probe_perm_test (a b : Nat) (l : List Nat) (f : Nat → Int) :
    sumOver (a :: b :: l) f = sumOver (b :: a :: l) f := by
  simp only [sumOver_cons]
  omega

#check List.Perm
#check List.filter
#check List.nodup_range

theorem probe_getD_cons_test (v : Nat) (vs : List Nat) (i : Nat) :
    (v :: vs).getD (i + 1) 0 = vs.getD i 0 := by
  simp

theorem probe_getD_zero_test (v : Nat) (vs : List Nat) :
    (v :: vs).getD 0 0 = v := by
  simp

theorem probe_index_cons_test (x : Nat) (xs : List Nat) (a : Nat) :
    indexOf? (x :: xs) a = if x = a then some 0 else (indexOf? xs a).map (· + 1) := by
  simp [indexOf?]

theorem getD_mem_aux (l : List Nat) (i : Nat) (hi : i < l.length) :
    l.getD i 0 ∈ l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ n =>
      simp only [List.getD_cons_succ]
      simp only [List.mem_cons]
      have hi' : n < xs.length := by simpa using hi
      have h := ih n hi'
      exact Or.inr h

theorem getD_eq_getElem_aux (l : List Nat) (i : Nat) (hi : i < l.length) :
    l.getD i 0 = l[i] := by
  simp [hi]

theorem range_cons_map_succ_aux2 (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by
      simp [List.range_succ]
    have h2 : List.range n ++ [n] = List.range (n + 1) := by
      simp [List.range_succ]
    calc List.range (n + 1 + 1)
        = List.range (n + 1) ++ [n + 1] := h1
      _ = (0 :: (List.range n).map (· + 1)) ++ [n + 1] := by rw [ih]
      _ = 0 :: ((List.range n).map (· + 1) ++ [n + 1]) := by simp
      _ = 0 :: ((List.range n).map (· + 1) ++ [(n + 1)]) := rfl
      _ = 0 :: ((List.range (n + 1)).map (· + 1)) := by
          have hmap : ((List.range (n + 1)).map (· + 1)) = (List.range n).map (· + 1) ++ [n + 1] := by
            rw [← h2, List.map_append]
            simp
          rw [hmap]





theorem plan2_sumOver_recipients_share_eq_natSum (r : Request)
    (hrec : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) =
      ((natSum ((List.range r.recipients.length).map
        (weightedShare r.amount r.weights)) : Nat) : Int) := by sorry

theorem plan2_natSum_weighted_range_eq_amount (r : Request)
    (hne : r.recipients ≠ [])
    (hlen : r.weights.length = r.recipients.length)
    (hpos : ∀ w ∈ r.weights, 0 < w) :
    natSum ((List.range r.recipients.length).map
      (weightedShare r.amount r.weights)) = r.amount := by sorry

theorem plan2_sumOver_expectedBalance_eq (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts)
    (hshare : sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int)) :
    sumOver s.accounts (fun a => expectedBalance s r a) =
      sumOver s.accounts s.balance := by sorry

theorem plan2_shareOf_eq_indicator_sum (r : Request) (hrec : r.recipients.Nodup)
    (a : AccountId) :
    (shareOf r a : Int) =
      sumOver r.recipients (fun x => if x = a then (shareOf r x : Int) else 0) := by
  have hsum := sumOver_ite_var_aux4 r.recipients hrec a (fun x => (shareOf r x : Int))
  by_cases hmem : a ∈ r.recipients
  · rw [hsum, if_pos hmem]
  · rw [hsum, if_neg hmem]
    have hidx : indexOf? r.recipients a = none := indexOf?_eq_none hmem
    unfold shareOf
    rw [hidx]
    rfl

theorem plan2_sumOver_accounts_share_eq_recipients_probe : True := trivial

theorem plan2_sumOver_accounts_share_eq_recipients_aux2 (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  have hrew : ∀ a, (shareOf r a : Int)
      = sumOver r.recipients (fun x => if x = a then (shareOf r x : Int) else 0) :=
    fun a => plan2_shareOf_eq_indicator_sum r hrec a
  have hstep1 : sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver s.accounts (fun a => sumOver r.recipients (fun x => if x = a then (shareOf r x : Int) else 0)) := by
    apply sumOver_congr
    intro a _
    exact hrew a
  rw [hstep1]
  rw [sumOver_swap_aux2 s.accounts r.recipients (fun a x => if x = a then (shareOf r x : Int) else 0)]
  apply sumOver_congr
  intro x hx
  have hflip : ∀ a : Nat, (if x = a then (shareOf r x : Int) else 0) = (if a = x then (shareOf r x : Int) else 0) := by
    intro a
    by_cases h : x = a
    · have h2 : a = x := h.symm
      rw [if_pos h, if_pos h2]
    · have h2 : ¬ (a = x) := fun hh => h hh.symm
      rw [if_neg h, if_neg h2]
  have hcongr : sumOver s.accounts (fun a => (if x = a then (shareOf r x : Int) else 0))
      = sumOver s.accounts (fun a => (if a = x then (shareOf r x : Int) else 0)) := by
    apply sumOver_congr
    intro a _
    exact hflip a
  rw [hcongr]
  have hite := sumOver_ite_eq (l := s.accounts) hacc x ((shareOf r x : Int))
  rw [hite]
  have hmem : x ∈ s.accounts := hsub x hx
  rw [if_pos hmem]

theorem plan2_sumOver_accounts_share_eq_recipients (s : State) (r : Request)
    (hacc : s.accounts.Nodup) (hrec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) =
      sumOver r.recipients (fun a => (shareOf r a : Int)) := by
  have hrew : ∀ a, (shareOf r a : Int)
      = sumOver r.recipients (fun x => if x = a then (shareOf r x : Int) else 0) :=
    fun a => plan2_shareOf_eq_indicator_sum r hrec a
  have hstep1 : sumOver s.accounts (fun a => (shareOf r a : Int))
      = sumOver s.accounts (fun a => sumOver r.recipients (fun x => if x = a then (shareOf r x : Int) else 0)) := by
    apply sumOver_congr
    intro a _
    exact hrew a
  rw [hstep1]
  rw [sumOver_swap_aux2 s.accounts r.recipients (fun a x => if x = a then (shareOf r x : Int) else 0)]
  apply sumOver_congr
  intro x hx
  have hflip : ∀ a : Nat, (if x = a then (shareOf r x : Int) else 0) = (if a = x then (shareOf r x : Int) else 0) := by
    intro a
    by_cases h : x = a
    · have h2 : a = x := h.symm
      rw [if_pos h, if_pos h2]
    · have h2 : ¬ (a = x) := fun hh => h hh.symm
      rw [if_neg h, if_neg h2]
  have hcongr : sumOver s.accounts (fun a => (if x = a then (shareOf r x : Int) else 0))
      = sumOver s.accounts (fun a => (if a = x then (shareOf r x : Int) else 0)) := by
    apply sumOver_congr
    intro a _
    exact hflip a
  rw [hcongr]
  have hite := sumOver_ite_eq (l := s.accounts) hacc x ((shareOf r x : Int))
  rw [hite]
  have hmem : x ∈ s.accounts := hsub x hx
  rw [if_pos hmem]

theorem aux_shareOf_getD (r : Request) (hrec : r.recipients.Nodup) (i : Nat) (hi : i < r.recipients.length) :
    shareOf r (r.recipients.getD i 0) = weightedShare r.amount r.weights i := by
  unfold shareOf
  have hget : r.recipients.getD i 0 = r.recipients[i] := getD_eq_getElem_aux r.recipients i hi
  rw [hget]
  rw [indexOf?_getElem hrec i hi]

theorem probe_list_ext_check (l1 l2 : List Nat) (hlen : l1.length = l2.length)
    (hget : ∀ i (hi1 : i < l1.length) (hi2 : i < l2.length), l1[i] = l2[i]) : l1 = l2 := by
  exact List.ext_getElem hlen hget

theorem aux_range_map_getD_eq (l : List Nat) :
    (List.range l.length).map (fun i => l.getD i 0) = l := by
  have h := plan1_range_getD_map l (fun x => x)
  simp at h
  exact h

theorem plan2_sumOver_recipients_share_eq_natSum_alt2 (r : Request)
    (hrec : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) =
      ((natSum ((List.range r.recipients.length).map
        (weightedShare r.amount r.weights)) : Nat) : Int) := by
  have hmap : (List.range r.recipients.length).map (fun i => r.recipients.getD i 0) = r.recipients :=
    aux_range_map_getD_eq r.recipients
  have haux := sumOver_map_aux (List.range r.recipients.length) (fun i => r.recipients.getD i 0) (fun a => ((shareOf r a : Nat) : Int))
  -- haux : sumOver (map ...) = sumOver range (fun i => share (getD i))
  rw [hmap] at haux
  -- haux : sumOver recipients ... = sumOver range ...
  rw [haux]
  have hcongr : sumOver (List.range r.recipients.length) (fun i => ((shareOf r (r.recipients.getD i 0) : Nat) : Int))
      = sumOver (List.range r.recipients.length) (fun i => ((weightedShare r.amount r.weights i : Nat) : Int)) := by
    apply sumOver_congr
    intro i hi
    have hi_lt : i < r.recipients.length := List.mem_range.mp hi
    rw [aux_shareOf_getD r hrec i hi_lt]
  rw [hcongr]
  exact probe_sumOver_map_nat2 _ _

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization  : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hvp : ValidPayout s r
  · exact hvp.2.2.2.2.2.2.2.2.2.1
  · simp [hvp] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hvp : ValidPayout s r
  · unfold step
    simp [hvp]
  · unfold step at h
    simp [hvp] at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  by_cases hvp : ValidPayout s r
  · have hstep1 : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      unfold step; simp [hvp]
    have h2eq : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      rw [hstep1]
    have hmem : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
      rw [h2eq]; simp
    have hnot' : ¬ ValidPayout ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
      intro hc
      have hlast := hc.2.2.2.2.2.2.2.2.2.2.2
      simp at hlast
    have hstep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
      rw [h2eq]
      unfold step
      simp [hnot']
    exact ⟨hmem, hstep2⟩
  · unfold step at h
    simp [hvp] at h

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hvp : ValidPayout s r
  · have h2eq : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      unfold step
      simp [hvp]
    have ha' : a ∈ s.accounts := by
      rw [h2eq] at ha
      simpa using ha
    have hbal : (step s r).2.balance a = expectedBalance s r a := by
      rw [h2eq]
    rw [hbal]
    unfold expectedBalance
    by_cases heq : a = r.source
    · subst heq
      have hsrc_notin : r.source ∉ r.recipients := hvp.2.2.2.2.2.2.1
      have hidx : indexOf? r.recipients r.source = none :=
        indexOf?_eq_none hsrc_notin
      have hshare0 : shareOf r r.source = 0 := by
        unfold shareOf; rw [hidx]
      rw [hshare0]
      simp
      have hle : ((r.amount : Int)) ≤ s.balance r.source := hvp.2.2.2.2.2.2.2.2.2.2.1
      omega
    · simp [heq]
      have hb : (0 : Int) ≤ s.balance a := hnn a ha'
      have hs : (0 : Int) ≤ (((shareOf r a : Nat)) : Int) := Int.ofNat_nonneg _
      omega
  · have h2eq : (step s r).2 = s := by
      unfold step
      simp [hvp]
    have ha' : a ∈ s.accounts := by
      rw [h2eq] at ha
      exact ha
    have hbal : (step s r).2.balance a = s.balance a := by
      rw [h2eq]
    rw [hbal]
    exact hnn a ha'

theorem req_pro_rata : ProRataShares step := by
  intro s r h_ok i hi
  have hvp : ValidPayout s r := by
    by_cases hnv : ValidPayout s r
    · exact hnv
    · have hstep : (step s r).1 = .rejected := by unfold step; simp [hnv]
      rw [hstep] at h_ok
      exact False.elim (absurd h_ok (by decide))
  have h2bal : ∀ a, (step s r).2.balance a = expectedBalance s r a := by
    intro a
    unfold step
    simp [hvp]
  have hbal := h2bal r.recipients[i]
  obtain ⟨hNodupAcc, hAmtPos, hNe, hLen, hWpos, hNodupRec, hSrcNot, hSrcMem, hRecMem, hAuth, hBalLe, hTxFresh⟩ := hvp
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne_src : r.recipients[i] ≠ r.source := fun h => hSrcNot (h ▸ hmem)
  have hidx : indexOf? r.recipients r.recipients[i] = some i :=
    indexOf?_getElem hNodupRec i hi
  have hshare : shareOf r r.recipients[i] = weightedShare r.amount r.weights i := by
    unfold shareOf
    rw [hidx]
  have hdiff : (step s r).2.balance r.recipients[i] - s.balance r.recipients[i]
      = ((shareOf r r.recipients[i] : Nat) : Int) := by
    rw [hbal]
    unfold expectedBalance
    have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by simp [hne_src]
    rw [hif]
    simp
    omega
  rw [hdiff, hshare]

theorem req_rounding_bound : RoundingBound step := by
  intro s r h_ok i hi
  have hdiff : (step s r).2.balance r.recipients[i] - s.balance r.recipients[i]
      = (weightedShare r.amount r.weights i : Int) :=
    req_pro_rata s r h_ok i hi
  rw [hdiff]
  have hvp : ValidPayout s r := by
    by_cases hnv : ValidPayout s r
    · exact hnv
    · have hstep : (step s r).1 = .rejected := by unfold step; simp [hnv]
      rw [hstep] at h_ok
      exact False.elim (absurd h_ok (by decide))
  obtain ⟨hNodupAcc, hAmtPos, hNe, hLen, hWpos, hNodupRec, hSrcNot, hSrcMem, hRecMem, hAuth, hBalLe, hTxFresh⟩ := hvp
  have hW : 0 < natSum r.weights := by
    cases hrw : r.weights with
    | nil =>
      have hlen0 : r.recipients.length = 0 := by rw [← hLen, hrw]; simp
      have : r.recipients = [] := List.length_eq_zero_iff.mp hlen0
      exact False.elim (hNe this)
    | cons w rest =>
      simp only [natSum]
      have hw : 0 < w := hWpos w (by simp [hrw])
      omega
  unfold weightedShare floorShare
  by_cases hextra : i < leftover r.amount r.weights
  · have heq : (if i < leftover r.amount r.weights then (1 : Nat) else 0) = 1 := if_pos hextra
    rw [heq]
    have hnat := rounding_nat_aux r.amount (natSum r.weights) (r.weights.getD i 0) hW 1 (by omega)
    obtain ⟨hn1, hn2⟩ := hnat
    constructor <;> omega
  · have heq : (if i < leftover r.amount r.weights then (1 : Nat) else 0) = 0 := if_neg hextra
    rw [heq]
    have hnat := rounding_nat_aux r.amount (natSum r.weights) (r.weights.getD i 0) hW 0 (by omega)
    obtain ⟨hn1, hn2⟩ := hnat
    constructor <;> omega

theorem req_conservation   : Conserves step := sorry

end WeightedPayout
