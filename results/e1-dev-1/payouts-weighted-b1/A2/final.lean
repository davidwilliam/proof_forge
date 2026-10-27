import WeightedPayout.Spec
import WeightedPayout.Lemmas
namespace WeightedPayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { accounts := s.accounts
            balance := fun a => expectedBalance s r a
            auth := s.auth
            applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_effects_dbg2 : True := by
  have h1 : ∀ (s : State) (r : Request), (step s r).1 = .ok →
    (step s r).2.accounts = s.accounts := by
    intro s r h
    by_cases hv : ValidPayout s r
    · have hs : step s r = (.ok, { accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied }) := by unfold step; simp [hv]
      rw [hs]
    · have heq : step s r = (.rejected, s) := by unfold step; simp [hv]
      have hcon : (step s r).1 = .rejected := by rw [heq]
      rw [hcon] at h
      cases h
  trivial

theorem tmp_check_names : True := by
  have h1 : ∀ (a b : Nat), a / b * b ≤ a := fun a b => Nat.div_mul_le_self a b
  have h2 : ∀ (x y : Nat), 0 < y → x % y < y := fun x y h => Nat.mod_lt x h
  trivial

theorem tmp_Wpos_lemma (ws : List Nat) (hpos : ∀ w ∈ ws, 0 < w) (hne : ws ≠ []) : 0 < natSum ws := by
  match ws with
  | [] => simp at hne
  | w :: ws =>
    simp [natSum]
    have hw : 0 < w := hpos w (by simp)
    have hle : 0 ≤ natSum ws := Nat.zero_le _
    omega

theorem tmp_round_nat4 (a W f b d : Nat) (hW : 0 < W)
    (hd : d = f + b) (hb : b ≤ 1)
    (hf : f = a / W) :
    d * W ≤ a + W ∧ a < d * W + W := by
  subst hf; subst hd
  have hmod : W * (a / W) + a % W = a := Nat.div_add_mod a W
  have hmulc : W * (a / W) = a / W * W := Nat.mul_comm _ _
  have hmod2 : a / W * W + a % W = a := by omega
  have hle0 : a / W * W ≤ a := Nat.div_mul_le_self a W
  have hlt0 : a % W < W := Nat.mod_lt _ hW
  have h1 : (a / W + b) * W = a / W * W + b * W := Nat.add_mul _ _ _
  have hbW : b * W ≤ W := by
    calc b * W ≤ 1 * W := Nat.mul_le_mul_right W hb
      _ = W := Nat.one_mul W
  constructor
  · omega
  · omega

theorem tmp_probe2 : True := by
  have h : ((2 : Nat) : Int) = 2 := rfl
  trivial

theorem tmp_test_thm : True := trivial

theorem tmp_cancel_check (a b W : Nat) (h : a * W ≤ b * W) (hW : 0 < W) : a ≤ b := by
  exact Nat.le_of_mul_le_mul_right h hW

theorem tmp_natSum_append (l1 l2 : List Nat) : natSum (l1 ++ l2) = natSum l1 + natSum l2 := by
  induction l1 with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc]

theorem tmp_sumOver_append (l1 l2 : List Nat) (f : Nat → Int) : sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp [sumOver]
  | cons x xs ih => simp [ih]; omega

theorem tmp_int_coe_check : ((3 : Nat) : Int) = 3 := rfl

theorem tmp_int_coe_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  omega

theorem tmp_mem_le_sum (ws : List Nat) (w : Nat) (h : w ∈ ws) : w ≤ natSum ws := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    simp [natSum]
    simp at h
    rcases h with rfl | hmem
    · omega
    · have ihle := ih hmem
      omega

theorem tmp_natSum_map_mul (ws : List Nat) (c : Nat) : natSum (ws.map (fun w => c * w)) = c * natSum ws := by
  induction ws with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.mul_add]

theorem tmp_probe5 : True := by trivial
#check @Int.natCast_add
#check @Int.natCast_mul
#check @Int.ofNat_le
#check @Int.ofNat_lt

theorem tmp_probe_range : True := by
  let xs : List Nat := List.range 5
  have h : xs.length = 5 := List.length_range
  trivial
#check @List.length_range
#check @List.getElem_range
#check @List.mapIdx
#check @List.length_mapIdx

theorem tmp_probe_range2 : True := by
  have h1 : List.range 0 = ([] : List Nat) := rfl
  have h2 : List.range 3 = [0,1,2] := rfl
  have h3 : (List.range 3).length = 3 := List.length_range
  trivial
#check @List.length_range
#check @List.mem_range
#check @List.mapIdx
#check @List.length_mapIdx
#check @Nat.div_add_mod
#check @Nat.mul_comm
#check @Nat.div_mul_le_self
#check @Nat.mod_lt
#check @Nat.le_of_mul_le_mul_right
#check @Nat.mul_lt_mul_right

theorem tmp_natSum_map_add2 (ws : List Nat) (f g : Nat → Nat) :
    natSum (ws.map (fun w => f w + g w)) = natSum (ws.map f) + natSum (ws.map g) := by
  induction ws with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc, Nat.add_left_comm]

theorem tmp_natSum_map_mul_right (ws : List Nat) (f : Nat → Nat) (c : Nat) :
    natSum (ws.map (fun w => f w * c)) = natSum (ws.map f) * c := by
  induction ws with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_mul]

theorem tmp_natSum_mono (ws : List Nat) (f g : Nat → Nat) (h : ∀ w ∈ ws, f w ≤ g w) :
    natSum (ws.map f) ≤ natSum (ws.map g) := by
  induction ws with
  | nil => simp [natSum]
  | cons x xs ih =>
    simp [natSum]
    have hx : f x ≤ g x := h x (by simp)
    have ih' : natSum (xs.map f) ≤ natSum (xs.map g) := ih (fun w hw => h w (by simp [hw]))
    omega

theorem tmp_probe_natlib : True := by
  have h1 : ∀ (a b : Nat), a * b = b * a := fun a b => Nat.mul_comm a b
  have h2 : ∀ (a : Nat) (W : Nat), a / W * W ≤ a := fun a W => Nat.div_mul_le_self a W
  trivial
#check @Nat.lt_of_mul_lt_mul_right
#check @Nat.le_of_mul_le_mul_right
#check @Nat.mul_lt_mul_right
#check @Nat.mul_le_mul_right
#check @Nat.div_add_mod
#check @Nat.add_mul
#check @Nat.mul_add

theorem tmp_probe_range3 : True := by trivial
#check @List.range_zero
#check @List.range_succ
#check @List.range_succ_eq_map
#check @List.getD
#check @List.getElem_map
#check @List.length_range

theorem tmp_probe_range4 : True := by trivial
#check @List.range_succ
#check @List.range_zero
#check @List.nodup_range
#check @List.mem_range





theorem plan0_leftover_add_floor (amount : Nat) (ws : List Nat)
    (hW : 0 < natSum ws) :
    natSum (ws.map (floorShare amount (natSum ws))) + leftover amount ws = amount ∧
      leftover amount ws ≤ ws.length := by
  unfold leftover
  have h1 : natSum (ws.map (floorShare amount (natSum ws))) * natSum ws ≤ amount * natSum ws := by
    have e1 : natSum (ws.map (floorShare amount (natSum ws))) * natSum ws
        = natSum (ws.map (fun w => floorShare amount (natSum ws) w * natSum ws)) := by
      rw [tmp_natSum_map_mul_right]
    have e2 : amount * natSum ws = natSum (ws.map (fun w => amount * w)) := by
      rw [tmp_natSum_map_mul]
    rw [e1, e2]
    apply tmp_natSum_mono
    intro w _
    unfold floorShare
    exact Nat.div_mul_le_self _ _
  have hFle : natSum (ws.map (floorShare amount (natSum ws))) ≤ amount :=
    tmp_cancel_check _ _ _ h1 hW
  have h2 : amount * natSum ws ≤
      natSum (ws.map (floorShare amount (natSum ws))) * natSum ws + ws.length * natSum ws := by
    have hterm : ∀ w ∈ ws, amount * w ≤ floorShare amount (natSum ws) w * natSum ws + natSum ws := by
      intro w _
      unfold floorShare
      have hmod := Nat.div_add_mod (amount * w) (natSum ws)
      have hlt : (amount * w) % natSum ws < natSum ws := Nat.mod_lt _ hW
      have hcomm : natSum ws * ((amount * w) / natSum ws) = ((amount * w) / natSum ws) * natSum ws := Nat.mul_comm _ _
      omega
    have hmono := tmp_natSum_mono ws (fun w => amount * w)
      (fun w => floorShare amount (natSum ws) w * natSum ws + natSum ws) hterm
    have heq1 : natSum (ws.map (fun w => amount * w)) = amount * natSum ws :=
      tmp_natSum_map_mul ws amount
    have hsplit : natSum (ws.map (fun w => floorShare amount (natSum ws) w * natSum ws + natSum ws))
        = natSum (ws.map (fun w => floorShare amount (natSum ws) w * natSum ws))
          + natSum (ws.map (fun _ : Nat => natSum ws)) :=
      tmp_natSum_map_add2 ws (fun w => floorShare amount (natSum ws) w * natSum ws) (fun _ : Nat => natSum ws)
    have heqF : natSum (ws.map (fun w => floorShare amount (natSum ws) w * natSum ws))
        = natSum (ws.map (floorShare amount (natSum ws))) * natSum ws :=
      tmp_natSum_map_mul_right ws (floorShare amount (natSum ws)) (natSum ws)
    have hconst : ∀ (l : List Nat), natSum (l.map (fun _ : Nat => natSum ws)) = l.length * natSum ws := by
      intro l
      induction l with
      | nil => simp [natSum]
      | cons y ys ih2 => simp [natSum, ih2, Nat.add_mul, Nat.add_comm]
    have hconstWs : natSum (ws.map (fun _ : Nat => natSum ws)) = ws.length * natSum ws := hconst ws
    omega
  have hle2 : amount ≤ natSum (ws.map (floorShare amount (natSum ws))) + ws.length := by
    have hmul : (natSum (ws.map (floorShare amount (natSum ws))) + ws.length) * natSum ws =
        natSum (ws.map (floorShare amount (natSum ws))) * natSum ws + ws.length * natSum ws := by
      rw [Nat.add_mul]
    have hle_mul : amount * natSum ws ≤
        (natSum (ws.map (floorShare amount (natSum ws))) + ws.length) * natSum ws := by
      omega
    exact Nat.le_of_mul_le_mul_right hle_mul hW
  constructor
  · omega
  · omega






theorem plan0_sumOver_eq_of_subset (big sub : List Nat) (f : Nat → Int)
    (hbig : big.Nodup) (hsubnd : sub.Nodup)
    (hsub : ∀ a ∈ sub, a ∈ big) (hzero : ∀ a, a ∉ sub → f a = 0) :
    sumOver big f = sumOver sub f := by
  sorry

theorem plan0_floor_sum_mul_le (amount W : Nat) (ws : List Nat) :
    natSum (ws.map (floorShare amount W)) * W ≤ amount * natSum ws := by
  have h1 : natSum (ws.map (floorShare amount W)) * W
      = natSum (ws.map (fun w => floorShare amount W w * W)) := by
    rw [tmp_natSum_map_mul_right]
  have h2 : amount * natSum ws = natSum (ws.map (fun w => amount * w)) := by
    rw [tmp_natSum_map_mul]
  rw [h1, h2]
  apply tmp_natSum_mono
  intro w _
  unfold floorShare
  exact Nat.div_mul_le_self _ _

theorem plan0_amount_mul_le_floor_sum (amount W : Nat) (ws : List Nat)
    (hW : 0 < W) :
    amount * natSum ws ≤
      natSum (ws.map (floorShare amount W)) * W + ws.length * W := by
  have hterm : ∀ w ∈ ws, amount * w ≤ floorShare amount W w * W + W := by
    intro w _
    unfold floorShare
    have hmod := Nat.div_add_mod (amount * w) W
    have hlt : (amount * w) % W < W := Nat.mod_lt _ hW
    have hcomm : W * ((amount * w) / W) = ((amount * w) / W) * W := Nat.mul_comm _ _
    omega
  have hmono := tmp_natSum_mono ws (fun w => amount * w)
    (fun w => floorShare amount W w * W + W) hterm
  have heq1 : natSum (ws.map (fun w => amount * w)) = amount * natSum ws :=
    tmp_natSum_map_mul ws amount
  have hsplit : natSum (ws.map (fun w => floorShare amount W w * W + W))
      = natSum (ws.map (fun w => floorShare amount W w * W))
        + natSum (ws.map (fun _ : Nat => W)) :=
    tmp_natSum_map_add2 ws (fun w => floorShare amount W w * W) (fun _ : Nat => W)
  have heqF : natSum (ws.map (fun w => floorShare amount W w * W))
      = natSum (ws.map (floorShare amount W)) * W :=
    tmp_natSum_map_mul_right ws (floorShare amount W) W
  have hconst : ∀ (l : List Nat), natSum (l.map (fun _ : Nat => W)) = l.length * W := by
    intro l
    induction l with
    | nil => simp [natSum]
    | cons y ys ih2 => simp [natSum, ih2, Nat.add_mul, Nat.add_comm]
  have hconstWs : natSum (ws.map (fun _ : Nat => W)) = ws.length * W := hconst ws
  omega

theorem plan0_leftover_add_floor_aux (amount : Nat) (ws : List Nat)
    (hW : 0 < natSum ws) :
    natSum (ws.map (floorShare amount (natSum ws))) + leftover amount ws = amount ∧
      leftover amount ws ≤ ws.length := by
  unfold leftover
  have h1 : natSum (ws.map (floorShare amount (natSum ws))) * natSum ws ≤ amount * natSum ws :=
    plan0_floor_sum_mul_le amount (natSum ws) ws
  have hFle : natSum (ws.map (floorShare amount (natSum ws))) ≤ amount :=
    tmp_cancel_check _ _ _ h1 hW
  have h2 : amount * natSum ws ≤
      natSum (ws.map (floorShare amount (natSum ws))) * natSum ws + ws.length * natSum ws :=
    plan0_amount_mul_le_floor_sum amount (natSum ws) ws hW
  have hle2 : amount ≤ natSum (ws.map (floorShare amount (natSum ws))) + ws.length := by
    have hmul : (natSum (ws.map (floorShare amount (natSum ws))) + ws.length) * natSum ws =
        natSum (ws.map (floorShare amount (natSum ws))) * natSum ws + ws.length * natSum ws := by
      rw [Nat.add_mul]
    have hle_mul : amount * natSum ws ≤
        (natSum (ws.map (floorShare amount (natSum ws))) + ws.length) * natSum ws := by
      omega
    exact Nat.le_of_mul_le_mul_right hle_mul hW
  constructor
  · omega
  · omega

theorem plan0_leftover_inline_test : True := trivial

theorem tmp_probe_ext2 : True := by trivial
#check @List.getElem_map
#check @List.getElem_range
#check @List.ext_get
#check @List.range_succ
#check @List.getD

theorem tmp_probe_range5 : True := by trivial
#check @List.range_succ_eq_map
#check @List.range_succ
#check @List.map_append
#check @List.getD
#check @List.getElem_cons

theorem tmp_probe_rsq : True := trivial
#check List.range_succ_eq_map
#check List.map_append
#check List.range_succ

theorem tmpA_getD_cons_succ (x : Nat) (xs : List Nat) (i : Nat) :
    (x :: xs).getD (i + 1) 0 = xs.getD i 0 := by
  simp

theorem tmpA_map_congr_test (x : Nat) (xs : List Nat) (f : Nat → Nat) :
    (fun i => f ((x :: xs).getD (Nat.succ i) 0)) = (fun i => f (xs.getD i 0)) := by
  funext i
  rw [tmpA_getD_cons_succ]

theorem tmpA_mm : True := trivial
#check @List.map_map
#check @Function.comp









theorem plan1_weightedShare_range_decomp (amount : Nat) (ws : List Nat)
    (hlo : leftover amount ws ≤ ws.length) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) =
      natSum (ws.map (floorShare amount (natSum ws))) + leftover amount ws := by
  have hadd_gen : ∀ (l : List Nat) (f g : Nat → Nat),
      natSum (l.map (fun a => f a + g a)) = natSum (l.map f) + natSum (l.map g) := by
    intro l f g
    induction l with
    | nil => rfl
    | cons x xs ih => simp [natSum, ih, Nat.add_assoc, Nat.add_left_comm]
  have hcons_gen : ∀ (x : Nat) (xs : List Nat) (f : Nat → Nat),
      (List.range (x :: xs).length).map (fun i => f ((x :: xs).getD i 0)) =
        f x :: (List.range xs.length).map (fun i => f (xs.getD i 0)) := by
    intro x xs f
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    have hhead : f ((x :: xs).getD 0 0) = f x := by simp
    have h2 : List.map ((fun i => f ((x :: xs).getD i 0)) ∘ Nat.succ) (List.range xs.length)
        = (List.range xs.length).map (fun i => f (xs.getD i 0)) := by
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      rw [tmpA_getD_cons_succ]
    rw [hhead, h2]
  have hfloor_gen : ∀ (l : List Nat) (f : Nat → Nat),
      natSum ((List.range l.length).map (fun i => f (l.getD i 0))) = natSum (l.map f) := by
    intro l
    induction l with
    | nil => intro f; rfl
    | cons x xs ih =>
      intro f
      have hmap := hcons_gen x xs f
      rw [hmap]
      simp only [List.map_cons, natSum]
      rw [ih]
  have hind_gen : ∀ (m : Nat) (k : Nat),
      natSum ((List.range m).map (fun i => if i < k then 1 else 0)) = Nat.min k m := by
    intro m
    induction m with
    | zero => intro k; simp [natSum]
    | succ n ih =>
      intro k
      have hrw : List.range (n + 1) = List.range n ++ [n] := List.range_succ
      rw [hrw, List.map_append, tmp_natSum_append]
      have hsing : natSum ([n].map (fun i => if i < k then 1 else 0)) = (if n < k then 1 else 0) := by
        simp [natSum]
      rw [hsing, ih k]
      by_cases hnk : n < k
      · have h1 : Nat.min k n = n := Nat.min_eq_right (Nat.le_of_lt hnk)
        have h2 : n + 1 ≤ k := hnk
        have h3 : Nat.min k (n + 1) = n + 1 := Nat.min_eq_right h2
        simp only [hnk, ↓reduceIte] at hsing ⊢
        omega
      · simp only [hnk, ↓reduceIte]
        have hle : k ≤ n := by omega
        have h1 : Nat.min k n = k := Nat.min_eq_left hle
        have hle2 : k ≤ n + 1 := by omega
        have h2 : Nat.min k (n + 1) = k := Nat.min_eq_left hle2
        omega
  have hsplit : ((List.range ws.length).map (weightedShare amount ws))
    = ((List.range ws.length).map (fun i => (floorShare amount (natSum ws) (ws.getD i 0) + (if i < leftover amount ws then 1 else 0)))) := by
    apply List.map_congr_left
    intro i _
    rfl
  rw [hsplit]
  have hadd := hadd_gen (List.range ws.length)
    (fun i => floorShare amount (natSum ws) (ws.getD i 0))
    (fun i => (if i < leftover amount ws then 1 else 0))
  rw [hadd]
  have hfloor : natSum ((List.range ws.length).map (fun i => floorShare amount (natSum ws) (ws.getD i 0)))
      = natSum (ws.map (floorShare amount (natSum ws))) := hfloor_gen ws _
  have hmin : Nat.min (leftover amount ws) ws.length = leftover amount ws := Nat.min_eq_left hlo
  have hind : natSum ((List.range ws.length).map (fun i => (if i < leftover amount ws then 1 else 0)))
      = leftover amount ws := by rw [hind_gen ws.length (leftover amount ws), hmin]
  rw [hfloor, hind]


theorem plan1_natSum_map_add_fixed : True := trivial

theorem plan1_natSum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    natSum (l.map (fun a => f a + g a)) = natSum (l.map f) + natSum (l.map g) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc, Nat.add_left_comm]

theorem tmp_probe_rangeX : True := by trivial
#check @List.range_succ
#check @List.range_zero

theorem tmp_use_rangesucc (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  exact List.range_succ

theorem tmp_probe_append2 : True := by trivial
#check @List.map_append
#check @List.mem_range
#check @List.range_succ
#check @Nat.lt_succ_self
#check @Nat.lt_of_lt_of_le
#check @Nat.le_step

theorem plan1_natSum_range_indicator (k n : Nat) (hkn : k ≤ n) :
    natSum ((List.range n).map (fun i => if i < k then 1 else 0)) = k := by
  have hall : ∀ (m : Nat) (k : Nat),
      natSum ((List.range m).map (fun i => if i < k then 1 else 0)) = Nat.min k m := by
    intro m
    induction m with
    | zero =>
      intro k
      simp [natSum]
    | succ n ih =>
      intro k
      have hrw : List.range (n + 1) = List.range n ++ [n] := List.range_succ
      rw [hrw, List.map_append, tmp_natSum_append]
      have hsing : natSum ([n].map (fun i => if i < k then 1 else 0)) = (if n < k then 1 else 0) := by
        simp [natSum]
      rw [hsing, ih k]
      by_cases hnk : n < k
      · have h1 : Nat.min k n = n := Nat.min_eq_right (Nat.le_of_lt hnk)
        have h2 : n + 1 ≤ k := hnk
        have h3 : Nat.min k (n + 1) = n + 1 := Nat.min_eq_right h2
        simp only [hnk, ↓reduceIte] at hsing ⊢
        omega
      · simp only [hnk, ↓reduceIte]
        have hle : k ≤ n := by omega
        have h1 : Nat.min k n = k := Nat.min_eq_left hle
        have hle2 : k ≤ n + 1 := by omega
        have h2 : Nat.min k (n + 1) = k := Nat.min_eq_left hle2
        omega
  have hmin : Nat.min k n = k := Nat.min_eq_left hkn
  rw [hall n k, hmin]

theorem tmp_check_sig : True := trivial
#check @List.getElem_range
#check @List.length_range
#check @List.getElem_map

theorem tmp_check2 : True := trivial
#check @List.range_succ_eq_map
#check @List.map_map

theorem tmp_show_type : True := by
  have h := @List.range_succ_eq_map
  have h2 : True := by exact trivial
  trivial
#check @List.range_succ_eq_map

theorem plan1_map_range_getD_cons (x : Nat) (xs : List Nat) (f : Nat → Nat) :
    (List.range (x :: xs).length).map (fun i => f ((x :: xs).getD i 0)) =
      f x :: (List.range xs.length).map (fun i => f (xs.getD i 0)) := by
  have hlen : (x :: xs).length = xs.length + 1 := rfl
  rw [hlen, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  have hhead : f ((x :: xs).getD 0 0) = f x := by simp
  have h2 : List.map ((fun i => f ((x :: xs).getD i 0)) ∘ Nat.succ) (List.range xs.length)
      = (List.range xs.length).map (fun i => f (xs.getD i 0)) := by
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [tmpA_getD_cons_succ]
  rw [hhead, h2]

theorem tmp_getD_eq_test (xs : List Nat) (f : Nat → Nat) :
    (fun i => f (xs.getD i 0)) = (fun i => f (xs[i]?.getD 0)) := by
  rfl

theorem tmp_try_range_getD2 (ws : List Nat) (f : Nat → Nat) :
    natSum ((List.range ws.length).map (fun i => f (ws.getD i 0))) =
      natSum (ws.map f) := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    have hmap := plan1_map_range_getD_cons x xs f
    rw [hmap]
    simp only [List.map_cons, natSum]
    rw [ih]

theorem plan1_natSum_range_getD (ws : List Nat) (f : Nat → Nat) :
    natSum ((List.range ws.length).map (fun i => f (ws.getD i 0))) =
      natSum (ws.map f) := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    have hmap := plan1_map_range_getD_cons x xs f
    rw [hmap]
    simp only [List.map_cons, natSum]
    rw [ih]

theorem plan1_weightedShare_range_decomp2 (amount : Nat) (ws : List Nat)
    (hlo : leftover amount ws ≤ ws.length) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) =
      natSum (ws.map (floorShare amount (natSum ws))) + leftover amount ws := by
  have hsplit : ((List.range ws.length).map (weightedShare amount ws))
    = ((List.range ws.length).map (fun i => (floorShare amount (natSum ws) (ws.getD i 0) + (if i < leftover amount ws then 1 else 0)))) := by
    apply List.map_congr_left
    intro i _
    rfl
  rw [hsplit]
  have hadd := plan1_natSum_map_add (List.range ws.length)
    (fun i => floorShare amount (natSum ws) (ws.getD i 0))
    (fun i => (if i < leftover amount ws then 1 else 0))
  rw [hadd]
  have hfloor : natSum ((List.range ws.length).map (fun i => floorShare amount (natSum ws) (ws.getD i 0)))
      = natSum (ws.map (floorShare amount (natSum ws))) := plan1_natSum_range_getD ws _
  have hind : natSum ((List.range ws.length).map (fun i => (if i < leftover amount ws then 1 else 0)))
      = leftover amount ws := plan1_natSum_range_indicator (leftover amount ws) ws.length hlo
  rw [hfloor, hind]

theorem plan1_decomp_selfcontained (amount : Nat) (ws : List Nat)
    (hlo : leftover amount ws ≤ ws.length) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) =
      natSum (ws.map (floorShare amount (natSum ws))) + leftover amount ws := by
  have hadd_gen : ∀ (l : List Nat) (f g : Nat → Nat),
      natSum (l.map (fun a => f a + g a)) = natSum (l.map f) + natSum (l.map g) := by
    intro l f g
    induction l with
    | nil => rfl
    | cons x xs ih => simp [natSum, ih, Nat.add_assoc, Nat.add_left_comm]
  have hcons_gen : ∀ (x : Nat) (xs : List Nat) (f : Nat → Nat),
      (List.range (x :: xs).length).map (fun i => f ((x :: xs).getD i 0)) =
        f x :: (List.range xs.length).map (fun i => f (xs.getD i 0)) := by
    intro x xs f
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    have hhead : f ((x :: xs).getD 0 0) = f x := by simp
    have h2 : List.map ((fun i => f ((x :: xs).getD i 0)) ∘ Nat.succ) (List.range xs.length)
        = (List.range xs.length).map (fun i => f (xs.getD i 0)) := by
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      rw [tmpA_getD_cons_succ]
    rw [hhead, h2]
  have hfloor_gen : ∀ (l : List Nat) (f : Nat → Nat),
      natSum ((List.range l.length).map (fun i => f (l.getD i 0))) = natSum (l.map f) := by
    intro l
    induction l with
    | nil => intro f; rfl
    | cons x xs ih =>
      intro f
      have hmap := hcons_gen x xs f
      rw [hmap]
      simp only [List.map_cons, natSum]
      rw [ih]
  have hind_gen : ∀ (m : Nat) (k : Nat),
      natSum ((List.range m).map (fun i => if i < k then 1 else 0)) = Nat.min k m := by
    intro m
    induction m with
    | zero => intro k; simp [natSum]
    | succ n ih =>
      intro k
      have hrw : List.range (n + 1) = List.range n ++ [n] := List.range_succ
      rw [hrw, List.map_append, tmp_natSum_append]
      have hsing : natSum ([n].map (fun i => if i < k then 1 else 0)) = (if n < k then 1 else 0) := by
        simp [natSum]
      rw [hsing, ih k]
      by_cases hnk : n < k
      · have h1 : Nat.min k n = n := Nat.min_eq_right (Nat.le_of_lt hnk)
        have h2 : n + 1 ≤ k := hnk
        have h3 : Nat.min k (n + 1) = n + 1 := Nat.min_eq_right h2
        simp only [hnk, ↓reduceIte] at hsing ⊢
        omega
      · simp only [hnk, ↓reduceIte]
        have hle : k ≤ n := by omega
        have h1 : Nat.min k n = k := Nat.min_eq_left hle
        have hle2 : k ≤ n + 1 := by omega
        have h2 : Nat.min k (n + 1) = k := Nat.min_eq_left hle2
        omega
  have hsplit : ((List.range ws.length).map (weightedShare amount ws))
    = ((List.range ws.length).map (fun i => (floorShare amount (natSum ws) (ws.getD i 0) + (if i < leftover amount ws then 1 else 0)))) := by
    apply List.map_congr_left
    intro i _
    rfl
  rw [hsplit]
  have hadd := hadd_gen (List.range ws.length)
    (fun i => floorShare amount (natSum ws) (ws.getD i 0))
    (fun i => (if i < leftover amount ws then 1 else 0))
  rw [hadd]
  have hfloor : natSum ((List.range ws.length).map (fun i => floorShare amount (natSum ws) (ws.getD i 0)))
      = natSum (ws.map (floorShare amount (natSum ws))) := hfloor_gen ws _
  have hmin : Nat.min (leftover amount ws) ws.length = leftover amount ws := Nat.min_eq_left hlo
  have hind : natSum ((List.range ws.length).map (fun i => (if i < leftover amount ws then 1 else 0)))
      = leftover amount ws := by rw [hind_gen ws.length (leftover amount ws), hmin]
  rw [hfloor, hind]

theorem plan0_weightedShare_range_sum (amount : Nat) (ws : List Nat)
    (hW : 0 < natSum ws) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) = amount := by
  have h := plan0_leftover_add_floor amount ws hW
  obtain ⟨hadd, hlo⟩ := h
  have hdecomp := plan1_weightedShare_range_decomp2 amount ws hlo
  omega

theorem tmp_explore_range (n : Nat) : List.range (n+1) = List.range n ++ [n] := List.range_succ
#check @List.range_succ_eq_map
#check @List.range_succ

theorem tmp_idx_some_aux (l : List Nat) (a : Nat) (h : a ∈ l) : ∃ i, indexOf? l a = some i := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    unfold indexOf?
    by_cases hx : x = a
    · simp [hx]
    · simp [hx]
      simp only [List.mem_cons] at h
      rcases h with rfl | hm
      · simp at hx
      · obtain ⟨i, hi⟩ := ih hm
        exact ⟨i + 1, by simp [hi]⟩

theorem tmp_chk_sig2 : True := trivial
#check @List.range_succ_eq_map

theorem tmp_getD_cons_mem2 (x : Nat) (xs : List Nat) (a : Nat) (hm : a ∈ xs) (hne : x ≠ a) :
    (indexOf? (x :: xs) a).getD 0 = (indexOf? xs a).getD 0 + 1 := by
  have hcons : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by simp [indexOf?, hne]
  rw [hcons]
  cases hxs : indexOf? xs a with
  | none =>
    have hcontra : ∃ i, indexOf? xs a = some i := tmp_idx_some_aux xs a hm
    rw [hxs] at hcontra
    simp at hcontra
  | some i => simp

theorem tmp_probe_succ_use (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  exact List.range_succ

theorem plan2_indexOf_exists_of_mem (l : List Nat) (a : Nat) (h : a ∈ l) :
    ∃ i, indexOf? l a = some i :=
  tmp_idx_some_aux l a h


theorem plan2_indexOf_cons_getD (x : Nat) (xs : List Nat) (a : Nat)
    (hne : x ≠ a) (hmem : a ∈ xs) :
    (indexOf? (x :: xs) a).getD 0 = (indexOf? xs a).getD 0 + 1 := by
  have hcons : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by simp [indexOf?, hne]
  obtain ⟨i, hi⟩ := tmp_idx_some_aux xs a hmem
  rw [hcons, hi]
  simp


theorem plan2_sumOver_cons_indexOf (x : Nat) (xs : List Nat)
    (amount : Nat) (ws : List Nat) (k : Nat) (hl : (x :: xs).Nodup) :
    sumOver (x :: xs)
        (fun a => (weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Int)) =
      (weightedShare amount ws k : Int) +
        sumOver xs
          (fun a => (weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Int)) := by
  have hnod := List.nodup_cons.mp hl
  have hx_not : x ∉ xs := hnod.1
  have hhead : (indexOf? (x :: xs) x).getD 0 = 0 := by simp [indexOf?]
  have hhead_val : (weightedShare amount ws (k + (indexOf? (x :: xs) x).getD 0) : Int)
      = (weightedShare amount ws k : Int) := by rw [hhead, Nat.add_zero]
  have htail_eq : ∀ a ∈ xs,
      ((weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Nat) : Int)
      = ((weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Nat) : Int) := by
    intro a ha
    have hne : x ≠ a := fun h => hx_not (h ▸ ha)
    have hcons : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by simp [indexOf?, hne]
    obtain ⟨i, hi⟩ := tmp_idx_some_aux xs a ha
    rw [hcons, hi]
    simp only [Option.map_some, Option.getD_some]
    have : k + (i + 1) = (k + 1) + i := by omega
    rw [this]
  have hsum : sumOver xs (fun a => ((weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Nat) : Int))
      = sumOver xs (fun a => ((weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Nat) : Int)) := by
    apply sumOver_congr
    intro a ha
    exact htail_eq a ha
  calc sumOver (x :: xs) (fun a => (weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Int))
      = (weightedShare amount ws (k + (indexOf? (x :: xs) x).getD 0) : Int)
        + sumOver xs (fun a => (weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Int)) := rfl
    _ = (weightedShare amount ws k : Int)
        + sumOver xs (fun a => (weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Int)) := by
        rw [hhead_val, hsum]


theorem plan2_natSum_range_succ (f : Nat → Nat) (n k : Nat) :
    natSum ((List.range (n + 1)).map (fun i => f (k + i))) =
      f k + natSum ((List.range n).map (fun i => f ((k + 1) + i))) := by
  have hr : List.range (n + 1) = 0 :: List.map Nat.succ (List.range n) := by
    exact @List.range_succ_eq_map n
  rw [hr]
  simp only [List.map_cons]
  have hhead : f (k + 0) = f k := by simp
  rw [hhead]
  simp only [natSum]
  congr 1
  rw [List.map_map]
  apply congrArg (natSum ·)
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  congr 1
  omega


theorem plan2_indexOf_exists_of_mem_aux (l : List Nat) (a : Nat) (h : a ∈ l) :
    ∃ i, indexOf? l a = some i := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    unfold indexOf?
    by_cases hx : x = a
    · simp [hx]
    · simp [hx]
      simp only [List.mem_cons] at h
      rcases h with rfl | hm
      · simp at hx
      · obtain ⟨i, hi⟩ := ih hm
        exact ⟨i + 1, by simp [hi]⟩

theorem plan2_indexOf_exists_of_mem2 (l : List Nat) (a : Nat) (h : a ∈ l) :
    ∃ i, indexOf? l a = some i :=
  plan2_indexOf_exists_of_mem_aux l a h

theorem plan2_indexOf_exists_of_mem3 (l : List Nat) (a : Nat) (h : a ∈ l) :
    ∃ i, indexOf? l a = some i :=
  tmp_idx_some_aux l a h

theorem plan2_indexOf_cons_getD_proof (x : Nat) (xs : List Nat) (a : Nat)
    (hne : x ≠ a) (hmem : a ∈ xs) :
    (indexOf? (x :: xs) a).getD 0 = (indexOf? xs a).getD 0 + 1 := by
  have hcons : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by simp [indexOf?, hne]
  obtain ⟨i, hi⟩ := tmp_idx_some_aux xs a hmem
  rw [hcons, hi]
  simp

theorem plan2_sumOver_cons_indexOf_aux_test : True := trivial

theorem plan2_sumOver_cons_indexOf_proof (x : Nat) (xs : List Nat)
    (amount : Nat) (ws : List Nat) (k : Nat) (hl : (x :: xs).Nodup) :
    sumOver (x :: xs)
        (fun a => (weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Int)) =
      (weightedShare amount ws k : Int) +
        sumOver xs
          (fun a => (weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Int)) := by
  have hnod := List.nodup_cons.mp hl
  have hx_not : x ∉ xs := hnod.1
  have hhead : (indexOf? (x :: xs) x).getD 0 = 0 := by simp [indexOf?]
  have hhead_val : (weightedShare amount ws (k + (indexOf? (x :: xs) x).getD 0) : Int)
      = (weightedShare amount ws k : Int) := by rw [hhead, Nat.add_zero]
  have htail_eq : ∀ a ∈ xs,
      ((weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Nat) : Int)
      = ((weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Nat) : Int) := by
    intro a ha
    have hne : x ≠ a := fun h => hx_not (h ▸ ha)
    have hcons : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by simp [indexOf?, hne]
    obtain ⟨i, hi⟩ := tmp_idx_some_aux xs a ha
    rw [hcons, hi]
    simp only [Option.map_some, Option.getD_some]
    have : k + (i + 1) = (k + 1) + i := by omega
    rw [this]
  have hsum : sumOver xs (fun a => ((weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Nat) : Int))
      = sumOver xs (fun a => ((weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Nat) : Int)) := by
    apply sumOver_congr
    intro a ha
    exact htail_eq a ha
  calc sumOver (x :: xs) (fun a => (weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Int))
      = (weightedShare amount ws (k + (indexOf? (x :: xs) x).getD 0) : Int)
        + sumOver xs (fun a => (weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Int)) := rfl
    _ = (weightedShare amount ws k : Int)
        + sumOver xs (fun a => (weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Int)) := by
        rw [hhead_val, hsum]

theorem plan2_natSum_range_succ_proof (f : Nat → Nat) (n k : Nat) :
    natSum ((List.range (n + 1)).map (fun i => f (k + i))) =
      f k + natSum ((List.range n).map (fun i => f ((k + 1) + i))) := by
  have hr : List.range (n + 1) = 0 :: List.map Nat.succ (List.range n) := by
    exact @List.range_succ_eq_map n
  rw [hr]
  simp only [List.map_cons]
  have hhead : f (k + 0) = f k := by simp
  rw [hhead]
  simp only [natSum]
  congr 1
  rw [List.map_map]
  apply congrArg (natSum ·)
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  congr 1
  omega

theorem plan0_sumOver_indexOf_offset (l : List AccountId) (amount : Nat)
    (ws : List Nat) (k : Nat) (hl : l.Nodup) :
    sumOver l
        (fun a => (weightedShare amount ws (k + (indexOf? l a).getD 0) : Int)) =
      ((natSum ((List.range l.length).map
        (fun i => weightedShare amount ws (k + i)))) : Int) := by
  induction l generalizing k with
  | nil => rfl
  | cons x xs ih =>
    have h1 := plan2_sumOver_cons_indexOf_proof x xs amount ws k hl
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    have h2 := plan2_natSum_range_succ_proof (fun j => weightedShare amount ws j) xs.length k
    rw [hlen]
    have hL : sumOver (x :: xs) (fun a => (weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Int))
      = (weightedShare amount ws k : Int) +
        sumOver xs (fun a => (weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Int)) := h1
    rw [hL]
    have hIH := ih (k + 1) (List.nodup_cons.mp hl).2
    rw [hIH]
    have hNat : natSum ((List.range (xs.length + 1)).map (fun i => weightedShare amount ws (k + i)))
      = weightedShare amount ws k + natSum ((List.range xs.length).map (fun i => weightedShare amount ws ((k + 1) + i))) := h2
    rw [hNat]
    simp only [Int.natCast_add]

theorem plan0_aux_zero (l : List Nat) : sumOver l (fun _ : Nat => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization  : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hv : ValidPayout s r
  · exact hv.2.2.2.2.2.2.2.2.2.1
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have hs : step s r = (.ok, { accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied }) := by unfold step; simp [hv]
    rw [hs]
    exact ⟨rfl, rfl, fun a => rfl⟩
  · have heq : step s r = (.rejected, s) := by unfold step; simp [hv]
    have hcon : (step s r).1 = .rejected := by rw [heq]
    rw [hcon] at h
    cases h

theorem req_idempotency    : Idempotent step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have hs : step s r = (.ok, ({ accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied } : State)) := by unfold step; simp [hv]
    have h2 : (step s r).2 = (({ accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied } : State)) := by rw [hs]
    have happ : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
      rw [h2]
      intro x
      simp
    refine ⟨happ, ?_⟩
    have hnot_s2 : ¬ ValidPayout (({ accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied } : State)) r := by
      intro hcon
      rcases hcon with ⟨_,_,_,_,_,_,_,_,_,_,_, hmem⟩
      simp at hmem
    have hstep_s2 : step (({ accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied } : State)) r = (.rejected, (({ accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied } : State))) := by
      unfold step
      simp [hnot_s2]
    calc step (step s r).2 r
        = step (({ accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied } : State)) r := by rw [h2]
      _ = (.rejected, (({ accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied } : State))) := hstep_s2
      _ = (.rejected, (step s r).2) := by rw [h2]
  · have heq : step s r = (.rejected, s) := by unfold step; simp [hv]
    have hcon : (step s r).1 = .rejected := by rw [heq]
    rw [hcon] at h
    cases h

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hv0 := hv
    rcases hv with ⟨hNodup, hpos, hne, hlen, hposW, hNodupR, hsrcNot, hsrcMem, hmem, hauth, hle, hfresh⟩
    have hs : step s r = (.ok, ({ accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied } : State)) := by unfold step; simp [hv0]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hs]
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [hs]
    rw [hacc] at ha
    rw [hbal]
    unfold expectedBalance
    by_cases heq : a = r.source
    · subst heq
      have hshare0 : shareOf r r.source = 0 := by unfold shareOf; rw [indexOf?_eq_none hsrcNot]
      simp [hshare0]
      omega
    · have hif : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [heq]
      rw [hif]
      have h1 : 0 ≤ s.balance a := hnn a ha
      have h2 : (0 : Int) ≤ ((shareOf r a : Nat) : Int) := by omega
      omega
  · have hs : step s r = (.rejected, s) := by unfold step; simp [hv]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hs]
    have hbal : (step s r).2.balance a = s.balance a := by rw [hs]
    rw [hacc] at ha
    rw [hbal]
    exact hnn a ha

theorem req_pro_rata : ProRataShares step := by
  intro s r h i hi
  by_cases hv : ValidPayout s r
  · have hs : step s r = (.ok, ({ accounts := s.accounts, balance := fun a => expectedBalance s r a, auth := s.auth, applied := r.txId :: s.applied } : State)) := by unfold step; simp [hv]
    have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by rw [hs]
    obtain ⟨_, _, _, _, _, hnodupR, hsrcNot, _, _, _, _, _⟩ := hv
    have hne : r.recipients[i] ≠ r.source := by
      intro heq
      apply hsrcNot
      rw [← heq]
      exact List.getElem_mem hi
    have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by simp [hne]
    have hidx : indexOf? r.recipients r.recipients[i] = some i := indexOf?_getElem hnodupR i hi
    have hshare : shareOf r r.recipients[i] = weightedShare r.amount r.weights i := by
      unfold shareOf; rw [hidx]
    unfold expectedBalance at hbal
    rw [hbal, hif, hshare]
    simp; omega
  · have heq : step s r = (.rejected, s) := by unfold step; simp [hv]
    have hcon : (step s r).1 = .rejected := by rw [heq]
    rw [hcon] at h
    cases h

theorem req_rounding_bound : RoundingBound step := by
  intro s r h i hi
  by_cases hv : ValidPayout s r
  · have hpr := req_pro_rata s r h i hi
    obtain ⟨hNodup, hpos, hneR, hlen, hposW, hNodupR, hsrcNot, hsrcMem, hmem, hauth, hle, hfresh⟩ := hv
    have hneW : r.weights ≠ [] := by
      intro hc
      have hlen0 : r.recipients.length = 0 := by rw [← hlen, hc]; rfl
      have hemp : r.recipients = [] := List.length_eq_zero_iff.mp hlen0
      exact hneR hemp
    have hWpos : 0 < natSum r.weights := tmp_Wpos_lemma r.weights hposW hneW
    have hws : weightedShare r.amount r.weights i
        = floorShare r.amount (natSum r.weights) (r.weights.getD i 0)
          + (if i < leftover r.amount r.weights then 1 else 0) := rfl
    have hfloor : floorShare r.amount (natSum r.weights) (r.weights.getD i 0)
        = r.amount * r.weights.getD i 0 / natSum r.weights := rfl
    have hb_le : (if i < leftover r.amount r.weights then 1 else 0) ≤ 1 := by
      by_cases hc : i < leftover r.amount r.weights <;> simp [hc]
    have hNat := tmp_round_nat4 (r.amount * r.weights.getD i 0) (natSum r.weights)
      (floorShare r.amount (natSum r.weights) (r.weights.getD i 0))
      (if i < leftover r.amount r.weights then 1 else 0)
      (weightedShare r.amount r.weights i) hWpos (by rw [hws]) hb_le (by rw [hfloor])
    obtain ⟨h1Nat, h2Nat⟩ := hNat
    have eMul : ∀ (x y : Nat), (((x * y : Nat) : Int) = ((x : Int)) * ((y : Int))) := fun x y => by rw [Int.natCast_mul]
    have eAdd : ∀ (x y : Nat), (((x + y : Nat) : Int) = ((x : Int)) + ((y : Int))) := fun x y => by rw [Int.natCast_add]
    have g1 : ((((weightedShare r.amount r.weights i * natSum r.weights : Nat) : Int))
        ≤ (((r.amount * r.weights.getD i 0 + natSum r.weights : Nat) : Int))) :=
      Int.ofNat_le.mpr h1Nat
    have g2 : ((((r.amount * r.weights.getD i 0 : Nat) : Int))
        < (((weightedShare r.amount r.weights i * natSum r.weights + natSum r.weights : Nat) : Int))) :=
      Int.ofNat_lt.mpr h2Nat
    rw [eMul, eAdd] at g1
    rw [eMul, eAdd] at g2
    rw [hpr]
    exact ⟨g1, g2⟩
  · have heq : step s r = (.rejected, s) := by unfold step; simp [hv]
    have hcon : (step s r).1 = .rejected := by rw [heq]
    rw [hcon] at h
    cases h

theorem req_conservation   : Conserves step := sorry

end WeightedPayout
