import WeightedPayout.Spec
import WeightedPayout.Lemmas

namespace WeightedPayout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout
  infer_instance

def step : Impl := fun s r =>
  if ValidPayout s r then
    (Outcome.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (Outcome.rejected, s)

/-! basic step facts -/

theorem ok_valid {s : State} {r : Request} (h : (step s r).1 = Outcome.ok) : ValidPayout s r := by
  unfold step at h
  by_cases hv : ValidPayout s r
  · exact hv
  · simp [hv] at h

theorem step_ok_eq {s : State} {r : Request} (h : ValidPayout s r) :
    step s r = (Outcome.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
  unfold step
  simp [h]

theorem step_rej_eq {s : State} {r : Request} (h : ¬ ValidPayout s r) :
    step s r = (Outcome.rejected, s) := by
  unfold step
  simp [h]

/-! Nat division facts -/

theorem div_mul_le_self' (m W : Nat) : (m / W) * W ≤ m := by
  have h := Nat.div_add_mod m W
  have hcomm : m / W * W = W * (m / W) := Nat.mul_comm _ _
  omega

theorem div_succ_mul_lt' (m W : Nat) (hw : 0 < W) : m < (m / W + 1) * W := by
  have h := Nat.div_add_mod m W
  have hlt : m % W < W := Nat.mod_lt m hw
  have heq : (m / W + 1) * W = W * (m / W) + W := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

theorem le_of_mul_le_mul_right'' {a b W : Nat} (h : a * W ≤ b * W) (hw : 0 < W) : a ≤ b := by
  by_contra hn
  push_neg at hn
  have hle : b * W ≤ a * W := Nat.mul_le_mul hn (le_refl W)
  omega

theorem lt_of_mul_lt_mul_right'' {a b W : Nat} (h : a * W < b * W) (hw : 0 < W) : a < b := by
  by_contra hn
  push_neg at hn
  have hle : b * W ≤ a * W := Nat.mul_le_mul hn (le_refl W)
  omega

/-! natSum pointwise -/

theorem natSum_le_of_pointwise' (ws : List Nat) (f g : Nat → Nat)
    (h : ∀ w ∈ ws, f w ≤ g w) : natSum (ws.map f) ≤ natSum (ws.map g) := by
  induction ws with
  | nil => simp [natSum]
  | cons x xs ih =>
    simp only [List.map_cons, natSum]
    have hx : f x ≤ g x := h x (by simp)
    have ht : natSum (List.map f xs) ≤ natSum (List.map g xs) :=
      ih (fun w hw => h w (by simp [hw]))
    omega

theorem natSum_lt_of_pointwise' (ws : List Nat) (f g : Nat → Nat)
    (hle : ∀ w ∈ ws, f w ≤ g w) (hlt : ∃ w ∈ ws, f w < g w) :
    natSum (ws.map f) < natSum (ws.map g) := by
  induction ws with
  | nil => simp at hlt
  | cons x xs ih =>
    simp only [List.map_cons, natSum]
    have hxle : f x ≤ g x := hle x (by simp)
    have hxsle : ∀ w ∈ xs, f w ≤ g w := fun w hw => hle w (by simp [hw])
    have hxsle2 : ∀ w ∈ xs, f w ≤ g w := hxsle
    obtain ⟨w0, hw0mem, hw0lt⟩ := hlt
    simp at hw0mem
    cases hw0mem with
    | inl heq =>
      subst heq
      have htail_le : natSum (List.map f xs) ≤ natSum (List.map g xs) :=
        natSum_le_of_pointwise' xs f g hxsle2
      omega
    | inr hmem =>
      have htail : natSum (List.map f xs) < natSum (List.map g xs) :=
        ih hxsle (⟨w0, hmem, hw0lt⟩)
      omega

theorem amount_mul_natSum' (ws : List Nat) (amount : Nat) :
    amount * natSum ws = natSum (ws.map (amount * ·)) := by
  induction ws with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, Nat.mul_add, ih]

theorem natSum_pos_of_pos' {ws : List Nat} (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) : 0 < natSum ws := by
  induction ws with
  | nil => simp at hne
  | cons x xs ih =>
    simp only [natSum]
    have hx : 0 < x := hpos x (by simp)
    by_cases hxs : xs = []
    · subst hxs
      simp [natSum]
      omega
    · have htail : 0 < natSum xs := ih hxs (fun w hw => hpos w (by simp [hw]))
      omega

theorem valid_W_pos' {s : State} {r : Request} (h : ValidPayout s r) : 0 < natSum r.weights := by
  obtain ⟨_, _, hne, hlen, hpos, _, _, _, _, _, _, _⟩ := h
  have hwsne : r.weights ≠ [] := by
    intro hc
    rw [hc] at hlen
    simp at hlen
    rw [hlen] at hne
    exact hne rfl
  exact natSum_pos_of_pos' hwsne hpos

theorem sum_floor_mul_le' (ws : List Nat) (amount W : Nat) :
    (natSum (ws.map (floorShare amount W))) * W ≤ amount * natSum ws := by
  induction ws with
  | nil => simp [natSum, floorShare]
  | cons w xs ih =>
    simp only [List.map_cons, natSum]
    rw [Nat.add_mul]
    have h1 : floorShare amount W w * W ≤ amount * w := by
      unfold floorShare
      exact div_mul_le_self' (amount * w) W
    have h2 := ih
    have h3 : amount * (w + natSum xs) = amount * w + amount * natSum xs := Nat.mul_add _ _ _
    rw [h3]
    exact Nat.add_le_add h1 h2

theorem floor_le_succ' (amount W w : Nat) (hw : 0 < W) :
    amount * w ≤ (floorShare amount W w + 1) * W := by
  unfold floorShare
  exact Nat.le_of_lt (div_succ_mul_lt' (amount * w) W hw) |>.trans (by omega) |>.trans_eq (by rw [Nat.add_mul, Nat.one_mul]) |>.trans (by omega)
  -- fallback direct
theorem floor_lt_succW (amount W w : Nat) (hw : 0 < W) :
    amount * w < (floorShare amount W w + 1) * W := by
  unfold floorShare
  exact div_succ_mul_lt' (amount * w) W hw

theorem sum_floor_succ_eq' (ws : List Nat) (amount W : Nat) :
    natSum (ws.map (fun w => (floorShare amount W w + 1) * W))
      = (natSum (ws.map (floorShare amount W)) + ws.length) * W) := by
  induction ws with
  | nil => simp [natSum]
  | cons x xs ih =>
    simp only [List.map_cons, natSum, List.length]
    rw [ih]
    rw [Nat.add_mul, Nat.add_mul]
    simp [Nat.one_mul]
    omega

theorem valid_S_le' {s : State} {r : Request} (h : ValidPayout s r) :
    natSum (r.weights.map (floorShare r.amount (natSum r.weights))) ≤ r.amount := by
  have hw := valid_W_pos' h
  have hle := sum_floor_mul_le' r.weights r.amount (natSum r.weights)
  exact le_of_mul_le_mul_right'' hle hw

theorem valid_leftover_le_len' {s : State} {r : Request} (h : ValidPayout s r) :
    leftover r.amount r.weights ≤ r.recipients.length := by
  obtain ⟨hnodup_acc, hamt, hne, hlen, hpos, hnodup_rec, hsrc_not, hsrc_mem, hmem, hauth, hle_bal, hfresh⟩ := h
  have hV : ValidPayout s r :=
    ⟨hnodup_acc, hamt, hne, hlen, hpos, hnodup_rec, hsrc_not, hsrc_mem, hmem, hauth, hle_bal, hfresh⟩
  have hw : 0 < natSum r.weights := valid_W_pos' hV
  have hwsne : r.weights ≠ [] := by
    intro hc
    rw [hc] at hlen
    simp at hlen
    rw [hlen] at hne
    exact hne rfl
  have hSle : natSum (r.weights.map (floorShare r.amount (natSum r.weights))) ≤ r.amount :=
    valid_S_le' hV
  -- strict sum
  have hpt_lt : ∀ w ∈ r.weights, r.amount * w < (floorShare r.amount (natSum r.weights) w + 1) * natSum r.weights := by
    intro w _
    exact floor_lt_succW r.amount (natSum r.weights) w hw
  have hex : ∃ w ∈ r.weights, r.amount * w < (floorShare r.amount (natSum r.weights) w + 1) * natSum r.weights := by
    cases he : r.weights with
    | nil => simp at hwsne
    | cons x xs =>
      exact ⟨x, by simp, hpt_lt x (by simp)⟩
  have hlt_sum : natSum (r.weights.map (r.amount * ·)) < natSum (r.weights.map (fun w => (floorShare r.amount (natSum r.weights) w + 1) * natSum r.weights)) := by
    apply natSum_lt_of_pointwise' _ _ _ _ hex
    intro w hwmem
    exact Nat.le_of_lt (hpt_lt w hwmem)
  have heq1 : natSum (r.weights.map (r.amount * ·)) = r.amount * natSum r.weights := by
    rw [← amount_mul_natSum']
  have heq2 := sum_floor_succ_eq' r.weights r.amount (natSum r.weights)
  rw [heq1] at hlt_sum
  rw [heq2] at hlt_sum
  have hlt : r.amount < natSum (r.weights.map (floorShare r.amount (natSum r.weights))) + r.weights.length := by
    apply lt_of_mul_lt_mul_right'' (W := natSum r.weights) hw
    exact hlt_sum
  have hlen_eq : r.weights.length = r.recipients.length := hlen
  rw [← hlen_eq] at hlt
  unfold leftover
  omega

/-! finite sums over indices -/

def sumFinNat (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ m => sumFinNat m f + f m

def sumFinInt (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | Nat.succ m => sumFinInt m f + f m

theorem sumFinNat_succ_eq (m : Nat) (f : Nat → Nat) :
    sumFinNat (Nat.succ m) f = sumFinNat m f + f m := rfl

theorem sumFinInt_succ_eq (m : Nat) (f : Nat → Int) :
    sumFinInt (Nat.succ m) f = sumFinInt m f + f m := rfl

theorem sumFinNat_add (n : Nat) (f g : Nat → Nat) :
    sumFinNat n (fun i => f i + g i) = sumFinNat n f + sumFinNat n g := by
  induction n with
  | zero => simp [sumFinNat]
  | succ m ih => simp only [sumFinNat_succ_eq, ih]; omega

theorem sumFinInt_add (n : Nat) (f g : Nat → Int) :
    sumFinInt n (fun i => f i + g i) = sumFinInt n f + sumFinInt n g := by
  induction n with
  | zero => simp [sumFinInt]
  | succ m ih => simp only [sumFinInt_succ_eq, ih]; omega

theorem sumFinInt_zero (n : Nat) : sumFinInt n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => simp [sumFinInt_succ_eq, ih]

theorem sumFinNat_zero (n : Nat) : sumFinNat n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => simp [sumFinNat_succ_eq, ih]

theorem sumFinNat_congr (n : Nat) (f g : Nat → Nat) (h : ∀ i, i < n → f i = g i) :
    sumFinNat n f = sumFinNat n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumFinNat_succ_eq, sumFinNat_succ_eq]
    rw [ih (fun i hi => h i (by omega))]
    rw [h m (by omega)]

theorem sumFinInt_congr (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i = g i) :
    sumFinInt n f = sumFinInt n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumFinInt_succ_eq, sumFinInt_succ_eq]
    rw [ih (fun i hi => h i (by omega))]
    rw [h m (by omega)]

theorem sumFinNat_head (m : Nat) (f : Nat → Nat) :
    sumFinNat (Nat.succ m) f = f 0 + sumFinNat m (fun i => f (i + 1)) := by
  induction m with
  | zero => simp [sumFinNat_succ_eq, sumFinNat]
  | succ k ih =>
    rw [sumFinNat_succ_eq (Nat.succ k)]
    rw [ih]
    rw [sumFinNat_succ_eq k (fun i => f (i + 1))]
    omega

theorem sumFinNat_indic (n L : Nat) :
    sumFinNat n (fun i => if i < L then 1 else 0) = Nat.min L n := by
  induction n with
  | zero => simp [sumFinNat]
  | succ m ih =>
    rw [sumFinNat_succ_eq]
    rw [ih]
    by_cases h : m < L
    · simp [h]
      omega
    · simp [h]
      omega

theorem sumFinNat_cast (n : Nat) (f : Nat → Nat) :
    (sumFinNat n f : Int) = sumFinInt n (fun i => (f i : Int)) := by
  induction n with
  | zero => simp [sumFinNat, sumFinInt]
  | succ m ih => simp [sumFinNat_succ_eq, sumFinInt_succ_eq, ih]; omega

theorem sumFinNat_ite_const (n x : Nat) (c : Nat) :
    sumFinNat n (fun i => if i = x then c else 0) = if x < n then c else 0 := by
  induction n with
  | zero => simp [sumFinNat]
  | succ m ih =>
    rw [sumFinNat_succ_eq]
    rw [ih]
    by_cases hxm : m = x
    · subst hxm
      simp
      omega
    · have h1 : (if m = x then c else 0) = 0 := by simp [hxm]
      rw [h1]
      by_cases hxmn : x < m
      · have h2 : x < m + 1 := by omega
        simp [hxmn]
        simp [h2]
        omega
      · have h3 : ¬ x < m + 1 := by omega
        simp [hxmn, h3]

theorem sumFinInt_ite_const (n x : Nat) (c : Int) :
    sumFinInt n (fun i => if i = x then c else 0) = if x < n then c else 0 := by
  induction n with
  | zero => simp [sumFinInt]
  | succ m ih =>
    rw [sumFinInt_succ_eq]
    rw [ih]
    by_cases hxm : m = x
    · subst hxm
      simp
      omega
    · have h1 : (if m = x then c else 0) = 0 := by simp [hxm]
      rw [h1]
      by_cases hxmn : x < m
      · have h2 : x < m + 1 := by omega
        simp [hxmn, h2]
        omega
      · have h3 : ¬ x < m + 1 := by omega
        simp [hxmn, h3]

/-! getD facts -/

theorem getD_eq_getElem'' (l : List Nat) (i : Nat) (hi : i < l.length) : l.getD i 0 = l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ m =>
      have hm : m < xs.length := by simpa using hi
      have h1 : (x :: xs).getD (m + 1) 0 = xs.getD m 0 := rfl
      have h2 : (x :: xs)[m + 1] = xs[m] := rfl
      rw [h1, h2, ih m hm]

theorem getD_mem'' (l : List Nat) (i : Nat) (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [getD_eq_getElem'' l i hi]
  exact List.getElem_mem hi

theorem getD_inj'' {l : List Nat} (hl : l.Nodup) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (heq : l.getD i 0 = l.getD j 0) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotin, htail⟩ := hl
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ m =>
        have hm : m < xs.length := by simpa using hj
        have hmem : xs.getD m 0 ∈ xs := getD_mem'' xs m hm
        have heq2 : x = xs.getD m 0 := heq
        rw [heq2] at hmem
        exact absurd hmem hnotin
    | succ n =>
      cases j with
      | zero =>
        have hn : n < xs.length := by simpa using hi
        have hmem : xs.getD n 0 ∈ xs := getD_mem'' xs n hn
        have heq2 : xs.getD n 0 = x := heq
        rw [heq2] at hmem
        exact absurd hmem hnotin
      | succ m =>
        have hn : n < xs.length := by simpa using hi
        have hm : m < xs.length := by simpa using hj
        have heq2 : xs.getD n 0 = xs.getD m 0 := heq
        have hnm : n = m := ih htail hn hm heq2
        rw [hnm]

theorem mem_iff_getElem'' (l : List Nat) (a : Nat) :
    a ∈ l ↔ ∃ i (_ : i < l.length), l[i] = a := by
  constructor
  · intro h
    induction l with
    | nil => simp at h
    | cons x xs ih =>
      simp at h
      cases h with
      | inl heq =>
        subst heq
        exact ⟨0, by simp, rfl⟩
      | inr hmem =>
        obtain ⟨i, hi, heq⟩ := ih hmem
        exact ⟨i + 1, by simpa, by simpa [heq]⟩
  · intro h
    obtain ⟨i, hi, heq⟩ := h
    rw [heq]
    exact List.getElem_mem hi

theorem shareOf_none' {r : Request} {a : AccountId} (h : a ∉ r.recipients) : shareOf r a = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]

/-! sum of floors over indices -/

theorem sumFinNat_floor_eq' (ws : List Nat) (amount W : Nat) :
    sumFinNat ws.length (fun i => floorShare amount W (ws.getD i 0)) = natSum (ws.map (floorShare amount W)) := by
  induction ws with
  | nil => simp [sumFinNat, natSum]
  | cons x xs ih =>
    have hlen : (x :: xs).length = Nat.succ xs.length := rfl
    rw [hlen]
    rw [sumFinNat_head]
    simp only [List.map_cons, natSum]
    have h0 : (x :: xs).getD 0 0 = x := rfl
    rw [h0]
    have htail : sumFinNat xs.length (fun i => floorShare amount W ((x :: xs).getD (i + 1) 0))
        = sumFinNat xs.length (fun i => floorShare amount W (xs.getD i 0)) := by
      apply sumFinNat_congr
      intro i _
      rfl
    rw [htail, ih]

theorem sumFinNat_weighted_eq (ws : List Nat) (amount : Nat) :
    sumFinNat ws.length (fun i => weightedShare amount ws i)
      = natSum (ws.map (floorShare amount (natSum ws))) + Nat.min (leftover amount ws) ws.length := by
  have h1 : (fun i => weightedShare amount ws i)
      = (fun i => floorShare amount (natSum ws) (ws.getD i 0) + (if i < leftover amount ws then 1 else 0)) := by
    funext i
    unfold weightedShare
    rfl
  rw [h1]
  rw [sumFinNat_add]
  rw [sumFinNat_floor_eq']
  rw [sumFinNat_indic]

theorem sumFinNat_weighted_eq_amount {s : State} {r : Request} (h : ValidPayout s r) :
    sumFinNat r.recipients.length (fun i => weightedShare r.amount r.weights i) = r.amount := by
  have hlen : r.weights.length = r.recipients.length := (by obtain ⟨_, _, _, hl, _, _, _, _, _, _, _, _⟩ := h; exact hl)
  have hSle := valid_S_le' h
  have hLle := valid_leftover_le_len' h
  have heq := sumFinNat_weighted_eq r.weights r.amount
  rw [hlen] at heq
  -- rewrite lhs length: recipients.length = weights.length
  have hlhs : sumFinNat r.recipients.length (fun i => weightedShare r.amount r.weights i)
      = sumFinNat r.weights.length (fun i => weightedShare r.amount r.weights i) := by
    rw [hlen]
  rw [hlhs, heq]
  have hmin : Nat.min (leftover r.amount r.weights) r.weights.length = leftover r.amount r.weights := by
    omega
  rw [hmin]
  unfold leftover
  omega

/-! share as fin sum -/

theorem shareOf_eq_finsum (r : Request) (hnd : r.recipients.Nodup) (a : AccountId) :
    shareOf r a
      = sumFinNat r.recipients.length
          (fun i => if r.recipients.getD i 0 = a then weightedShare r.amount r.weights i else 0) := by
  by_cases ha : a ∈ r.recipients
  · obtain ⟨i0, hi0, heq0⟩ := (mem_iff_getElem'' r.recipients a).mp ha
    have hidx : indexOf? r.recipients a = some i0 := by
      have h1 : r.recipients[i0] = a := heq0.symm
      -- indexOf of getElem
      have h2 : indexOf? r.recipients r.recipients[i0] = some i0 :=
        indexOf?_getElem hnd i0 hi0
      rw [h1] at h2
      exact h2
    have hshare : shareOf r a = weightedShare r.amount r.weights i0 := by
      unfold shareOf
      rw [hidx]
    rw [hshare]
    have hg0 : r.recipients.getD i0 0 = a := by
      rw [getD_eq_getElem'' _ _ hi0, heq0]
    -- each term equals if i = i0 then ... else 0 with constant
    have hterm : ∀ i, i < r.recipients.length →
        ((if r.recipients.getD i 0 = a then weightedShare r.amount r.weights i else 0)
          = (if i = i0 then weightedShare r.amount r.weights i0 else 0)) := by
      intro i hi
      by_cases hii : i = i0
      · subst hii
        simp [hg0]
      · have hne : r.recipients.getD i 0 ≠ a := by
          intro hc
          have := getD_inj'' hnd hi hi0 (hc.trans hg0.symm)
          exact hii this
        simp [hne, hii]
    have hcongr := sumFinNat_congr r.recipients.length _ _ (fun i hi => hterm i hi)
    rw [hcongr]
    rw [sumFinNat_ite_const]
    simp [hi0]
  · have hshare : shareOf r a = 0 := shareOf_none' ha
    rw [hshare]
    have hzero : ∀ i, i < r.recipients.length →
        (if r.recipients.getD i 0 = a then weightedShare r.amount r.weights i else 0) = 0 := by
      intro i hi
      have hmem : r.recipients.getD i 0 ∈ r.recipients := getD_mem'' _ _ hi
      have hne : r.recipients.getD i 0 ≠ a := fun hc => ha (hc ▸ hmem)
      simp [hne]
    have hcongr := sumFinNat_congr r.recipients.length _ _ (fun i hi => by rw [hzero i hi]; rfl)
    rw [hcongr]
    exact sumFinNat_zero _

theorem sumOver_natCast {α : Type} (l : List α) (f : α → Nat) :
    sumOver l (fun a => ((f a : Nat) : Int)) = ((natSum (l.map f) : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [natSum, sumOver_cons, ih]; omega

theorem sumOver_swap (l : List AccountId) (n : Nat) (g : AccountId → Nat → Int) :
    sumOver l (fun a => sumFinInt n (fun i => g a i))
      = sumFinInt n (fun i => sumOver l (fun a => g a i)) := by
  induction l with
  | nil =>
    simp [sumOver_nil]
    exact (sumFinInt_zero n).symm
  | cons x xs ih =>
    simp only [sumOver_cons]
    rw [ih]
    rw [sumFinInt_add]
    apply congrArg₂ (· + ·)
    · apply sumFinInt_congr
      intro i _
      rfl
    · rfl

theorem sumOver_share_eq {s : State} {r : Request} (h : ValidPayout s r) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))
      = ((sumFinNat r.recipients.length (fun i => weightedShare r.amount r.weights i) : Nat) : Int) := by
  obtain ⟨hnodup_acc, _, _, hlen, _, hnodup_rec, _, _, hmem_sub, _, _, _⟩ := h
  have hrewrite : ∀ a : AccountId,
      ((shareOf r a : Nat) : Int)
        = sumFinInt r.recipients.length
            (fun i => if r.recipients.getD i 0 = a then ((weightedShare r.amount r.weights i : Nat) : Int) else 0) := by
    intro a
    rw [shareOf_eq_finsum r hnodup_rec a]
    rw [sumFinNat_cast]
    apply sumFinInt_congr
    intro i _
    by_cases hh : r.recipients.getD i 0 = a
    · simp [hh]
    · simp [hh]
  have h1 : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))
      = sumOver s.accounts (fun a => sumFinInt r.recipients.length
          (fun i => if r.recipients.getD i 0 = a then ((weightedShare r.amount r.weights i : Nat) : Int) else 0)) := by
    apply sumOver_congr
    intro a _
    exact hrewrite a
  rw [h1]
  rw [sumOver_swap]
  have hinner : ∀ i, i < r.recipients.length →
      sumOver s.accounts (fun a => if r.recipients.getD i 0 = a then ((weightedShare r.amount r.weights i : Nat) : Int) else 0)
        = ((weightedShare r.amount r.weights i : Nat) : Int) := by
    intro i hi
    have hfun_eq : (fun a => (if r.recipients.getD i 0 = a then ((weightedShare r.amount r.weights i : Nat) : Int) else 0))
        = (fun a => (if a = r.recipients.getD i 0 then ((weightedShare r.amount r.weights i : Nat) : Int) else 0)) := by
      funext a
      by_cases hh : r.recipients.getD i 0 = a
      · simp [hh, Eq.symm hh]
      · simp [hh, fun h2 => hh h2.symm]
    rw [hfun_eq]
    rw [sumOver_ite_eq hnodup_acc]
    have hmem_get : r.recipients.getD i 0 ∈ s.accounts := by
      have hmem_rec : r.recipients.getD i 0 ∈ r.recipients := getD_mem'' _ _ (by omega)
      exact hmem_sub _ hmem_rec
    simp [hmem_get]
  have h2 : (fun i => sumOver s.accounts (fun a => if r.recipients.getD i 0 = a then ((weightedShare r.amount r.weights i : Nat) : Int) else 0))
      = (fun i => ((weightedShare r.amount r.weights i : Nat) : Int)) := by
    funext i
    by_cases hi : i < r.recipients.length
    · exact hinner i hi
    · -- outside range, both sides? LHS sumOver of indicator where getD i = 0 default; still equals? Actually need equality only on range for sumFinInt_congr.
      -- we use congr instead
      rfl
  -- use congr to replace inside sumFinInt
  have hcongr : sumFinInt r.recipients.length
      (fun i => sumOver s.accounts (fun a => if r.recipients.getD i 0 = a then ((weightedShare r.amount r.weights i : Nat) : Int) else 0))
      = sumFinInt r.recipients.length (fun i => ((weightedShare r.amount r.weights i : Nat) : Int)) := by
    apply sumFinInt_congr
    intro i hi
    exact hinner i hi
  rw [hcongr]
  rw [← sumFinNat_cast]

theorem sumOver_source_indicator (s : State) (r : Request) (hsrc : r.source ∈ s.accounts) :
    sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
  have h := sumOver_ite_eq (l := s.accounts) (x := r.source) (c := (r.amount : Int)) (by
    -- Nodup of accounts? need it; derive from? Actually sumOver_ite_eq needs Nodup. Caller must supply.
    sorry)
  sorry

/-! required theorems -/

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  show (step s r).1 = Outcome.ok
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  show step s r = (Outcome.rejected, s)
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  have hV := ok_valid h
  obtain ⟨_, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hV
  exact hauth

theorem req_effects : Effects step := by
  intro s r h
  have hV := ok_valid h
  have heq := step_ok_eq hV
  constructor
  · show (step s r).2.accounts = s.accounts
    rw [heq]
    rfl
  constructor
  · show (step s r).2.auth = s.auth
    rw [heq]
    rfl
  · intro a
    show (step s r).2.balance a = expectedBalance s r a
    rw [heq]
    rfl

theorem req_idempotency : Idempotent step := by
  intro s r h
  have hV := ok_valid h
  have heq := step_ok_eq hV
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfresh⟩ := hV
  have happ : (step s r).2.applied = r.txId :: s.applied := by
    rw [heq]
    rfl
  constructor
  · intro x
    rw [happ]
    simp
  · have hNot : ¬ ValidPayout (step s r).2 r := by
      intro hc
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfresh2⟩ := hc
      rw [happ] at hfresh2
      simp at hfresh2
    have hrej := step_rej_eq hNot
    have h2eq : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
      rw [heq]
      rfl
    show step (step s r).2 r = (Outcome.rejected, (step s r).2)
    rw [h2eq] at hrej ⊢
    exact hrej

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hV : ValidPayout s r
  · have heq := step_ok_eq hV
    have hbal : (step s r).2.balance a = expectedBalance s r a := by
      rw [heq]
      rfl
    rw [hbal]
    have hacc_eq : (step s r).2.accounts = s.accounts := by
      rw [heq]
      rfl
    have ha_mem : a ∈ s.accounts := by
      have hmem : a ∈ (step s r).2.accounts := ha
      rw [hacc_eq] at hmem
      exact hmem
    have hbal_nn : 0 ≤ s.balance a := hnn a ha_mem
    obtain ⟨_, _, _, _, _, _, hsrc_not, _, _, _, _, _⟩ := hV
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hnone : indexOf? r.recipients a = none := indexOf?_eq_none hsrc_not
      unfold shareOf
      rw [hnone]
      simp
      omega
    · simp [hsrc]
      omega
  · have heq := step_rej_eq hV
    have h2eq : (step s r).2 = s := by
      rw [heq]
      rfl
    rw [h2eq] at ha ⊢
    exact hnn a ha

theorem req_pro_rata : ProRataShares step := by
  intro s r h i hi
  have hV := ok_valid h
  have heq := step_ok_eq hV
  obtain ⟨_, _, _, _, _, hnodup_rec, hsrc_not, _, hmem, _, _, _⟩ := hV
  have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
    rw [heq]
    rfl
  rw [hbal]
  unfold expectedBalance
  have hmem_i : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne_src : ¬ (r.recipients[i] = r.source) := by
    intro hc
    rw [hc] at hmem_i
    exact hsrc_not hmem_i
  simp [hne_src]
  have hidx : indexOf? r.recipients r.recipients[i] = some i :=
    indexOf?_getElem hnodup_rec i hi
  unfold shareOf
  rw [hidx]
  omega

theorem req_rounding_bound : RoundingBound step := by
  intro s r h i hi
  have hV := ok_valid h
  have hdiff : (step s r).2.balance r.recipients[i] - s.balance r.recipients[i]
      = ((weightedShare r.amount r.weights i : Nat) : Int) := req_pro_rata s r h i hi
  rw [hdiff]
  have hVcopy := hV
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := hVcopy
  have hw : 0 < natSum r.weights := valid_W_pos' hV
  have hdiv_le : floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights
      ≤ r.amount * r.weights.getD i 0 := by
    unfold floorShare
    exact div_mul_le_self' (r.amount * r.weights.getD i 0) (natSum r.weights)
  have hdiv_lt : r.amount * r.weights.getD i 0
      < (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights :=
    floor_lt_succW r.amount (natSum r.weights) (r.weights.getD i 0) hw
  have hfloor_eq : floorShare r.amount (natSum r.weights) (r.weights.getD i 0)
      = floorShare r.amount (natSum r.weights) (r.weights.getD i 0) := rfl
  unfold weightedShare
  by_cases hc : i < leftover r.amount r.weights
  · simp [hc]
    have hNat1 : (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights
        ≤ r.amount * r.weights.getD i 0 + natSum r.weights := by omega
    have hNat2 : r.amount * r.weights.getD i 0
        < (floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1) * natSum r.weights + natSum r.weights := by omega
    have g1 : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1 : Nat) : Int)) * ((natSum r.weights : Nat) : Int)
        ≤ ((r.amount * r.weights.getD i 0 : Nat) : Int) + ((natSum r.weights : Nat) : Int)) := by
      have hh := Int.ofNat_le.mpr hNat1
      simpa [Nat.cast_add, Nat.cast_mul] using hh
    have g2 : (((r.amount * r.weights.getD i 0 : Nat) : Int)
        < ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) + 1 : Nat) : Int)) * ((natSum r.weights : Nat) : Int) + ((natSum r.weights : Nat) : Int))) := by
      have hh := Int.ofNat_lt.mpr hNat2
      simpa [Nat.cast_add, Nat.cast_mul] using hh
    exact ⟨g1, g2⟩
  · simp [hc]
    have hNat1 : floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights
        ≤ r.amount * r.weights.getD i 0 + natSum r.weights := by omega
    have hNat2 : r.amount * r.weights.getD i 0
        < floorShare r.amount (natSum r.weights) (r.weights.getD i 0) * natSum r.weights + natSum r.weights := by omega
    have g1 : ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) : Nat) : Int)) * ((natSum r.weights : Nat) : Int)
        ≤ ((r.amount * r.weights.getD i 0 : Nat) : Int) + ((natSum r.weights : Nat) : Int)) := by
      have hh := Int.ofNat_le.mpr hNat1
      simpa [Nat.cast_add, Nat.cast_mul] using hh
    have g2 : (((r.amount * r.weights.getD i 0 : Nat) : Int)
        < ((((floorShare r.amount (natSum r.weights) (r.weights.getD i 0) : Nat) : Int)) * ((natSum r.weights : Nat) : Int) + ((natSum r.weights : Nat) : Int))) := by
      have hh := Int.ofNat_lt.mpr hNat2
      simpa [Nat.cast_add, Nat.cast_mul] using hh
    exact ⟨g1, g2⟩

theorem req_conservation : Conserves step := by
  intro s r h
  have hV := ok_valid h
  have heq := step_ok_eq hV
  obtain ⟨hnodup_acc, _, _, _, _, _, hsrc_not, hsrc_mem, hmem_sub, _, hle_bal, _⟩ := hV
  have hVfull : ValidPayout s r := hV
  show total (step s r).2 = total s
  rw [heq]
  simp only [total]
  -- balance of new state
  have hbal_eq : (fun a => expectedBalance s r a) = (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)) := by
    funext a
    unfold expectedBalance
    rfl
  -- sum decomposition
  have hsum1 : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance
        - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0))
        + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
    have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) := by
      rw [← sumOver_sub]
      apply sumOver_congr
      intro a _
      rfl
    have hadd : sumOver s.accounts (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)))
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
      rw [← sumOver_add]
      apply sumOver_congr
      intro a _
      rfl
    have hexp : (fun a => expectedBalance s r a)
        = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int))) := by
      funext a
      unfold expectedBalance
      rfl
    rw [hexp, hadd, hsub]
  rw [hsum1]
  have hsrc_sum : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup_acc r.source (r.amount : Int)
    simpa [hsrc_mem] using h
  have hshare_sum : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
    rw [sumOver_share_eq hVfull]
    rw [sumFinNat_weighted_eq_amount hVfull]
  rw [hsrc_sum, hshare_sum]
  omega

end WeightedPayout
