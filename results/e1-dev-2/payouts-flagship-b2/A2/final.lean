import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem sumOver_append (l1 l2 : List Nat) (f : Nat → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem tmp_check_div : ∀ (m n : Nat), 0 < n → n * (m / n) + m % n = m := fun m n _ => Nat.div_add_mod m n

theorem tmp_probe3 : True := trivial
#check Int.mul_add
#check Int.add_mul
#check Int.mul_comm
#check Int.mul_assoc

theorem tmp_probe4 : True := trivial
#check @Int.mul_add
#check @Int.add_mul
#check @Int.mul_comm
#check @Int.add_zero
#check @Int.zero_add

theorem tmp_distrib (n : Int) (c : Int) : n * c + c = (n + 1) * c := by
  have h : (n + 1) * c = n * c + 1 * c := Int.add_mul n 1 c
  rw [h]
  rw [Int.one_mul c]

theorem tmp_probe6 (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  simp
#check Nat.succ

theorem probe_idem (s : State) (r : Request) (hv : ValidPayout s r) : (step s r).1 = .ok := by simp [step, hv]

theorem req_idempotency_aux3 : Idempotent step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      simp [step, hv]
    have heq2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      rw [hstep]
    have happlied : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
      intro x
      rw [heq2]
      simp
    have hNotValid2 : ¬ ValidPayout ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
      intro hval
      obtain ⟨_, _, _, _, _, _, _, _, _, hfresh⟩ := hval
      apply hfresh
      simp
    have hrej2 : step ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r = (.rejected, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      simp [step, hNotValid2]
    have hrej : step (step s r).2 r = (.rejected, (step s r).2) := by rw [heq2, hrej2]
    exact ⟨happlied, hrej⟩
  · have heq : (step s r).1 = Outcome.rejected := by simp [step, hv]
    rw [heq] at hok
    exact absurd hok (by decide)

theorem tmp_range_succ (m : Nat) (f : Nat → Int) :
    sumOver (List.range (m+1)) f = sumOver (List.range m) f + f m := by
  have h : List.range (m+1) = List.range m ++ [m] := by simp [List.range_succ]
  rw [h, sumOver_append]
  simp

theorem tmp_sum_const2 (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [tmp_range_succ, ih]
    have hcast : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]

theorem tmp_ite_range (r n : Nat) :
    sumOver (List.range n) (fun i => if i < r then (1 : Int) else 0) = ((Nat.min r n : Nat) : Int) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [tmp_range_succ, ih]
    by_cases h : m < r
    · have h1 : Nat.min r m = m := Nat.min_eq_right (Nat.le_of_lt h)
      have h2 : Nat.min r (m + 1) = m + 1 := Nat.min_eq_right (Nat.succ_le_of_lt h)
      rw [h1, h2]
      simp [h]
    · have h1 : Nat.min r m = r := Nat.min_eq_left (Nat.le_of_not_lt h)
      have h2 : Nat.min r (m + 1) = r := Nat.min_eq_left (by omega)
      rw [h1, h2]
      simp [h]

theorem tmp_fair_cast (amount n i : Nat) :
    ((fairShare amount n i : Nat) : Int) = ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) := by
  unfold fairShare
  by_cases h : i < amount % n <;> simp [h]

theorem tmp_nat_cast_add2 (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem tmp_sum_fair2 (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int)) = (amount : Int) := by
  have h1 : ∀ i ∈ List.range n, ((fairShare amount n i : Nat) : Int)
      = ((amount / n : Nat) : Int) + (if i < amount % n then (1 : Int) else 0) :=
    fun i _ => tmp_fair_cast amount n i
  rw [sumOver_congr _ _ _ h1, sumOver_add]
  rw [tmp_sum_const2 n ((amount / n : Nat) : Int)]
  rw [tmp_ite_range]
  have hmod : amount % n < n := Nat.mod_lt _ hn
  have hmin : Nat.min (amount % n) n = amount % n := Nat.min_eq_left (Nat.le_of_lt hmod)
  rw [hmin]
  have hdiv : n * (amount / n) + amount % n = amount := Nat.div_add_mod amount n
  have e1 : ((n * (amount / n) + amount % n : Nat) : Int)
      = (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by
    simp
  have hcast : ((n * (amount / n) + amount % n : Nat) : Int) = (amount : Int) := by
    rw [hdiv]
  have heq : (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) = (amount : Int) := by
    rw [← e1, hcast]
  exact heq

theorem tmp_sum_map (l : List Nat) (g : Nat → Nat) (F : Nat → Int) :
    sumOver (List.map g l) F = sumOver l (fun x => F (g x)) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]



theorem plan0_sumOver_eq_of_subset_trivial : True := trivial








theorem plan0_removed_placeholder : True := trivial


theorem probe_beq (x a : Nat) (h : x ≠ a) : (x == a) = false :=
  beq_eq_false_iff_ne.mpr h

theorem probe_beq2 (x a : Nat) (h : x ≠ a) : decide (x = a) = false :=
  decide_eq_false h







theorem plan1_sumOver_erase_add_final (l : List AccountId) (f : AccountId → Int)
    (a : AccountId) (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (List.erase l a) f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    simp only [List.mem_cons] at ha
    simp only [sumOver_cons]
    by_cases hxa : x = a
    · rw [hxa]
      simp
    · have hne : (x == a) = false := beq_eq_false_iff_ne.mpr hxa
      have her : List.erase (x :: xs) a = x :: List.erase xs a := by simp [hne]
      rw [her]
      simp only [sumOver_cons]
      have ha_xs : a ∈ xs := by
        cases ha with
        | inl heq => exact absurd heq.symm hxa
        | inr hm => exact hm
      have ih_eq := ih hl.2 ha_xs
      omega


theorem plan1_exists_split_of_mem (l : List AccountId) (a : AccountId) (ha : a ∈ l) :
    ∃ l1 l2 : List AccountId, l = l1 ++ a :: l2 ∧ a ∉ l1 := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases h : x = a
    · subst h
      exact ⟨[], xs, rfl, by simp⟩
    · have hmem : a = x ∨ a ∈ xs := List.mem_cons.mp ha
      have ha' : a ∈ xs := by
        cases hmem with
        | inl heq => exact absurd heq.symm h
        | inr hm => exact hm
      obtain ⟨l1, l2, heq, hnotin⟩ := ih ha'
      refine ⟨x :: l1, l2, ?_, ?_⟩
      · simp [heq]
      · simp only [List.mem_cons, not_or]
        exact ⟨Ne.symm h, hnotin⟩

theorem plan1_erase_append_cons (l1 l2 : List AccountId) (a : AccountId)
    (h : a ∉ l1) :
    List.erase (l1 ++ a :: l2) a = l1 ++ l2 := by
  induction l1 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at h
    have hxa : (x == a) = false := beq_eq_false_iff_ne.mpr (fun heq => h.1 heq.symm)
    simp [hxa, ih h.2]

theorem plan1_sumOver_append_cons (l1 l2 : List AccountId) (a : AccountId)
    (f : AccountId → Int) :
    sumOver (l1 ++ a :: l2) f = f a + (sumOver l1 f + sumOver l2 f) := by
  have h : l1 ++ a :: l2 = (l1 ++ [a]) ++ l2 := by simp
  rw [h, sumOver_append, sumOver_append]
  simp
  omega

theorem plan1_erase_pf2 (l : List AccountId) (f : AccountId → Int)
    (a : AccountId) (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (List.erase l a) f := by
  obtain ⟨l1, l2, heq, hnotin⟩ := plan1_exists_split_of_mem l a ha
  subst heq
  rw [plan1_erase_append_cons l1 l2 a hnotin]
  rw [plan1_sumOver_append_cons l1 l2 a f]
  rw [sumOver_append l1 l2 f]

theorem probe_erase1 (xs : List Nat) (a : Nat) : List.erase (a :: xs) a = xs := by simp

theorem probe_erase2 (x t : Nat) (xs : List Nat) (h : (x == t) = false) : List.erase (x :: xs) t = x :: List.erase xs t := by simp [h]

theorem plan1_erase_direct3 (l : List AccountId) (f : AccountId → Int)
    (t : AccountId) : l.Nodup → t ∈ l →
    sumOver l f = f t + sumOver (List.erase l t) f := by
  induction l with
  | nil => intro _ ha; simp at ha
  | cons x xs ih =>
    intro hl ha
    rw [List.nodup_cons] at hl
    simp only [List.mem_cons] at ha
    simp only [sumOver_cons]
    by_cases hxa : x = t
    · subst hxa
      simp
    · have hne : (x == t) = false := beq_eq_false_iff_ne.mpr hxa
      have her : List.erase (x :: xs) t = x :: List.erase xs t := by simp [hne]
      rw [her]
      simp only [sumOver_cons]
      have ha_xs : t ∈ xs := by
        cases ha with
        | inl heq => exact absurd heq.symm hxa
        | inr hm => exact hm
      have ih_eq := ih hl.2 ha_xs
      omega

theorem plan0_sumOver_erase_add (l : List AccountId) (f : AccountId → Int)
    (a : AccountId) (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (List.erase l a) f := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    simp only [List.mem_cons] at ha
    simp only [sumOver_cons]
    by_cases hxa : x = a
    · subst hxa
      simp
    · have hne : (x == a) = false := beq_eq_false_iff_ne.mpr hxa
      have her : List.erase (x :: xs) a = x :: List.erase xs a := by simp [hne]
      rw [her]
      simp only [sumOver_cons]
      have ha_xs : a ∈ xs := by
        cases ha with
        | inl heq => exact absurd heq.symm hxa
        | inr hm => exact hm
      have ih_eq := ih hl.2 ha_xs
      omega

theorem tmp_probe_beq2 : True := trivial

theorem tmp_beq_true_of_eq (x a : Nat) (h : x = a) : (x == a) = true := by
  subst h
  simp

theorem tmp_beq_false_of_ne (x a : Nat) (h : x ≠ a) : (x == a) = false :=
  beq_eq_false_iff_ne.mpr h

theorem tmp_probe_list_api : True := trivial



theorem plan2_mem_of_mem_erase_deleted : True := trivial








theorem plan2_sumOver_eq_zero_of_forall_zero (l : List AccountId) (f : AccountId → Int)
    (h : ∀ x ∈ l, f x = 0) : sumOver l f = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [sumOver_cons]
    have hx : f x = 0 := h x (by simp)
    have ih' : sumOver xs f = 0 := ih (fun y hy => h y (by simp [hy]))
    simp [hx, ih']

def tmp_erase_ex : List Nat := List.erase [1,1] 1
#check tmp_erase_ex

theorem tmp_erase_eval : List.erase [1,1] (1:Nat) = [1] := by rfl

theorem tmp_erase_eval2 : List.erase [1,2,1] (1:Nat) = [2,1] := by rfl

theorem tmp_mem_erase_mem_true (l : List AccountId) (a x : AccountId)
    (h : x ∈ List.erase l a) : x ∈ l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    by_cases hya : y = a
    · subst hya
      simp at h ⊢
      exact Or.inr h
    · have hne_beq : (y == a) = false := beq_eq_false_iff_ne.mpr hya
      have her : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hne_beq]
      rw [her] at h
      simp only [List.mem_cons] at h ⊢
      cases h with
      | inl heq => exact Or.inl heq
      | inr hm => exact Or.inr (ih hm)

theorem tmp_nodup_erase2 (l : List AccountId) (a : AccountId)
    (h : l.Nodup) : (List.erase l a).Nodup := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    by_cases hya : y = a
    · subst hya
      simp
      rw [List.nodup_cons] at h
      exact h.2
    · have hne_beq : (y == a) = false := beq_eq_false_iff_ne.mpr hya
      have her : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hne_beq]
      rw [her]
      rw [List.nodup_cons] at h ⊢
      constructor
      · intro hmem
        have hmem2 := tmp_mem_erase_mem_true ys a y hmem
        exact h.1 hmem2
      · exact ih h.2

theorem tmp_mem_erase_ne_of_nodup (l : List AccountId) (a x : AccountId)
    (hL : l.Nodup) (h : x ∈ List.erase l a) : x ≠ a := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨hynot, hNodup⟩ := hL
    by_cases hya : y = a
    · subst hya
      simp at h
      intro heq
      subst heq
      exact hynot h
    · have hne_beq : (y == a) = false := beq_eq_false_iff_ne.mpr hya
      have her : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hne_beq]
      rw [her] at h
      simp only [List.mem_cons] at h
      cases h with
      | inl heq => subst heq; exact hya
      | inr hm => exact ih hNodup hm

theorem tmp_mem_erase_of_ne_test (l : List AccountId) (a x : AccountId)
    (hx : x ∈ l) (h : x ≠ a) : x ∈ List.erase l a := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    by_cases hya : y = a
    · subst hya
      simp
      cases hx with
      | inl heq => exact absurd heq h
      | inr hm => exact hm
    · have hne_beq : (y == a) = false := beq_eq_false_iff_ne.mpr hya
      have her : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hne_beq]
      rw [her]
      simp only [List.mem_cons]
      cases hx with
      | inl heq => exact Or.inl heq
      | inr hm => exact Or.inr (ih hm)

theorem plan2_mem_erase_of_mem_of_ne (l : List AccountId) (a x : AccountId)
    (hx : x ∈ l) (h : x ≠ a) : x ∈ List.erase l a := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    by_cases hya : y = a
    · subst hya
      simp
      cases hx with
      | inl heq => exact absurd heq h
      | inr hm => exact hm
    · have hne_beq : (y == a) = false := beq_eq_false_iff_ne.mpr hya
      have her : List.erase (y :: ys) a = y :: List.erase ys a := by simp [hne_beq]
      rw [her]
      simp only [List.mem_cons]
      cases hx with
      | inl heq => exact Or.inl heq
      | inr hm => exact Or.inr (ih hm)

theorem plan2_nodup_erase (l : List AccountId) (a : AccountId)
    (h : l.Nodup) : (List.erase l a).Nodup := tmp_nodup_erase2 l a h

theorem plan2_erase_subset_step_fixed (L R : List AccountId) (a : AccountId) (f : AccountId → Int)
    (hL : L.Nodup)
    (haR : a ∉ R) (hsub : ∀ x ∈ a :: R, x ∈ L)
    (hvan : ∀ x ∈ L, x ∉ a :: R → f x = 0) :
    (∀ x ∈ R, x ∈ List.erase L a) ∧
      (∀ x ∈ List.erase L a, x ∉ R → f x = 0) := by
  constructor
  · intro x hx
    have hxL : x ∈ L := hsub x (by simp [hx])
    have hne : x ≠ a := by
      intro heq
      subst heq
      exact haR hx
    exact plan2_mem_erase_of_mem_of_ne L a x hxL hne
  · intro x hxmem hxR
    have hxL : x ∈ L := tmp_mem_erase_mem_true L a x hxmem
    have hne : x ≠ a := tmp_mem_erase_ne_of_nodup L a x hL hxmem
    have hxNot : x ∉ a :: R := by
      simp only [List.mem_cons, not_or]
      exact ⟨hne, hxR⟩
    exact hvan x hxL hxNot

theorem plan2_erase_subset_step_deleted : True := trivial


theorem plan2_erase_subset_step_newproof : True := trivial

theorem plan2_mem_of_mem_erase_nodup (l : List AccountId) (a x : AccountId)
    (hL : l.Nodup) (h : x ∈ List.erase l a) : x ∈ l ∧ x ≠ a :=
  ⟨tmp_mem_erase_mem_true l a x h, tmp_mem_erase_ne_of_nodup l a x hL h⟩

theorem plan0_sumOver_range_fair_proof (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int))
      = (amount : Int) := tmp_sum_fair2 amount n hn

theorem plan0_sumOver_range_succ_proof (g : Nat → Int) (n : Nat) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 : sumOver (List.range (m + 1 + 1)) g
        = sumOver (List.range (m + 1)) g + g (m + 1) := tmp_range_succ (m+1) g
    have h2 : sumOver (List.range (m + 1)) (fun i => g (i + 1))
        = sumOver (List.range m) (fun i => g (i + 1)) + g (m + 1) := by
      have := tmp_range_succ m (fun i => g (i + 1))
      simpa using this
    rw [h1, ih, h2]
    omega

theorem plan0_sumOver_eq_of_subset_new (L : List AccountId) (hL : L.Nodup) :
    ∀ (R : List AccountId), R.Nodup → (∀ x ∈ R, x ∈ L) →
      ∀ f : AccountId → Int, (∀ x ∈ L, x ∉ R → f x = 0) →
        sumOver L f = sumOver R f := by
  intro R
  induction R generalizing L with
  | nil =>
    intro _ _ f hvan
    simp only [sumOver_nil]
    have hz : sumOver L f = 0 := by
      apply plan2_sumOver_eq_zero_of_forall_zero
      intro x hx
      exact hvan x hx (by simp)
    exact hz
  | cons a R ih =>
    intro hR hsub f hvan
    rw [List.nodup_cons] at hR
    obtain ⟨haR, hRnodup⟩ := hR
    have haL : a ∈ L := hsub a (by simp)
    have herase : sumOver L f = f a + sumOver (List.erase L a) f :=
      plan0_sumOver_erase_add L f a hL haL
    have hcons : sumOver (a :: R) f = f a + sumOver R f := rfl
    rw [herase, hcons]
    congr 1
    have hL' : (List.erase L a).Nodup := plan2_nodup_erase L a hL
    have hpair := plan2_erase_subset_step_fixed L R a f hL haR
      (fun x hx => hsub x hx)
      (fun x hx hxNot => hvan x hx hxNot)
    obtain ⟨hsub', hvan'⟩ := hpair
    exact ih (List.erase L a) hL' hRnodup hsub' f hvan'

theorem plan0_sumOver_eq_of_subset (L : List AccountId) (hL : L.Nodup) :
    ∀ (R : List AccountId), R.Nodup → (∀ x ∈ R, x ∈ L) →
      ∀ f : AccountId → Int, (∀ x ∈ L, x ∉ R → f x = 0) →
        sumOver L f = sumOver R f :=
  fun R hR hsub f hvan => plan0_sumOver_eq_of_subset_new L hL R hR hsub f hvan

theorem plan0_sumOver_range_succ (g : Nat → Int) (n : Nat) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) :=
  plan0_sumOver_range_succ_proof g n

theorem plan0_sumOver_range_fair (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int))
      = (amount : Int) := tmp_sum_fair2 amount n hn

theorem plan0_sumOver_indexOf_eq_range_aux (l : List AccountId) (hl : l.Nodup) :
    ∀ g : Nat → Int,
      sumOver l (fun a => match indexOf? l a with
        | some i => g i
        | none => 0)
      = sumOver (List.range l.length) g := by
  induction l with
  | nil =>
    intro g
    simp
  | cons x xs ih =>
    intro g
    rw [List.nodup_cons] at hl
    obtain ⟨hx_not, hx_nodup⟩ := hl
    have ih_shift : sumOver xs (fun a => match indexOf? xs a with | some i => g (i+1) | none => 0)
        = sumOver (List.range xs.length) (fun i => g (i+1)) := ih hx_nodup _
    have h_head : (match indexOf? (x :: xs) x with | some i => g i | none => 0) = g 0 := by
      simp [indexOf?]
    have h_congr : ∀ a ∈ xs, (match indexOf? (x :: xs) a with | some i => g i | none => 0)
        = (match indexOf? xs a with | some i => g (i+1) | none => 0) := by
      intro a ha
      have hne : x ≠ a := fun heq => hx_not (heq ▸ ha)
      have hunfold : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
        simp [indexOf?, hne]
      rw [hunfold]
      cases h : indexOf? xs a
      case none => rfl
      case some i => rfl
    have h_sum_cons : sumOver (x :: xs) (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
        = (match indexOf? (x :: xs) x with | some i => g i | none => 0) + sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0) := rfl
    rw [h_sum_cons, h_head]
    have h_eq : sumOver xs (fun a => match indexOf? (x :: xs) a with | some i => g i | none => 0)
        = sumOver xs (fun a => match indexOf? xs a with | some i => g (i+1) | none => 0) :=
      sumOver_congr xs _ _ h_congr
    rw [h_eq, ih_shift]
    have h_range : sumOver (List.range (xs.length + 1)) g = g 0 + sumOver (List.range xs.length) (fun i => g (i + 1)) :=
      plan0_sumOver_range_succ_proof g xs.length
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen, h_range]

theorem check_order_tmp : True := trivial







theorem plan3_indexOf_cons_tail (x a : AccountId) (xs : List AccountId)
    (g : Nat → Int) (hne : x ≠ a) :
    (match indexOf? (x :: xs) a with
     | some i => g i
     | none => 0)
      = (match indexOf? xs a with
         | some i => g (i + 1)
         | none => 0) := by
  have hunfold : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
    simp [indexOf?, hne]
  rw [hunfold]
  cases h : indexOf? xs a with
  | none => simp
  | some i => simp


theorem plan3_sumOver_range_succ_last (n : Nat) (g : Nat → Int) :
    sumOver (List.range (n + 1)) g = sumOver (List.range n) g + g n :=
  tmp_range_succ n g

theorem plan3_head_test (n : Nat) (g : Nat → Int) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) :=
  plan0_sumOver_range_succ_proof g n

theorem plan3_head_check (n : Nat) (g : Nat → Int) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by
  exact plan0_sumOver_range_succ_proof g n

theorem plan3_sumOver_range_succ_head (n : Nat) (g : Nat → Int) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) :=
  plan0_sumOver_range_succ_proof g n

theorem plan3_indexOf_cons_head (x : AccountId) (xs : List AccountId) (g : Nat → Int) :
    (match indexOf? (x :: xs) x with
     | some i => g i
     | none => 0) = g 0 := by
  simp [indexOf?]

theorem plan0_sumOver_indexOf_eq_range (l : List AccountId) (hl : l.Nodup) :
    ∀ g : Nat → Int,
      sumOver l (fun a => match indexOf? l a with
        | some i => g i
        | none => 0)
      = sumOver (List.range l.length) g :=
  plan0_sumOver_indexOf_eq_range_aux l hl

theorem plan0_sumOver_expectedBalance_eq_proof (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance := by
  obtain ⟨hNodupAcc, hpos, hne, hRnodup, hsrcNot, hsrcIn, hmem, hauth, hle, hfresh⟩ := hv
  have hn : 0 < r.recipients.length := by
    cases h : r.recipients with
    | nil => exact False.elim (hne h)
    | cons x xs => simp
  -- debit sum
  have hdebit : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    have h := sumOver_ite_eq hNodupAcc r.source (r.amount : Int)
    rw [h]
    simp [hsrcIn]
  -- vanishing of credits outside recipients
  have hvan : ∀ x ∈ s.accounts, x ∉ r.recipients → ((shareOf r x : Nat) : Int) = 0 := by
    intro x _ hxNot
    unfold shareOf
    rw [indexOf?_eq_none hxNot]
    rfl
  -- restrict credit sum to recipients
  have hrestrict : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))
      = sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int)) := by
    apply plan0_sumOver_eq_of_subset s.accounts hNodupAcc r.recipients hRnodup _ _ _
    · intro x hx; exact hmem x hx
    · intro x hx hxNot; exact hvan x hx hxNot
  -- reindex recipient sum to range
  have gdef : ∀ a ∈ r.recipients, ((shareOf r a : Nat) : Int)
      = (match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => 0) := by
    intro a _
    unfold shareOf
    cases h : indexOf? r.recipients a with
    | none => rfl
    | some i => rfl
  have hcongrR : sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int))
      = sumOver r.recipients (fun a => match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => 0) :=
    sumOver_congr r.recipients _ _ gdef
  have hreindex : sumOver r.recipients (fun a => match indexOf? r.recipients a with | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int) | none => 0)
      = sumOver (List.range r.recipients.length) (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int)) :=
    plan0_sumOver_indexOf_eq_range r.recipients hRnodup _
  have hfair : sumOver (List.range r.recipients.length) (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int)) = (r.amount : Int) :=
    tmp_sum_fair2 r.amount r.recipients.length hn
  have hcredit : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
    rw [hrestrict, hcongrR, hreindex, hfair]
  -- decompose expectedBalance sum
  have hdecomp : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
    have h1 : ∀ a ∈ s.accounts, expectedBalance s r a
        = (s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)) := by
      intro a _
      unfold expectedBalance shareOf
      cases h : indexOf? r.recipients a with
      | none => rfl
      | some i => rfl
    rw [sumOver_congr s.accounts _ _ h1]
    have h2 : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int))
        = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + ((shareOf r a : Nat) : Int)) := by rfl
    rw [h2, sumOver_add]
    congr 1
    rw [sumOver_sub]
  rw [hdecomp, hdebit, hcredit]
  omega

theorem plan4_expectedBalance_sum_decomp (s : State) (r : Request) :
    sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance
        - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
  have h1 : ∀ a ∈ s.accounts, expectedBalance s r a
      = ((s.balance a - (if a = r.source then (r.amount : Int) else 0)) + ((shareOf r a : Nat) : Int)) := by
    intro a _
    rfl
  rw [sumOver_congr s.accounts _ _ h1]
  rw [sumOver_add]
  congr 1
  rw [sumOver_sub]




theorem plan4_shareOf_eq_zero_of_not_mem (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) :
    shareOf r a = 0 := by sorry

theorem plan4_credit_sum_eq_recipient_sum (s : State) (r : Request)
    (hAcc : s.accounts.Nodup) (hRec : r.recipients.Nodup)
    (hsub : ∀ x ∈ r.recipients, x ∈ s.accounts) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))
      = sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int)) := by sorry

theorem plan4_recipient_credit_sum_eq_range (r : Request) (hRec : r.recipients.Nodup) :
    sumOver r.recipients (fun a => ((shareOf r a : Nat) : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => ((fairShare r.amount r.recipients.length i : Nat) : Int)) := by sorry

theorem plan4_range_fair_sum_eq_amount (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int))
      = (amount : Int) := by sorry

theorem plan4_expectedBalance_sum_decomp_proof (s : State) (r : Request) :
    sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts s.balance
        - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
  have h1 : ∀ a ∈ s.accounts, expectedBalance s r a
      = ((s.balance a - (if a = r.source then (r.amount : Int) else 0)) + ((shareOf r a : Nat) : Int)) := by
    intro a _
    rfl
  rw [sumOver_congr s.accounts _ _ h1]
  rw [sumOver_add]
  congr 1
  rw [sumOver_sub]

theorem plan4_expectedBalance_sum_decomp_alt : sumOver ([] : List AccountId) (fun a => expectedBalance ⟨[], fun _ => 0, fun _ _ => false, []⟩ ⟨0,0,0,[],0⟩ a) = sumOver ([] : List AccountId) (fun _ => (0 : Int)) := by simp

theorem plan4_debit_sum_eq (s : State) (r : Request)
    (hNodup : s.accounts.Nodup) (hsrc : r.source ∈ s.accounts) :
    sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
  have h := sumOver_ite_eq hNodup r.source (r.amount : Int)
  rw [h, if_pos hsrc]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · have heq : (step s r).1 = Outcome.rejected := by simp [step, hv]
    rw [heq] at h
    exact absurd h (by decide)

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · simp [step, hv]
  · have heq : (step s r).1 = Outcome.rejected := by simp [step, hv]
    rw [heq] at h
    exact absurd h (by decide)

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hstep : step s r = (.ok, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      simp [step, hv]
    have heq2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := by
      rw [hstep]
    have happlied : ∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied := by
      intro x
      rw [heq2]
      simp
    have hNotValid2 : ¬ ValidPayout ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r := by
      intro hval
      obtain ⟨_, _, _, _, _, _, _, _, _, hfresh⟩ := hval
      apply hfresh
      simp
    have hrej2 : step ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) r = (.rejected, ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State)) := by
      simp [step, hNotValid2]
    have hrej : step (step s r).2 r = (.rejected, (step s r).2) := by rw [heq2, hrej2]
    exact ⟨happlied, hrej⟩
  · have heq : (step s r).1 = Outcome.rejected := by simp [step, hv]
    rw [heq] at hok
    exact absurd hok (by decide)

theorem req_nonnegative : NonNegative step := by
  intro s r hall a ha
  by_cases hv : ValidPayout s r
  · have hacc : (step s r).2.accounts = s.accounts := by simp [step, hv]
    have hbal : ∀ b, (step s r).2.balance b = expectedBalance s r b := by
      intro b; simp [step, hv]
    rw [hacc] at ha
    rw [hbal a]
    unfold expectedBalance
    obtain ⟨hnodup, hpos, hne, hrnodup, hsrcNot, hsrcIn, hmem, hauth, hle, hfresh⟩ := hv
    have h0 : 0 ≤ s.balance a := hall a ha
    by_cases heq : a = r.source
    · subst heq
      have hshare0 : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hsrcNot]
      rw [if_pos rfl, hshare0]
      omega
    · rw [if_neg heq]
      have hshare : (0 : Int) ≤ (shareOf r a : Int) := Int.ofNat_nonneg _
      omega
  · have hst : (step s r).2 = s := by simp [step, hv]
    rw [hst] at ha ⊢
    exact hall a ha

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  by_cases hv : ValidPayout s r
  · have hbal2 : ∀ b, (step s r).2.balance b = expectedBalance s r b := by
      intro b
      simp [step, hv]
    rw [hbal2]
    unfold expectedBalance shareOf
    obtain ⟨hnodup, hpos, hne, hrnodup, hsrcNot, hsrcIn, hmem, hauth, hle, hfresh⟩ := hv
    have hmem_i : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_src : r.recipients[i] ≠ r.source := fun heq => hsrcNot (heq ▸ hmem_i)
    have hidx : indexOf? r.recipients r.recipients[i] = some i :=
      indexOf?_getElem hrnodup i hi
    rw [hidx]
    simp only [hne_src, ↓reduceIte]
    omega
  · have heq : (step s r).1 = Outcome.rejected := by simp [step, hv]
    rw [heq] at hok
    exact absurd hok (by decide)

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hacc : (step s r).2.accounts = s.accounts := by simp [step, hv]
    have hbal : ∀ b, (step s r).2.balance b = expectedBalance s r b := by
      intro b; simp [step, hv]
    unfold total
    rw [hacc]
    have hcongr : ∀ a ∈ s.accounts, (step s r).2.balance a = expectedBalance s r a := fun a _ => hbal a
    rw [sumOver_congr s.accounts _ _ hcongr]
    exact plan0_sumOver_expectedBalance_eq_proof s r hv
  · have heq : (step s r).1 = Outcome.rejected := by simp [step, hv]
    rw [heq] at hok
    exact absurd hok (by decide)

end Payout
