import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def decision (l : List Entry) (r : Request) : Bool :=
  let maxA := l.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0
  let maxD := l.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0
  (maxA != 0 && decide (maxD < maxA))

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem tmp1 (s : State) (r : Request) (hmem : r.user ∈ s.users) : decide (r.user ∈ s.users) = true :=
  decide_eq_true hmem

theorem tmp2 (a : Nat) (h : a ≠ 0) : (a != 0) = true := by simp [h]

theorem tmp3 (s : State) (r : Request) (hmem : r.user ∈ s.users) : s.users.contains r.user = true := by
  rw [List.contains_eq_mem]
  exact decide_eq_true hmem

theorem tmp4 (s : State) (r : Request) (hmem : r.user ∈ s.users) (hne : r.user ≠ 0) :
  (s.users.contains r.user && (r.user != 0)) = true := by
  have hc : s.users.contains r.user = true := tmp3 s r hmem
  have hnz : (r.user != 0) = true := tmp2 r.user hne
  rw [hc, hnz]
  rfl

theorem my_probe5 (s : State) (r : Request) : (step s r) = (step s r) := by rfl

#print step

theorem beq_nat_true (a b : Nat) : (a == b) = true ↔ a = b := by
  simp

theorem isPrefixOf_iff_prefix_aux4 (xs ys : List Nat) : (xs.isPrefixOf ys = true) ↔ (xs <+: ys) := by
  induction xs generalizing ys with
  | nil =>
    simp
  | cons x xs ih =>
    cases ys with
    | nil =>
      constructor
      · intro h
        simp [List.isPrefixOf] at h
      · intro h
        obtain ⟨t, ht⟩ := h
        simp at ht
    | cons y ys =>
      simp only [List.isPrefixOf, Bool.and_eq_true, beq_nat_true]
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := h
        subst h1
        obtain ⟨t, ht⟩ := (ih ys).mp h2
        exact ⟨t, by simp only [List.cons_append]; rw [ht]⟩
      · intro h
        obtain ⟨t, ht⟩ := h
        simp at ht
        obtain ⟨hxy, hrest⟩ := ht
        subst hxy
        exact ⟨rfl, (ih _).mpr ⟨_, hrest⟩⟩

theorem matchesB_iff_test (e : Entry) (r : Request) : (matchesB e r = true) ↔ Matches e r := by
  unfold matchesB Matches
  simp only [Bool.and_eq_true]
  constructor
  · intro h
    obtain ⟨hsub, hpref⟩ := h
    simp only [Bool.or_eq_true, beq_nat_true] at hsub
    exact ⟨hsub, (isPrefixOf_iff_prefix_aux4 _ _).mp hpref⟩
  · intro h
    obtain ⟨hsub, hpref⟩ := h
    simp only [Bool.or_eq_true, beq_nat_true] at hsub ⊢
    exact ⟨hsub, (isPrefixOf_iff_prefix_aux4 _ _).mpr hpref⟩

theorem effect_allow_beq2 (e : Entry) : ((e.effect == .allow) = true) ↔ e.effect = .allow := by
  cases e.effect <;> simp

theorem effect_deny_beq3 (e : Entry) : ((e.effect == .deny) = true) ↔ e.effect = .deny := by
  cases e.effect <;> simp

theorem foldAllow_ge2 (r : Request) (l : List Entry) (acc : Nat) :
  acc ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) acc l := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl acc
  | cons hd tl ih =>
    simp only [List.foldl]
    split
    · exact Nat.le_trans (Nat.le_max_left acc _) (ih _)
    · exact ih _

theorem helpSA_condAllow_iff2 (r : Request) (e : Entry) :
  ((matchesB e r && e.effect == .allow) = true) ↔ (Matches e r ∧ e.effect = .allow) := by
  have h1 : ((matchesB e r && e.effect == .allow) = true) ↔
    (matchesB e r = true ∧ (e.effect == .allow) = true) := by
    simp only [Bool.and_eq_true]
  rw [h1, matchesB_iff_test, effect_allow_beq2]

theorem helpSA_condDeny_iff2 (r : Request) (e : Entry) :
  ((matchesB e r && e.effect == .deny) = true) ↔ (Matches e r ∧ e.effect = .deny) := by
  have h1 : ((matchesB e r && e.effect == .deny) = true) ↔
    (matchesB e r = true ∧ (e.effect == .deny) = true) := by
    simp only [Bool.and_eq_true]
  rw [h1, matchesB_iff_test, effect_deny_beq3]

theorem helpSA_maxmono_probe (x y k : Nat) (h : x ≤ y) : Nat.max x k ≤ Nat.max y k := by
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_trans h (Nat.le_max_left y k)
  · exact Nat.le_max_right y k
#check @Nat.max_le

theorem helpSA_foldA_mono3 (r : Request) (l : List Entry) (x y : Nat) (h : x ≤ y) :
  List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) x l ≤
  List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) y l := by
  induction l generalizing x y with
  | nil =>
    simpa using h
  | cons hd tl ih =>
    simp only [List.foldl]
    by_cases hc : ((matchesB hd r && hd.effect == .allow) = true)
    · rw [if_pos hc, if_pos hc]
      exact ih _ _ (helpSA_maxmono_probe x y _ h)
    · rw [if_neg hc, if_neg hc]
      exact ih _ _ h

theorem helpSA_foldA_mem_ge3 (r : Request) (l : List Entry) (a : Entry) (acc : Nat) :
  a ∈ l → ((matchesB a r && a.effect == .allow) = true) →
  a.path.length + 1 ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) acc l := by
  induction l generalizing acc with
  | nil =>
    intro hm _
    simp at hm
  | cons hd tl ih =>
    intro hm hcond
    have hdisj : a = hd ∨ a ∈ tl := by simpa using hm
    cases hdisj with
    | inl heq =>
      subst heq
      simp only [List.foldl, if_pos hcond]
      exact Nat.le_trans (Nat.le_max_right acc _) (foldAllow_ge2 r tl _)
    | inr hmem =>
      simp only [List.foldl]
      by_cases hc : ((matchesB hd r && hd.effect == .allow) = true)
      · rw [if_pos hc]
        exact Nat.le_trans (ih _ hmem hcond) (helpSA_foldA_mono3 r tl _ _ (Nat.le_max_left _ _))
      · rw [if_neg hc]
        exact ih _ hmem hcond

theorem foldDeny_ge2 (r : Request) (l : List Entry) (acc : Nat) :
  acc ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) acc l := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl acc
  | cons hd tl ih =>
    simp only [List.foldl]
    split
    · exact Nat.le_trans (Nat.le_max_left acc _) (ih _)
    · exact ih _

theorem helpDeny_mono3 (r : Request) (l : List Entry) (x y : Nat) (h : x ≤ y) :
  List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) x l ≤
  List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) y l := by
  induction l generalizing x y with
  | nil => simpa using h
  | cons hd tl ih =>
    simp only [List.foldl]
    by_cases hc : ((matchesB hd r && hd.effect == .deny) = true)
    · rw [if_pos hc, if_pos hc]
      exact ih _ _ (Nat.max_le.mpr ⟨Nat.le_trans h (Nat.le_max_left y _), Nat.le_max_right y _⟩)
    · rw [if_neg hc, if_neg hc]
      exact ih _ _ h

theorem helpDeny_mem_ge3 (r : Request) (l : List Entry) (a : Entry) (acc : Nat) :
  a ∈ l → ((matchesB a r && a.effect == .deny) = true) →
  a.path.length + 1 ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) acc l := by
  induction l generalizing acc with
  | nil =>
    intro hm _
    simp at hm
  | cons hd tl ih =>
    intro hm hcond
    have hdisj : a = hd ∨ a ∈ tl := by simpa using hm
    cases hdisj with
    | inl heq =>
      subst heq
      simp only [List.foldl, if_pos hcond]
      exact Nat.le_trans (Nat.le_max_right acc _) (foldDeny_ge2 r tl _)
    | inr hmem =>
      simp only [List.foldl]
      by_cases hc : ((matchesB hd r && hd.effect == .deny) = true)
      · rw [if_pos hc]
        exact Nat.le_trans (ih _ hmem hcond) (helpDeny_mono3 r tl _ _ (Nat.le_max_left _ _))
      · rw [if_neg hc]
        exact ih _ hmem hcond

theorem foldA_le_upper2 (r : Request) (l : List Entry) (acc N : Nat) :
  acc ≤ N → (∀ e ∈ l, ((matchesB e r && e.effect == .allow) = true) → e.path.length + 1 ≤ N) →
  List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) acc l ≤ N := by
  induction l generalizing acc with
  | nil =>
    intro hacc _
    simpa using hacc
  | cons hd tl ih =>
    intro hacc hall
    simp only [List.foldl]
    by_cases hc : ((matchesB hd r && hd.effect == .allow) = true)
    · rw [if_pos hc]
      refine ih _ ?_ ?_
      · exact Nat.max_le.mpr ⟨hacc, hall hd (List.mem_cons_self) hc⟩
      · intro e hmem hcond
        exact hall e (List.mem_cons_of_mem hd hmem) hcond
    · rw [if_neg hc]
      refine ih _ hacc ?_
      intro e hmem hcond
      exact hall e (List.mem_cons_of_mem hd hmem) hcond

theorem test_ifpos (a b : Bool) (h : ((a && b) = true)) : (if ((a && b) = true) then (1 : Nat) else 2) = 1 := by
  rw [if_pos h]

theorem probe_max_lemmas (a b : Nat) (h : b ≤ a) : Nat.max a b = a := by
  exact Nat.max_eq_left h
#check @Nat.max_eq_left
#check @Nat.max_eq_right

theorem probe_mem_iff2 (l1 l2 : List Entry) (h : l1.Perm l2) (e : Entry) (hm : e ∈ l1) : e ∈ l2 := by
  have hiff : e ∈ l1 ↔ e ∈ l2 := List.Perm.mem_iff h
  exact hiff.mp hm

theorem oi_foldA_perm (r : Request) (l1 l2 : List Entry) (h : l1.Perm l2) :
  List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l1 =
  List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l2 := by
  apply Nat.le_antisymm
  · apply foldA_le_upper2 r l1 0 _ (Nat.zero_le _) _
    intro e hmem hcond
    have hmem2 : e ∈ l2 := (List.Perm.mem_iff h).mp hmem
    exact helpSA_foldA_mem_ge3 r l2 e 0 hmem2 hcond
  · apply foldA_le_upper2 r l2 0 _ (Nat.zero_le _) _
    intro e hmem hcond
    have hmem1 : e ∈ l1 := (List.Perm.mem_iff h.symm).mp hmem
    exact helpSA_foldA_mem_ge3 r l1 e 0 hmem1 hcond

theorem probe_decision_unfold (l : List Entry) (r : Request) :
  decision l r = ((List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l != 0) && decide (List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l < List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l)) := by
  unfold decision
  rfl
#check @List.foldl

theorem foldD_le_upper2 (r : Request) (l : List Entry) (acc N : Nat) :
  acc ≤ N → (∀ e ∈ l, ((matchesB e r && e.effect == .deny) = true) → e.path.length + 1 ≤ N) →
  List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) acc l ≤ N := by
  induction l generalizing acc with
  | nil =>
    intro hacc _
    simpa using hacc
  | cons hd tl ih =>
    intro hacc hall
    simp only [List.foldl]
    by_cases hc : ((matchesB hd r && hd.effect == .deny) = true)
    · rw [if_pos hc]
      refine ih _ ?_ ?_
      · exact Nat.max_le.mpr ⟨hacc, hall hd (List.mem_cons_self) hc⟩
      · intro e hmem hcond
        exact hall e (List.mem_cons_of_mem hd hmem) hcond
    · rw [if_neg hc]
      refine ih _ hacc ?_
      intro e hmem hcond
      exact hall e (List.mem_cons_of_mem hd hmem) hcond

theorem max_choice_eq (a b : Nat) : Nat.max a b = a ∨ Nat.max a b = b := by
  rcases Nat.le_total a b with h | h
  · exact Or.inr (Nat.max_eq_right h)
  · exact Or.inl (Nat.max_eq_left h)

theorem attainD_aux (r : Request) (l : List Entry) (acc : Nat) :
  List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) acc l = acc ∨
  ∃ e ∈ l, ((matchesB e r && e.effect == .deny) = true) ∧ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) acc l = e.path.length + 1 := by
  induction l generalizing acc with
  | nil => exact Or.inl rfl
  | cons hd tl ih =>
    simp only [List.foldl]
    by_cases hc : ((matchesB hd r && hd.effect == .deny) = true)
    · rw [if_pos hc]
      have hmax : Nat.max acc (hd.path.length + 1) = acc ∨ Nat.max acc (hd.path.length + 1) = hd.path.length + 1 := max_choice_eq _ _
      have hih := ih (Nat.max acc (hd.path.length + 1))
      cases hih with
      | inl heq =>
        rw [heq] at *
        cases hmax with
        | inl h =>
          exact Or.inl h
        | inr h =>
          rw [h]
          exact Or.inr ⟨hd, List.mem_cons_self, hc, rfl⟩
      | inr hex =>
        obtain ⟨e, hmem, hcond, heq⟩ := hex
        exact Or.inr ⟨e, List.mem_cons_of_mem hd hmem, hcond, heq⟩
    · rw [if_neg hc]
      have hih := ih acc
      cases hih with
      | inl heq => exact Or.inl heq
      | inr hex =>
        obtain ⟨e, hmem, hcond, heq⟩ := hex
        exact Or.inr ⟨e, List.mem_cons_of_mem hd hmem, hcond, heq⟩

theorem attainD (r : Request) (l : List Entry) (hpos : 0 < List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l) :
  ∃ e ∈ l, ((matchesB e r && e.effect == .deny) = true) ∧ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l = e.path.length + 1 := by
  have h := attainD_aux r l 0
  cases h with
  | inl heq => omega
  | inr hex => exact hex

theorem attainA_aux (r : Request) (l : List Entry) (acc : Nat) :
  List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) acc l = acc ∨
  ∃ e ∈ l, ((matchesB e r && e.effect == .allow) = true) ∧ List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) acc l = e.path.length + 1 := by
  induction l generalizing acc with
  | nil => exact Or.inl rfl
  | cons hd tl ih =>
    simp only [List.foldl]
    by_cases hc : ((matchesB hd r && hd.effect == .allow) = true)
    · rw [if_pos hc]
      have hmax : Nat.max acc (hd.path.length + 1) = acc ∨ Nat.max acc (hd.path.length + 1) = hd.path.length + 1 := max_choice_eq _ _
      have hih := ih (Nat.max acc (hd.path.length + 1))
      cases hih with
      | inl heq =>
        rw [heq] at *
        cases hmax with
        | inl h =>
          exact Or.inl h
        | inr h =>
          rw [h]
          exact Or.inr ⟨hd, List.mem_cons_self, hc, rfl⟩
      | inr hex =>
        obtain ⟨e, hmem, hcond, heq⟩ := hex
        exact Or.inr ⟨e, List.mem_cons_of_mem hd hmem, hcond, heq⟩
    · rw [if_neg hc]
      have hih := ih acc
      cases hih with
      | inl heq => exact Or.inl heq
      | inr hex =>
        obtain ⟨e, hmem, hcond, heq⟩ := hex
        exact Or.inr ⟨e, List.mem_cons_of_mem hd hmem, hcond, heq⟩

theorem attainA (r : Request) (l : List Entry) (hpos : 0 < List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l) :
  ∃ e ∈ l, ((matchesB e r && e.effect == .allow) = true) ∧ List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l = e.path.length + 1 := by
  have h := attainA_aux r l 0
  cases h with
  | inl heq => omega
  | inr hex => exact hex

theorem probe_contains_rev (s : State) (r : Request) (h : s.users.contains r.user = true) : r.user ∈ s.users := by
  rw [List.contains_eq_mem] at h
  exact of_decide_eq_true h

theorem probe_ne_rev (u : Nat) (h : (u != 0) = true) : u ≠ 0 := by
  intro heq
  rw [heq] at h
  simp at h

theorem decision_false_of_overridden_auxDO (l : List Entry) (r : Request) (hO : Overridden l r) : decision l r = false := by
  obtain ⟨d, hdmem, hMatchD, hEffD, hLe⟩ := hO
  have hcondD : ((matchesB d r && d.effect == .deny) = true) := (helpSA_condDeny_iff2 r d).mpr ⟨hMatchD, hEffD⟩
  have hGeD : d.path.length + 1 ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l :=
    helpDeny_mem_ge3 r l d 0 hdmem hcondD
  have hLeA : List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l ≤ d.path.length + 1 := by
    apply foldA_le_upper2 r l 0 (d.path.length + 1) (Nat.zero_le _)
    intro e hmem hcond
    obtain ⟨hM, hEff⟩ := (helpSA_condAllow_iff2 r e).mp hcond
    have hle : depth e ≤ depth d := hLe e hmem hM hEff
    have hle2 : e.path.length ≤ d.path.length := hle
    omega
  have hleMax : List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l ≤
    List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l :=
    Nat.le_trans hLeA hGeD
  have hNotLt : ¬ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l <
    List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l :=
    Nat.not_lt.mpr hleMax
  have hDecEq : decide (List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l <
    List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l) = false :=
    decide_eq_false hNotLt
  have hUnfold := probe_decision_unfold l r
  rw [hUnfold, hDecEq]
  simp

theorem probe_bne_aux3 (x : Nat) (h : x ≠ 0) : (x != 0) = true := by
  exact (bne_iff_ne).mpr h

theorem decision_true_of_permitted_auxSA (l : List Entry) (r : Request) (hP : Permitted l r) : decision l r = true := by
  obtain ⟨a, hamem, hMatchA, hEffA, hLt⟩ := hP
  have hcondA : ((matchesB a r && a.effect == .allow) = true) := (helpSA_condAllow_iff2 r a).mpr ⟨hMatchA, hEffA⟩
  have hGeA : a.path.length + 1 ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l :=
    helpSA_foldA_mem_ge3 r l a 0 hamem hcondA
  have hNeA : List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l ≠ 0 := by
    omega
  have hNeB : (List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l != 0) = true := by
    exact (bne_iff_ne).mpr hNeA
  have hLeD : List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l ≤ a.path.length := by
    apply foldD_le_upper2 r l 0 (a.path.length) (Nat.zero_le _)
    intro e hmem hcond
    obtain ⟨hM, hEff⟩ := (helpSA_condDeny_iff2 r e).mp hcond
    have hlt : depth e < depth a := hLt e hmem hM hEff
    unfold depth at hlt
    omega
  have hLtAD : List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l <
    List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l := by
    omega
  have hDec : decide (List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l <
    List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l) = true :=
    decide_eq_true hLtAD
  have hUnfold := probe_decision_unfold l r
  rw [hUnfold, hNeB, hDec]
  rfl

theorem req_grant_justified_aux_test : True := trivial
#check @Bool.and_eq_true

theorem grant_just_lemma1 (l : List Entry) (r : Request) (h : decision l r = true) :
  ((List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l != 0) = true) := by
  have hU := probe_decision_unfold l r
  rw [h] at hU
  have hB : (((List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l != 0) && decide (List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l < List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l)) = true) := hU.symm
  exact ((Bool.and_eq_true_iff).mp hB).1

theorem grant_just_lemma2 (l : List Entry) (r : Request) (h : decision l r = true) :
  decide (List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l < List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l) = true := by
  have hU := probe_decision_unfold l r
  rw [h] at hU
  have hB : (((List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l != 0) && decide (List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l < List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l)) = true) := hU.symm
  exact ((Bool.and_eq_true_iff).mp hB).2

theorem oi_foldD_perm_aux (r : Request) (l1 l2 : List Entry) (h : l1.Perm l2) :
  List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l1 =
  List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l2 := by
  apply Nat.le_antisymm
  · apply foldD_le_upper2 r l1 0 _ (Nat.zero_le _) _
    intro e hmem hcond
    have hmem2 : e ∈ l2 := (List.Perm.mem_iff h).mp hmem
    exact helpDeny_mem_ge3 r l2 e 0 hmem2 hcond
  · apply foldD_le_upper2 r l2 0 _ (Nat.zero_le _) _
    intro e hmem hcond
    have hmem1 : e ∈ l1 := (List.Perm.mem_iff h.symm).mp hmem
    exact helpDeny_mem_ge3 r l1 e 0 hmem1 hcond

theorem oi_probe2 (s : State) (r : Request) (l : List Entry) :
  (({ s with entries := l } : State).users.contains r.user && (r.user != 0)) = (s.users.contains r.user && (r.user != 0)) := rfl

theorem oi_probe3 (s : State) (r : Request) (l : List Entry) :
  decision (({ s with entries := l } : State).entries) r = decision l r := rfl

theorem oi_aux_test2 (s1 s2 : State) (r : Request)
  (huser : s1.users = s2.users)
  (hdec : decision s1.entries r = decision s2.entries r) :
  (step s1 r).1 = (step s2 r).1 := by
  unfold step
  rw [huser, hdec]
  by_cases hc : (s2.users.contains r.user && (r.user != 0)) = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

theorem req_valid_answered : ValidAnswered step := by
  intro s r h
  obtain ⟨hmem, hne⟩ := h
  have hcond : ((s.users.contains r.user && (r.user != 0)) = true) := tmp4 s r hmem hne
  have hEq : step s r = ((if decision s.entries r then Outcome.granted else Outcome.denied), { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
    unfold step
    rw [if_pos hcond]
  rw [hEq]
  simp only
  cases h : decision s.entries r <;> simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hcond_false : (s.users.contains r.user && (r.user != 0)) = false := by
    cases hcb : (s.users.contains r.user && (r.user != 0)) with
    | true =>
      exfalso
      apply h
      have h1 : s.users.contains r.user = true := by
        have hh := (Bool.and_eq_true_iff).mp hcb
        exact hh.1
      have h2 : (r.user != 0) = true := by
        have hh := (Bool.and_eq_true_iff).mp hcb
        exact hh.2
      exact ⟨probe_contains_rev s r h1, probe_ne_rev r.user h2⟩
    | false => rfl
  have hneg : ¬ ((s.users.contains r.user && (r.user != 0)) = true) := by
    rw [hcond_false]
    simp
  unfold step
  rw [if_neg hneg]

theorem req_effects : Effects step := by
  intro s r hNe
  by_cases hcond : (s.users.contains r.user && (r.user != 0)) = true
  · have hEq : step s r = ((if decision s.entries r then Outcome.granted else Outcome.denied), { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
      unfold step
      rw [if_pos hcond]
    rw [hEq]
    refine ⟨rfl, rfl, ?_⟩
    cases hg : decision s.entries r <;> simp
  · have hEq : step s r = ((.rejected, s)) := by
      unfold step
      rw [if_neg hcond]
    exfalso
    apply hNe
    rw [hEq]

theorem req_default_deny : DefaultDeny step := by
  intro s r hNoAllow hEq
  have hFoldLe : List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries ≤ 0 := by
    apply foldA_le_upper2 r s.entries 0 0 (Nat.zero_le 0)
    intro e hmem hcond
    exfalso
    apply hNoAllow
    obtain ⟨hM, hEff⟩ := (helpSA_condAllow_iff2 r e).mp hcond
    exact ⟨e, hmem, hM, hEff⟩
  have hFoldZero : List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries = 0 :=
    Nat.le_zero.mp hFoldLe
  have hDecFalse : decision s.entries r = false := by
    unfold decision
    rw [hFoldZero]
    simp
  have hNot : (step s r).1 ≠ .granted := by
    by_cases hc : (s.users.contains r.user && (r.user != 0)) = true
    · have hEqS : step s r = ((if decision s.entries r then Outcome.granted else Outcome.denied), { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
        unfold step
        rw [if_pos hc]
      have hStep : (step s r).1 = .denied := by
        rw [hEqS]
        simp [hDecFalse]
      rw [hStep]
      simp
    · have hEqS : step s r = (.rejected, s) := by
        unfold step
        rw [if_neg hc]
      have hStep : (step s r).1 = .rejected := by
        rw [hEqS]
      rw [hStep]
      simp
  exact hNot hEq

theorem req_deny_overrides : DenyOverrides step := by
  intro s r hOvr hEq
  have hDecFalse : decision s.entries r = false := decision_false_of_overridden_auxDO s.entries r hOvr
  by_cases hc : (s.users.contains r.user && (r.user != 0)) = true
  · have hEqS : step s r = ((if decision s.entries r then Outcome.granted else Outcome.denied), { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
      unfold step
      rw [if_pos hc]
    have hStep : (step s r).1 = .denied := by
      rw [hEqS]
      simp [hDecFalse]
    rw [hStep] at hEq
    simp at hEq
  · have hEqS : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hc]
    have hStep : (step s r).1 = .rejected := by rw [hEqS]
    rw [hStep] at hEq
    simp at hEq

theorem req_specific_allow : SpecificAllow step := by
  intro s r hValid hPerm
  obtain ⟨hmem, hne⟩ := hValid
  have hcond : ((s.users.contains r.user && (r.user != 0)) = true) := tmp4 s r hmem hne
  have hDec : decision s.entries r = true := decision_true_of_permitted_auxSA s.entries r hPerm
  have hEq : step s r = ((if decision s.entries r then Outcome.granted else Outcome.denied), { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
    unfold step
    rw [if_pos hcond]
  have hFst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) := by
    rw [hEq]
  rw [hFst, hDec]
  rfl

theorem req_grant_justified    : GrantJustified step := by
  intro s r hG
  by_cases hc : (s.users.contains r.user && (r.user != 0)) = true
  · have hEq : step s r = ((if decision s.entries r then Outcome.granted else Outcome.denied), { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
      unfold step
      rw [if_pos hc]
    have hFst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) := by
      rw [hEq]
    have hIf : (if decision s.entries r then Outcome.granted else Outcome.denied) = Outcome.granted := by
      rw [← hFst]
      exact hG
    have hDec : decision s.entries r = true := by
      cases hdec : decision s.entries r with
      | true => rfl
      | false =>
        simp [hdec] at hIf
    have hNeB := grant_just_lemma1 s.entries r hDec
    have hLtB := grant_just_lemma2 s.entries r hDec
    have hNe : List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries ≠ 0 := by
      intro hz
      rw [hz] at hNeB
      simp at hNeB
    have hPos : 0 < List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries :=
      Nat.pos_of_ne_zero hNe
    have hLt : List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries <
      List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries :=
      of_decide_eq_true hLtB
    obtain ⟨a, hamem, hcondA, hEqA⟩ := attainA r s.entries hPos
    have hcondA2 : ((matchesB a r && a.effect == .allow) = true) := of_decide_eq_true hcondA
    obtain ⟨hMatchA, hEffA⟩ := (helpSA_condAllow_iff2 r a).mp hcondA2
    refine ⟨a, hamem, hMatchA, hEffA, ?_⟩
    intro d hdmem hMatchD hEffD
    have hcondD : ((matchesB d r && d.effect == .deny) = true) := (helpSA_condDeny_iff2 r d).mpr ⟨hMatchD, hEffD⟩
    have hGeD : d.path.length + 1 ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries :=
      helpDeny_mem_ge3 r s.entries d 0 hdmem hcondD
    have hchain : d.path.length + 1 < a.path.length + 1 := by
      calc d.path.length + 1 ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries := hGeD
        _ < List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries := hLt
        _ = a.path.length + 1 := hEqA
    show depth d < depth a
    unfold depth at *
    omega
  · have hEq : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hc]
    have hFst : (step s r).1 = .rejected := by
      rw [hEq]
    rw [hFst] at hG
    simp at hG

theorem req_order_independent  : OrderIndependent step := by
  intro s r l hperm
  have hA : List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 l =
    List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries :=
    oi_foldA_perm r l s.entries hperm
  have hD : List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 l =
    List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries :=
    oi_foldD_perm_aux r l s.entries hperm
  have hdec : decision l r = decision s.entries r := by
    unfold decision
    rw [hA, hD]
  exact oi_aux_test2 { s with entries := l } s r rfl hdec

theorem req_denial_explained : DenialExplained step := by
  intro s r hDen
  by_cases hc : (s.users.contains r.user && (r.user != 0)) = true
  · have hEq : step s r = ((if decision s.entries r then Outcome.granted else Outcome.denied), { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
      unfold step
      rw [if_pos hc]
    have hFst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) := by rw [hEq]
    rw [hFst] at hDen
    have hDecFalse : decision s.entries r = false := by
      cases hdec : decision s.entries r with
      | false => rfl
      | true => simp [hdec] at hDen
    by_cases hHas : HasAllow s.entries r
    · right
      obtain ⟨a0, ha0mem, ha0M, ha0E⟩ := hHas
      have hcondA0 : ((matchesB a0 r && a0.effect == .allow) = true) :=
        (helpSA_condAllow_iff2 r a0).mpr ⟨ha0M, ha0E⟩
      have hGeA0 : a0.path.length + 1 ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries :=
        helpSA_foldA_mem_ge3 r s.entries a0 0 ha0mem hcondA0
      have hNeA : List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries ≠ 0 := by omega
      have hNeB : (List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries != 0) = true :=
        (bne_iff_ne).mpr hNeA
      have hU := probe_decision_unfold s.entries r
      rw [hDecFalse] at hU
      have hAnd : ((List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries != 0) && decide (List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries < List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries)) = false := hU.symm
      rw [hNeB, Bool.true_and] at hAnd
      have hNotLt : ¬ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries < List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries :=
        of_decide_eq_false hAnd
      have hLe : List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries := by
        omega
      have hPosD : 0 < List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries := by omega
      obtain ⟨d, hdmem, hcondD_raw, hEqD⟩ := attainD r s.entries hPosD
      have hcondD : ((matchesB d r && d.effect == .deny) = true) := of_decide_eq_true hcondD_raw
      obtain ⟨hMatchD, hEffD⟩ := (helpSA_condDeny_iff2 r d).mp hcondD
      refine ⟨d, hdmem, hMatchD, hEffD, ?_⟩
      intro a hamem hMatchA hEffA
      have hcondA : ((matchesB a r && a.effect == .allow) = true) := (helpSA_condAllow_iff2 r a).mpr ⟨hMatchA, hEffA⟩
      have hGeA : a.path.length + 1 ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries :=
        helpSA_foldA_mem_ge3 r s.entries a 0 hamem hcondA
      have hchain : a.path.length + 1 ≤ d.path.length + 1 := by
        calc a.path.length + 1 ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .allow) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries := hGeA
          _ ≤ List.foldl (fun acc e => if (matchesB e r && e.effect == .deny) then Nat.max acc (e.path.length + 1) else acc) 0 s.entries := hLe
          _ = d.path.length + 1 := hEqD
      show depth a ≤ depth d
      unfold depth at *
      omega
    · left
      exact hHas
  · have hEq : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hc]
    have hFst : (step s r).1 = .rejected := by rw [hEq]
    rw [hFst] at hDen
    simp at hDen

end Acl
