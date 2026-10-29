import Acl.Spec

namespace Acl

def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def permittedB (l : List Entry) (r : Request) : Bool :=
  l.any (fun a => matchesB a r && decide (a.effect = .allow) && l.all (fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (depth d < depth a)))

def validB (s : State) (r : Request) : Bool :=
  decide (r.user ∈ s.users) && decide (r.user ≠ 0)

def step : Impl := fun s r =>
  if !validB s r then (.rejected, s)
  else if permittedB s.entries r then
    (.granted, { s with log := s.log ++ [{ user := r.user, path := r.path, granted := true }] })
  else
    (.denied, { s with log := s.log ++ [{ user := r.user, path := r.path, granted := false }] })

theorem validB_true_of_ValidQuery {s : State} {r : Request} (h : ValidQuery s r) : validB s r = true := by
  unfold ValidQuery at h
  unfold validB
  simp [h.1, h.2]

#check validB_true_of_ValidQuery

theorem validB_false_of_not_ValidQuery_aux {s : State} {r : Request} (h : ¬ ValidQuery s r) : validB s r = false := by
  unfold ValidQuery at h
  unfold validB
  by_cases h1 : r.user ∈ s.users
  · by_cases h2 : r.user ≠ 0
    · exact absurd ⟨h1, h2⟩ h
    · simp [h1, h2]
  · simp [h1]

theorem t_prefix_true (xs ys : Path) (h : xs.isPrefixOf ys = true) : xs <+: ys := by
  simpa using h

theorem t_prefix_false (xs ys : Path) (h : xs <+: ys) : xs.isPrefixOf ys = true := by
  simpa using h

theorem matchesB_iff_aux (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hsub, hpref⟩ := h
    simp only [Bool.or_eq_true, beq_iff_eq] at hsub
    constructor
    · rcases hsub with h0 | hu <;> simp_all
    · exact List.isPrefixOf_iff_prefix.mp hpref
  · intro h
    obtain ⟨hsub, hpref⟩ := h
    simp only [Bool.and_eq_true]
    constructor
    · simp only [Bool.or_eq_true, beq_iff_eq]
      rcases hsub with h0 | hu <;> simp_all
    · exact List.isPrefixOf_iff_prefix.mpr hpref

theorem permittedB_true_iff_aux (l : List Entry) (r : Request) : permittedB l r = true ↔ Permitted l r := by
  unfold permittedB Permitted
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, hmema, ha⟩
    simp only [Bool.and_eq_true] at ha
    obtain ⟨⟨hmB, heff⟩, hall⟩ := ha
    have hMa : Matches a r := (matchesB_iff_aux a r).mp hmB
    have heffA : a.effect = .allow := of_decide_eq_true heff
    refine ⟨a, hmema, hMa, heffA, ?_⟩
    intro d hmemd hMd heffd
    have hMdB : matchesB d r = true := (matchesB_iff_aux d r).mpr hMd
    have heffdB : decide (d.effect = .deny) = true := by simp [heffd]
    rw [List.all_eq_true] at hall
    have hx := hall d hmemd
    simp only [hMdB, heffdB] at hx
    simp only [Bool.and_self, Bool.not_true, Bool.false_or] at hx
    exact of_decide_eq_true hx
  · rintro ⟨a, hmema, hMa, heffA, hallP⟩
    refine ⟨a, hmema, ?_⟩
    have hmB : matchesB a r = true := (matchesB_iff_aux a r).mpr hMa
    have heffB : decide (a.effect = .allow) = true := by simp [heffA]
    simp only [Bool.and_eq_true]
    refine ⟨⟨hmB, heffB⟩, ?_⟩
    rw [List.all_eq_true]
    intro d hmemd
    by_cases hMd : Matches d r
    · by_cases heffd : d.effect = .deny
      · have hlt : depth d < depth a := hallP d hmemd hMd heffd
        have hMdB : matchesB d r = true := (matchesB_iff_aux d r).mpr hMd
        have heffdB : decide (d.effect = .deny) = true := by simp [heffd]
        have hltB : decide (depth d < depth a) = true := by simp [hlt]
        simp [hMdB, heffdB, hltB]
      · have hdec : decide (d.effect = .deny) = false := by simp [heffd]
        have hMB : matchesB d r = true := (matchesB_iff_aux d r).mpr hMd
        simp [hMB, hdec]
    · have hMBf : matchesB d r = false := by
        cases hMB : matchesB d r with
        | false => rfl
        | true => exact absurd ((matchesB_iff_aux d r).mp hMB) hMd
      simp [hMBf]

theorem bool_eq_of_true_iff4 {b1 b2 : Bool} {P Q : Prop} (h1 : b1 = true ↔ P) (h2 : b2 = true ↔ Q) (hPQ : P ↔ Q) : b1 = b2 := by
  cases b1 <;> cases b2 <;> simp_all

theorem permitted_perm_aux4 (l1 l2 : List Entry) (r : Request) (h : l1.Perm l2) : Permitted l1 r ↔ Permitted l2 r := by
  constructor
  · rintro ⟨a, hm1, hM, heff, hall⟩
    refine ⟨a, h.mem_iff.mp hm1, hM, heff, ?_⟩
    intro d hmd hMd heff2
    exact hall d (h.mem_iff.mpr hmd) hMd heff2
  · rintro ⟨a, hm2, hM, heff, hall⟩
    refine ⟨a, h.mem_iff.mpr hm2, hM, heff, ?_⟩
    intro d hmd hMd heff2
    exact hall d (h.mem_iff.mp hmd) hMd heff2

theorem permittedB_perm_aux4 (l1 l2 : List Entry) (r : Request) (h : l1.Perm l2) : permittedB l1 r = permittedB l2 r := by
  apply bool_eq_of_true_iff4 (permittedB_true_iff_aux l1 r) (permittedB_true_iff_aux l2 r)
  exact permitted_perm_aux4 l1 l2 r h

theorem validB_entries_irrel4 (s : State) (l : List Entry) (r : Request) : validB { s with entries := l } r = validB s r := by
  unfold validB
  simp

theorem foo_test_thm : 1 = 1 := rfl

theorem mem_test_aux (hd : Entry) (tl : List Entry) : hd ∈ hd :: tl := by
  simp

theorem probe_mem_aux : ∀ (hd : Entry) (tl : List Entry), hd ∈ hd :: tl ∧ (∀ (a : Entry), a ∈ tl → a ∈ hd :: tl) := by
  intro hd tl
  constructor
  · exact List.Mem.head _
  · intro a h
    exact List.Mem.tail _ h

theorem maximal_allow_auxDD (l : List Entry) (r : Request) : HasAllow l r → ∃ a, a ∈ l ∧ Matches a r ∧ a.effect = .allow ∧ ∀ b, b ∈ l → Matches b r → b.effect = .allow → depth b ≤ depth a := by
  induction l with
  | nil =>
    intro h
    unfold HasAllow at h
    obtain ⟨a, hm, _, _⟩ := h
    simp at hm
  | cons hd tl ih =>
    intro h
    by_cases htl : HasAllow tl r
    · obtain ⟨a0, hm0, hM0, he0, hmax0⟩ := ih htl
      by_cases hhd : Matches hd r ∧ hd.effect = .allow
      · obtain ⟨hMhd, hehd⟩ := hhd
        rcases Nat.le_total (depth a0) (depth hd) with hle | hle
        · refine ⟨hd, List.Mem.head _, hMhd, hehd, ?_⟩
          intro b hb hMb heb
          rcases List.mem_cons.mp hb with rfl | hmem
          · exact Nat.le_refl _
          · exact Nat.le_trans (hmax0 b hmem hMb heb) hle
        · refine ⟨a0, List.Mem.tail _ hm0, hM0, he0, ?_⟩
          intro b hb hMb heb
          rcases List.mem_cons.mp hb with rfl | hmem
          · exact hle
          · exact hmax0 b hmem hMb heb
      · refine ⟨a0, List.Mem.tail _ hm0, hM0, he0, ?_⟩
        intro b hb hMb heb
        rcases List.mem_cons.mp hb with rfl | hmem
        · exact absurd ⟨hMb, heb⟩ hhd
        · exact hmax0 b hmem hMb heb
    · by_cases hhd : Matches hd r ∧ hd.effect = .allow
      · obtain ⟨hMhd, hehd⟩ := hhd
        refine ⟨hd, List.Mem.head _, hMhd, hehd, ?_⟩
        intro b hb hMb heb
        rcases List.mem_cons.mp hb with rfl | hmem
        · exact Nat.le_refl _
        · unfold HasAllow at htl
          have hex : ∃ a, a ∈ tl ∧ Matches a r ∧ a.effect = .allow := ⟨b, hmem, hMb, heb⟩
          exact absurd hex htl
      · unfold HasAllow at h
        obtain ⟨a, hm, hMa, hea⟩ := h
        rcases List.mem_cons.mp hm with rfl | hmem
        · exact absurd ⟨hMa, hea⟩ hhd
        · unfold HasAllow at htl
          have hex : ∃ a, a ∈ tl ∧ Matches a r ∧ a.effect = .allow := ⟨a, hmem, hMa, hea⟩
          exact absurd hex htl

theorem probe_not_lt_aux (n m : Nat) (h : ¬ n < m) : m ≤ n := by
  exact Nat.le_of_not_gt h

theorem probe_step_denied_aux (s : State) (r : Request) (hv : validB s r = true) (hp : permittedB s.entries r = false) : (step s r).1 = .denied := by
  unfold step
  simp [hv, hp]

theorem overridden_not_permitted_aux (l : List Entry) (r : Request) : Overridden l r → ¬ Permitted l r := by
  intro hO hP
  obtain ⟨d, hmd, hMd, hed, hle⟩ := hO
  obtain ⟨a, hma, hMa, hea, hlt⟩ := hP
  have h1 : depth a ≤ depth d := hle a hma hMa hea
  have h2 : depth d < depth a := hlt d hmd hMd hed
  omega

theorem denied_perm_false_aux (s : State) (r : Request) (h : (step s r).1 = .denied) : permittedB s.entries r = false := by
  unfold step at h
  by_cases hv : validB s r = true
  · have hnot : (!validB s r) = false := by simp [hv]
    simp only [hnot, Bool.false_eq_true, reduceIte] at h ⊢
    cases hpb : permittedB s.entries r with
    | true => simp [hpb] at h
    | false => rfl
  · have hvf : validB s r = false := by cases hb : validB s r with | true => simp [hb] at hv | false => rfl
    have hnot : (!validB s r) = true := by simp [hvf]
    simp only [hnot, reduceIte] at h
    simp at h

theorem not_permitted_of_perm_false_aux2 (l : List Entry) (r : Request) (h : permittedB l r = false) : ¬ Permitted l r := by
  intro hP
  have ht : permittedB l r = true := (permittedB_true_iff_aux l r).mpr hP
  rw [ht] at h
  simp at h

theorem all_false_exists_aux (q : Entry → Bool) : ∀ (l : List Entry), l.all q = false → ∃ d ∈ l, q d = false := by
  intro l
  induction l with
  | nil =>
    intro h
    simp at h
  | cons hd tl ih =>
    intro h
    simp only [List.all_cons] at h
    simp only [Bool.and_eq_false_iff] at h
    cases h with
    | inl hq =>
      exact ⟨hd, List.Mem.head _, hq⟩
    | inr ht =>
      obtain ⟨d, hmem, hq⟩ := ih ht
      exact ⟨d, List.Mem.tail _ hmem, hq⟩

theorem any_mem_false_aux3 (f : Entry → Bool) (l : List Entry) (h : l.any f = false) (x : Entry) (hm : x ∈ l) : f x = false := by
  by_cases hfx : f x = true
  · have hex : ∃ y, y ∈ l ∧ f y = true := ⟨x, hm, hfx⟩
    have ht : l.any f = true := List.any_eq_true.mpr hex
    rw [ht] at h
    simp at h
  · cases hfx2 : f x with
    | true => simp [hfx2] at hfx
    | false => rfl

theorem bool_or_false_aux (x y : Bool) (h : (x || y) = false) : x = false ∧ y = false := by
  cases x <;> cases y <;> simp_all

theorem req_valid_answered     : ValidAnswered step := by
  intro s r h
  have hv : validB s r = true := validB_true_of_ValidQuery h
  unfold step
  simp only [hv, Bool.not_true]
  by_cases hp : permittedB s.entries r = true
  · simp [hp]
  · simp [hp]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hv : validB s r = false := validB_false_of_not_ValidQuery_aux h
  unfold step
  simp [hv]

theorem req_effects : Effects step := by
  intro s r hne
  unfold step at hne ⊢
  by_cases hv : validB s r = true
  · have hnot : (!validB s r) = false := by simp [hv]
    simp only [hnot] at hne ⊢
    by_cases hp : permittedB s.entries r
    · simp only [hp] at ⊢
      refine ⟨rfl, rfl, ?_⟩
      simp
    · simp only [hp] at ⊢
      refine ⟨rfl, rfl, ?_⟩
      simp
  · have hvf : validB s r = false := by
      cases hb : validB s r <;> simp_all
    have hnot : (!validB s r) = true := by simp [hvf]
    simp only [hnot] at hne ⊢
    simp at hne

theorem req_default_deny       : DefaultDeny step := by
  intro s r hNo hEq
  have hPermT : permittedB s.entries r = true := by
    unfold step at hEq
    by_cases hv : validB s r = true
    · have hnot : (!validB s r) = false := by simp [hv]
      simp only [hnot, Bool.false_eq_true, reduceIte] at hEq
      cases hpb : permittedB s.entries r with
      | true => rfl
      | false =>
        simp only [hpb, Bool.false_eq_true, reduceIte] at hEq
        simp at hEq
    · have hvf : validB s r = false := by cases hb : validB s r with | true => simp [hb] at hv | false => rfl
      have hnot : (!validB s r) = true := by simp [hvf]
      simp only [hnot, reduceIte] at hEq
      simp at hEq
  have hPerm : Permitted s.entries r := (permittedB_true_iff_aux _ _).mp hPermT
  obtain ⟨a, hm, hM, heff, _⟩ := hPerm
  exact hNo ⟨a, hm, hM, heff⟩

theorem req_deny_overrides     : DenyOverrides step := by
  intro s r hO hEq
  have hPermT : permittedB s.entries r = true := by
    unfold step at hEq
    by_cases hv : validB s r = true
    · have hnot : (!validB s r) = false := by simp [hv]
      simp only [hnot, Bool.false_eq_true, reduceIte] at hEq
      cases hpb : permittedB s.entries r with
      | true => rfl
      | false =>
        simp only [hpb, Bool.false_eq_true, reduceIte] at hEq
        simp at hEq
    · have hvf : validB s r = false := by cases hb : validB s r with | true => simp [hb] at hv | false => rfl
      have hnot : (!validB s r) = true := by simp [hvf]
      simp only [hnot, reduceIte] at hEq
      simp at hEq
  have hPerm : Permitted s.entries r := (permittedB_true_iff_aux _ _).mp hPermT
  exact (overridden_not_permitted_aux s.entries r hO) hPerm

theorem req_specific_allow : SpecificAllow step := by
  intro s r hV hP
  have hv : validB s r = true := validB_true_of_ValidQuery hV
  have hp : permittedB s.entries r = true := (permittedB_true_iff_aux s.entries r).mpr hP
  unfold step
  simp [hv, hp]

theorem req_grant_justified    : GrantJustified step := by
  intro s r hEq
  have hPermT : permittedB s.entries r = true := by
    unfold step at hEq
    by_cases hv : validB s r = true
    · have hnot : (!validB s r) = false := by simp [hv]
      simp only [hnot, Bool.false_eq_true, reduceIte] at hEq
      cases hpb : permittedB s.entries r with
      | true => rfl
      | false =>
        simp only [hpb, Bool.false_eq_true, reduceIte] at hEq
        simp at hEq
    · have hvf : validB s r = false := by cases hb : validB s r with | true => simp [hb] at hv | false => rfl
      have hnot : (!validB s r) = true := by simp [hvf]
      simp only [hnot, reduceIte] at hEq
      simp at hEq
  exact (permittedB_true_iff_aux _ _).mp hPermT

theorem req_order_independent  : OrderIndependent step := by
  intro s r l hperm
  unfold step
  have hv : validB { s with entries := l } r = validB s r := validB_entries_irrel4 s l r
  rw [hv]
  have hp : permittedB (({ s with entries := l } : State).entries) r = permittedB s.entries r := by
    have hentries : (({ s with entries := l } : State).entries) = l := rfl
    rw [hentries]
    exact permittedB_perm_aux4 l s.entries r hperm
  rw [hp]
  by_cases h1 : (!validB s r) = true
  · simp [h1]
  · simp [h1]
    by_cases h2 : permittedB s.entries r = true
    · simp [h2]
    · simp [h2]

theorem req_denial_explained   : DenialExplained step := by
  intro s r hDen
  have hPermF : permittedB s.entries r = false := denied_perm_false_aux s r hDen
  by_cases hHas : HasAllow s.entries r
  · right
    obtain ⟨a0, hm0, hM0, he0, hmax0⟩ := maximal_allow_auxDD s.entries r hHas
    have hmB0 : matchesB a0 r = true := (matchesB_iff_aux a0 r).mpr hM0
    have heB0 : decide (a0.effect = .allow) = true := by simp [he0]
    have hAny : s.entries.any (fun a => matchesB a r && decide (a.effect = .allow) && s.entries.all (fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (depth d < depth a))) = false := hPermF
    have hf0 : (matchesB a0 r && decide (a0.effect = .allow) && s.entries.all (fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (depth d < depth a0))) = false :=
      any_mem_false_aux3 _ s.entries hAny a0 hm0
    have hallF : s.entries.all (fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (depth d < depth a0)) = false := by
      simp only [hmB0, heB0, Bool.true_and] at hf0
      exact hf0
    obtain ⟨d, hmemd, hqd⟩ := all_false_exists_aux _ s.entries hallF
    have hpair := bool_or_false_aux _ _ hqd
    obtain ⟨hnot, hltF⟩ := hpair
    have hmand : (matchesB d r && decide (d.effect = .deny)) = true := by
      cases hb : (matchesB d r && decide (d.effect = .deny)) with
      | true => rfl
      | false => simp [hb] at hnot
    have hmBd : matchesB d r = true := (Bool.and_eq_true_iff.mp hmand).1
    have hdenB : decide (d.effect = .deny) = true := (Bool.and_eq_true_iff.mp hmand).2
    have hMd : Matches d r := (matchesB_iff_aux d r).mp hmBd
    have hed : d.effect = .deny := of_decide_eq_true hdenB
    have hnge : ¬ (depth d < depth a0) := of_decide_eq_false hltF
    have hle0 : depth a0 ≤ depth d := Nat.le_of_not_gt hnge
    exact ⟨d, hmemd, hMd, hed, fun a hma hMa hea => Nat.le_trans (hmax0 a hma hMa hea) hle0⟩
  · left
    exact hHas

end Acl
