import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance

def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def permittedB (l : List Entry) (r : Request) : Bool :=
  l.any (fun a =>
    matchesB a r && decide (a.effect = .allow) &&
    l.all (fun d =>
      !(matchesB d r && decide (d.effect = .deny)) || decide (depth d < depth a)
    )
  )

def step : Impl := fun s r =>
  if h : ValidQuery s r then
    let g := permittedB s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

private theorem aux_matchesB2 (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  simp only [Bool.and_eq_true_iff, Bool.or_eq_true_iff, beq_iff_eq, List.isPrefixOf_iff_prefix]

theorem permittedB_correct (l : List Entry) (r : Request) : permittedB l r = true ↔ Permitted l r := by
  unfold permittedB Permitted
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨a, ha_mem, ha_cond⟩ := h
    simp only [Bool.and_eq_true] at ha_cond
    obtain ⟨⟨hMb, hAb⟩, hAll⟩ := ha_cond
    have ha_match : Matches a r := (aux_matchesB2 a r).mp hMb
    have ha_eff : a.effect = .allow := of_decide_eq_true hAb
    refine ⟨a, ha_mem, ha_match, ha_eff, ?_⟩
    intro d hd_mem hd_match hd_eff
    have hd_mb : matchesB d r = true := (aux_matchesB2 d r).mpr hd_match
    have hd_effB : decide (d.effect = .deny) = true := by simp [hd_eff]
    have h1 := List.all_eq_true.mp hAll d hd_mem
    simp only [hd_mb, hd_effB, Bool.true_and] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    exact of_decide_eq_true h1
  · intro h
    obtain ⟨a, ha_mem, ha_match, ha_eff, ha_spec⟩ := h
    rw [List.any_eq_true]
    refine ⟨a, ha_mem, ?_⟩
    simp only [Bool.and_eq_true]
    have hmb : matchesB a r = true := (aux_matchesB2 a r).mpr ha_match
    refine ⟨⟨hmb, by simp [ha_eff]⟩, ?_⟩
    rw [List.all_eq_true]
    intro d hd_mem
    by_cases hm : matchesB d r = true
    · by_cases he : d.effect = .deny
      · have hd_match : Matches d r := (aux_matchesB2 d r).mp hm
        have hlt := ha_spec d hd_mem hd_match he
        have hdec : decide (depth d < depth a) = true := decide_eq_true hlt
        simp [hm, he, hdec]
      · simp [hm, he]
    · have heq : matchesB d r = false := by cases hmb2 : matchesB d r <;> simp_all
      simp [heq]

def matchingDenyAux2 (l : List Entry) (r : Request) : List Entry :=
  l.filter (fun e => matchesB e r && decide (e.effect = .deny))

theorem mem_matchingDenyAux2_iff (l : List Entry) (r : Request) (e : Entry) :
  e ∈ matchingDenyAux2 l r ↔ e ∈ l ∧ Matches e r ∧ e.effect = .deny := by
  unfold matchingDenyAux2
  rw [List.mem_filter]
  constructor
  · intro h
    obtain ⟨hmem, hcond⟩ := h
    simp only [Bool.and_eq_true_iff] at hcond
    obtain ⟨hMb, hEff⟩ := hcond
    exact ⟨hmem, (aux_matchesB2 e r).mp hMb, of_decide_eq_true hEff⟩
  · intro h
    obtain ⟨hmem, hMatch, hEff⟩ := h
    refine ⟨hmem, ?_⟩
    simp only [Bool.and_eq_true_iff]
    exact ⟨(aux_matchesB2 e r).mpr hMatch, by simp [hEff]⟩

theorem req_valid_answered : ValidAnswered step := by
  intro s r h
  simp only [step, h, dite_true]
  intro heq
  cases hp : permittedB s.entries r <;> simp_all

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp only [step, h, dite_false]

theorem req_effects : Effects step := by
  intro s r h
  simp only [step] at h ⊢
  by_cases hv : ValidQuery s r
  · simp only [hv, dite_true] at h ⊢
    refine ⟨?_, ?_, ?_⟩
    · simp
    · simp
    · simp
  · simp only [hv, dite_false] at h
    exact absurd rfl h

theorem req_default_deny : DefaultDeny step := by
  intro s r hNoAllow hGrant
  simp only [step] at hGrant
  by_cases hv : ValidQuery s r
  · simp only [hv, dite_true] at hGrant
    cases hp : permittedB s.entries r with
    | false =>
      simp [hp] at hGrant
    | true =>
      unfold permittedB at hp
      simp only [List.any_eq_true] at hp
      obtain ⟨a, ha_mem, ha_cond⟩ := hp
      simp only [Bool.and_eq_true_iff] at ha_cond
      obtain ⟨⟨hMb, hEffB⟩, _⟩ := ha_cond
      have hEff : a.effect = .allow := of_decide_eq_true hEffB
      have hMatches : Matches a r := by
        unfold matchesB Matches at *
        simp only [Bool.and_eq_true_iff] at hMb
        obtain ⟨hsubj, hpref⟩ := hMb
        simp only [Bool.or_eq_true_iff, beq_iff_eq] at hsubj
        exact ⟨hsubj, List.isPrefixOf_iff_prefix.mp hpref⟩
      exact hNoAllow ⟨a, ha_mem, hMatches, hEff⟩
  · simp only [hv, dite_false] at hGrant
    simp_all

theorem req_deny_overrides : DenyOverrides step := by
  intro s r ⟨d, hd_mem, hd_match, hd_eff, hd_depth⟩ hGrant
  simp only [step] at hGrant
  by_cases hv : ValidQuery s r
  · simp only [hv, dite_true] at hGrant
    have hGrantB : permittedB s.entries r = true := by cases hp : permittedB s.entries r; simp [hp] at hGrant; rfl
    unfold permittedB at hGrantB
    rw [List.any_eq_true] at hGrantB
    obtain ⟨a, ha_mem, ha_cond⟩ := hGrantB
    have hma_true : matchesB a r = true := by have h := ha_cond; simp only [Bool.and_eq_true_iff] at h; exact h.1.1
    have heff_true : decide (a.effect = .allow) = true := by have h := ha_cond; simp only [Bool.and_eq_true_iff] at h; exact h.1.2
    have hall_true : (s.entries.all fun d_2 => !(matchesB d_2 r && decide (d_2.effect = .deny)) || decide (depth d_2 < depth a)) = true := by have h := ha_cond; simp only [Bool.and_eq_true_iff] at h; exact h.2
    have ha_match : Matches a r := by
      have : (a.subject == 0 || a.subject == r.user) && a.path.isPrefixOf r.path = true := hma_true
      simp only [Bool.and_eq_true_iff, Bool.or_eq_true_iff, beq_iff_eq] at this
      obtain ⟨hsubj, hpref⟩ := this
      exact ⟨hsubj, List.isPrefixOf_iff_prefix.mp hpref⟩
    have ha_eff : a.effect = .allow := of_decide_eq_true heff_true
    have hle : depth a ≤ depth d := hd_depth a ha_mem ha_match ha_eff
    have hd_matchB : matchesB d r = true := by
      have h1 := hd_match.1; have h2 := hd_match.2
      unfold matchesB; simp only [Bool.and_eq_true_iff, Bool.or_eq_true_iff, beq_iff_eq]; exact ⟨h1, List.isPrefixOf_iff_prefix.mpr h2⟩
    have hd_effB : decide (d.effect = .deny) = true := by simp [hd_eff]
    have hall_d : (!(matchesB d r && decide (d.effect = .deny)) || decide (depth d < depth a)) = true := List.all_eq_true.mp hall_true d hd_mem
    simp [hd_matchB, hd_effB] at hall_d
    exact absurd hall_d (by simp [Nat.not_lt.mpr hle])
  · simp only [hv, dite_false] at hGrant; exact absurd hGrant (by decide)

theorem req_specific_allow : SpecificAllow step := by
  intro s r hv hPerm
  simp only [step, hv, dite_true]
  have hgoal : permittedB s.entries r = true := by
    unfold permittedB
    obtain ⟨a, ha_mem, ha_match, ha_eff, ha_spec⟩ := hPerm
    rw [List.any_eq_true]
    refine ⟨a, ha_mem, ?_⟩
    have hmb : matchesB a r = true := (aux_matchesB2 a r).mpr ha_match
    simp only [Bool.and_eq_true_iff]
    refine ⟨⟨hmb, ?_⟩, ?_⟩
    · simp [ha_eff]
    · rw [List.all_eq_true]
      intro d hd_mem
      by_cases hm : matchesB d r = true
      · by_cases he : d.effect = .deny
        · have : Matches d r := (aux_matchesB2 d r).mp hm
          have hlt := ha_spec d hd_mem this he
          simp [hm, he, hlt]
        · simp [hm, he]
      · simp [hm]
  simp [hgoal]

theorem req_grant_justified : GrantJustified step := by
  intro s r hGrant
  simp only [step] at hGrant
  by_cases hv : ValidQuery s r
  · simp only [hv, dite_true] at hGrant
    have hpb : permittedB s.entries r = true := by
      cases hp : permittedB s.entries r with
      | true => rfl
      | false => simp [hp] at hGrant
    exact (permittedB_correct s.entries r).mp hpb
  · simp only [hv, dite_false] at hGrant
    simp_all

theorem req_order_independent : OrderIndependent step := by
  intro s r l hPerm
  simp only [step]
  have hv_eq : ValidQuery { s with entries := l } r ↔ ValidQuery s r := by
    unfold ValidQuery
    simp
  by_cases hv : ValidQuery s r
  · have hv2 : ValidQuery { s with entries := l } r := hv_eq.mpr hv
    simp only [hv, hv2, dite_true]
    have hperm_eq : permittedB l r = permittedB s.entries r := by
      have hiff : (permittedB l r = true) ↔ (permittedB s.entries r = true) := by
        constructor
        · intro h1
          have hP : Permitted l r := (permittedB_correct l r).mp h1
          have hP2 : Permitted s.entries r := by
            obtain ⟨a, ha_mem, ha_match, ha_eff, ha_spec⟩ := hP
            have ha_mem2 : a ∈ s.entries := hPerm.mem_iff.mp ha_mem
            refine ⟨a, ha_mem2, ha_match, ha_eff, ?_⟩
            intro d hd_mem hd_match hd_eff2
            have hd_mem_l : d ∈ l := hPerm.mem_iff.mpr hd_mem
            exact ha_spec d hd_mem_l hd_match hd_eff2
          exact (permittedB_correct s.entries r).mpr hP2
        · intro h1
          have hP : Permitted s.entries r := (permittedB_correct s.entries r).mp h1
          obtain ⟨a, ha_mem, ha_match, ha_eff, ha_spec⟩ := hP
          have ha_mem2 : a ∈ l := hPerm.mem_iff.mpr ha_mem
          have hP2 : Permitted l r := by
            refine ⟨a, ha_mem2, ha_match, ha_eff, ?_⟩
            intro d hd_mem hd_match hd_eff2
            have hd_mem_s : d ∈ s.entries := hPerm.mem_iff.mp hd_mem
            exact ha_spec d hd_mem_s hd_match hd_eff2
          exact (permittedB_correct l r).mpr hP2
      cases h1 : permittedB l r <;> cases h2 : permittedB s.entries r <;> simp_all
    simp [hperm_eq]
  · have hv2 : ¬ ValidQuery { s with entries := l } r := by
      intro h; exact hv (hv_eq.mp h)
    simp [hv, hv2]

private theorem exists_max_depth (l : List Entry) (hne : l ≠ []) :
    ∃ m ∈ l, ∀ x ∈ l, depth x ≤ depth m := by
  induction l with
  | nil => exact absurd rfl hne
  | cons hd tl ih =>
    by_cases htl : tl = []
    · subst htl
      refine ⟨hd, by simp, ?_⟩
      intro x hx
      simp at hx
      subst hx
      exact Nat.le_refl _
    · have hne_tl : tl ≠ [] := htl
      obtain ⟨m, hm_mem, hm_max⟩ := ih hne_tl
      by_cases hle : depth hd ≤ depth m
      · refine ⟨m, List.mem_cons.mpr (Or.inr hm_mem), ?_⟩
        intro x hx
        have hx' := hx
        rw [List.mem_cons] at hx
        cases hx with
        | inl heq =>
          subst heq
          exact hle
        | inr hmem =>
          exact hm_max x hmem
      · refine ⟨hd, List.mem_cons.mpr (Or.inl rfl), ?_⟩
        intro x hx
        rw [List.mem_cons] at hx
        cases hx with
        | inl heq =>
          subst heq
          exact Nat.le_refl _
        | inr hmem =>
          have h1 := hm_max x hmem
          have hlt : depth m < depth hd := Nat.lt_of_not_ge hle
          exact Nat.le_trans h1 (Nat.le_of_lt hlt)

theorem req_denial_explained : DenialExplained step := by
  intro s r hDenied
  have hStep : (step s r).1 = .denied := hDenied
  simp only [step] at hStep
  by_cases hv : ValidQuery s r
  · simp only [hv, dite_true] at hStep
    have hperm_false : permittedB s.entries r = false := by
      cases hp : permittedB s.entries r with
      | true => simp [hp] at hStep
      | false => rfl
    have hNotPerm : ¬ Permitted s.entries r := by
      intro hP
      have := (permittedB_correct s.entries r).mpr hP
      rw [this] at hperm_false
      contradiction
    by_cases hHas : HasAllow s.entries r
    · right
      have hForallBlocked : ∀ a ∈ s.entries, Matches a r → a.effect = .allow → ∃ d ∈ s.entries, Matches d r ∧ d.effect = .deny ∧ depth a ≤ depth d := by
        intro a ha_mem ha_match ha_eff
        apply Classical.byContradiction
        intro hNone
        have hPerm : Permitted s.entries r := by
          refine ⟨a, ha_mem, ha_match, ha_eff, ?_⟩
          intro d hd_mem hd_match hd_eff
          have hNotLE : ¬ depth a ≤ depth d := by
            intro hle
            apply hNone
            exact ⟨d, hd_mem, hd_match, hd_eff, hle⟩
          exact Nat.lt_of_not_ge hNotLE
        exact hNotPerm hPerm
      obtain ⟨a0, ha0_mem, ha0_match, ha0_eff⟩ := hHas
      obtain ⟨d0, hd0_mem, hd0_match, hd0_eff, _hd0_le⟩ := hForallBlocked a0 ha0_mem ha0_match ha0_eff
      let Ds := matchingDenyAux2 s.entries r
      have hDs_mem_d0 : d0 ∈ Ds := (mem_matchingDenyAux2_iff s.entries r d0).mpr ⟨hd0_mem, hd0_match, hd0_eff⟩
      have hDs_ne : Ds ≠ [] := by
        intro hnil
        have : d0 ∈ Ds := hDs_mem_d0
        rw [hnil] at this
        simp at this
      obtain ⟨m, hm_mem_ds, hm_max⟩ := exists_max_depth Ds hDs_ne
      have hm_prop := (mem_matchingDenyAux2_iff s.entries r m).mp hm_mem_ds
      obtain ⟨hm_mem, hm_match, hm_eff⟩ := hm_prop
      refine ⟨m, hm_mem, hm_match, hm_eff, ?_⟩
      intro a ha_mem ha_match ha_eff
      obtain ⟨d, hd_mem, hd_match, hd_eff, hd_le⟩ := hForallBlocked a ha_mem ha_match ha_eff
      have hd_in_ds : d ∈ Ds := (mem_matchingDenyAux2_iff s.entries r d).mpr ⟨hd_mem, hd_match, hd_eff⟩
      have hle1 : depth d ≤ depth m := hm_max d hd_in_ds
      exact Nat.le_trans hd_le hle1
    · left; exact hHas
  · simp only [hv, dite_false] at hStep
    simp at hStep

end Acl
