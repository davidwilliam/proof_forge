import Acl.Spec
namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance

instance instDecidableMatches (e : Entry) (r : Request) : Decidable (Matches e r) := by
  unfold Matches; infer_instance

instance instDecidablePermitted (l : List Entry) (r : Request) : Decidable (Permitted l r) := by
  unfold Permitted; infer_instance

instance instDecidableHasAllow (l : List Entry) (r : Request) : Decidable (HasAllow l r) := by
  unfold HasAllow; infer_instance

instance instDecidableOverridden (l : List Entry) (r : Request) : Decidable (Overridden l r) := by
  unfold Overridden; infer_instance

def permittedB (l : List Entry) (r : Request) : Bool :=
  decide (Permitted l r)

theorem permittedB_true_iff (l : List Entry) (r : Request) :
    permittedB l r = true ↔ Permitted l r := by
  unfold permittedB; simp

theorem permittedB_false_iff (l : List Entry) (r : Request) :
    permittedB l r = false ↔ ¬ Permitted l r := by
  unfold permittedB; simp

def step : Impl := fun s r =>
  if ValidQuery s r then
    let g := permittedB s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem Permitted_perm {l l' : List Entry} (hperm : l.Perm l') (r : Request) :
    Permitted l r ↔ Permitted l' r := by
  unfold Permitted
  constructor
  · rintro ⟨a, ha, hm, heAllow, hall⟩
    exact ⟨a, hperm.mem_iff.mp ha, hm, heAllow, fun d hd hmd hed => hall d (hperm.mem_iff.mpr hd) hmd hed⟩
  · rintro ⟨a, ha, hm, heAllow, hall⟩
    exact ⟨a, hperm.mem_iff.mpr ha, hm, heAllow, fun d hd hmd hed => hall d (hperm.mem_iff.mp hd) hmd hed⟩

theorem overridden_not_permitted {l : List Entry} {r : Request} (h : Overridden l r) : ¬ Permitted l r := by
  intro hp
  obtain ⟨a, ha, hma, hea, hallP⟩ := hp
  obtain ⟨d, hd, hmd, hed, hallO⟩ := h
  have h1 : depth d < depth a := hallP d hd hmd hed
  have h2 : depth a ≤ depth d := hallO a ha hma hea
  omega

theorem not_hasAllow_not_permitted {l : List Entry} {r : Request} (h : ¬ HasAllow l r) : ¬ Permitted l r := by
  intro hp
  obtain ⟨a, ha, hma, hea, _⟩ := hp
  exact h ⟨a, ha, hma, hea⟩

theorem exists_max_deny (l : List Entry) (r : Request)
    (hex : ∃ d ∈ l, Matches d r ∧ d.effect = .deny) :
    ∃ dmax ∈ l, Matches dmax r ∧ dmax.effect = .deny ∧
      ∀ d ∈ l, Matches d r ∧ d.effect = .deny → depth d ≤ depth dmax := by
  induction l with
  | nil => simp at hex
  | cons hd tl ih =>
    simp only [List.mem_cons] at hex ⊢
    by_cases hhd : Matches hd r ∧ hd.effect = .deny
    · by_cases htl : ∃ d ∈ tl, Matches d r ∧ d.effect = .deny
      · obtain ⟨dmax, hmem, hm, he, hmax⟩ := ih htl
        by_cases hle : depth hd ≤ depth dmax
        · refine ⟨dmax, Or.inr hmem, hm, he, ?_⟩
          intro d hdmem hdprop
          rcases hdmem with rfl | hmem'
          · exact hle
          · exact hmax d hmem' hdprop
        · refine ⟨hd, Or.inl rfl, hhd.1, hhd.2, ?_⟩
          intro d hdmem hdprop
          rcases hdmem with rfl | hmem'
          · omega
          · have := hmax d hmem' hdprop; omega
      · refine ⟨hd, Or.inl rfl, hhd.1, hhd.2, ?_⟩
        intro d hdmem hdprop
        rcases hdmem with rfl | hmem'
        · omega
        · exfalso; exact htl ⟨d, hmem', hdprop⟩
    · have htl : ∃ d ∈ tl, Matches d r ∧ d.effect = .deny := by
        obtain ⟨d, hmem, hprop⟩ := hex
        rcases hmem with rfl | hmem'
        · exact absurd hprop hhd
        · exact ⟨d, hmem', hprop⟩
      obtain ⟨dmax, hmem, hm, he, hmax⟩ := ih htl
      refine ⟨dmax, Or.inr hmem, hm, he, ?_⟩
      intro d hdmem hdprop
      rcases hdmem with rfl | hmem'
      · exfalso; exact hhd hdprop
      · exact hmax d hmem' hdprop

theorem not_permitted_imp_overridden_or_not_hasAllow (l : List Entry) (r : Request)
    (h : ¬ Permitted l r) : ¬ HasAllow l r ∨ Overridden l r := by
  by_cases hhas : HasAllow l r
  · right
    have hdeny_exists : ∃ d ∈ l, Matches d r ∧ d.effect = .deny := by
      by_cases hex : ∃ d ∈ l, Matches d r ∧ d.effect = .deny
      · exact hex
      · exfalso
        have hperm : Permitted l r := by
          obtain ⟨a, ha, hma, hea⟩ := hhas
          refine ⟨a, ha, hma, hea, ?_⟩
          intro d hd hmd hed
          exact False.elim (hex ⟨d, hd, hmd, hed⟩)
        exact h hperm
    obtain ⟨dmax, hdmax_mem, hdmax_match, hdmax_eff, hdmax_max⟩ := exists_max_deny l r hdeny_exists
    refine ⟨dmax, hdmax_mem, hdmax_match, hdmax_eff, ?_⟩
    intro a ha hma hea
    by_cases hle : depth a ≤ depth dmax
    · exact hle
    · exfalso
      have hlt : depth dmax < depth a := Nat.lt_of_not_ge hle
      have hall : ∀ d ∈ l, Matches d r → d.effect = .deny → depth d < depth a := by
        intro d hd hmd hed
        have h1 : depth d ≤ depth dmax := hdmax_max d hd ⟨hmd, hed⟩
        omega
      exact h ⟨a, ha, hma, hea, hall⟩
  · left; exact hhas

theorem req_valid_answered : ValidAnswered step := by
  unfold ValidAnswered step
  intro s r hvalid hEq
  simp only [hvalid, ↓reduceIte] at hEq
  cases hg : permittedB s.entries r with
  | true => simp [hg] at hEq
  | false => simp [hg] at hEq

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop step
  intro s r hinvalid
  simp [hinvalid]

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hne
  by_cases h : ValidQuery s r
  · unfold step
    simp only [h, ↓reduceIte]
    have hdec : decide ((if permittedB s.entries r then Outcome.granted else Outcome.denied) = Outcome.granted) = permittedB s.entries r := by
      cases hg : permittedB s.entries r <;> simp [hg]
    simp [hdec]
  · exfalso
    unfold step at hne
    simp [h] at hne

theorem req_default_deny : DefaultDeny step := by
  unfold DefaultDeny
  intro s r hno hgr
  have hnp : ¬ Permitted s.entries r := not_hasAllow_not_permitted hno
  have hpb : permittedB s.entries r = false := (permittedB_false_iff _ _).mpr hnp
  unfold step at hgr
  by_cases h : ValidQuery s r
  · simp [h, hpb] at hgr
  · simp [h] at hgr

theorem req_deny_overrides : DenyOverrides step := by
  unfold DenyOverrides
  intro s r hover hgr
  have hnp : ¬ Permitted s.entries r := overridden_not_permitted hover
  have hpb : permittedB s.entries r = false := (permittedB_false_iff _ _).mpr hnp
  unfold step at hgr
  by_cases h : ValidQuery s r
  · simp [h, hpb] at hgr
  · simp [h] at hgr

theorem req_specific_allow : SpecificAllow step := by
  unfold SpecificAllow
  intro s r hvalid hperm
  have hpb : permittedB s.entries r = true := (permittedB_true_iff _ _).mpr hperm
  unfold step
  simp [hvalid, hpb]

theorem req_grant_justified : GrantJustified step := by
  unfold GrantJustified
  intro s r hgr
  unfold step at hgr
  by_cases h : ValidQuery s r
  · simp only [h, ↓reduceIte] at hgr
    have hg : permittedB s.entries r = true := by
      cases hc : permittedB s.entries r with
      | true => rfl
      | false => simp [hc] at hgr
    exact (permittedB_true_iff _ _).mp hg
  · simp [h] at hgr

theorem req_order_independent : OrderIndependent step := by
  unfold OrderIndependent
  intro s r l hperm
  have hperm_eq : Permitted l r ↔ Permitted s.entries r := Permitted_perm hperm r
  have hbool_eq : permittedB l r = permittedB s.entries r := by
    have h1 : permittedB l r = true ↔ permittedB s.entries r = true := by
      simp [permittedB_true_iff, hperm_eq]
    by_cases hl : permittedB l r <;> by_cases hs : permittedB s.entries r <;> simp_all
  unfold step
  by_cases h : ValidQuery s r
  · have h2 : ValidQuery { s with entries := l } r := by
      unfold ValidQuery at h ⊢; exact h
    simp [h, h2, hbool_eq]
  · have h2 : ¬ ValidQuery { s with entries := l } r := by
      unfold ValidQuery at h ⊢; simp [h]
    simp [h, h2]

theorem req_denial_explained : DenialExplained step := by
  unfold DenialExplained
  intro s r hden
  unfold step at hden
  by_cases h : ValidQuery s r
  · simp only [h, ↓reduceIte] at hden
    have hg : permittedB s.entries r = false := by
      cases hc : permittedB s.entries r with
      | false => rfl
      | true => simp [hc] at hden
    have hnp : ¬ Permitted s.entries r := (permittedB_false_iff _ _).mp hg
    exact not_permitted_imp_overridden_or_not_hasAllow s.entries r hnp
  · simp [h] at hden

end Acl
