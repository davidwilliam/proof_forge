import Acl.Spec

namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance

def matchesB (e : Entry) (r : Request) : Bool :=
  decide (e.subject = 0 ∨ e.subject = r.user) && decide (e.path <+: r.path)

theorem matchesB_true_iff (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches; simp

def permittedB (l : List Entry) (r : Request) : Bool :=
  l.any fun a =>
    (matchesB a r && decide (a.effect = .allow)) &&
    l.all fun d => decide (depth d < depth a) || !(matchesB d r && decide (d.effect = .deny))

theorem permittedB_iff (l : List Entry) (r : Request) :
    permittedB l r = true ↔ Permitted l r := by
  unfold permittedB Permitted
  simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨a, ha_mem, h1, hall⟩
    refine ⟨a, ha_mem, (matchesB_true_iff a r).mp h1.1, h1.2, fun d hd_mem hdM hdE2 => ?_⟩
    have h := hall d hd_mem
    have hb1 : matchesB d r = true := (matchesB_true_iff d r).mpr hdM
    have hb2 : decide (d.effect = .deny) = true := by simp [hdE2]
    simp only [hb1, hb2] at h
    simp at h; exact h
  · rintro ⟨a, ha_mem, haM, haE, hall⟩
    refine ⟨a, ha_mem, ⟨(matchesB_true_iff a r).mpr haM, haE⟩, fun d hd_mem => ?_⟩
    simp only [Bool.or_eq_true]
    by_cases hM : matchesB d r = true
    · by_cases hE : decide (d.effect = .deny) = true
      · have hdM : Matches d r := (matchesB_true_iff d r).mp hM
        have hdE : d.effect = Effect.deny := by simpa using hE
        have hlt : depth d < depth a := hall d hd_mem hdM hdE
        left; simp [hlt]
      · simp [hM, hE]
    · simp [hM]

theorem permitted_implies_hasAllow {l : List Entry} {r : Request} :
    Permitted l r → HasAllow l r := by
  rintro ⟨a, ha_mem, haM, haE, _⟩; exact ⟨a, ha_mem, haM, haE⟩

theorem overridden_implies_not_permitted {l : List Entry} {r : Request} :
    Overridden l r → ¬ Permitted l r := by
  intro hO hP
  obtain ⟨d, hd_mem, hdM, hdE, hd_le⟩ := hO
  obtain ⟨a, ha_mem, haM, haE, ha_lt⟩ := hP
  have hle := hd_le a ha_mem haM haE
  have hlt := ha_lt d hd_mem hdM hdE; omega

theorem permitted_perm {l₁ l₂ : List Entry} (hPerm : l₁.Perm l₂) (r : Request) :
    Permitted l₁ r ↔ Permitted l₂ r := by
  unfold Permitted
  constructor
  · rintro ⟨a, ha_mem, haM, haE, hall⟩
    exact ⟨a, hPerm.mem_iff.mp ha_mem, haM, haE, fun d hd_mem hdM hdE => hall d (hPerm.mem_iff.mpr hd_mem) hdM hdE⟩
  · rintro ⟨a, ha_mem, haM, haE, hall⟩
    exact ⟨a, hPerm.mem_iff.mpr ha_mem, haM, haE, fun d hd_mem hdM hdE => hall d (hPerm.mem_iff.mp hd_mem) hdM hdE⟩

theorem permittedB_perm (l₁ l₂ : List Entry) (hPerm : l₁.Perm l₂) (r : Request) :
    permittedB l₁ r = permittedB l₂ r := by
  have hIff : Permitted l₁ r ↔ Permitted l₂ r := permitted_perm hPerm r
  have h1 := permittedB_iff l₁ r
  have h2 := permittedB_iff l₂ r
  have hEq : (permittedB l₁ r = true) ↔ (permittedB l₂ r = true) := by
    rw [h1, h2, hIff]
  cases hc1 : permittedB l₁ r <;> cases hc2 : permittedB l₂ r <;> simp_all

theorem exists_max_deny (l : List Entry) (r : Request)
    (h : ∃ d ∈ l, Matches d r ∧ d.effect = .deny) :
    ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧
      ∀ d' ∈ l, Matches d' r → d'.effect = .deny → depth d' ≤ depth d := by
  induction l with
  | nil => obtain ⟨d, hd_mem, _⟩ := h; simp at hd_mem
  | cons hd tl ih =>
    by_cases hhd : Matches hd r ∧ hd.effect = .deny
    · by_cases htl : ∃ d ∈ tl, Matches d r ∧ d.effect = .deny
      · obtain ⟨d₀, hd₀_mem, hd₀M, hd₀E, hd₀max⟩ := ih htl
        by_cases hle : depth hd ≤ depth d₀
        · refine ⟨d₀, List.mem_cons.mpr (Or.inr hd₀_mem), hd₀M, hd₀E, fun d' hd'_mem hd'M hd'E => ?_⟩
          rcases List.mem_cons.mp hd'_mem with heq | hmem
          · subst heq; exact hle
          · exact hd₀max d' hmem hd'M hd'E
        · refine ⟨hd, List.mem_cons.mpr (Or.inl rfl), hhd.1, hhd.2, fun d' hd'_mem hd'M hd'E => ?_⟩
          rcases List.mem_cons.mp hd'_mem with heq | hmem
          · subst heq; exact Nat.le_refl _
          · have hle' := hd₀max d' hmem hd'M hd'E; omega
      · refine ⟨hd, List.mem_cons.mpr (Or.inl rfl), hhd.1, hhd.2, fun d' hd'_mem hd'M hd'E => ?_⟩
        rcases List.mem_cons.mp hd'_mem with heq | hmem
        · subst heq; exact Nat.le_refl _
        · exfalso; exact htl ⟨d', hmem, hd'M, hd'E⟩
    · have htl : ∃ d ∈ tl, Matches d r ∧ d.effect = .deny := by
        obtain ⟨d, hd_mem, hdM, hdE⟩ := h
        rcases List.mem_cons.mp hd_mem with heq | hmem
        · subst heq; exact absurd ⟨hdM, hdE⟩ hhd
        · exact ⟨d, hmem, hdM, hdE⟩
      obtain ⟨d₀, hd₀_mem, hd₀M, hd₀E, hd₀max⟩ := ih htl
      refine ⟨d₀, List.mem_cons.mpr (Or.inr hd₀_mem), hd₀M, hd₀E, fun d' hd'_mem hd'M hd'E => ?_⟩
      rcases List.mem_cons.mp hd'_mem with heq | hmem
      · subst heq; exact absurd ⟨hd'M, hd'E⟩ hhd
      · exact hd₀max d' hmem hd'M hd'E

theorem notPerm_hasAllow_overridden (l : List Entry) (r : Request)
    (hHas : HasAllow l r) (hNotPerm : ¬ Permitted l r) : Overridden l r := by
  have hDenyExists : ∃ d ∈ l, Matches d r ∧ d.effect = .deny := by
    by_cases hEx : ∃ d ∈ l, Matches d r ∧ d.effect = .deny
    · exact hEx
    · exfalso; apply hNotPerm
      obtain ⟨a, ha_mem, haM, haE⟩ := hHas
      refine ⟨a, ha_mem, haM, haE, fun d hd_mem hdM hdE => ?_⟩
      exfalso; exact hEx ⟨d, hd_mem, hdM, hdE⟩
  obtain ⟨dmax, hdmax_mem, hdmaxM, hdmaxE, hdmax_le⟩ := exists_max_deny l r hDenyExists
  refine ⟨dmax, hdmax_mem, hdmaxM, hdmaxE, fun a ha_mem haM haE => ?_⟩
  by_cases hle : depth a ≤ depth dmax
  · exact hle
  · exfalso; apply hNotPerm
    have hlt : depth dmax < depth a := Nat.lt_of_not_ge hle
    exact ⟨a, ha_mem, haM, haE, fun d hd_mem hdM hdE2 => by
      have hle2 := hdmax_le d hd_mem hdM hdE2; omega⟩

def step : Impl := fun s r =>
  if ValidQuery s r then
    if permittedB s.entries r then
      (.granted, { s with log := s.log ++ [({ user := r.user, path := r.path, granted := true } : Record)] })
    else
      (.denied, { s with log := s.log ++ [({ user := r.user, path := r.path, granted := false } : Record)] })
  else
    (.rejected, s)

theorem req_valid_answered : ValidAnswered step := by
  intro s r hV; show (step s r).1 ≠ .rejected
  simp only [step, hV, ↓reduceIte]; split <;> intro h <;> cases h

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hInv; show step s r = (.rejected, s); simp [step, hInv]

theorem req_effects : Effects step := by
  intro s r hNe; show (step s r).2.users = s.users ∧ (step s r).2.entries = s.entries ∧ (step s r).2.log = s.log ++ [({ user := r.user, path := r.path, granted := decide ((step s r).1 = .granted) } : Record)]
  simp only [step] at hNe ⊢
  by_cases hv : ValidQuery s r
  · simp only [hv, ↓reduceIte]; by_cases hp : permittedB s.entries r = true <;> simp [hp]
  · simp [hv] at hNe

theorem req_default_deny : DefaultDeny step := by
  intro s r hNoAllow; show (step s r).1 ≠ .granted
  simp only [step]; by_cases hv : ValidQuery s r
  · simp only [hv, ↓reduceIte]; by_cases hp : permittedB s.entries r = true
    · simp only [hp, ↓reduceIte]; have hP : Permitted s.entries r := (permittedB_iff s.entries r).mp hp
      intro h; exact hNoAllow (permitted_implies_hasAllow hP)
    · simp [hp]
  · simp [hv]

theorem req_deny_overrides : DenyOverrides step := by
  intro s r hOver; show (step s r).1 ≠ .granted
  simp only [step]; by_cases hv : ValidQuery s r
  · simp only [hv, ↓reduceIte]; by_cases hp : permittedB s.entries r = true
    · simp only [hp, ↓reduceIte]; intro h
      have hP : Permitted s.entries r := (permittedB_iff s.entries r).mp hp
      exact (overridden_implies_not_permitted hOver) hP
    · simp [hp]
  · simp [hv]

theorem req_specific_allow : SpecificAllow step := by
  intro s r hV hPerm; show (step s r).1 = .granted
  simp [step, hV, (permittedB_iff s.entries r).mpr hPerm]

theorem req_grant_justified : GrantJustified step := by
  intro s r hGrant; show Permitted s.entries r
  have : (step s r).1 = .granted := hGrant; simp only [step] at this
  by_cases hv : ValidQuery s r
  · simp only [hv, ↓reduceIte] at this; by_cases hp : permittedB s.entries r = true
    · exact (permittedB_iff s.entries r).mp hp
    · simp [hp] at this
  · simp [hv] at this

theorem req_order_independent : OrderIndependent step := by
  intro s r l hPerm; show (step { s with entries := l } r).1 = (step s r).1
  simp only [step]
  have hv_eq : ValidQuery s r ↔ ValidQuery { s with entries := l } r := by simp [ValidQuery]
  have hb : permittedB l r = permittedB s.entries r := permittedB_perm l s.entries hPerm r
  by_cases hv : ValidQuery s r
  · have hv2 : ValidQuery { s with entries := l } r := hv_eq.mp hv
    simp only [hv, hv2, ↓reduceIte, hb]; cases h : permittedB s.entries r <;> simp
  · have hv2 : ¬ ValidQuery { s with entries := l } r := fun h => hv (hv_eq.mpr h)
    simp only [hv, hv2, ↓reduceIte]

theorem req_denial_explained : DenialExplained step := by
  intro s r hDen; show ¬HasAllow s.entries r ∨ Overridden s.entries r
  have hDen' : (step s r).1 = .denied := hDen; simp only [step] at hDen'
  by_cases hv : ValidQuery s r
  · simp only [hv, ↓reduceIte] at hDen'
    by_cases hpb : permittedB s.entries r = true
    · simp [hpb] at hDen'
    · simp [hpb] at hDen'
      have hNotPerm : ¬ Permitted s.entries r := by
        intro hP; have : permittedB s.entries r = true := (permittedB_iff s.entries r).mpr hP
        rw [this] at hpb; contradiction
      by_cases hHas : HasAllow s.entries r
      · exact Or.inr (notPerm_hasAllow_overridden s.entries r hHas hNotPerm)
      · exact Or.inl hHas
  · simp [hv] at hDen'

end Acl
