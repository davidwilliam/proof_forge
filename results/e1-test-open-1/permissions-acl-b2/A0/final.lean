import Acl.Spec
namespace Acl
instance decValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool := (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path
theorem matchesB_iff {e r} : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches; simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h; exact ⟨by rcases h.1 with h1|h1; exact Or.inl h1; exact Or.inr h1, List.isPrefixOf_iff_prefix.mp h.2⟩
  · intro h; exact ⟨by rcases h.1 with h1|h1; exact Or.inl h1; exact Or.inr h1, List.isPrefixOf_iff_prefix.mpr h.2⟩
theorem not_matchesB_iff {e r} : matchesB e r = false ↔ ¬ Matches e r := by
  have h := matchesB_iff (e:=e) (r:=r); cases hm : matchesB e r <;> simp_all
def permittedB (l : List Entry) (r : Request) : Bool :=
  l.any fun a => matchesB a r && (a.effect == .allow) && l.all fun d => (!(matchesB d r && (d.effect == .deny)) || decide (d.path.length < a.path.length))
theorem permittedB_true_iff {l r} : permittedB l r = true ↔ Permitted l r := by
  unfold permittedB Permitted depth; simp only [List.any_eq_true, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · intro h; obtain ⟨a, ha, ⟨⟨hMb, hEa⟩, hall⟩⟩ := h
    refine ⟨a, ha, matchesB_iff.mp hMb, hEa, ?_⟩
    intro d hd hdm hde
    have hb : matchesB d r = true := matchesB_iff.mpr hdm
    have hbe : (d.effect == Effect.deny) = true := by simp [hde]
    have hd0 := hall d hd; simp [hb, hbe] at hd0; exact hd0
  · intro h; obtain ⟨a, ha, hm, he, hall⟩ := h
    refine ⟨a, ha, ⟨⟨matchesB_iff.mpr hm, he⟩, ?_⟩⟩
    intro d hd
    by_cases hdm : Matches d r
    · by_cases hde : d.effect = Effect.deny
      · have hlt := hall d hd hdm hde; simp [matchesB_iff.mpr hdm, hde, hlt]
      · have hbeF : (d.effect == Effect.deny) = false := by cases heq : d.effect with | allow => rfl | deny => exact absurd heq hde
        have hMb : matchesB d r = true := matchesB_iff.mpr hdm; simp [hMb, hbeF]
    · have hMbF : matchesB d r = false := not_matchesB_iff.mpr hdm; simp [hMbF]
def step : Impl := fun s r =>
  if _ : ValidQuery s r then
    match permittedB s.entries r with
    | true => (.granted, { s with log := s.log ++ [⟨r.user, r.path, true⟩] })
    | false => (.denied, { s with log := s.log ++ [⟨r.user, r.path, false⟩] })
  else (.rejected, s)
theorem step_valid_eq (s : State) (r : Request) (hV : ValidQuery s r) :
  step s r = match permittedB s.entries r with | true => (.granted, { s with log := s.log ++ [⟨r.user, r.path, true⟩] }) | false => (.denied, { s with log := s.log ++ [⟨r.user, r.path, false⟩] }) := by simp [step, hV]
theorem step_fst_valid (s : State) (r : Request) (hV : ValidQuery s r) :
  (step s r).1 = match permittedB s.entries r with | true => Outcome.granted | false => Outcome.denied := by
  rw [step_valid_eq s r hV]; cases permittedB s.entries r <;> rfl
theorem permitted_imp_hasAllow {l r} (h : Permitted l r) : HasAllow l r := by obtain ⟨a, ha, hm, he, _⟩ := h; exact ⟨a, ha, hm, he⟩
theorem overridden_imp_notPermitted {l r} : Overridden l r → ¬ Permitted l r := by
  intro hO hP; obtain ⟨d, hd, hdm, hde, hall⟩ := hO; obtain ⟨a, ha, ham, hae, hall2⟩ := hP
  have h1 := hall a ha ham hae; have h2 := hall2 d hd hdm hde; omega
def deniesB (l : List Entry) (r : Request) : List Entry := l.filter fun e => matchesB e r && (e.effect == .deny)
theorem deniesB_mem_iff {l r e} : e ∈ deniesB l r ↔ e ∈ l ∧ Matches e r ∧ e.effect = .deny := by
  unfold deniesB; simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h; exact ⟨h.1, matchesB_iff.mp h.2.1, h.2.2⟩
  · intro h; exact ⟨h.1, ⟨matchesB_iff.mpr h.2.1, h.2.2⟩⟩
theorem exists_max (l : List Entry) (hne : l ≠ []) : ∃ m ∈ l, ∀ y ∈ l, y.path.length ≤ m.path.length := by
  induction l with
  | nil => simp at hne
  | cons hd tl ih =>
    by_cases htlNil : tl = []
    · subst htlNil
      refine ⟨hd, List.mem_cons_self, fun y hy => ?_⟩
      have hy_eq : y = hd := by simpa using hy
      subst hy_eq
      omega
    · have htlNe : tl ≠ [] := htlNil
      obtain ⟨m, hmMem, hmMax⟩ := ih htlNe
      by_cases hle : hd.path.length ≤ m.path.length
      · exact ⟨m, List.mem_cons_of_mem hd hmMem, fun y hy => by rcases List.mem_cons.mp hy with rfl | hy2; exact hle; exact hmMax y hy2⟩
      · exact ⟨hd, List.mem_cons_self, fun y hy => by rcases List.mem_cons.mp hy with rfl | hy2; omega; have h1 := hmMax y hy2; omega⟩
theorem deniesB_nonempty_of_hasAllow_notPermitted {l r} (hHas : HasAllow l r) (hNot : ¬ Permitted l r) : deniesB l r ≠ [] := by
  intro hNil; apply hNot; obtain ⟨a, ha, hm, he⟩ := hHas
  refine ⟨a, ha, hm, he, ?_⟩
  intro d hd hdm hde
  have hdIn : d ∈ deniesB l r := deniesB_mem_iff.mpr ⟨hd, hdm, hde⟩
  rw [hNil] at hdIn; simp at hdIn
theorem hasAllow_notPermitted_imp_overridden {l r} (hHas : HasAllow l r) (hNot : ¬ Permitted l r) : Overridden l r := by
  have hDnonNil : deniesB l r ≠ [] := deniesB_nonempty_of_hasAllow_notPermitted hHas hNot
  obtain ⟨m, hmMem, hmMax⟩ := exists_max (deniesB l r) hDnonNil
  have hmDen := deniesB_mem_iff.mp hmMem
  refine ⟨m, hmDen.1, hmDen.2.1, hmDen.2.2, ?_⟩
  intro a ha ham hae
  show depth a ≤ depth m; unfold depth
  have hNotLt : ¬ (m.path.length < a.path.length) := by
    intro hlt
    have hall : ∀ d ∈ l, Matches d r → d.effect = Effect.deny → d.path.length < a.path.length := by
      intro d hd hdm hde
      have hdIn : d ∈ deniesB l r := deniesB_mem_iff.mpr ⟨hd, hdm, hde⟩
      have hle2 : d.path.length ≤ m.path.length := hmMax d hdIn
      omega
    have hP : Permitted l r := ⟨a, ha, ham, hae, hall⟩
    exact hNot hP
  omega
theorem valid_of_not_rejected {s r} (hNe : (step s r).1 ≠ .rejected) : ValidQuery s r := by
  by_cases hv : ValidQuery s r
  · exact hv
  · exfalso; exact hNe (by simp [step, hv])
theorem req_valid_answered : ValidAnswered step := by
  intro s r hV; have hEq := step_valid_eq s r hV; rw [hEq]; cases permittedB s.entries r <;> simp
theorem req_invalid_noop : InvalidNoop step := by
  intro s r hInv; simp [step, hInv]
theorem req_effects : Effects step := by
  intro s r hNe; have hV : ValidQuery s r := valid_of_not_rejected hNe; rw [step_valid_eq s r hV]; cases permittedB s.entries r <;> simp
theorem req_default_deny : DefaultDeny step := by
  intro s r hNo hGr
  by_cases hv : ValidQuery s r
  · have hf := step_fst_valid s r hv; rw [hf] at hGr
    cases hc : permittedB s.entries r with
    | true =>
      have hPerm : Permitted s.entries r := permittedB_true_iff.mp hc
      exact hNo (permitted_imp_hasAllow hPerm)
    | false => simp [hc] at hGr
  · have hR : (step s r).1 = .rejected := by simp [step, hv]
    rw [hR] at hGr; simp at hGr
theorem req_deny_overrides : DenyOverrides step := by
  intro s r hO hGr
  by_cases hv : ValidQuery s r
  · have hf := step_fst_valid s r hv; rw [hf] at hGr
    cases hc : permittedB s.entries r with
    | true =>
      have hPerm : Permitted s.entries r := permittedB_true_iff.mp hc
      exact (overridden_imp_notPermitted hO) hPerm
    | false => simp [hc] at hGr
  · have hR : (step s r).1 = .rejected := by simp [step, hv]
    rw [hR] at hGr; simp at hGr
theorem req_specific_allow : SpecificAllow step := by
  intro s r hV hP; have hPb : permittedB s.entries r = true := permittedB_true_iff.mpr hP; simp [step, hV, hPb]
theorem req_grant_justified : GrantJustified step := by
  intro s r hGr
  by_cases hv : ValidQuery s r
  · have hf := step_fst_valid s r hv; rw [hf] at hGr
    cases hc : permittedB s.entries r with
    | false => simp [hc] at hGr
    | true => exact permittedB_true_iff.mp hc
  · have hR : (step s r).1 = .rejected := by simp [step, hv]
    rw [hR] at hGr; simp at hGr
theorem req_order_independent : OrderIndependent step := by
  intro s r l hPerm
  have hPiff : permittedB l r = permittedB s.entries r := by
    have h1 : Permitted l r ↔ Permitted s.entries r := by
      constructor
      · intro h; obtain ⟨a, ha, hm, he, hall⟩ := h; refine ⟨a, hPerm.mem_iff.mp ha, hm, he, ?_⟩; intro d hd hdm hde; exact hall d (hPerm.mem_iff.mpr hd) hdm hde
      · intro h; obtain ⟨a, ha, hm, he, hall⟩ := h; refine ⟨a, hPerm.mem_iff.mpr ha, hm, he, ?_⟩; intro d hd hdm hde; exact hall d (hPerm.mem_iff.mp hd) hdm hde
    have eq_true_iff : (permittedB l r = true) ↔ (permittedB s.entries r = true) := by rw [permittedB_true_iff, permittedB_true_iff, h1]
    cases hl : permittedB l r <;> cases hs : permittedB s.entries r <;> try rfl
    · have hCon := eq_true_iff; rw [hl] at hCon; rw [hs] at hCon; simp at hCon
    · have hCon := eq_true_iff; rw [hl] at hCon; rw [hs] at hCon; simp at hCon
  have hViff : ValidQuery { s with entries := l } r ↔ ValidQuery s r := by simp [ValidQuery]
  by_cases hV : ValidQuery s r
  · have hVl : ValidQuery { s with entries := l } r := hViff.mpr hV
    have hf1 := step_fst_valid { s with entries := l } r hVl
    have hf2 := step_fst_valid s r hV
    rw [hf1, hf2]
    have : permittedB { s with entries := l }.entries r = permittedB l r := rfl
    rw [this, hPiff]
  · have hVl : ¬ ValidQuery { s with entries := l } r := fun h => hV (hViff.mp h)
    simp [step, hV, hVl]
theorem req_denial_explained : DenialExplained step := by
  intro s r hDen
  by_cases hv : ValidQuery s r
  · have hf := step_fst_valid s r hv; rw [hf] at hDen
    cases hc : permittedB s.entries r with
    | true => simp [hc] at hDen
    | false =>
      simp [hc] at hDen
      have hNotP : ¬ Permitted s.entries r := by intro hP; have := permittedB_true_iff.mpr hP; rw [this] at hc; simp at hc
      by_cases hHas : HasAllow s.entries r
      · exact Or.inr (hasAllow_notPermitted_imp_overridden hHas hNotP)
      · exact Or.inl hHas
  · have hR : (step s r).1 = .rejected := by simp [step, hv]
    rw [hR] at hDen; simp at hDen
end Acl
