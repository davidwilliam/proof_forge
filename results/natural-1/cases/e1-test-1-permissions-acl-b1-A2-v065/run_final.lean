import Acl.Spec
namespace Acl

def matchesB (e : Entry) (r : Request) : Bool :=
  decide (e.subject = 0 ∨ e.subject = r.user) && decide (e.path <+: r.path)

def permittedB (l : List Entry) (r : Request) : Bool :=
  l.any (fun a => matchesB a r && decide (a.effect = .allow) && l.all (fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length)))

def validB (s : State) (r : Request) : Bool :=
  decide (r.user ∈ s.users) && decide (r.user ≠ 0)

def step : Impl := fun s r =>
  if validB s r then
    let g := permittedB s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem validB_true_of_ValidQuery2 (s : State) (r : Request) (h : ValidQuery s r) : validB s r = true := by
  unfold validB ValidQuery at *
  obtain ⟨hm, hne⟩ := h
  simp [hm, hne]

theorem validB_false_of_not_ValidQuery (s : State) (r : Request) (h : ¬ ValidQuery s r) : validB s r = false := by
  unfold validB ValidQuery at *
  by_cases hm : r.user ∈ s.users
  · by_cases hne : r.user ≠ 0
    · exact absurd ⟨hm, hne⟩ h
    · simp [hm, hne]
  · simp [hm]

theorem effects_helper_valid (s : State) (r : Request) (hne : (step s r).1 ≠ .rejected) : validB s r = true := by
  unfold step at hne
  by_cases h : validB s r = true
  · exact h
  · have hf : validB s r = false := by cases hb : validB s r with | true => simp [hb] at h | false => rfl
    simp [hf] at hne

theorem matchesB_iff_thm (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  simp [Bool.and_eq_true, decide_eq_true_eq]

theorem permittedB_hasAllow_thm (l : List Entry) (r : Request) (h : permittedB l r = true) : HasAllow l r := by
  unfold permittedB at h
  rw [List.any_eq_true] at h
  obtain ⟨a, haMem, ha⟩ := h
  have h1 : (matchesB a r && decide (a.effect = .allow) && l.all (fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length))) = true := ha
  rw [Bool.and_eq_true] at h1
  obtain ⟨h12, _hall⟩ := h1
  rw [Bool.and_eq_true] at h12
  obtain ⟨hm, hal⟩ := h12
  have hm' : Matches a r := (matchesB_iff_thm a r).mp hm
  have hal' : a.effect = .allow := (decide_eq_true_eq.mp hal)
  exact ⟨a, haMem, hm', hal'⟩

theorem my_perm_true_imp (l : List Entry) (r : Request) (h : permittedB l r = true) : Permitted l r := by
  unfold permittedB at h
  rw [List.any_eq_true] at h
  obtain ⟨a, haMem, ha⟩ := h
  have h1 : (matchesB a r && decide (a.effect = .allow) && l.all (fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length))) = true := ha
  rw [Bool.and_eq_true] at h1
  obtain ⟨h12, hallTrue⟩ := h1
  rw [Bool.and_eq_true] at h12
  obtain ⟨hmB, halB⟩ := h12
  have hm' : Matches a r := (matchesB_iff_thm a r).mp hmB
  have hal' : a.effect = .allow := (decide_eq_true_eq.mp halB)
  refine ⟨a, haMem, hm', hal', ?_⟩
  intro d hdMem hdMatch hdDeny
  have hdAll : (!(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length)) = true := by
    have hall : ∀ x ∈ l, (!(matchesB x r && decide (x.effect = .deny)) || decide (x.path.length < a.path.length)) = true := (List.all_eq_true.mp hallTrue)
    exact hall d hdMem
  have hmBd : matchesB d r = true := (matchesB_iff_thm d r).mpr hdMatch
  have heB : decide (d.effect = .deny) = true := decide_eq_true_eq.mpr hdDeny
  have hc : decide (d.path.length < a.path.length) = true := by
    rw [hmBd, heB] at hdAll
    simpa using hdAll
  have hlt : d.path.length < a.path.length := of_decide_eq_true hc
  show depth d < depth a
  unfold depth
  exact hlt

theorem my_grant_perm_true2 (s : State) (r : Request) (hg : (step s r).1 = .granted) : permittedB s.entries r = true := by
  by_cases hv : validB s r = true
  · unfold step at hg
    simp only [hv] at hg
    by_cases hp : permittedB s.entries r = true
    · exact hp
    · have hpf : permittedB s.entries r = false := by
        cases hb : permittedB s.entries r with
        | true => simp [hb] at hp
        | false => rfl
      simp only [hpf] at hg
      simp at hg
  · have hvf : validB s r = false := by
      cases hb : validB s r with
      | true => simp [hb] at hv
      | false => rfl
    unfold step at hg
    simp only [hvf] at hg
    simp at hg

theorem my_over_contra (l : List Entry) (r : Request) (hov : Overridden l r) (hper : Permitted l r) : False := by
  obtain ⟨d, hdMem, hdMatch, hdDeny, hle⟩ := hov
  obtain ⟨a, haMem, haMatch, haAllow, hlt⟩ := hper
  have h1 : depth a ≤ depth d := hle a haMem haMatch haAllow
  have h2 : depth d < depth a := hlt d hdMem hdMatch hdDeny
  omega

theorem test_perm_aux3 (l : List Entry) (r : Request) (a : Entry) (hlt : ∀ d ∈ l, Matches d r → d.effect = .deny → d.path.length < a.path.length) : l.all (fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length)) = true := by
  apply List.all_eq_true.mpr
  intro d hdMem
  by_cases hdM : Matches d r
  · by_cases hdD : d.effect = .deny
    · have hlt' : d.path.length < a.path.length := hlt d hdMem hdM hdD
      have hdec2 : decide (d.path.length < a.path.length) = true := decide_eq_true_eq.mpr hlt'
      simp only [hdec2, Bool.or_true]
    · have hne : decide (d.effect = .deny) = false := by simp [hdD]
      simp only [hne, Bool.and_false, Bool.not_false, Bool.true_or]
  · have hmf : matchesB d r = false := by
      cases hb : matchesB d r with
      | true => exact absurd ((matchesB_iff_thm d r).mp hb) hdM
      | false => rfl
    simp only [hmf, Bool.false_and, Bool.not_false, Bool.true_or]

theorem permittedB_of_Permitted_rw (l : List Entry) (r : Request) (h : Permitted l r) : permittedB l r = true := by
  obtain ⟨a, haMem, haMatch, haAllow, hlt⟩ := h
  unfold permittedB
  rw [List.any_eq_true]
  refine ⟨a, haMem, ?_⟩
  have hmB : matchesB a r = true := (matchesB_iff_thm a r).mpr haMatch
  have halB : decide (a.effect = .allow) = true := decide_eq_true_eq.mpr haAllow
  have hlt' : ∀ d ∈ l, Matches d r → d.effect = .deny → d.path.length < a.path.length := by
    intro d hd hdm hdd
    have hh := hlt d hd hdm hdd
    unfold depth at hh
    exact hh
  have hall := test_perm_aux3 l r a hlt'
  simp only [hmB, halB, hall, Bool.true_and]

theorem permittedB_of_Permitted_clean (l : List Entry) (r : Request) (h : Permitted l r) : permittedB l r = true := by
  exact permittedB_of_Permitted_rw l r h

theorem Permitted_transfer_test (r : Request) (l1 l2 : List Entry) (h : l1.Perm l2) (hp : Permitted l1 r) : Permitted l2 r := by
  obtain ⟨a, haMem, haMatch, haAllow, hlt⟩ := hp
  refine ⟨a, (List.Perm.mem_iff (a := a) h).mp haMem, haMatch, haAllow, ?_⟩
  intro d hdMem hdMatch hdDeny
  have hdMem1 : d ∈ l1 := (List.Perm.mem_iff (a := d) h).mpr hdMem
  exact hlt d hdMem1 hdMatch hdDeny

theorem req_order_independent_aux_validEq (s : State) (r : Request) (l : List Entry) :
    validB { s with entries := l } r = validB s r := by
  unfold validB
  rfl

theorem req_order_independent_aux_permEq (r : Request) (l1 l2 : List Entry) (h : l1.Perm l2) :
    permittedB l1 r = permittedB l2 r := by
  by_cases h1 : permittedB l1 r = true
  · have hp1 : Permitted l1 r := my_perm_true_imp l1 r h1
    have hp2 : Permitted l2 r := Permitted_transfer_test r l1 l2 h hp1
    have ht2 : permittedB l2 r = true := permittedB_of_Permitted_clean l2 r hp2
    rw [h1, ht2]
  · have hf1 : permittedB l1 r = false := by cases hb : permittedB l1 r with | true => simp [hb] at h1 | false => rfl
    by_cases h2 : permittedB l2 r = true
    · have hp2 : Permitted l2 r := my_perm_true_imp l2 r h2
      have hp1 : Permitted l1 r := Permitted_transfer_test r l2 l1 h.symm hp2
      have ht1 : permittedB l1 r = true := permittedB_of_Permitted_clean l1 r hp1
      rw [ht1] at hf1
      simp at hf1
    · have hf2 : permittedB l2 r = false := by cases hb : permittedB l2 r with | true => simp [hb] at h2 | false => rfl
      rw [hf1, hf2]

theorem req_deny_overrides_aux_proof : DenyOverrides step := by
  intro s r hov hEq
  have hpermB : permittedB s.entries r = true := my_grant_perm_true2 s r hEq
  have hperm : Permitted s.entries r := my_perm_true_imp s.entries r hpermB
  exact my_over_contra s.entries r hov hperm

theorem maxAllow_exists3 (l : List Entry) (r : Request) (h : HasAllow l r) : ∃ a ∈ l, Matches a r ∧ a.effect = .allow ∧ ∀ b ∈ l, Matches b r → b.effect = .allow → depth b ≤ depth a := by
  induction l with
  | nil =>
    unfold HasAllow at h
    obtain ⟨a, haMem, _, _⟩ := h
    simp at haMem
  | cons hd tl ih =>
    by_cases hTl : HasAllow tl r
    · obtain ⟨aT, haTmem, haTmatch, haTallow, haTmax⟩ := ih hTl
      by_cases hHd : (Matches hd r ∧ hd.effect = .allow)
      · obtain ⟨hHdMatch, hHdAllow⟩ := hHd
        by_cases hle : depth aT ≤ depth hd
        · refine ⟨hd, (by simp : hd ∈ hd :: tl), hHdMatch, hHdAllow, ?_⟩
          intro b hb hbMatch hbAllow
          have hb2 : b = hd ∨ b ∈ tl := by simpa using hb
          cases hb2 with
          | inl heq =>
            subst heq
            exact Nat.le_refl _
          | inr hmem =>
            have h1 : depth b ≤ depth aT := haTmax b hmem hbMatch hbAllow
            omega
        · have hge : depth hd ≤ depth aT := by omega
          refine ⟨aT, (by simp [haTmem] : aT ∈ hd :: tl), haTmatch, haTallow, ?_⟩
          intro b hb hbMatch hbAllow
          have hb2 : b = hd ∨ b ∈ tl := by simpa using hb
          cases hb2 with
          | inl heq => subst heq; exact hge
          | inr hmem => exact haTmax b hmem hbMatch hbAllow
      · refine ⟨aT, (by simp [haTmem] : aT ∈ hd :: tl), haTmatch, haTallow, ?_⟩
        intro b hb hbMatch hbAllow
        have hb2 : b = hd ∨ b ∈ tl := by simpa using hb
        cases hb2 with
        | inl heq =>
          subst heq
          exact absurd ⟨hbMatch, hbAllow⟩ hHd
        | inr hmem => exact haTmax b hmem hbMatch hbAllow
    · have hHd : Matches hd r ∧ hd.effect = .allow := by
        unfold HasAllow at h hTl
        obtain ⟨a, haMem, haMatch, haAllow⟩ := h
        have ha2 : a = hd ∨ a ∈ tl := by simpa using haMem
        cases ha2 with
        | inl heq =>
          subst heq
          exact ⟨haMatch, haAllow⟩
        | inr hmem => exact absurd ⟨a, hmem, haMatch, haAllow⟩ hTl
      obtain ⟨hHdMatch, hHdAllow⟩ := hHd
      refine ⟨hd, (by simp : hd ∈ hd :: tl), hHdMatch, hHdAllow, ?_⟩
      intro b hb hbMatch hbAllow
      have hb2 : b = hd ∨ b ∈ tl := by simpa using hb
      cases hb2 with
      | inl heq => subst heq; exact Nat.le_refl _
      | inr hmem =>
        have hcon : HasAllow tl r := ⟨b, hmem, hbMatch, hbAllow⟩
        exact absurd hcon hTl

theorem denied_validB_true (s : State) (r : Request) (h : (step s r).1 = .denied) : validB s r = true := by
  unfold step at h
  by_cases hv : validB s r = true
  · exact hv
  · have hvf : validB s r = false := by cases hb : validB s r with | true => simp [hb] at hv | false => rfl
    simp [hvf] at h

theorem denied_permittedB_false (s : State) (r : Request) (h : (step s r).1 = .denied) : permittedB s.entries r = false := by
  have hv := denied_validB_true s r h
  unfold step at h
  simp [hv] at h
  by_cases hp : permittedB s.entries r = true
  · simp [hp] at h
  · cases hb : permittedB s.entries r with | true => simp [hb] at hp | false => rfl

theorem notPermitted_of_permittedB_false (l : List Entry) (r : Request) (h : permittedB l r = false) : ¬ Permitted l r := by
  intro hP
  have ht := permittedB_of_Permitted_clean l r hP
  rw [ht] at h
  simp at h

theorem plan0_exists_deny_ge_of_allow_not_permitted (l : List Entry) (r : Request) (a : Entry) (haMem : a ∈ l) (haMatch : Matches a r) (haAllow : a.effect = .allow) (hNot : ¬ Permitted l r) : ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧ depth a ≤ depth d := by
  apply Classical.byContradiction
  intro hnone
  apply hNot
  refine ⟨a, haMem, haMatch, haAllow, ?_⟩
  intro d hdMem hdMatch hdDeny
  by_cases hlt : depth d < depth a
  · exact hlt
  · have hle : depth a ≤ depth d := Nat.le_of_not_lt hlt
    exact False.elim (hnone ⟨d, hdMem, hdMatch, hdDeny, hle⟩)

theorem plan0_overridden_of_hasAllow_not_permitted_proof (l : List Entry) (r : Request) (hHas : HasAllow l r) (hNot : ¬ Permitted l r) : Overridden l r := by
  obtain ⟨a, haMem, haMatch, haAllow, haMax⟩ := maxAllow_exists3 l r hHas
  obtain ⟨d, hdMem, hdMatch, hdDeny, hge⟩ := plan0_exists_deny_ge_of_allow_not_permitted l r a haMem haMatch haAllow hNot
  exact ⟨d, hdMem, hdMatch, hdDeny, fun b hb hbMatch hbAllow => Nat.le_trans (haMax b hb hbMatch hbAllow) hge⟩

theorem plan0_not_permitted_of_denied (s : State) (r : Request) (h : (step s r).1 = .denied) : ¬ Permitted s.entries r :=
  notPermitted_of_permittedB_false s.entries r (denied_permittedB_false s r h)

theorem plan0_denial_explained_of_denied (s : State) (r : Request) (h : (step s r).1 = .denied) : ¬ HasAllow s.entries r ∨ Overridden s.entries r := by
  by_cases hHas : HasAllow s.entries r
  · right
    have hNot : ¬ Permitted s.entries r := plan0_not_permitted_of_denied s r h
    exact plan0_overridden_of_hasAllow_not_permitted_proof s.entries r hHas hNot
  · left
    exact hHas

theorem req_valid_answered : ValidAnswered step := by
  intro s r h
  have hv : validB s r = true := validB_true_of_ValidQuery2 s r h
  unfold step
  simp only [hv, ↓reduceIte]
  split
  · simp
  · simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hv : validB s r = false := validB_false_of_not_ValidQuery s r h
  unfold step
  simp [hv]

theorem req_effects : Effects step := by
  intro s r hne
  have hv := effects_helper_valid s r hne
  unfold step
  simp only [hv, ↓reduceIte]
  by_cases hg : permittedB s.entries r = true
  · simp only [hg, ↓reduceIte]
    simp
  · have hg2 : permittedB s.entries r = false := by
      cases hb : permittedB s.entries r with
      | true => simp [hb] at hg
      | false => rfl
    simp only [hg2]
    simp

theorem req_default_deny : DefaultDeny step := by
  intro s r hNo
  have hPerm : permittedB s.entries r = false := by
    cases hb : permittedB s.entries r
    case true => exact absurd (permittedB_hasAllow_thm s.entries r hb) hNo
    case false => rfl
  unfold step
  by_cases hv : validB s r = true
  · simp [hv, hPerm]
  · have hvf : validB s r = false := by
      cases hb : validB s r with
      | true => exact absurd hb (by simp [hv])
      | false => rfl
    simp [hvf]

theorem req_deny_overrides : DenyOverrides step := req_deny_overrides_aux_proof

theorem req_specific_allow : SpecificAllow step := by
  intro s r hV hP
  have hv : validB s r = true := validB_true_of_ValidQuery2 s r hV
  have hp : permittedB s.entries r = true := permittedB_of_Permitted_rw s.entries r hP
  unfold step
  simp [hv, hp]

theorem req_grant_justified : GrantJustified step := by
  intro s r hg
  exact my_perm_true_imp s.entries r (my_grant_perm_true2 s r hg)

theorem req_order_independent : OrderIndependent step := by
  intro s r l hperm
  have hP : permittedB l r = permittedB s.entries r :=
    req_order_independent_aux_permEq r l s.entries hperm
  have hV : validB { s with entries := l } r = validB s r :=
    req_order_independent_aux_validEq s r l
  by_cases hv : validB s r = true
  · have hv2 : validB { s with entries := l } r = true := by rw [hV, hv]
    have e1 : (step { s with entries := l } r).1 = (if permittedB l r then .granted else .denied) := by
      unfold step
      simp [hv2]
    have e2 : (step s r).1 = (if permittedB s.entries r then .granted else .denied) := by
      unfold step
      simp [hv]
    rw [e1, e2, hP]
  · have hvf : validB s r = false := by cases hb : validB s r with | true => simp [hb] at hv | false => rfl
    have hv2 : validB { s with entries := l } r = false := by rw [hV, hvf]
    have e1 : (step { s with entries := l } r).1 = .rejected := by
      unfold step
      simp [hv2]
    have e2 : (step s r).1 = .rejected := by
      unfold step
      simp [hvf]
    rw [e1, e2]

theorem req_denial_explained : DenialExplained step := by
  intro s r h
  exact plan0_denial_explained_of_denied s r h

end Acl
