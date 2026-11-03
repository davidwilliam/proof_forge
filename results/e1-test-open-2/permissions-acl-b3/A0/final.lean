import Acl.Spec

namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance

instance instDecidableMatches (e : Entry) (r : Request) : Decidable (Matches e r) := by
  unfold Matches; infer_instance

instance instDecidableHasAllow (l : List Entry) (r : Request) : Decidable (HasAllow l r) := by
  unfold HasAllow; infer_instance

instance instDecidableOverridden (l : List Entry) (r : Request) : Decidable (Overridden l r) := by
  unfold Overridden; infer_instance

instance instDecidablePermitted (l : List Entry) (r : Request) : Decidable (Permitted l r) := by
  unfold Permitted; infer_instance

def step : Impl := fun s r =>
  if _h : ValidQuery s r then
    let g := decide (Permitted s.entries r)
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem permitted_perm {l₁ l₂ : List Entry} (h : l₁.Perm l₂) (r : Request) :
    Permitted l₁ r ↔ Permitted l₂ r := by
  unfold Permitted
  have hm : ∀ x, x ∈ l₁ ↔ x ∈ l₂ := fun x => h.mem_iff
  constructor
  · intro h1
    rcases h1 with ⟨a, ha, h1, h2, h3⟩
    exact ⟨a, (hm a).mp ha, h1, h2, fun d hd h4 h5 => h3 d ((hm d).mpr hd) h4 h5⟩
  · intro h1
    rcases h1 with ⟨a, ha, h1, h2, h3⟩
    exact ⟨a, (hm a).mpr ha, h1, h2, fun d hd h4 h5 => h3 d ((hm d).mp hd) h4 h5⟩

theorem permitted_imp_hasAllow {l : List Entry} {r : Request} (h : Permitted l r) : HasAllow l r := by
  unfold Permitted at h
  unfold HasAllow
  rcases h with ⟨a, ha, hm, he, _⟩
  exact ⟨a, ha, hm, he⟩

theorem not_permitted_of_overridden {l : List Entry} {r : Request}
    (ho : Overridden l r) : ¬ Permitted l r := by
  unfold Overridden at ho
  unfold Permitted
  intro h2
  rcases ho with ⟨d, hd, hmd, hed, hall⟩
  rcases h2 with ⟨a, ha, hma, hea, hall2⟩
  have h1 := hall a ha hma hea
  have h2' := hall2 d hd hmd hed
  exact absurd (Nat.lt_of_le_of_lt h1 h2') (Nat.lt_irrefl _)

theorem exists_max_entry (p : Entry → Prop) [DecidablePred p] (l : List Entry)
    (h : ∃ e ∈ l, p e) : ∃ m ∈ l, p m ∧ ∀ e ∈ l, p e → depth e ≤ depth m := by
  induction l with
  | nil =>
    exfalso
    obtain ⟨e, he, _⟩ := h
    simp at he
  | cons hd tl ih =>
    by_cases hp : p hd
    · by_cases ht : ∃ e ∈ tl, p e
      · obtain ⟨m, hm, hpm, hall⟩ := ih ht
        by_cases hle : depth hd ≤ depth m
        · refine ⟨m, List.Mem.tail hd hm, hpm, fun e he hpe => ?_⟩
          rcases List.mem_cons.mp he with rfl | he2
          · exact hle
          · exact hall e he2 hpe
        · have hgt : depth m ≤ depth hd := Nat.le_of_not_le hle
          refine ⟨hd, List.Mem.head tl, hp, fun e he hpe => ?_⟩
          rcases List.mem_cons.mp he with rfl | he2
          · exact Nat.le_refl _
          · exact Nat.le_trans (hall e he2 hpe) hgt
      · refine ⟨hd, List.Mem.head tl, hp, fun e he hpe => ?_⟩
        rcases List.mem_cons.mp he with rfl | he2
        · exact Nat.le_refl _
        · exfalso
          exact ht ⟨e, he2, hpe⟩
    · have ht : ∃ e ∈ tl, p e := by
        obtain ⟨e, he, hpe⟩ := h
        rcases List.mem_cons.mp he with rfl | he2
        · exact absurd hpe hp
        · exact ⟨e, he2, hpe⟩
      obtain ⟨m, hm, hpm, hall⟩ := ih ht
      refine ⟨m, List.Mem.tail hd hm, hpm, fun e he hpe => ?_⟩
      rcases List.mem_cons.mp he with rfl | he2
      · exact absurd hpe hp
      · exact hall e he2 hpe

theorem hasAllow_notPermitted_imp_overridden (l : List Entry) (r : Request)
    (ha : HasAllow l r) (hnp : ¬ Permitted l r) : Overridden l r := by
  have hallows : ∃ e ∈ l, (Matches e r ∧ e.effect = .allow) := by
    obtain ⟨a, ha1, hm, he⟩ := ha
    exact ⟨a, ha1, ⟨hm, he⟩⟩
  obtain ⟨aMax, haMaxMem, hpaMax, haMaxGreatest⟩ :=
    exists_max_entry (fun e => Matches e r ∧ e.effect = .allow) l hallows
  by_cases hDenExists : ∃ e ∈ l, (Matches e r ∧ e.effect = .deny)
  · obtain ⟨dMax, hdMaxMem, hpdMax, hdMaxGreatest⟩ :=
      exists_max_entry (fun e => Matches e r ∧ e.effect = .deny) l hDenExists
    have hdMaxMatch := hpdMax.1
    have hdMaxEff := hpdMax.2
    have haMaxMatch := hpaMax.1
    have haMaxEff := hpaMax.2
    have h_over_aMax : depth aMax ≤ depth dMax := by
      by_cases hle : depth aMax ≤ depth dMax
      · exact hle
      · exfalso
        have hlt' : depth dMax < depth aMax := Nat.lt_of_not_le hle
        have hPerm : Permitted l r :=
          ⟨aMax, haMaxMem, haMaxMatch, haMaxEff, fun d hd hmd hed => by
            have hleD := hdMaxGreatest d hd ⟨hmd, hed⟩
            exact Nat.lt_of_le_of_lt hleD hlt'⟩
        exact hnp hPerm
    exact ⟨dMax, hdMaxMem, hdMaxMatch, hdMaxEff, fun a ha hma hea => by
      have hleA : depth a ≤ depth aMax := haMaxGreatest a ha ⟨hma, hea⟩
      exact Nat.le_trans hleA h_over_aMax⟩
  · exfalso
    have hPerm : Permitted l r :=
      ⟨aMax, haMaxMem, hpaMax.1, hpaMax.2, fun d hd hmd hed => by
        exfalso
        exact hDenExists ⟨d, hd, ⟨hmd, hed⟩⟩⟩
    exact hnp hPerm

theorem notPermitted_imp (l : List Entry) (r : Request) :
    ¬ Permitted l r → (¬ HasAllow l r ∨ Overridden l r) := by
  intro h
  by_cases ha : HasAllow l r
  · exact Or.inr (hasAllow_notPermitted_imp_overridden l r ha h)
  · exact Or.inl ha

theorem step_of_valid (s : State) (r : Request) (hv : ValidQuery s r) :
    step s r = (if decide (Permitted s.entries r) then .granted else .denied,
                { s with log := s.log ++ [⟨r.user, r.path, decide (Permitted s.entries r)⟩] }) := by
  unfold step
  simp [hv]

theorem step_of_invalid (s : State) (r : Request) (hn : ¬ ValidQuery s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [hn]

theorem step_fst_of_valid (s : State) (r : Request) (hv : ValidQuery s r) :
    (step s r).1 = if decide (Permitted s.entries r) then .granted else .denied := by
  rw [step_of_valid s r hv]

theorem step_fst_of_invalid (s : State) (r : Request) (hn : ¬ ValidQuery s r) :
    (step s r).1 = .rejected := by
  rw [step_of_invalid s r hn]

theorem valid_of_not_rejected (s : State) (r : Request) (hne : (step s r).1 ≠ .rejected) :
    ValidQuery s r := by
  by_cases hv : ValidQuery s r
  · exact hv
  · exfalso
    have hs := step_fst_of_invalid s r hv
    rw [hs] at hne
    exact hne rfl

theorem permitted_of_granted_valid (s : State) (r : Request) (hv : ValidQuery s r)
    (hgr : (step s r).1 = .granted) : Permitted s.entries r := by
  have hs := step_fst_of_valid s r hv
  rw [hs] at hgr
  by_cases hp : Permitted s.entries r
  · exact hp
  · simp [hp] at hgr

theorem not_permitted_of_denied_valid (s : State) (r : Request) (hv : ValidQuery s r)
    (hden : (step s r).1 = .denied) : ¬ Permitted s.entries r := by
  have hs := step_fst_of_valid s r hv
  rw [hs] at hden
  by_cases hp : Permitted s.entries r
  · simp [hp] at hden
  · exact hp

theorem req_valid_answered : ValidAnswered step := by
  unfold ValidAnswered
  intro s r hv
  have h := step_fst_of_valid s r hv
  rw [h]
  by_cases hp : Permitted s.entries r <;> simp [hp]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r hn
  exact step_of_invalid s r hn

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hne
  have hv : ValidQuery s r := valid_of_not_rejected s r hne
  have hs := step_of_valid s r hv
  rw [hs]
  refine ⟨rfl, rfl, ?_⟩
  have hg : decide ((if decide (Permitted s.entries r) then Outcome.granted else Outcome.denied) = Outcome.granted) = decide (Permitted s.entries r) := by
    by_cases hp : Permitted s.entries r
    · simp [hp]
    · simp [hp]
  rw [hg]

theorem req_default_deny : DefaultDeny step := by
  unfold DefaultDeny
  intro s r hna hgr
  have hv : ValidQuery s r := valid_of_not_rejected s r (by rw [hgr]; simp)
  have hPerm := permitted_of_granted_valid s r hv hgr
  exact hna (permitted_imp_hasAllow hPerm)

theorem req_deny_overrides : DenyOverrides step := by
  unfold DenyOverrides
  intro s r ho hgr
  have hv : ValidQuery s r := valid_of_not_rejected s r (by rw [hgr]; simp)
  have hPerm := permitted_of_granted_valid s r hv hgr
  exact not_permitted_of_overridden ho hPerm

theorem req_specific_allow : SpecificAllow step := by
  unfold SpecificAllow
  intro s r hvq hp
  have hs := step_of_valid s r hvq
  rw [hs]
  simp [hp]

theorem req_grant_justified : GrantJustified step := by
  unfold GrantJustified
  intro s r h
  have hv : ValidQuery s r := valid_of_not_rejected s r (by rw [h]; simp)
  exact permitted_of_granted_valid s r hv h

theorem req_order_independent : OrderIndependent step := by
  unfold OrderIndependent
  intro s r l hperm
  have hv1 : ValidQuery s r ↔ ValidQuery { s with entries := l } r := by
    unfold ValidQuery
    simp
  by_cases hvq : ValidQuery s r
  · have hvq2 : ValidQuery { s with entries := l } r := hv1.mp hvq
    have hs1 := step_of_valid s r hvq
    have hs2 := step_of_valid { s with entries := l } r hvq2
    rw [hs1, hs2]
    simp
    have hiff := permitted_perm hperm r
    by_cases hp : Permitted s.entries r
    · have hp2 : Permitted l r := hiff.mpr hp
      simp [hp, hp2]
    · have hp2 : ¬ Permitted l r := fun h => hp (hiff.mp h)
      simp [hp, hp2]
  · have hvq2 : ¬ ValidQuery { s with entries := l } r := fun h => hvq (hv1.mpr h)
    have hs1 := step_of_invalid s r hvq
    have hs2 := step_of_invalid { s with entries := l } r hvq2
    rw [hs1, hs2]

theorem req_denial_explained : DenialExplained step := by
  unfold DenialExplained
  intro s r hden
  have hv : ValidQuery s r := valid_of_not_rejected s r (by rw [hden]; simp)
  have hnp := not_permitted_of_denied_valid s r hv hden
  exact notPermitted_imp s.entries r hnp

end Acl
