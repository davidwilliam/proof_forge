import Acl.Spec

namespace Acl

def step : Impl :=
  fun s r =>
    if h : r.user ∈ s.users ∧ r.user ≠ 0 then
      if h2 : Permitted s.entries r then
        (.granted, { s with log := s.log ++ [⟨r.user, r.path, true⟩] })
      else
        (.denied,  { s with log := s.log ++ [⟨r.user, r.path, false⟩] })
    else
      (.rejected, s)

theorem req_valid_answered : ValidAnswered step := by
  intro s r hq
  simp [step, hq]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step]
  by_cases h' : r.user ∈ s.users ∧ r.user ≠ 0
  · exact absurd h' h
  · simp [h']

theorem req_effects : Effects step := by
  intro s r hneq
  simp [step] at hneq ⊢
  by_cases hvalid : r.user ∈ s.users ∧ r.user ≠ 0
  · by_cases hperm : Permitted s.entries r
    · simp [hvalid, hperm, hneq]
    · simp [hvalid, hperm, hneq]
  · exfalso; apply hneq; simp [hvalid]

theorem permitted_hasAllow {l r} : Permitted l r → HasAllow l r := by
  intro ⟨a, ha, hma, haff, _⟩; exact ⟨a, ha, hma, haff⟩

theorem permitted_notOverridden {l r} : Permitted l r → ¬Overridden l r := by
  intro hp ⟨d, hd, hmd, heff, hall⟩
  rcases hp with ⟨a, ha, hma, haff, hden⟩
  have h1 := hall a ha hma haff
  have h2 := hden d hd hmd heff
  omega

theorem req_default_deny : DefaultDeny step := by
  intro s r hno
  simp [step]
  by_cases hvalid : r.user ∈ s.users ∧ r.user ≠ 0
  · by_cases hperm : Permitted s.entries r
    · exfalso; exact hno (permitted_hasAllow hperm)
    · simp
  · simp

theorem req_deny_overrides : DenyOverrides step := by
  intro s r hov
  simp [step]
  by_cases hvalid : r.user ∈ s.users ∧ r.user ≠ 0
  · by_cases hperm : Permitted s.entries r
    · exfalso; exact permitted_notOverridden hperm hov
    · simp
  · simp

theorem req_specific_allow : SpecificAllow step := by
  intro s r hvalid hperm
  simp [step, hvalid, hperm]

theorem req_grant_justified : GrantJustified step := by
  intro s r hgr
  simp [step] at hgr
  by_cases hvalid : r.user ∈ s.users ∧ r.user ≠ 0
  · by_cases hperm : Permitted s.entries r
    · simp [hvalid, hperm] at hgr; exact hperm
    · simp [hvalid, hperm] at hgr; contradiction
  · simp [hvalid] at hgr; contradiction

theorem perm_permitted {l1 l2 r} (h : l1.Perm l2) :
    Permitted l1 r ↔ Permitted l2 r := by
  unfold Permitted
  constructor
  · intro ⟨a, ha, hma, haff, hden⟩
    have hmem := List.Perm.mem_iff h
    refine ⟨a, (hmem a).mp ha, hma, haff, fun d hd hmd heff => ?_⟩
    exact hden d ((hmem d).mpr hd) hmd heff
  · intro ⟨a, ha, hma, haff, hden⟩
    have hmem := List.Perm.mem_iff h
    refine ⟨a, (hmem a).mpr ha, hma, haff, fun d hd hmd heff => ?_⟩
    exact hden d ((hmem d).mp hd) hmd heff

theorem req_order_independent : OrderIndependent step := by
  intro s r l hperm
  simp [step]
  by_cases hvalid : r.user ∈ s.users ∧ r.user ≠ 0
  · simp [hvalid]
    rw [perm_permitted hperm]
  · simp [hvalid]

theorem exists_max_allow {l r} (hhas : HasAllow l r) :
    ∃ a ∈ l, Matches a r ∧ a.effect = .allow ∧
      ∀ a' ∈ l, Matches a' r → a'.effect = .allow → depth a' ≤ depth a := by
  induction l with
  | nil => cases hhas
  | cons e l' ih =>
    simp at hhas
    rcases hhas with ⟨a, ha, hma, haff⟩
    cases ha with
    | inl heq =>
      subst heq
      have he_match : Matches e r := hma
      have he_eff : e.effect = .allow := haff
      by_cases hhas' : HasAllow l' r
      · obtain ⟨a', ha', hma', haff', hmax'⟩ := ih hhas'
        by_cases hle : depth e ≤ depth a'
        · exact ⟨a', Or.inr ha', hma', haff', fun a'' ha'' hma'' haff'' =>
            exact hmax' a'' ha'' hma'' haff''
        · exact ⟨e, Or.inl rfl, he_match, he_eff, fun a'' ha'' hma'' haff'' =>
            cases ha'' with
            | inl h => subst h; exact Nat.le_refl _
            | inr hmem =>
              have hle' := hmax' a'' hmem hma'' haff''
              exact Nat.le_trans hle' hle
      · exact ⟨e, Or.inl rfl, he_match, he_eff, fun a'' ha'' hma'' haff'' =>
          cases ha'' with
          | inl h => subst h; exact Nat.le_refl _
          | inr hmem => exfalso; cases hhas'
    | inr ha' =>
      obtain ⟨a', ha', hma', haff', hmax'⟩ := ih ⟨a, ha', hma, haff⟩
      exact ⟨a', Or.inr ha', hma', haff', hmax'⟩

theorem notPermitted_imp_denial_explained {l r} :
    ¬Permitted l r → ¬HasAllow l r ∨ Overridden l r := by
  intro hnp
  by_cases hhas : HasAllow l r
  · right
    obtain ⟨a, ha, hma, haff, hmax⟩ := exists_max_allow hhas
    have hnot_perm : ¬ (∀ d ∈ l, Matches d r → d.effect = .deny → depth d < depth a) := by
      intro h
      exact hnp ⟨a, ha, hma, haff, h⟩
    push_neg at hnot_perm
    obtain ⟨d, hd, hmd, heff, hge⟩ := hnot_perm
    exact ⟨d, hd, hmd, heff, fun a' ha' hma' haff' =>
      Nat.le_trans (hmax a' ha' hma' haff') hge⟩
  · left; exact hhas

theorem req_denial_explained : DenialExplained step := by
  intro s r hden
  simp [step] at hden
  by_cases hvalid : r.user ∈ s.users ∧ r.user ≠ 0
  · by_cases hperm : Permitted s.entries r
    · simp [hvalid, hperm] at hden; contradiction
    · simp [hvalid, hperm] at hden
      exact notPermitted_imp_denial_explained hperm
  · simp [hvalid] at hden; contradiction

end Acl
