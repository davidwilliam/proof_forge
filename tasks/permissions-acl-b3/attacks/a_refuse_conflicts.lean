import Acl.Spec

namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance

instance instDecidableMatches (e : Entry) (r : Request) : Decidable (Matches e r) := by
  unfold Matches; infer_instance

instance instDecidablePermitted (l : List Entry) (r : Request) : Decidable (Permitted l r) := by
  unfold Permitted; infer_instance

def decision (l : List Entry) (r : Request) : Bool := decide (Permitted l r)

def refStep : Impl := fun s r =>
  if ValidQuery s r then
    ((if decision s.entries r then .granted else .denied),
     { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] })
  else (.rejected, s)

theorem decision_iff (l : List Entry) (r : Request) : decision l r = true ↔ Permitted l r := by
  simp [decision]

/-- A most specific matching allow entry. -/
theorem exists_max_allow (r : Request) : ∀ (l : List Entry), HasAllow l r →
    ∃ a ∈ l, Matches a r ∧ a.effect = .allow ∧
      ∀ b ∈ l, Matches b r → b.effect = .allow → depth b ≤ depth a := by
  intro l
  induction l with
  | nil => intro ⟨a, ha, _⟩; cases ha
  | cons x xs ih =>
    intro hall
    by_cases hx : Matches x r ∧ x.effect = .allow
    · by_cases hxs : HasAllow xs r
      · obtain ⟨a, ha, hma, hea, hmax⟩ := ih hxs
        by_cases hle : depth x ≤ depth a
        · refine ⟨a, List.mem_cons_of_mem _ ha, hma, hea, fun b hb hmb heb => ?_⟩
          rcases List.mem_cons.1 hb with rfl | hb
          · exact hle
          · exact hmax b hb hmb heb
        · refine ⟨x, List.mem_cons_self, hx.1, hx.2, fun b hb hmb heb => ?_⟩
          rcases List.mem_cons.1 hb with rfl | hb
          · exact Nat.le_refl _
          · have := hmax b hb hmb heb; omega
      · refine ⟨x, List.mem_cons_self, hx.1, hx.2, fun b hb hmb heb => ?_⟩
        rcases List.mem_cons.1 hb with rfl | hb
        · exact Nat.le_refl _
        · exact absurd ⟨b, hb, hmb, heb⟩ hxs
    · obtain ⟨a, ha, hma, hea⟩ := hall
      rcases List.mem_cons.1 ha with rfl | ha
      · exact absurd ⟨hma, hea⟩ hx
      · obtain ⟨a', ha', hma', hea', hmax⟩ := ih ⟨a, ha, hma, hea⟩
        refine ⟨a', List.mem_cons_of_mem _ ha', hma', hea', fun b hb hmb heb => ?_⟩
        rcases List.mem_cons.1 hb with rfl | hb
        · exact absurd ⟨hmb, heb⟩ hx
        · exact hmax b hb hmb heb

theorem decision_false (l : List Entry) (r : Request) (h : decision l r = false) :
    ¬ HasAllow l r ∨ Overridden l r := by
  have hp : ¬ Permitted l r := fun hp => by rw [(decision_iff l r).2 hp] at h; cases h
  by_cases hall : HasAllow l r
  · right
    obtain ⟨a, ha, hma, hea, hmax⟩ := exists_max_allow r l hall
    have : ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧ depth a ≤ depth d := by
      apply Classical.byContradiction
      intro hno
      apply hp
      refine ⟨a, ha, hma, hea, fun d hd hmd hed => ?_⟩
      apply Classical.byContradiction
      intro hlt
      exact hno ⟨d, hd, hmd, hed, by omega⟩
    obtain ⟨d, hd, hmd, hed, hle⟩ := this
    exact ⟨d, hd, hmd, hed, fun b hb hmb heb => Nat.le_trans (hmax b hb hmb heb) hle⟩
  · exact Or.inl hall

theorem permitted_perm {l l' : List Entry} (hp : l.Perm l') (r : Request) :
    Permitted l r ↔ Permitted l' r := by
  unfold Permitted
  constructor
  · rintro ⟨a, ha, h1, h2, h3⟩
    exact ⟨a, hp.mem_iff.1 ha, h1, h2, fun d hd => h3 d (hp.mem_iff.2 hd)⟩
  · rintro ⟨a, ha, h1, h2, h3⟩
    exact ⟨a, hp.mem_iff.2 ha, h1, h2, fun d hd => h3 d (hp.mem_iff.1 hd)⟩

theorem decision_perm {l l' : List Entry} (hp : l.Perm l') (r : Request) :
    decision l r = decision l' r := by
  simp only [decision, permitted_perm hp r]

theorem refStep_of_valid {s : State} {r : Request} (h : ValidQuery s r) :
    refStep s r = ((if decision s.entries r then .granted else .denied),
      { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
  simp [refStep, h]

theorem refStep_of_invalid {s : State} {r : Request} (h : ¬ ValidQuery s r) :
    refStep s r = (.rejected, s) := by
  simp [refStep, h]

theorem answered_valid {s : State} {r : Request} (h : (refStep s r).1 ≠ .rejected) : ValidQuery s r := by
  by_cases hv : ValidQuery s r
  · exact hv
  · rw [refStep_of_invalid hv] at h; exact absurd rfl h

theorem granted_iff (s : State) (r : Request) :
    (refStep s r).1 = .granted ↔ ValidQuery s r ∧ decision s.entries r = true := by
  by_cases hv : ValidQuery s r
  · rw [refStep_of_valid hv]; cases decision s.entries r <;> simp [hv]
  · rw [refStep_of_invalid hv]; simp [hv]

theorem denied_iff (s : State) (r : Request) :
    (refStep s r).1 = .denied ↔ ValidQuery s r ∧ decision s.entries r = false := by
  by_cases hv : ValidQuery s r
  · rw [refStep_of_valid hv]; cases decision s.entries r <;> simp [hv]
  · rw [refStep_of_invalid hv]; simp [hv]

theorem ref_req_valid_answered : ValidAnswered refStep := by
  intro s r h
  rw [refStep_of_valid h]
  cases decision s.entries r <;> simp

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s r h; exact refStep_of_invalid h

theorem ref_req_effects : Effects refStep := by
  intro s r h
  rw [refStep_of_valid (answered_valid h)]
  cases decision s.entries r <;> simp

theorem ref_req_grant_justified : GrantJustified refStep := by
  intro s r h
  exact (decision_iff _ _).1 ((granted_iff s r).1 h).2

theorem ref_req_default_deny : DefaultDeny refStep := by
  intro s r hno h
  obtain ⟨a, ha, hm, he, _⟩ := ref_req_grant_justified s r h
  exact hno ⟨a, ha, hm, he⟩

theorem ref_req_deny_overrides : DenyOverrides refStep := by
  intro s r ⟨d, hd, hmd, hed, hall⟩ h
  obtain ⟨a, ha, hma, hea, hden⟩ := ref_req_grant_justified s r h
  have h1 := hall a ha hma hea
  have h2 := hden d hd hmd hed
  omega

theorem ref_req_specific_allow : SpecificAllow refStep := by
  intro s r hv hp
  exact (granted_iff s r).2 ⟨hv, (decision_iff _ _).2 hp⟩

theorem ref_req_order_independent : OrderIndependent refStep := by
  intro s r l hp
  have hv : ValidQuery { s with entries := l } r ↔ ValidQuery s r := Iff.rfl
  by_cases h : ValidQuery s r
  · rw [refStep_of_valid h, refStep_of_valid (hv.2 h)]
    simp only [decision_perm hp r]
  · rw [refStep_of_invalid h, refStep_of_invalid (fun h' => h (hv.1 h'))]

theorem ref_req_denial_explained : DenialExplained refStep := by
  intro s r h
  exact decision_false _ _ ((denied_iff s r).1 h).2


/-- Attack: refuse every check where both an allow and a deny entry apply. -/
def conflict (l : List Entry) (r : Request) : Bool :=
  l.any (fun e => decide (Matches e r) && e.effect == .allow) &&
    l.any (fun e => decide (Matches e r) && e.effect == .deny)

def step : Impl := fun s r => if conflict s.entries r then (.rejected, s) else refStep s r

theorem conflict_perm {l l' : List Entry} (hp : l.Perm l') (r : Request) :
    conflict l r = conflict l' r := by
  simp only [conflict, hp.any_eq]

theorem step_answered {s : State} {r : Request} (h : (step s r).1 ≠ .rejected) :
    conflict s.entries r = false ∧ step s r = refStep s r := by
  unfold step at *
  cases hg : conflict s.entries r <;> simp_all

theorem step_fst_ne {s : State} {r : Request} {o : Outcome} (ho : o ≠ .rejected)
    (h : (step s r).1 = o) : (refStep s r).1 = o := by
  have := step_answered (s := s) (r := r) (by rw [h]; exact ho)
  rw [← this.2]; exact h

theorem req_valid_answered : ∀ s r, ValidQuery s r → conflict s.entries r = false →
    (step s r).1 ≠ .rejected := by
  intro s r h hg
  simp only [step, hg]
  exact ref_req_valid_answered s r h

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  cases conflict s.entries r <;> simp [ref_req_invalid_noop s r h]

theorem req_effects : Effects step := by
  intro s r h
  have he := (step_answered h).2
  rw [he] at h ⊢
  exact ref_req_effects s r h

theorem req_default_deny : DefaultDeny step := by
  intro s r hno h
  exact ref_req_default_deny s r hno (step_fst_ne (by decide) h)

theorem req_deny_overrides : DenyOverrides step := by
  intro s r ho h
  exact ref_req_deny_overrides s r ho (step_fst_ne (by decide) h)

theorem req_specific_allow : ∀ s r, ValidQuery s r → Permitted s.entries r →
    conflict s.entries r = false → (step s r).1 = .granted := by
  intro s r hv hp hg
  simp only [step, hg]
  exact ref_req_specific_allow s r hv hp

theorem req_grant_justified : GrantJustified step := by
  intro s r h
  exact ref_req_grant_justified s r (step_fst_ne (by decide) h)

theorem req_order_independent : OrderIndependent step := by
  intro s r l hp
  have hc := conflict_perm hp r
  unfold step
  simp only [hc]
  split
  · rfl
  · exact ref_req_order_independent s r l hp

theorem req_denial_explained : DenialExplained step := by
  intro s r h
  exact ref_req_denial_explained s r (step_fst_ne (by decide) h)

end Acl
