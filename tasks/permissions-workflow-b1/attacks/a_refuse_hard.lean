import Workflow.Spec

namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance

def refStep : Impl := fun s r =>
  if ValidRequest s r then
    (.ok, { s with status := expectedStatus s r, content := expectedContent s r,
                   audit := expectedAudit s r })
  else
    (.rejected, s)

theorem refStep_of_valid {s : State} {r : Request} (h : ValidRequest s r) :
    refStep s r = (.ok,
      { s with status := expectedStatus s r, content := expectedContent s r,
               audit := expectedAudit s r }) := by
  simp [refStep, h]

theorem refStep_of_invalid {s : State} {r : Request} (h : ¬ ValidRequest s r) :
    refStep s r = (.rejected, s) := by
  simp [refStep, h]

theorem ref_ok_valid {s : State} {r : Request} (h : (refStep s r).1 = .ok) : ValidRequest s r := by
  by_cases hv : ValidRequest s r
  · exact hv
  · rw [refStep_of_invalid hv] at h; cases h

/-- Replaying a list with one more entry at the end. -/
theorem replay_append_single (l : List Entry) (e : Entry) (d : DocId) (st : Status) :
    replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
  induction l generalizing st with
  | nil => simp [replay]
  | cons x xs ih => simp [replay, ih]

/-- The only edge out of `published` leads to `archived`, and none leaves `archived`. -/
theorem allowed_from_published {q : Role} {dst : Status} (h : allowed q .published dst = true) :
    dst = .archived := by
  cases q <;> cases dst <;> simp [allowed] at h ⊢

theorem allowed_from_archived {q : Role} {dst : Status} : allowed q .archived dst = false := by
  cases q <;> cases dst <;> rfl

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s r h; rw [refStep_of_valid h]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s r h; exact refStep_of_invalid h

theorem ref_req_authorization : Authorized refStep := by
  intro s r h
  exact (ref_ok_valid h).2.2

theorem ref_req_single_doc : SingleDoc refStep := by
  intro s r h d hd
  rw [refStep_of_valid (ref_ok_valid h)]
  simp [expectedStatus, expectedContent, hd]

theorem ref_req_effects : Effects refStep := by
  intro s r h
  rw [refStep_of_valid (ref_ok_valid h)]
  exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem ref_req_published_immutable : PublishedImmutable refStep := by
  intro s r d hd
  by_cases hv : ValidRequest s r
  · rw [refStep_of_valid hv]
    show expectedContent s r d = s.content d
    unfold expectedContent
    split
    · rename_i hk
      obtain ⟨hk, rfl⟩ := hk
      have := (hv.2.2.2 hk).2
      rcases hd with hd | hd <;> rw [hd] at this <;> cases this
    · rfl
  · rw [refStep_of_invalid hv]

theorem ref_req_no_unpublish : NoUnpublish refStep := by
  intro s r d
  by_cases hv : ValidRequest s r
  · rw [refStep_of_valid hv]
    show (s.status d = .published → expectedStatus s r d = .published ∨ expectedStatus s r d = .archived) ∧
      (s.status d = .archived → expectedStatus s r d = .archived)
    unfold expectedStatus
    split
    · rename_i hk
      obtain ⟨hk, rfl⟩ := hk
      have ha := hv.2.2.1 hk
      refine ⟨fun hp => Or.inr ?_, fun hp => ?_⟩
      · rw [hp] at ha; exact allowed_from_published ha
      · rw [hp, allowed_from_archived] at ha; cases ha
    · exact ⟨fun hp => Or.inl hp, id⟩
  · rw [refStep_of_invalid hv]
    exact ⟨fun hp => Or.inl hp, id⟩

theorem ref_req_audit_append_only : AuditAppendOnly refStep := by
  intro s r
  by_cases hv : ValidRequest s r
  · rw [refStep_of_valid hv]
    show s.audit <+: expectedAudit s r
    unfold expectedAudit
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  · rw [refStep_of_invalid hv]; exact List.prefix_refl _

theorem ref_req_audit_consistent : KeepsAuditConsistent refStep := by
  intro s r hc
  by_cases hv : ValidRequest s r
  · rw [refStep_of_valid hv]
    intro d hd
    show replay (expectedAudit s r) d .draft = expectedStatus s r d
    unfold expectedAudit expectedStatus
    by_cases hk : r.kind = .move
    · simp only [hk, ite_true, true_and, replay_append_single]
      by_cases hdd : d = r.doc
      · subst hdd; simp
      · have : r.doc ≠ d := fun h => hdd h.symm
        simp [this, hdd, hc d hd]
    · simp [hk, hc d hd]
  · rw [refStep_of_invalid hv]; exact hc


/-- Attack: refuse some requests outright, otherwise run the reference. Every move by a publisher is refused. -/
def refuse (s : State) (r : Request) : Bool := r.kind == .move && s.role r.actor == .publisher

def step : Impl := fun s r => if refuse s r then (.rejected, s) else refStep s r

theorem step_ok {s : State} {r : Request} (h : (step s r).1 = .ok) :
    refuse s r = false ∧ step s r = refStep s r := by
  unfold step at *
  cases hg : refuse s r <;> simp_all

theorem req_valid_succeeds : ∀ s r, ValidRequest s r → refuse s r = false → (step s r).1 = .ok := by
  intro s r h hg
  simp only [step, hg]
  exact ref_req_valid_succeeds s r h

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  cases refuse s r <;> simp [ref_req_invalid_noop s r h]

theorem req_authorization : Authorized step := by
  intro s r h
  have he := (step_ok h).2
  exact ref_req_authorization s r (he ▸ h)

theorem req_single_doc : SingleDoc step := by
  intro s r h
  have he := (step_ok h).2
  rw [he]
  exact ref_req_single_doc s r (he ▸ h)

theorem req_effects : Effects step := by
  intro s r h
  have he := (step_ok h).2
  rw [he]
  exact ref_req_effects s r (he ▸ h)

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hd
  unfold step
  split
  · rfl
  · exact ref_req_published_immutable s r d hd

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  unfold step
  split
  · exact ⟨fun hp => Or.inl hp, id⟩
  · exact ref_req_no_unpublish s r d

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  unfold step
  split
  · exact List.prefix_refl _
  · exact ref_req_audit_append_only s r

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hc
  unfold step
  split
  · exact hc
  · exact ref_req_audit_consistent s r hc

end Workflow
