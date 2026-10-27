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


/-- Attack: every successful edit also writes an audit entry. -/
def touch (r : Request) (t : State) : State :=
  if r.kind = .edit then { t with audit := t.audit ++ [⟨r.doc, r.actor, .draft, .draft⟩] } else t

theorem touch_docs (r : Request) (t : State) : (touch r t).docs = t.docs := by
  unfold touch; split <;> rfl
theorem touch_users (r : Request) (t : State) : (touch r t).users = t.users := by
  unfold touch; split <;> rfl
theorem touch_role (r : Request) (t : State) : (touch r t).role = t.role := by
  unfold touch; split <;> rfl
theorem touch_status (r : Request) (t : State) : (touch r t).status = t.status := by
  unfold touch; split <;> rfl
theorem touch_content (r : Request) (t : State) : (touch r t).content = t.content := by
  unfold touch; split <;> rfl

def step : Impl := fun s r =>
  if (refStep s r).1 = .ok then (.ok, touch r (refStep s r).2) else refStep s r

theorem step_ok {s : State} {r : Request} (h : (step s r).1 = .ok) :
    (refStep s r).1 = .ok ∧ step s r = (.ok, touch r (refStep s r).2) := by
  unfold step at *
  by_cases hk : (refStep s r).1 = .ok
  · simp [hk]
  · simp [hk] at h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, ref_req_valid_succeeds s r h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, ref_req_invalid_noop s r h]

theorem req_authorization : Authorized step := by
  intro s r h
  exact ref_req_authorization s r (step_ok h).1

theorem req_single_doc : SingleDoc step := by
  intro s r h d hd
  obtain ⟨hk, he⟩ := step_ok h
  rw [he]
  simp only [touch_status, touch_content]
  exact ref_req_single_doc s r hk d hd

theorem req_effects : ∀ s r, (step s r).1 = .ok →
    (step s r).2.docs = s.docs ∧
    (step s r).2.users = s.users ∧
    (step s r).2.role = s.role ∧
    (∀ d, (step s r).2.status d = expectedStatus s r d) ∧
    (∀ d, (step s r).2.content d = expectedContent s r d) := by
  intro s r h
  obtain ⟨hk, he⟩ := step_ok h
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := ref_req_effects s r hk
  rw [he]
  simp only [touch_docs, touch_users, touch_role, touch_status, touch_content]
  exact ⟨h1, h2, h3, h4, h5⟩

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hd
  unfold step
  split
  · simp only [touch_content]; exact ref_req_published_immutable s r d hd
  · exact ref_req_published_immutable s r d hd

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  unfold step
  split
  · simp only [touch_status]; exact ref_req_no_unpublish s r d
  · exact ref_req_no_unpublish s r d

theorem touch_prefix (r : Request) (t : State) : t.audit <+: (touch r t).audit := by
  unfold touch
  split
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  unfold step
  split
  · exact (ref_req_audit_append_only s r).trans (touch_prefix r _)
  · exact ref_req_audit_append_only s r

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hc
  unfold step
  split
  · rename_i hk
    have hc' := ref_req_audit_consistent s r hc
    have hv := ref_ok_valid hk
    obtain ⟨h1, _, _, h4, _, _⟩ := ref_req_effects s r hk
    intro d hd
    rw [touch_docs] at hd
    rw [touch_status]
    unfold touch
    split
    · rename_i he
      simp only [replay_append_single]
      split
      · rename_i hdd
        subst hdd
        rw [h4, expectedStatus]
        have : ¬ (r.kind = .move ∧ r.doc = r.doc) := fun h => by rw [he] at h; cases h.1
        rw [if_neg this]
        exact ((hv.2.2.2 he).2).symm
      · exact hc' d hd
    · exact hc' d hd
  · exact ref_req_audit_consistent s r hc

end Workflow
