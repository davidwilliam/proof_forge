import Workflow.Spec
/-!
# Reference solution A (build team; hidden from agents)

Closed form: check the specification predicate, then write the expected fields.
-/

namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance

def edges : List (Role × Status × Status) :=
  [(.author, .draft, .review), (.author, .draft, .archived), (.author, .review, .draft),
   (.reviewer, .review, .approved), (.reviewer, .review, .draft),
   (.publisher, .approved, .published), (.publisher, .approved, .draft),
   (.publisher, .published, .archived), (.publisher, .published, .draft)]

def mayMove (s : State) (r : Request) : Bool :=
  edges.contains (s.role r.actor, s.status r.doc, r.dst)

def mayEdit (s : State) (r : Request) : Bool :=
  s.role r.actor == .author && s.status r.doc == .draft

def doMove (s : State) (r : Request) : State :=
  { s with status := fun d => if d == r.doc then r.dst else s.status d,
           audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] }

def doEdit (s : State) (r : Request) : State :=
  { s with content := fun d => if d == r.doc then r.body else s.content d }

def buggyStep : Impl := fun s r =>
  if s.docs.contains r.doc && s.users.contains r.actor then
    match r.kind with
    | .move => if mayMove s r then (.ok, doMove s r) else (.rejected, s)
    | .edit => if mayEdit s r then (.ok, doEdit s r) else (.rejected, s)
  else (.rejected, s)

@[implemented_by buggyStep]
def step : Impl := fun s r =>
  if ValidRequest s r then
    (.ok, { s with status := expectedStatus s r, content := expectedContent s r,
                   audit := expectedAudit s r })
  else
    (.rejected, s)

theorem step_of_valid {s : State} {r : Request} (h : ValidRequest s r) :
    step s r = (.ok,
      { s with status := expectedStatus s r, content := expectedContent s r,
               audit := expectedAudit s r }) := by
  simp [step, h]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidRequest s r) :
    step s r = (.rejected, s) := by
  simp [step, h]

theorem ok_valid {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidRequest s r := by
  by_cases hv : ValidRequest s r
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [step_of_valid h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_invalid h

theorem req_authorization : Authorized step := by
  intro s r h
  exact (ok_valid h).2.2

theorem req_single_doc : SingleDoc step := by
  intro s r h d hd
  rw [step_of_valid (ok_valid h)]
  simp [expectedStatus, expectedContent, hd]

theorem req_effects : Effects step := by
  intro s r h
  rw [step_of_valid (ok_valid h)]
  exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hd
  by_cases hv : ValidRequest s r
  · rw [step_of_valid hv]
    show expectedContent s r d = s.content d
    unfold expectedContent
    split
    · rename_i hk
      obtain ⟨hk, rfl⟩ := hk
      have := (hv.2.2.2 hk).2
      rcases hd with hd | hd <;> rw [hd] at this <;> cases this
    · rfl
  · rw [step_of_invalid hv]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  by_cases hv : ValidRequest s r
  · rw [step_of_valid hv]
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
  · rw [step_of_invalid hv]
    exact ⟨fun hp => Or.inl hp, id⟩

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  by_cases hv : ValidRequest s r
  · rw [step_of_valid hv]
    show s.audit <+: expectedAudit s r
    unfold expectedAudit
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  · rw [step_of_invalid hv]; exact List.prefix_refl _

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hc
  by_cases hv : ValidRequest s r
  · rw [step_of_valid hv]
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
  · rw [step_of_invalid hv]; exact hc

end Workflow
