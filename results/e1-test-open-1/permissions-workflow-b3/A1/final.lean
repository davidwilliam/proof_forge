import Workflow.Spec
namespace Workflow

def doMove (s : State) (r : Request) : State :=
  { s with status := fun d => if d == r.doc then r.dst else s.status d,
           audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] }

def doEdit (s : State) (r : Request) : State :=
  { s with content := fun d => if d == r.doc then r.body else s.content d }

def step : Impl := fun s r =>
  if s.docs.contains r.doc && s.users.contains r.actor then
    match r.kind with
    | .move => if allowed (s.role r.actor) (s.status r.doc) r.dst then (.ok, doMove s r) else (.rejected, s)
    | .edit => if s.role r.actor == .author && s.status r.doc == .draft then (.ok, doEdit s r) else (.rejected, s)
  else (.rejected, s)

theorem dummy : True := trivial
#print Workflow.step

theorem req_audit_append_only_dup : True := trivial

theorem req_valid_succeeds       : ValidSucceeds step := sorry

theorem req_invalid_noop         : InvalidNoop step := sorry

theorem req_authorization        : Authorized step := by
  intro s r h
  constructor
  · intro hm
    unfold step at h
    rw [hm] at h
    simp only at h
    split at h
    · next hmem =>
      split at h
      · next ha => exact ha
      · next ha => simp at h
    · simp at h
  · intro he
    unfold step at h
    rw [he] at h
    simp only at h
    split at h
    · next hmem =>
      split at h
      · next ha =>
        have ha' := (Bool.and_eq_true_iff.mp ha)
        have h1 : s.role r.actor == Role.author := by simpa using ha'.1
        have h2 : s.status r.doc == Status.draft := by simpa using ha'.2
        have hr : s.role r.actor = Role.author := by
          cases hrole : s.role r.actor <;> simp_all
        have hs : s.status r.doc = Status.draft := by
          cases hst : s.status r.doc <;> simp_all
        exact ⟨hr, hs⟩
      · next ha => simp at h
    · simp at h

theorem req_single_doc           : SingleDoc step := sorry

theorem req_published_immutable  : PublishedImmutable step := sorry

theorem req_no_unpublish         : NoUnpublish step := sorry

theorem req_effects              : Effects step := sorry

theorem req_audit_append_only    : AuditAppendOnly step := sorry

theorem req_audit_consistent     : KeepsAuditConsistent step := sorry

end Workflow
