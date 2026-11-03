import Workflow.Spec
namespace Workflow
instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance
def edges : List (Role × Status × Status) :=
  [(.author, .draft, .review), (.author, .draft, .archived), (.author, .review, .draft),
   (.reviewer, .review, .approved), (.reviewer, .review, .draft),
   (.publisher, .approved, .published), (.publisher, .approved, .draft),
   (.publisher, .published, .archived)]

def mayMove (s : State) (r : Request) : Bool :=
  edges.contains (s.role r.actor, s.status r.doc, r.dst)

def mayEdit (s : State) (r : Request) : Bool :=
  s.role r.actor == .author && s.status r.doc == .draft

def doMove (s : State) (r : Request) : State :=
  { s with status := fun d => if d == r.doc then r.dst else s.status d,
           audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] }

def doEdit (s : State) (r : Request) : State :=
  { s with content := fun d => if d == r.doc then r.body else s.content d }

def step : Impl := fun s r =>
  if s.docs.contains r.doc && s.users.contains r.actor then
    match r.kind with
    | .move => if mayMove s r then (.ok, doMove s r) else (.rejected, s)
    | .edit => if mayEdit s r then (.ok, doEdit s r) else (.rejected, s)
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨hdocMem, huserMem, hmove, hedit⟩ := h
  unfold step
  have hconj : (r.doc ∈ s.docs ∧ r.actor ∈ s.users) := ⟨hdocMem, huserMem⟩
  simp [hconj]
  cases hk : r.kind with
  | move =>
    have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hk
    have hmay : mayMove s r = true := by unfold mayMove allowed at *; cases hr : s.role r.actor <;> cases hs : s.status r.doc <;> cases hd : r.dst <;> simp_all [edges]
    simp [hk, hmay]
  | edit =>
    have he := hedit hk
    have hmay : mayEdit s r = true := by unfold mayEdit; simp [he.1, he.2]
    simp [hk, hmay]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  by_cases hdoc : r.doc ∈ s.docs <;> by_cases huser : r.actor ∈ s.users
  · have hmem : ¬ ((r.kind = .move → allowed (s.role r.actor) (s.status r.doc) r.dst = true) ∧ (r.kind = .edit → s.role r.actor = .author ∧ s.status r.doc = .draft)) := by
      intro hc
      exact h ⟨hdoc, huser, hc.1, hc.2⟩
    simp [hdoc, huser]
    cases hk : r.kind
    · have hMayFalse : mayMove s r = false := by
        unfold mayMove allowed at *
        have hneed : ¬ (allowed (s.role r.actor) (s.status r.doc) r.dst = true) := by
          intro hall
          apply hmem
          constructor
          · intro _; exact hall
          · intro heq; simp [hk] at heq
        cases hr : s.role r.actor <;> cases hs : s.status r.doc <;> cases hd : r.dst <;> simp_all [edges]
      simp [hk, hMayFalse]
    · have hMayFalse : mayEdit s r = false := by
        unfold mayEdit
        have hneed : ¬ (s.role r.actor = .author ∧ s.status r.doc = .draft) := by
          intro hall
          apply hmem
          constructor
          · intro heq; simp [hk] at heq
          · intro _; exact hall
        cases hr : s.role r.actor <;> cases hs : s.status r.doc <;> simp_all
      simp [hk, hMayFalse]
  · simp [hdoc, huser]
  · simp [hdoc, huser]
  · simp [hdoc, huser]

theorem req_authorization : Authorized step := by
  intro s r hok
  have hok' : (step s r).1 = Outcome.ok := hok
  unfold step at hok'
  by_cases hconj : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · simp [hconj] at hok'
    cases hk : r.kind
    · simp [hk] at hok'
      by_cases hm : mayMove s r = true
      · simp [hm] at hok'
        constructor
        · intro _
          unfold mayMove at hm
          unfold allowed
          cases hr : s.role r.actor <;> cases hs : s.status r.doc <;> cases hd : r.dst <;> simp_all [edges]
        · intro heq
          simp [hk] at heq
      · simp [hm] at hok'
    · simp [hk] at hok'
      by_cases hm : mayEdit s r = true
      · simp [hm] at hok'
        constructor
        · intro heq
          simp [hk] at heq
        · intro _
          unfold mayEdit at hm
          have hAnd : (s.role r.actor == Role.author && s.status r.doc == Status.draft) = true := hm
          have hA : (s.role r.actor == Role.author) = true := (Bool.and_eq_true_iff.mp hAnd).1
          have hB : (s.status r.doc == Status.draft) = true := (Bool.and_eq_true_iff.mp hAnd).2
          have hr : s.role r.actor = Role.author := by
            cases h : s.role r.actor <;> simp_all
          have hs : s.status r.doc = Status.draft := by
            cases h : s.status r.doc <;> simp_all
          exact ⟨hr, hs⟩
      · simp [hm] at hok'
  · simp [hconj] at hok'

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hneq
  have hok' : (step s r).1 = Outcome.ok := hok
  unfold step at hok'
  by_cases hconj : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · simp [hconj] at hok'
    cases hk : r.kind
    · simp [hk] at hok'
      by_cases hm : mayMove s r = true
      · simp [hm] at hok'
        -- now (step s r).2 = doMove s r
        have hstep : (step s r).2 = doMove s r := by
          unfold step; simp [hconj, hk, hm]
        rw [hstep]
        unfold doMove
        have hbeq : (d == r.doc) = false := by
          simp [beq_iff_eq]
          intro heq; exact hneq heq
        simp [hbeq]
      · simp [hm] at hok'
    · simp [hk] at hok'
      by_cases hm : mayEdit s r = true
      · simp [hm] at hok'
        have hstep : (step s r).2 = doEdit s r := by
          unfold step; simp [hconj, hk, hm]
        rw [hstep]
        unfold doEdit
        have hbeq : (d == r.doc) = false := by
          simp [beq_iff_eq]
          intro heq; exact hneq heq
        simp [hbeq]
      · simp [hm] at hok'
  · simp [hconj] at hok'

theorem req_published_immutable  : PublishedImmutable step := by
  intro s r d h
  unfold step
  by_cases hconj : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · simp [hconj]
    cases hk : r.kind
    · simp only [hk]
      by_cases hm : mayMove s r = true
      · simp [hm]
        show (doMove s r).content d = s.content d
        unfold doMove; simp
      · simp [hm]
    · simp only [hk]
      by_cases hm : mayEdit s r = true
      · simp only [hm]
        show (doEdit s r).content d = s.content d
        have hDraft : s.status r.doc = Status.draft := by
          unfold mayEdit at hm
          have hAnd : (s.role r.actor == Role.author && s.status r.doc == Status.draft) = true := hm
          have h2 := (Bool.and_eq_true_iff.mp hAnd).2
          cases hs : s.status r.doc <;> simp_all
        unfold doEdit
        simp only
        by_cases heq : d == r.doc
        · have heq' : d = r.doc := by simp [beq_iff_eq] at heq; exact heq
          rw [heq'] at h
          rw [hDraft] at h
          simp at h
        · simp [heq]
      · simp [hm]
  · simp [hconj]

theorem req_no_unpublish         : NoUnpublish step := sorry

theorem req_effects              : Effects step := sorry

theorem req_audit_append_only    : AuditAppendOnly step := sorry

theorem req_audit_consistent     : KeepsAuditConsistent step := sorry

end Workflow
