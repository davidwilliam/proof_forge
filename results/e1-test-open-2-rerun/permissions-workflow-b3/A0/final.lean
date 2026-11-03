import Workflow.Spec
namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest
  infer_instance

def step : Impl := fun s r =>
  if _h : ValidRequest s r then
    (.ok,
      { docs := s.docs
        users := s.users
        status := fun d => expectedStatus s r d
        content := fun d => expectedContent s r d
        role := s.role
        audit := expectedAudit s r })
  else
    (.rejected, s)

theorem replayAppendOne (l : List Entry) (e : Entry) (d : DocId) (init : Status) :
    replay (l ++ [e]) d init = if e.doc = d then e.dst else replay l d init := by
  induction l generalizing init with
  | nil =>
    simp only [List.nil_append, replay]
  | cons hd tl ih =>
    have heq : (hd :: tl) ++ [e] = hd :: (tl ++ [e]) := by simp
    rw [heq]
    simp only [replay]
    by_cases h : hd.doc = d
    · simp only [h, ↓reduceIte]
      rw [ih]
    · simp only [h, ↓reduceIte]
      rw [ih]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hVR
  show (step s r).1 = Outcome.ok
  simp [step, hVR]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hN
  show step s r = (Outcome.rejected, s)
  simp [step, hN]

theorem req_authorization : Authorized step := by
  intro s r hOk
  show (r.kind = Kind.move → allowed (s.role r.actor) (s.status r.doc) r.dst = true) ∧ (r.kind = Kind.edit → s.role r.actor = Role.author ∧ s.status r.doc = Status.draft)
  by_cases hVR : ValidRequest s r
  · exact ⟨hVR.2.2.1, hVR.2.2.2⟩
  · have h1 : (step s r).1 = Outcome.rejected := by simp [step, hVR]
    rw [h1] at hOk
    cases hOk

theorem req_single_doc : SingleDoc step := by
  intro s r hOk d hNe
  show (step s r).2.status d = s.status d ∧ (step s r).2.content d = s.content d
  by_cases hVR : ValidRequest s r
  · have hSt : (step s r).2.status d = expectedStatus s r d := by simp [step, hVR]
    have hCo : (step s r).2.content d = expectedContent s r d := by simp [step, hVR]
    rw [hSt, hCo]
    constructor
    · unfold expectedStatus
      simp [show ¬ (r.kind = Kind.move ∧ d = r.doc) from fun ⟨_, hEq⟩ => hNe hEq]
    · unfold expectedContent
      simp [show ¬ (r.kind = Kind.edit ∧ d = r.doc) from fun ⟨_, hEq⟩ => hNe hEq]
  · have h1 : (step s r).1 = Outcome.rejected := by simp [step, hVR]
    rw [h1] at hOk
    cases hOk

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hPub
  show (step s r).2.content d = s.content d
  by_cases hVR : ValidRequest s r
  · have hCo : (step s r).2.content d = expectedContent s r d := by simp [step, hVR]
    rw [hCo]
    unfold expectedContent
    by_cases hK : r.kind = Kind.edit ∧ d = r.doc
    · obtain ⟨hKe, hDe⟩ := hK
      have hEdit := hVR.2.2.2 hKe
      have hDraft : s.status r.doc = Status.draft := hEdit.2
      have hPub' : s.status r.doc = Status.published ∨ s.status r.doc = Status.archived := by
        rw [← hDe]; exact hPub
      rcases hPub' with hP | hA
      · rw [hP] at hDraft; cases hDraft
      · rw [hA] at hDraft; cases hDraft
    · simp [hK]
  · have hEq : (step s r).2 = s := by simp [step, hVR]
    rw [hEq]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  show (s.status d = Status.published → (step s r).2.status d = Status.published ∨ (step s r).2.status d = Status.archived) ∧ (s.status d = Status.archived → (step s r).2.status d = Status.archived)
  constructor
  · intro hPub
    by_cases hVR : ValidRequest s r
    · have hSt : (step s r).2.status d = expectedStatus s r d := by simp [step, hVR]
      rw [hSt]
      unfold expectedStatus
      by_cases hKM : r.kind = Kind.move ∧ d = r.doc
      · obtain ⟨hKm, hEq⟩ := hKM
        have hEq' : d = r.doc := hEq
        simp only [hKm, hEq', and_self, ↓reduceIte]
        have hAll : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hVR.2.2.1 hKm
        have hPub' : s.status r.doc = Status.published := by rw [← hEq']; exact hPub
        rw [hPub'] at hAll
        cases hRole : s.role r.actor <;> cases hDst : r.dst <;> simp_all [allowed]
      · simp [hKM, hPub]
    · have hEq : (step s r).2 = s := by simp [step, hVR]
      rw [hEq, hPub]; left; rfl
  · intro hArch
    by_cases hVR : ValidRequest s r
    · have hSt : (step s r).2.status d = expectedStatus s r d := by simp [step, hVR]
      rw [hSt]
      unfold expectedStatus
      by_cases hKM : r.kind = Kind.move ∧ d = r.doc
      · obtain ⟨hKm, hEq⟩ := hKM
        have hAll : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hVR.2.2.1 hKm
        have hArch' : s.status r.doc = Status.archived := by rw [← hEq]; exact hArch
        rw [hArch'] at hAll
        cases hRole : s.role r.actor <;> cases hDst : r.dst <;> simp_all [allowed]
      · simp [hKM, hArch]
    · have hEq : (step s r).2 = s := by simp [step, hVR]
      rw [hEq, hArch]

theorem req_effects : Effects step := by
  intro s r hOk
  show (step s r).2.docs = s.docs ∧ (step s r).2.users = s.users ∧ (step s r).2.role = s.role ∧ (∀ d, (step s r).2.status d = expectedStatus s r d) ∧ (∀ d, (step s r).2.content d = expectedContent s r d) ∧ (step s r).2.audit = expectedAudit s r
  by_cases hVR : ValidRequest s r
  · simp [step, hVR]
  · have h1 : (step s r).1 = Outcome.rejected := by simp [step, hVR]
    rw [h1] at hOk
    cases hOk

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  show s.audit <+: (step s r).2.audit
  by_cases hVR : ValidRequest s r
  · have hAu : (step s r).2.audit = expectedAudit s r := by simp [step, hVR]
    rw [hAu]
    unfold expectedAudit
    by_cases hK : r.kind = Kind.move
    · simp only [hK, ↓reduceIte, List.prefix_append]
    · simp only [hK, ↓reduceIte]
      exact ⟨[], by simp⟩
  · have hAu : (step s r).2 = s := by simp [step, hVR]
    rw [hAu]
    exact ⟨[], by simp⟩

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons
  show AuditConsistent (step s r).2
  intro d hd
  by_cases hVR : ValidRequest s r
  · have hStDocs : (step s r).2.docs = s.docs := by simp [step, hVR]
    have hStStatus : ∀ x, (step s r).2.status x = expectedStatus s r x := by intro x; simp [step, hVR]
    have hStAudit : (step s r).2.audit = expectedAudit s r := by simp [step, hVR]
    have hdOld : d ∈ s.docs := by rw [← hStDocs]; exact hd
    have hRepOld : replay s.audit d Status.draft = s.status d := hCons d hdOld
    rw [hStAudit, hStStatus]
    by_cases hK : r.kind = Kind.move
    · have hEA : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by
        unfold expectedAudit; simp only [hK, ↓reduceIte]
      rw [hEA]
      have hEq : replay (s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }]) d Status.draft = if r.doc = d then r.dst else replay s.audit d Status.draft := replayAppendOne s.audit _ d _
      rw [hEq, hRepOld]
      unfold expectedStatus
      by_cases hEq2 : r.doc = d
      · have hAnd : r.kind = Kind.move ∧ d = r.doc := ⟨hK, hEq2.symm⟩
        rw [if_pos hEq2, if_pos hAnd]
      · have hAnd : ¬ (r.kind = Kind.move ∧ d = r.doc) := fun ⟨_, h2⟩ => hEq2 h2.symm
        rw [if_neg hEq2, if_neg hAnd]
    · have hEA : expectedAudit s r = s.audit := by unfold expectedAudit; simp only [hK, ↓reduceIte]
      rw [hEA, hRepOld]
      unfold expectedStatus
      have hCond : ¬ (r.kind = Kind.move ∧ d = r.doc) := fun ⟨h1,_⟩ => hK h1
      rw [if_neg hCond]
  · have hEq : (step s r).2 = s := by simp [step, hVR]
    rw [hEq] at hd ⊢
    exact hCons d hd

end Workflow
