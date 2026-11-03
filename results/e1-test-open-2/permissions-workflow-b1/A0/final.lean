import Workflow.Spec

namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest
  infer_instance

def step : Impl := fun s r =>
  if _h : ValidRequest s r then
    (.ok, { docs := s.docs, users := s.users, status := expectedStatus s r, content := expectedContent s r, role := s.role, audit := expectedAudit s r })
  else
    (.rejected, s)

private theorem step_ok_iff (s : State) (r : Request) : (step s r).1 = .ok ↔ ValidRequest s r := by
  unfold step
  split
  · next h => simp [h]
  · next h => simp [h]

private theorem step_eq_ok_state (s : State) (r : Request) (h : ValidRequest s r) :
    (step s r).2 = { docs := s.docs, users := s.users, status := expectedStatus s r, content := expectedContent s r, role := s.role, audit := expectedAudit s r } := by
  unfold step
  simp [h]

private theorem step_eq_rejected_state (s : State) (r : Request) (h : ¬ ValidRequest s r) :
    (step s r).2 = s := by
  unfold step
  simp [h]

private theorem replay_append_single (l : List Entry) (e : Entry) (d : DocId) (st : Status) :
    replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
  induction l generalizing st with
  | nil => simp [replay]
  | cons hd tl ih => simp [replay, ih]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  exact (step_ok_iff s r).mpr h

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : Authorized step := by
  intro s r hOk
  have hVR : ValidRequest s r := (step_ok_iff s r).mp hOk
  exact ⟨fun heq => hVR.2.2.1 heq, fun heq => hVR.2.2.2 heq⟩

theorem req_single_doc : SingleDoc step := by
  intro s r hOk d hNe
  have hVR : ValidRequest s r := (step_ok_iff s r).mp hOk
  have hEq := step_eq_ok_state s r hVR
  have hCond : ¬ (r.kind = .move ∧ d = r.doc) := fun h => hNe h.2
  have hCond2 : ¬ (r.kind = .edit ∧ d = r.doc) := fun h => hNe h.2
  constructor
  · have h1 : (step s r).2.status d = expectedStatus s r d := by rw [hEq]
    rw [h1]
    unfold expectedStatus
    simp [hCond]
  · have h1 : (step s r).2.content d = expectedContent s r d := by rw [hEq]
    rw [h1]
    unfold expectedContent
    simp [hCond2]

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hPub
  by_cases hVR : ValidRequest s r
  · have hEq := step_eq_ok_state s r hVR
    have h1 : (step s r).2.content d = expectedContent s r d := by rw [hEq]
    rw [h1]
    unfold expectedContent
    by_cases hCase : r.kind = .edit ∧ d = r.doc
    · have hk : r.kind = .edit := hCase.1
      have heqd : d = r.doc := hCase.2
      subst heqd
      have hEdit := hVR.2.2.2 hk
      have hDraft : s.status r.doc = .draft := hEdit.2
      rcases hPub with hP | hA
      · rw [hP] at hDraft; cases hDraft
      · rw [hA] at hDraft; cases hDraft
    · simp [hCase]
  · have hEq := step_eq_rejected_state s r hVR
    rw [hEq]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hPub
    by_cases hVR : ValidRequest s r
    · have hEq : (step s r).2.status d = expectedStatus s r d := by
        calc (step s r).2.status d = ({ docs := s.docs, users := s.users, status := expectedStatus s r, content := expectedContent s r, role := s.role, audit := expectedAudit s r } : State).status d := by rw [← step_eq_ok_state s r hVR]
          _ = expectedStatus s r d := rfl
      rw [hEq]
      unfold expectedStatus
      by_cases hM : r.kind = .move ∧ d = r.doc
      · have hM1 : r.kind = .move := hM.1
        have hDEq : d = r.doc := hM.2
        subst hDEq
        have hAllowed : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hVR.2.2.1 hM1
        have hDstArch : r.dst = .archived := by
          unfold allowed at hAllowed
          cases hr : s.role r.actor <;> cases hs : s.status r.doc <;> cases hd : r.dst <;> simp_all
        simp [hM, hDstArch]
      · simp [hM, hPub]
    · have hEq := step_eq_rejected_state s r hVR
      rw [hEq]; left; exact hPub
  · intro hArch
    by_cases hVR : ValidRequest s r
    · have hEq : (step s r).2.status d = expectedStatus s r d := by
        calc (step s r).2.status d = ({ docs := s.docs, users := s.users, status := expectedStatus s r, content := expectedContent s r, role := s.role, audit := expectedAudit s r } : State).status d := by rw [← step_eq_ok_state s r hVR]
          _ = expectedStatus s r d := rfl
      rw [hEq]
      unfold expectedStatus
      by_cases hM : r.kind = .move ∧ d = r.doc
      · have hM1 : r.kind = .move := hM.1
        have hDEq : d = r.doc := hM.2
        subst hDEq
        exfalso
        have hAllowed : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hVR.2.2.1 hM1
        have hDocArch : s.status r.doc = .archived := hArch
        unfold allowed at hAllowed
        cases hr : s.role r.actor <;> cases hs : s.status r.doc <;> cases hd : r.dst <;> simp_all
      · simp [hM, hArch]
    · have hEq := step_eq_rejected_state s r hVR
      rw [hEq]; exact hArch

theorem req_effects : Effects step := by
  intro s r hOk
  have hVR : ValidRequest s r := (step_ok_iff s r).mp hOk
  have hEq := step_eq_ok_state s r hVR
  rw [hEq]
  exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  by_cases hVR : ValidRequest s r
  · have hEq : (step s r).2.audit = expectedAudit s r := by
      calc (step s r).2.audit = ({ docs := s.docs, users := s.users, status := expectedStatus s r, content := expectedContent s r, role := s.role, audit := expectedAudit s r } : State).audit := by rw [← step_eq_ok_state s r hVR]
        _ = expectedAudit s r := rfl
    rw [hEq]
    unfold expectedAudit
    by_cases hM : r.kind = .move
    · simp [hM]
    · simp [hM]
  · have hEq := step_eq_rejected_state s r hVR
    rw [hEq]
    exact List.prefix_rfl

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons d hMem
  by_cases hVR : ValidRequest s r
  · have hStepAll : (step s r).2 = { docs := s.docs, users := s.users, status := expectedStatus s r, content := expectedContent s r, role := s.role, audit := expectedAudit s r } := step_eq_ok_state s r hVR
    have hMemS : d ∈ s.docs := by
      have : d ∈ (step s r).2.docs := hMem
      rw [hStepAll] at this
      simpa using this
    have hReplayOrig : replay s.audit d .draft = s.status d := hCons d hMemS
    have hAuditEq : (step s r).2.audit = expectedAudit s r := by rw [hStepAll]
    have hStatusEq : (step s r).2.status d = expectedStatus s r d := by rw [hStepAll]
    rw [hAuditEq, hStatusEq]
    by_cases hKindMove : r.kind = .move
    · have hAuditExp : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by unfold expectedAudit; simp [hKindMove]
      rw [hAuditExp, replay_append_single]
      unfold expectedStatus
      by_cases hDocEq : r.doc = d
      · have hCond : (r.kind = .move ∧ d = r.doc) := ⟨hKindMove, hDocEq.symm⟩
        have hIf1 : (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = r.dst := if_pos hCond
        have hIf2 : (if (⟨r.doc, r.actor, s.status r.doc, r.dst⟩ : Entry).doc = d then r.dst else replay s.audit d .draft) = r.dst := if_pos hDocEq
        rw [hIf1, hIf2]
      · have hCond : ¬ (r.kind = .move ∧ d = r.doc) := fun h => hDocEq h.2.symm
        have hIf1 : (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = s.status d := if_neg hCond
        have hIf2 : (if (⟨r.doc, r.actor, s.status r.doc, r.dst⟩ : Entry).doc = d then r.dst else replay s.audit d .draft) = replay s.audit d .draft := if_neg hDocEq
        rw [hIf1, hIf2, hReplayOrig]
    · have hAuditExp : expectedAudit s r = s.audit := by unfold expectedAudit; simp [hKindMove]
      have hES : expectedStatus s r d = s.status d := by unfold expectedStatus; simp [hKindMove]
      rw [hAuditExp, hES, hReplayOrig]
  · have hStep : (step s r).2 = s := step_eq_rejected_state s r hVR
    rw [hStep] at hMem ⊢
    exact hCons d hMem

end Workflow
