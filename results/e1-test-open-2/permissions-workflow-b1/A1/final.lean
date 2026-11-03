import Workflow.Spec
namespace Workflow
instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance

def doMove (s : State) (r : Request) : State :=
  { s with status := fun d => if d = r.doc then r.dst else s.status d,
           audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] }

def doEdit (s : State) (r : Request) : State :=
  { s with content := fun d => if d = r.doc then r.body else s.content d }

def step : Impl := fun s r =>
  if _h : ValidRequest s r then
    match hr : r.kind with
    | .move => (.ok, doMove s r)
    | .edit => (.ok, doEdit s r)
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]
  split
  · rfl
  · cases hk : r.kind <;> simp [hk] at h ⊢

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : Authorized step := by
  intro s r hok
  have hVR : ValidRequest s r := by
    by_cases h : ValidRequest s r
    · exact h
    · have heq : (step s r).1 = .rejected := by simp [step, h]
      rw [heq] at hok
      contradiction
  exact ⟨fun hm => hVR.2.2.1 hm, fun he => ⟨hVR.2.2.2 he |>.1, hVR.2.2.2 he |>.2⟩⟩

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  have hVR : ValidRequest s r := by
    by_cases h : ValidRequest s r
    · exact h
    · have heq : (step s r).1 = .rejected := by simp [step, h]
      rw [heq] at hok
      contradiction
  simp only [step, hVR, dite_true] at hok ⊢
  cases hk : r.kind
  · simp [doMove, hne]
  · simp [doEdit, hne]

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hstat
  simp only [step]
  by_cases hVR : ValidRequest s r
  · simp only [hVR, dite_true]
    cases hk : r.kind
    · simp [doMove]
    · simp only [doEdit]
      -- show content unchanged
      have hEdit := hVR.2.2.2 hk
      -- edit requires doc is draft
      have hDraft : s.status r.doc = .draft := hEdit.2
      by_cases heq : d = r.doc
      · subst heq
        cases hstat with
        | inl hpub => rw [hpub] at hDraft; contradiction
        | inr harc => rw [harc] at hDraft; contradiction
      · simp [heq]
  · simp [hVR]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    simp only [step]
    by_cases hVR : ValidRequest s r
    · simp only [hVR, dite_true]
      cases hk : r.kind
      · simp only [doMove]
        by_cases heq : d = r.doc
        · subst heq
          have hAllow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hVR.2.2.1 hk
          rw [hpub] at hAllow
          cases hrole : s.role r.actor <;> cases hdst : r.dst <;> simp [allowed, hrole, hdst] at hAllow ⊢
        · simp [heq, hpub]
      · simp [doEdit, hpub]
    · simp [hVR, hpub]
  · intro harc
    simp only [step]
    by_cases hVR : ValidRequest s r
    · simp only [hVR, dite_true]
      cases hk : r.kind
      · simp only [doMove]
        by_cases heq : d = r.doc
        · subst heq
          have hAllow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hVR.2.2.1 hk
          rw [harc] at hAllow
          cases hrole : s.role r.actor <;> cases hdst : r.dst <;> simp [allowed, hrole, hdst] at hAllow
        · simp [heq, harc]
      · simp [doEdit, harc]
    · simp [hVR, harc]

theorem req_effects : Effects step := by
  intro s r hok
  have hVR : ValidRequest s r := by
    by_cases h : ValidRequest s r
    · exact h
    · have heq : (step s r).1 = .rejected := by simp [step, h]
      rw [heq] at hok
      contradiction
  simp only [step, hVR, dite_true] at hok ⊢
  cases hk : r.kind
  · simp [doMove, expectedStatus, expectedContent, expectedAudit, hk]
  · simp [doEdit, expectedStatus, expectedContent, expectedAudit, hk]

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  simp only [step]
  by_cases hVR : ValidRequest s r
  · simp only [hVR, dite_true]
    cases hk : r.kind
    · simp [doMove]
    · simp [doEdit]
  · simp [hVR]

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons
  simp only [step]
  by_cases hVR : ValidRequest s r
  · simp only [hVR, dite_true]
    cases hk : r.kind with
    | move =>
      simp only [doMove]
      intro d hd
      -- prove helper: replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st
      have hAux : ∀ (l : List Entry) (e : Entry) (d : DocId) (st : Status),
        replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
        intro l
        induction l with
        | nil => intro e d st; simp [replay]
        | cons hd tl ih =>
          intro e d st
          simp only [List.cons_append]
          simp only [replay]
          rw [ih]
      have hReplay : replay (s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }]) d .draft
        = if r.doc = d then r.dst else replay s.audit d .draft := by
        exact hAux s.audit { doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst } d .draft
      -- Now show goal
      show replay (s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }]) d .draft = (if d = r.doc then r.dst else s.status d)
      rw [hReplay]
      have hOld : replay s.audit d .draft = s.status d := hCons d hd
      -- need to rewrite condition r.doc = d vs d = r.doc
      by_cases heq : d = r.doc
      · subst heq; simp [hOld]
      · have heq2 : ¬ (r.doc = d) := by intro h; apply heq; rw [← h]
        simp [heq2, hOld, heq]
    | edit =>
      simp only [doEdit]
      intro d hd
      exact hCons d hd
  · simp only [hVR, dite_false]
    exact hCons

end Workflow
