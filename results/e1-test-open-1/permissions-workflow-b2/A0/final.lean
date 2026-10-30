import Workflow.Spec
namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest
  infer_instance

def step : Impl := fun s r =>
  if ValidRequest s r then
    match r.kind with
    | .move =>
      (Outcome.ok,
        { s with
          status := fun d => if d = r.doc then r.dst else s.status d
          audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] })
    | .edit =>
      (Outcome.ok,
        { s with
          content := fun d => if d = r.doc then r.body else s.content d })
  else
    (Outcome.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp only [h, ite_true]
  cases hr : r.kind <;> rfl

private theorem ok_imp_valid {s r} (hOk : (step s r).1 = Outcome.ok) : ValidRequest s r := by
  by_cases hV : ValidRequest s r
  · exact hV
  · have hRej : (step s r).1 = Outcome.rejected := by unfold step; simp only [hV, ite_false]
    rw [hRej] at hOk; contradiction

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp only [h, ite_false]

theorem req_authorization : Authorized step := by
  intro s r hOk
  have hV := ok_imp_valid (s:=s) (r:=r) hOk
  exact ⟨fun hk => hV.2.2.1 hk, fun hk => hV.2.2.2 hk⟩

theorem req_single_doc : SingleDoc step := by
  intro s r hOk d hd
  have hV := ok_imp_valid (s:=s) (r:=r) hOk
  have hd' : ¬ d = r.doc := hd
  by_cases hk : r.kind = Kind.move
  · have hS : (step s r).2.status d = if d = r.doc then r.dst else s.status d := by
      unfold step; simp only [hV, ite_true, hk]
    have hC : (step s r).2.content d = s.content d := by
      unfold step; simp only [hV, ite_true, hk]
    exact ⟨by rw [hS]; simp only [hd', ite_false], hC⟩
  · have hEdit : r.kind = Kind.edit := by
      cases hr : r.kind with | move => contradiction | edit => rfl
    have hS : (step s r).2.status d = s.status d := by
      unfold step; simp only [hV, ite_true, hEdit]
    have hC : (step s r).2.content d = if d = r.doc then r.body else s.content d := by
      unfold step; simp only [hV, ite_true, hEdit]
    exact ⟨hS, by rw [hC]; simp only [hd', ite_false]⟩

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hs
  by_cases hV : ValidRequest s r
  · by_cases hk : r.kind = Kind.move
    · have : (step s r).2.content d = s.content d := by unfold step; simp only [hV, ite_true, hk]
      exact this
    · have hEdit : r.kind = Kind.edit := by cases hr : r.kind <;> simp_all
      have hNeed := hV.2.2.2 hEdit
      by_cases heq : d = r.doc
      · subst heq; rcases hs with hp | ha <;> simp_all
      · have hC : (step s r).2.content d = if d = r.doc then r.body else s.content d := by
          unfold step; simp only [hV, ite_true, hEdit]
        rw [hC]; simp only [heq, ite_false]
  · have : (step s r).2.content d = s.content d := by unfold step; simp only [hV, ite_false]
    exact this

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hV : ValidRequest s r
    · by_cases hk : r.kind = Kind.move
      · by_cases heq : d = r.doc
        · have hAll := hV.2.2.1 hk
          have hPub : s.status r.doc = Status.published := by rw [← heq, hpub]
          rw [hPub] at hAll
          have hS : (step s r).2.status d = r.dst := by
            unfold step; simp only [hV, ite_true, hk, heq, ite_true]
          rw [hS]
          cases hr : s.role r.actor <;> cases hd : r.dst <;> simp_all [allowed]
        · have hS : (step s r).2.status d = s.status d := by
            unfold step; simp only [hV, ite_true, hk, heq, ite_false]
          rw [hS]; exact Or.inl hpub
      · have hEdit : r.kind = Kind.edit := by cases hr : r.kind <;> simp_all
        have hS : (step s r).2.status d = s.status d := by
          unfold step; simp only [hV, ite_true, hEdit]
        rw [hS]; exact Or.inl hpub
    · have hS : (step s r).2.status d = s.status d := by
        unfold step; simp only [hV, ite_false]
      rw [hS]; exact Or.inl hpub
  · intro harch
    by_cases hV : ValidRequest s r
    · by_cases hk : r.kind = Kind.move
      · by_cases heq : d = r.doc
        · have hAll := hV.2.2.1 hk
          have hArc : s.status r.doc = Status.archived := by rw [← heq, harch]
          rw [hArc] at hAll
          cases hr : s.role r.actor <;> cases hd : r.dst <;> simp_all [allowed]
        · have hS : (step s r).2.status d = s.status d := by
            unfold step; simp only [hV, ite_true, hk, heq, ite_false]
          rw [hS, harch]
      · have hEdit : r.kind = Kind.edit := by cases hr : r.kind <;> simp_all
        have hS : (step s r).2.status d = s.status d := by
          unfold step; simp only [hV, ite_true, hEdit]
        rw [hS, harch]
    · have hS : (step s r).2.status d = s.status d := by
        unfold step; simp only [hV, ite_false]
      rw [hS, harch]

theorem req_effects : Effects step := by
  intro s r hOk
  have hV := ok_imp_valid hOk
  unfold step; simp only [hV, ite_true]
  cases hk : r.kind
  · refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro d; unfold expectedStatus; simp only [hk, true_and]
    · intro d; unfold expectedContent; have hne : ¬ (Kind.move = Kind.edit) := by decide
      simp only [hk, hne, false_and, ite_false]
    · unfold expectedAudit; simp only [hk, ite_true]
  · refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro d; unfold expectedStatus; have hne : ¬ (Kind.edit = Kind.move) := by decide
      simp only [hk, hne, false_and, ite_false]
    · intro d; unfold expectedContent; simp only [hk, true_and]
    · unfold expectedAudit; have hne : ¬ (Kind.edit = Kind.move) := by decide
      simp only [hk, hne, ite_false]

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  by_cases hV : ValidRequest s r
  · unfold step; simp only [hV, ite_true]; cases hk : r.kind
    · exact List.prefix_append s.audit _
    · exact ⟨[], by simp⟩
  · unfold step; simp only [hV, ite_false]; exact ⟨[], by simp⟩

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons d hd
  have hDocs : (step s r).2.docs = s.docs := by
    unfold step
    by_cases hV : ValidRequest s r
    · simp only [hV, ite_true]; cases hk : r.kind <;> rfl
    · simp only [hV, ite_false]
  have hd0 : d ∈ s.docs := by rw [← hDocs]; exact hd
  have hRep0 := hCons d hd0
  by_cases hV : ValidRequest s r
  · cases hk : r.kind
    · have hStepAudit : (step s r).2.audit = s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] := by
        unfold step; simp only [hV, ite_true, hk]
      have hStepStatus : (step s r).2.status d = if d = r.doc then r.dst else s.status d := by
        unfold step; simp only [hV, ite_true, hk]
      rw [hStepAudit, hStepStatus]
      have append_lemma : ∀ (l : List Entry) (e : Entry) (st : Status),
          replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
        intro l e st
        induction l generalizing st with
        | nil => simp [replay]
        | cons h t ih => simp [replay, ih]
      rw [append_lemma]
      by_cases heq : d = r.doc
      · simp only [heq.symm, ite_true]
      · have h1 : ¬ r.doc = d := fun h => heq h.symm
        simp only [heq, ite_false, h1, hRep0]
    · have hStepAudit : (step s r).2.audit = s.audit := by unfold step; simp only [hV, ite_true, hk]
      have hStepStatus : (step s r).2.status d = s.status d := by unfold step; simp only [hV, ite_true, hk]
      rw [hStepAudit, hStepStatus]; exact hRep0
  · have hStepAudit : (step s r).2.audit = s.audit := by unfold step; simp only [hV, ite_false]
    have hStepStatus : (step s r).2.status d = s.status d := by unfold step; simp only [hV, ite_false]
    rw [hStepAudit, hStepStatus]; exact hRep0

end Workflow
