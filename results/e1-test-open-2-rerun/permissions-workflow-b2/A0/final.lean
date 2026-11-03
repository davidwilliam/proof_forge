import Workflow.Spec

namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest
  infer_instance

def step : Impl := fun s r =>
  if _h : ValidRequest s r then
    match r.kind with
    | .move => (.ok, { s with status := fun d => if d = r.doc then r.dst else s.status d, audit := s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] })
    | .edit => (.ok, { s with content := fun d => if d = r.doc then r.body else s.content d })
  else (.rejected, s)

private theorem step_ok_of_valid {s : State} {r : Request} (h : ValidRequest s r) : (step s r).1 = .ok := by
  unfold step
  simp only [h, dite_true]
  cases hk : r.kind
  · simp
  · simp

private theorem step_eq_of_not_valid {s : State} {r : Request} (h : ¬ ValidRequest s r) : step s r = (.rejected, s) := by
  unfold step
  simp [h]

private theorem valid_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidRequest s r := by
  by_cases hv : ValidRequest s r
  · exact hv
  · exfalso
    have heq := step_eq_of_not_valid hv
    rw [heq] at h
    simp at h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hv
  exact step_ok_of_valid hv

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  exact step_eq_of_not_valid h

theorem req_authorization : Authorized step := by
  intro s r hOk
  have hv := valid_of_ok (s:=s) (r:=r) hOk
  rcases hv with ⟨_, _, hMove, hEdit⟩
  constructor
  · intro hm; exact hMove hm
  · intro he; exact hEdit he

theorem req_single_doc : SingleDoc step := by
  intro s r hOk d hd
  have hv := valid_of_ok hOk
  unfold step at hOk
  simp only [hv, dite_true] at hOk
  unfold step
  simp only [hv, dite_true]
  cases hk : r.kind with
  | move => simp [hd]
  | edit => simp [hd]

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d h
  by_cases hv : ValidRequest s r
  · unfold step
    simp only [hv, dite_true]
    cases hk : r.kind with
    | move => simp
    | edit =>
      by_cases heq : d = r.doc
      · subst heq
        rcases hv with ⟨_, _, _, hEdit⟩
        have hE := hEdit hk
        rcases h with hpub | harch
        · rw [hpub] at hE; simp at hE
        · rw [harch] at hE; simp at hE
      · simp [heq]
  · unfold step
    simp [hv]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hv : ValidRequest s r
    · unfold step
      simp only [hv, dite_true]
      cases hk : r.kind with
      | edit => simp [hpub]
      | move =>
        by_cases heq : d = r.doc
        · subst heq
          rcases hv with ⟨_, _, hMove, _⟩
          have hAll : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hMove hk
          rw [hpub] at hAll
          cases hdst : r.dst with
          | draft =>
            have ht : allowed (s.role r.actor) .published .draft = false := by
              cases hr2 : s.role r.actor <;> simp [allowed]
            rw [hdst] at hAll; rw [ht] at hAll; simp at hAll
          | review =>
            have ht : allowed (s.role r.actor) .published .review = false := by
              cases hr2 : s.role r.actor <;> simp [allowed]
            rw [hdst] at hAll; rw [ht] at hAll; simp at hAll
          | approved =>
            have ht : allowed (s.role r.actor) .published .approved = false := by
              cases hr2 : s.role r.actor <;> simp [allowed]
            rw [hdst] at hAll; rw [ht] at hAll; simp at hAll
          | published => simp
          | archived => simp
        · simp [heq, hpub]
    · unfold step
      simp [hv, hpub]
  · intro harch
    by_cases hv : ValidRequest s r
    · unfold step
      simp only [hv, dite_true]
      cases hk : r.kind with
      | edit => simp [harch]
      | move =>
        by_cases heq : d = r.doc
        · subst heq
          rcases hv with ⟨_, _, hMove, _⟩
          have hAll : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hMove hk
          rw [harch] at hAll
          have ht : allowed (s.role r.actor) .archived r.dst = false := by
            cases hr : s.role r.actor <;> cases hr2 : r.dst <;> simp [allowed]
          rw [ht] at hAll; simp at hAll
        · simp [heq, harch]
    · unfold step
      simp [hv, harch]

theorem req_effects : Effects step := by
  intro s r hOk
  have hv := valid_of_ok hOk
  unfold step
  simp only [hv, dite_true]
  cases hk : r.kind with
  | move => simp [expectedStatus, expectedContent, expectedAudit, hk]
  | edit => simp [expectedStatus, expectedContent, expectedAudit, hk]

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  by_cases hv : ValidRequest s r
  · unfold step
    simp only [hv, dite_true]
    cases hk : r.kind with
    | move => simp
    | edit => simp
  · unfold step
    simp [hv]

private theorem replay_append_single (l : List Entry) (e : Entry) (d : DocId) (st : Status) :
  replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
  induction l generalizing st with
  | nil => simp [replay]
  | cons hd tl ih => simp [replay, ih]

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons
  unfold AuditConsistent at hCons ⊢
  intro d hd
  by_cases hv : ValidRequest s r
  · cases hk : r.kind with
    | edit =>
      unfold step at hd ⊢
      simp only [hv, dite_true, hk] at hd ⊢
      exact hCons d hd
    | move =>
      unfold step at hd ⊢
      simp only [hv, dite_true, hk] at hd ⊢
      have hRep := hCons d hd
      have hReplay := replay_append_single s.audit ⟨r.doc, r.actor, s.status r.doc, r.dst⟩ d .draft
      rw [hReplay]
      by_cases heq : r.doc = d
      · subst heq; simp
      · have heq2 : ¬ (d = r.doc) := fun h => heq h.symm
        simp [heq, heq2, hRep]
  · have hStep := step_eq_of_not_valid hv
    rw [hStep] at hd ⊢
    exact hCons d hd

end Workflow
