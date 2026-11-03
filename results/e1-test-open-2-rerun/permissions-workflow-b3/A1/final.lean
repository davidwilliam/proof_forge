import Workflow.Spec
namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance

def step : Impl := fun s r =>
  if h : ValidRequest s r then
    match hk : r.kind with
    | .move =>
      (.ok,
        { docs := s.docs
          users := s.users
          status := fun d => if d = r.doc then r.dst else s.status d
          content := s.content
          role := s.role
          audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }]
        })
    | .edit =>
      (.ok,
        { docs := s.docs
          users := s.users
          status := s.status
          content := fun d => if d = r.doc then r.body else s.content d
          role := s.role
          audit := s.audit
        })
  else
    (.rejected, s)

theorem req_valid_succeeds       : ValidSucceeds step := by
  intro s r h
  unfold step
  simp only [h, dite_true]
  cases hk : r.kind <;> simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp only [h, dite_false]

theorem req_authorization : Authorized step := by
  intro s r hok
  have hVR : ValidRequest s r := by
    by_cases h : ValidRequest s r
    · exact h
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        simp [h]
      have : (step s r).1 = .rejected := by simp [hstep]
      rw [this] at hok
      contradiction
  obtain ⟨hdoc, huser, hmove, hedit⟩ := hVR
  constructor
  · intro hm
    exact hmove hm
  · intro he
    exact hedit he

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  have hVR : ValidRequest s r := by
    by_cases h : ValidRequest s r
    · exact h
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        simp [h]
      have : (step s r).1 = .rejected := by simp [hstep]
      rw [this] at hok
      contradiction
  unfold step at hok ⊢
  simp only [hVR, dite_true] at hok ⊢
  cases hk : r.kind with
  | move =>
    simp only at hok ⊢
    -- need to show both components
    have hstatus : (fun d => if d = r.doc then r.dst else s.status d) d = s.status d := by
      simp [hne]
    have hcontent : s.content d = s.content d := rfl
    -- The state is pair: need to reason about projections
    -- After simp, (step s r).2.status d simplifies
    simp [hne]
  | edit =>
    simp only at hok ⊢
    simp [hne]

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hpub
  unfold step
  by_cases hVR : ValidRequest s r
  · simp only [hVR, dite_true]
    cases hk : r.kind with
    | move => simp
    | edit =>
      simp only
      have h : (fun d_1 => if d_1 = r.doc then r.body else s.content d_1) d = s.content d := by
        by_cases heq : d = r.doc
        · subst heq
          unfold ValidRequest at hVR
          obtain ⟨_, _, _, hedit⟩ := hVR
          have hed := hedit hk
          rcases hpub with h1 | h1 <;> rw [hed.2] at h1 <;> contradiction
        · simp [heq]
      simpa [h]
  · simp only [hVR, dite_false]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  unfold step
  by_cases hVR : ValidRequest s r
  · simp only [hVR, dite_true]
    cases hk : r.kind
    · simp only
      constructor
      · intro hpub
        by_cases heq : d = r.doc
        · subst heq
          simp only [if_pos rfl]
          have hValid : ValidRequest s r := hVR
          unfold ValidRequest at hValid
          obtain ⟨_, _, hmove, _⟩ := hValid
          have hallow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hk
          rw [hpub] at hallow
          -- show dst must be archived
          have hdst : r.dst = .archived := by
            cases hrole : s.role r.actor <;> cases hd : r.dst <;> simp [allowed, hrole, hd] at hallow ⊢
          rw [hdst]
          exact Or.inr rfl
        · simp only [if_neg heq]
          exact Or.inl hpub
      · intro harch
        by_cases heq : d = r.doc
        · subst heq
          simp only [if_pos rfl]
          exfalso
          have hValid : ValidRequest s r := hVR
          unfold ValidRequest at hValid
          obtain ⟨_, _, hmove, _⟩ := hValid
          have hallow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hk
          rw [harch] at hallow
          cases hrole : s.role r.actor <;> cases hd : r.dst <;> simp [allowed, hrole, hd] at hallow
        · simp only [if_neg heq]
          exact harch
    · simp only
      constructor
      · intro hpub; exact Or.inl hpub
      · intro harch; exact harch
  · simp only [hVR, dite_false]
    constructor
    · intro hpub; exact Or.inl hpub
    · intro harch; exact harch

theorem req_effects : Effects step := by
  intro s r hok
  have hVR : ValidRequest s r := by
    by_cases h : ValidRequest s r
    · exact h
    · have hstep : step s r = (.rejected, s) := by unfold step; simp [h]
      have : (step s r).1 = .rejected := by simp [hstep]
      rw [this] at hok; contradiction
  unfold step at hok ⊢
  simp only [hVR, dite_true] at hok ⊢
  cases hkind : r.kind <;> simp_all [expectedStatus, expectedContent, expectedAudit, hkind]

theorem req_audit_append_only    : AuditAppendOnly step := by
  intro s r
  unfold step
  by_cases h : ValidRequest s r
  · simp only [h, dite_true]
    cases hk : r.kind
    · simp only
      exact List.prefix_append s.audit _
    · simp only
      exact List.prefix_rfl
  · simp only [h, dite_false]
    exact List.prefix_rfl

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons d hd
  have hAud : ∀ d ∈ s.docs, replay s.audit d .draft = s.status d := hCons
  show replay (step s r).2.audit d .draft = (step s r).2.status d
  have hStepDocs : (step s r).2.docs = s.docs := by
    unfold step
    by_cases hVR : ValidRequest s r
    · simp only [hVR, dite_true]
      cases h : r.kind <;> simp
    · simp [hVR]
  have hd' : d ∈ s.docs := hStepDocs ▸ hd
  have hCons_d : replay s.audit d .draft = s.status d := hAud d hd'
  unfold step
  by_cases hVR : ValidRequest s r
  · simp only [hVR, dite_true]
    cases hk : r.kind with
    | move =>
      have hLem : ∀ (l : List Entry) (e : Entry) (d : DocId) (st : Status),
        replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
        intro l e d st
        induction l generalizing st with
        | nil => simp [replay]
        | cons h tl IH => simp only [List.cons_append, replay]; rw [IH]
      have hreplay : replay (s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }]) d .draft =
        if r.doc = d then r.dst else replay s.audit d .draft := by
        have h := hLem s.audit ⟨r.doc, r.actor, s.status r.doc, r.dst⟩ d .draft
        simpa using h
      simp only [hreplay, hCons_d]
      by_cases heq : d = r.doc
      · simp only [if_pos heq, if_pos heq.symm]
      · have h2 : ¬ r.doc = d := fun h => heq h.symm
        simp only [if_neg heq, if_neg h2]
    | edit =>
      simp
      exact hCons_d
  · simp only [hVR, dite_false]
    exact hCons_d

end Workflow
