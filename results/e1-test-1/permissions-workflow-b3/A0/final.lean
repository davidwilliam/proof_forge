import Workflow.Spec
namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance

def step : Impl := fun s r =>
  if ValidRequest s r then
    (Outcome.ok,
      { docs := s.docs,
        users := s.users,
        status := expectedStatus s r,
        content := expectedContent s r,
        role := s.role,
        audit := expectedAudit s r })
  else
    (Outcome.rejected, s)

theorem aux_allowed_pub {ro : Role} {dst : Status}
    (h : allowed ro .published dst = true) : dst = .archived := by
  cases ro <;> cases dst <;> simp_all [allowed]

theorem aux_allowed_arch {ro : Role} {dst : Status}
    (h : allowed ro .archived dst = true) : False := by
  cases ro <;> cases dst <;> simp_all [allowed]

theorem aux_replay_append (l1 l2 : List Entry) (d : DocId) (st : Status) :
    replay (l1 ++ l2) d st = replay l2 d (replay l1 d st) := by
  induction l1 generalizing st with
  | nil => simp only [List.nil_append, replay]
  | cons hd tl ih => simp only [List.cons_append, replay, ih]

theorem aux_replay_singleton (e : Entry) (d : DocId) (st : Status) :
    replay [e] d st = (if e.doc = d then e.dst else st) := by
  simp only [replay]

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r hv
  have hstep : step s r = (Outcome.ok,
      { docs := s.docs,
        users := s.users,
        status := expectedStatus s r,
        content := expectedContent s r,
        role := s.role,
        audit := expectedAudit s r }) := by
    simp [step, hv]
  rw [hstep]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r hn
  have hstep : step s r = (Outcome.rejected, s) := by
    simp [step, hn]
  exact hstep

theorem req_authorization : Authorized step := by
  unfold Authorized
  intro s r hok
  by_cases hv : ValidRequest s r
  · obtain ⟨hdoc, huser, hmove, hedit⟩ := hv
    exact ⟨hmove, hedit⟩
  · exfalso
    have hstep : step s r = (Outcome.rejected, s) := by
      simp [step, hv]
    have hre : (step s r).1 = Outcome.rejected := by rw [hstep]
    rw [hre] at hok
    cases hok

theorem req_single_doc : SingleDoc step := by
  unfold SingleDoc
  intro s r hok d hdNe
  by_cases hv : ValidRequest s r
  · have hstep : step s r = (Outcome.ok,
        { docs := s.docs,
          users := s.users,
          status := expectedStatus s r,
          content := expectedContent s r,
          role := s.role,
          audit := expectedAudit s r }) := by
      simp [step, hv]
    have hst : (step s r).2.status d = expectedStatus s r d := by rw [hstep]
    have hco : (step s r).2.content d = expectedContent s r d := by rw [hstep]
    rw [hst, hco]
    have h1 : ¬ (r.kind = .move ∧ d = r.doc) := fun h => hdNe h.2
    have h2 : ¬ (r.kind = .edit ∧ d = r.doc) := fun h => hdNe h.2
    have e1 : expectedStatus s r d = s.status d := by
      unfold expectedStatus
      rw [if_neg h1]
    have e2 : expectedContent s r d = s.content d := by
      unfold expectedContent
      rw [if_neg h2]
    rw [e1, e2]
    exact ⟨rfl, rfl⟩
  · exfalso
    have hstep : step s r = (Outcome.rejected, s) := by
      simp [step, hv]
    have hre : (step s r).1 = Outcome.rejected := by rw [hstep]
    rw [hre] at hok
    cases hok

theorem req_published_immutable : PublishedImmutable step := by
  unfold PublishedImmutable
  intro s r d hst
  by_cases hv : ValidRequest s r
  · have hstep : step s r = (Outcome.ok,
        { docs := s.docs,
          users := s.users,
          status := expectedStatus s r,
          content := expectedContent s r,
          role := s.role,
          audit := expectedAudit s r }) := by
      simp [step, hv]
    have hco : (step s r).2.content d = expectedContent s r d := by rw [hstep]
    rw [hco]
    have hnc : ¬ (r.kind = .edit ∧ d = r.doc) := by
      intro hc
      obtain ⟨hkind, heq⟩ := hc
      obtain ⟨hdoc, huser, hmove, hedit⟩ := hv
      have hed := hedit hkind
      obtain ⟨_, hdraft⟩ := hed
      have hsd : s.status d = s.status r.doc := by rw [heq]
      rw [hsd, hdraft] at hst
      cases hst with
      | inl h => cases h
      | inr h => cases h
    have e2 : expectedContent s r d = s.content d := by
      unfold expectedContent
      rw [if_neg hnc]
    rw [e2]
  · have hstep : step s r = (Outcome.rejected, s) := by
      simp [step, hv]
    have hco : (step s r).2 = s := by rw [hstep]
    rw [hco]

theorem req_no_unpublish : NoUnpublish step := by
  unfold NoUnpublish
  intro s r d
  constructor
  · intro hpub
    by_cases hv : ValidRequest s r
    · have hstep : step s r = (Outcome.ok,
          { docs := s.docs,
            users := s.users,
            status := expectedStatus s r,
            content := expectedContent s r,
            role := s.role,
            audit := expectedAudit s r }) := by
        simp [step, hv]
      have hst : (step s r).2.status d = expectedStatus s r d := by rw [hstep]
      rw [hst]
      by_cases hc : (r.kind = .move ∧ d = r.doc)
      · have epos : expectedStatus s r d = r.dst := by
          unfold expectedStatus
          rw [if_pos hc]
        rw [epos]
        obtain ⟨hkind, heq⟩ := hc
        obtain ⟨hdoc, huser, hmove, hedit⟩ := hv
        have hm := hmove hkind
        have hsrc : s.status r.doc = .published := by
          rw [← heq]
          exact hpub
        rw [hsrc] at hm
        have hdst := aux_allowed_pub hm
        rw [hdst]
        right
        rfl
      · have eneg : expectedStatus s r d = s.status d := by
          unfold expectedStatus
          rw [if_neg hc]
        rw [eneg, hpub]
        left
        rfl
    · have hstep : step s r = (Outcome.rejected, s) := by
        simp [step, hv]
      have hst0 : (step s r).2.status d = s.status d := by rw [hstep]
      rw [hst0, hpub]
      left
      rfl
  · intro harch
    by_cases hv : ValidRequest s r
    · have hstep : step s r = (Outcome.ok,
          { docs := s.docs,
            users := s.users,
            status := expectedStatus s r,
            content := expectedContent s r,
            role := s.role,
            audit := expectedAudit s r }) := by
        simp [step, hv]
      have hst : (step s r).2.status d = expectedStatus s r d := by rw [hstep]
      rw [hst]
      have hnc : ¬ (r.kind = .move ∧ d = r.doc) := by
        intro hc
        obtain ⟨hkind, heq⟩ := hc
        obtain ⟨hdoc, huser, hmove, hedit⟩ := hv
        have hm := hmove hkind
        have hsrc : s.status r.doc = .archived := by
          rw [← heq]
          exact harch
        rw [hsrc] at hm
        exact aux_allowed_arch hm
      have eneg : expectedStatus s r d = s.status d := by
        unfold expectedStatus
        rw [if_neg hnc]
      rw [eneg, harch]
    · have hstep : step s r = (Outcome.rejected, s) := by
        simp [step, hv]
      have hst0 : (step s r).2.status d = s.status d := by rw [hstep]
      rw [hst0, harch]

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hok
  by_cases hv : ValidRequest s r
  · have hstep : step s r = (Outcome.ok,
        { docs := s.docs,
          users := s.users,
          status := expectedStatus s r,
          content := expectedContent s r,
          role := s.role,
          audit := expectedAudit s r }) := by
      simp [step, hv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstep]
    · rw [hstep]
    · rw [hstep]
    · intro d
      rw [hstep]
    · intro d
      rw [hstep]
    · rw [hstep]
  · exfalso
    have hstep : step s r = (Outcome.rejected, s) := by
      simp [step, hv]
    have hre : (step s r).1 = Outcome.rejected := by rw [hstep]
    rw [hre] at hok
    cases hok

theorem req_audit_append_only : AuditAppendOnly step := by
  unfold AuditAppendOnly
  intro s r
  by_cases hv : ValidRequest s r
  · have hstep : step s r = (Outcome.ok,
        { docs := s.docs,
          users := s.users,
          status := expectedStatus s r,
          content := expectedContent s r,
          role := s.role,
          audit := expectedAudit s r }) := by
      simp [step, hv]
    have ha : (step s r).2.audit = expectedAudit s r := by rw [hstep]
    rw [ha]
    by_cases hm : r.kind = .move
    · have heq : expectedAudit s r =
          s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] := by
        unfold expectedAudit
        rw [if_pos hm]
      rw [heq]
      exact ⟨[{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }], rfl⟩
    · have heq : expectedAudit s r = s.audit := by
        unfold expectedAudit
        rw [if_neg hm]
      rw [heq]
      exact ⟨[], by simp⟩
  · have hstep : step s r = (Outcome.rejected, s) := by
      simp [step, hv]
    have ha2 : (step s r).2.audit = s.audit := by rw [hstep]
    rw [ha2]
    exact ⟨[], by simp⟩

theorem req_audit_consistent : KeepsAuditConsistent step := by
  unfold KeepsAuditConsistent AuditConsistent
  intro s r hCons d hdMem
  by_cases hv : ValidRequest s r
  · have hstep : step s r = (Outcome.ok,
        { docs := s.docs,
          users := s.users,
          status := expectedStatus s r,
          content := expectedContent s r,
          role := s.role,
          audit := expectedAudit s r }) := by
      simp [step, hv]
    have hdocs : (step s r).2.docs = s.docs := by rw [hstep]
    have haudit : (step s r).2.audit = expectedAudit s r := by rw [hstep]
    have hstatus : (step s r).2.status = expectedStatus s r := by rw [hstep]
    rw [hdocs] at hdMem
    have hd : d ∈ s.docs := hdMem
    have hCons_d : replay s.audit d .draft = s.status d := hCons d hd
    rw [haudit, hstatus]
    cases hkr : r.kind with
    | move =>
      have hcond : (r.kind = Kind.move) := hkr
      have heA : expectedAudit s r =
          s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] := by
        unfold expectedAudit
        rw [if_pos hcond]
      have heS : expectedStatus s r d = (if d = r.doc then r.dst else s.status d) := by
        unfold expectedStatus
        by_cases heq : d = r.doc
        · have hc : (r.kind = Kind.move ∧ d = r.doc) := ⟨hcond, heq⟩
          rw [if_pos hc, if_pos heq]
        · have hc : ¬(r.kind = Kind.move ∧ d = r.doc) := fun h => heq h.2
          rw [if_neg hc, if_neg heq]
      rw [heA, heS, aux_replay_append, hCons_d, aux_replay_singleton]
      by_cases heq : d = r.doc
      · have heq' : r.doc = d := heq.symm
        rw [if_pos heq, if_pos heq']
      · have heq' : ¬ (r.doc = d) := fun h => heq h.symm
        rw [if_neg heq, if_neg heq']
    | edit =>
      have hne : ¬ (r.kind = Kind.move) := by
        rw [hkr]
        intro h
        cases h
      have hnc : ¬ (r.kind = Kind.move ∧ d = r.doc) := fun h => hne h.1
      have heA : expectedAudit s r = s.audit := by
        unfold expectedAudit
        rw [if_neg hne]
      have heS : expectedStatus s r d = s.status d := by
        unfold expectedStatus
        rw [if_neg hnc]
      rw [heA, heS]
      exact hCons_d
  · have hstep : step s r = (Outcome.rejected, s) := by
      simp [step, hv]
    have hdocs : (step s r).2.docs = s.docs := by rw [hstep]
    have haudit : (step s r).2.audit = s.audit := by rw [hstep]
    have hstatus : (step s r).2.status = s.status := by rw [hstep]
    rw [hdocs] at hdMem
    rw [haudit, hstatus]
    exact hCons d hdMem

end Workflow
