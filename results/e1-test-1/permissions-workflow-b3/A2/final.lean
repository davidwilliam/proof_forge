import Workflow.Spec
namespace Workflow
instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance

def step : Impl := fun s r =>
  if _h : ValidRequest s r then
    (.ok, { docs := s.docs, users := s.users, status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, role := s.role, audit := expectedAudit s r })
  else
    (.rejected, s)

theorem req_published_immutable_aux : PublishedImmutable step := by
  intro s r d hst
  unfold step
  by_cases hval : ValidRequest s r
  · simp only [dif_pos hval]
    show expectedContent s r d = s.content d
    unfold expectedContent
    by_cases hcond : r.kind = Kind.edit ∧ d = r.doc
    · obtain ⟨hk, hd⟩ := hcond
      subst hd
      obtain ⟨hdmem, hamem, hmove, hedit⟩ := hval
      have h := hedit hk
      rw [h.2] at hst
      cases hst with
      | inl h1 => cases h1
      | inr h1 => cases h1
    · simp [hcond]
  · simp only [dif_neg hval]

theorem my_replay_append : ∀ (l1 l2 : List Entry) (d : DocId) (st : Status), replay (l1 ++ l2) d st = replay l2 d (replay l1 d st) := by
  intro l1
  induction l1 with
  | nil => intro l2 d st; simp [replay]
  | cons e es ih => intro l2 d st; simp [replay, ih]

theorem my_replay_single (e : Entry) (d : DocId) (st : Status) : replay [e] d st = (if e.doc = d then e.dst else st) := by
  simp [replay]

theorem my_allowed_pub (role : Role) (dst : Status) : allowed role .published dst = true → dst = Status.archived := by
  intro h
  cases role <;> cases dst <;> simp_all [allowed]

theorem my_allowed_arch (role : Role) (dst : Status) : allowed role .archived dst = true → False := by
  intro h
  cases role <;> cases dst <;> simp_all [allowed]

theorem req_valid_succeeds       : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [dif_pos h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [dif_neg h]

theorem req_authorization : Authorized step := by
  intro s r hok
  by_cases hval : ValidRequest s r
  · obtain ⟨_, _, hmove, hedit⟩ := hval
    exact ⟨hmove, hedit⟩
  · have hrej : (step s r).1 = Outcome.rejected := by
      unfold step
      simp [dif_neg hval]
    rw [hrej] at hok
    contradiction

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  have hval : ValidRequest s r := by
    by_cases hc : ValidRequest s r
    · exact hc
    · have hrej : (step s r).1 = Outcome.rejected := by
        unfold step
        simp [dif_neg hc]
      rw [hrej] at hok
      contradiction
  have hpair : step s r = (Outcome.ok, { docs := s.docs, users := s.users, status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, role := s.role, audit := expectedAudit s r }) := by
    unfold step
    simp [dif_pos hval]
  have hst : (step s r).2.status d = expectedStatus s r d := by
    rw [hpair]
  have hco : (step s r).2.content d = expectedContent s r d := by
    rw [hpair]
  rw [hst, hco]
  unfold expectedStatus expectedContent
  have hdd : ¬ (r.kind = Kind.move ∧ d = r.doc) := by
    intro h
    exact hne h.2
  have hdd2 : ¬ (r.kind = Kind.edit ∧ d = r.doc) := by
    intro h
    exact hne h.2
  simp [hdd, hdd2]

theorem req_published_immutable  : PublishedImmutable step := by
  intro s r d hst
  unfold step
  by_cases hval : ValidRequest s r
  · simp only [dif_pos hval]
    show expectedContent s r d = s.content d
    unfold expectedContent
    by_cases hcond : r.kind = Kind.edit ∧ d = r.doc
    · obtain ⟨hk, hd⟩ := hcond
      subst hd
      obtain ⟨hdmem, hamem, hmove, hedit⟩ := hval
      have h := hedit hk
      rw [h.2] at hst
      cases hst with
      | inl h1 => cases h1
      | inr h1 => cases h1
    · simp [hcond]
  · simp only [dif_neg hval]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hval : ValidRequest s r
    · have h2 : (step s r).2 = ({ docs := s.docs, users := s.users, status := fun dd => expectedStatus s r dd, content := fun dd => expectedContent s r dd, role := s.role, audit := expectedAudit s r } : State) := by
        unfold step
        simp [dif_pos hval]
      have hst : (step s r).2.status d = expectedStatus s r d := by rw [h2]
      rw [hst]
      unfold expectedStatus
      by_cases hcond : r.kind = Kind.move ∧ d = r.doc
      · rw [if_pos hcond]
        obtain ⟨hkm, hdd⟩ := hcond
        have hsrc : s.status r.doc = Status.published := by rw [← hdd, hpub]
        obtain ⟨_, _, hmove, _⟩ := hval
        have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hkm
        rw [hsrc] at hall
        have hdst := my_allowed_pub _ _ hall
        rw [hdst]
        exact Or.inr rfl
      · rw [if_neg hcond, hpub]
        exact Or.inl rfl
    · have h2 : (step s r).2 = s := by
        unfold step
        simp [dif_neg hval]
      rw [h2, hpub]
      exact Or.inl rfl
  · intro harch
    by_cases hval : ValidRequest s r
    · have h2 : (step s r).2 = ({ docs := s.docs, users := s.users, status := fun dd => expectedStatus s r dd, content := fun dd => expectedContent s r dd, role := s.role, audit := expectedAudit s r } : State) := by
        unfold step
        simp [dif_pos hval]
      have hst : (step s r).2.status d = expectedStatus s r d := by rw [h2]
      rw [hst]
      unfold expectedStatus
      by_cases hcond : r.kind = Kind.move ∧ d = r.doc
      · obtain ⟨hkm, hdd⟩ := hcond
        have hsrc : s.status r.doc = Status.archived := by rw [← hdd, harch]
        obtain ⟨_, _, hmove, _⟩ := hval
        have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hkm
        rw [hsrc] at hall
        exact absurd hall (by cases (s.role r.actor) <;> cases r.dst <;> simp [allowed])
      · rw [if_neg hcond, harch]
    · have h2 : (step s r).2 = s := by
        unfold step
        simp [dif_neg hval]
      rw [h2, harch]

theorem req_effects : Effects step := by
  intro s r hok
  have hval : ValidRequest s r := by
    by_cases hc : ValidRequest s r
    · exact hc
    · have hrej : (step s r).1 = Outcome.rejected := by
        unfold step
        simp [dif_neg hc]
      rw [hrej] at hok
      contradiction
  have hpair : step s r = (Outcome.ok, ({ docs := s.docs, users := s.users, status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, role := s.role, audit := expectedAudit s r } : State)) := by
    unfold step
    simp [dif_pos hval]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hpair]
  · simp [hpair]
  · simp [hpair]
  · intro d
    simp [hpair]
  · intro d
    simp [hpair]
  · simp [hpair]

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  unfold step
  by_cases hval : ValidRequest s r
  · simp only [dif_pos hval]
    show s.audit <+: expectedAudit s r
    unfold expectedAudit
    by_cases hk : r.kind = Kind.move
    · simp only [if_pos hk]
      exact ⟨[_], rfl⟩
    · simp only [if_neg hk]
      exact ⟨[], by simp⟩
  · simp only [dif_neg hval]
    exact ⟨[], by simp⟩

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hcons
  by_cases hval : ValidRequest s r
  · have hpair : step s r = (Outcome.ok, ({ docs := s.docs, users := s.users, status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, role := s.role, audit := expectedAudit s r } : State)) := by
      unfold step
      simp [dif_pos hval]
    have h2 : (step s r).2 = ({ docs := s.docs, users := s.users, status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, role := s.role, audit := expectedAudit s r } : State) := by
      rw [hpair]
    rw [h2]
    unfold AuditConsistent
    intro d hd
    simp only []
    show replay (expectedAudit s r) d Status.draft = expectedStatus s r d
    by_cases hk : r.kind = Kind.move
    · have hAud : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by
        unfold expectedAudit
        simp [hk]
      have hStat : expectedStatus s r d = (if d = r.doc then r.dst else s.status d) := by
        unfold expectedStatus
        by_cases hdd : d = r.doc
        · simp [hk, hdd]
        · simp [hk, hdd]
      rw [hAud, hStat]
      have hreplay : replay s.audit d Status.draft = s.status d := hcons d hd
      have happ : replay (s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩]) d Status.draft = replay [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] d (replay s.audit d Status.draft) := my_replay_append s.audit [_] d Status.draft
      rw [happ, hreplay]
      have hsing : replay [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] d (s.status d) = (if r.doc = d then r.dst else s.status d) := my_replay_single _ d _
      rw [hsing]
      by_cases hdd : d = r.doc
      · rw [if_pos hdd.symm, if_pos hdd]
      · have h1 : ¬ (r.doc = d) := fun h => hdd h.symm
        rw [if_neg h1, if_neg hdd]
    · have hAud : expectedAudit s r = s.audit := by
        unfold expectedAudit
        simp [hk]
      have hStat : expectedStatus s r d = s.status d := by
        unfold expectedStatus
        have hcond : ¬ (r.kind = Kind.move ∧ d = r.doc) := fun h => hk h.1
        simp [hcond]
      rw [hAud, hStat]
      exact hcons d hd
  · have hpair : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [dif_neg hval]
    have h2 : (step s r).2 = s := by rw [hpair]
    rw [h2]
    exact hcons

end Workflow
