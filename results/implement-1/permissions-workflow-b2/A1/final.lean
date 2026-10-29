import Workflow.Spec

namespace Workflow

def step : Impl := fun s r =>
  let valid : Bool :=
    decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)
  if valid then
    (Outcome.ok,
      { docs := s.docs,
        users := s.users,
        status := fun d => expectedStatus s r d,
        content := fun d => expectedContent s r d,
        role := s.role,
        audit := expectedAudit s r })
  else (Outcome.rejected, s)

theorem tmp_valid_true4 (s : State) (r : Request) (hv : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true) :
      ValidRequest s r := by
  cases hkr : r.kind with
  | move =>
    have hv2 : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      allowed (s.role r.actor) (s.status r.doc) r.dst) = true := by
      have : (match (Kind.move : Kind) with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) =
        allowed (s.role r.actor) (s.status r.doc) r.dst := rfl
      have h3 : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        (match (r.kind : Kind) with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))) = true := hv
      rw [hkr] at h3
      simp at h3
      simpa using h3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv2
    obtain ⟨⟨hd, ha⟩, hall⟩ := hv2
    refine ⟨hd, ha, ?_, ?_⟩
    · intro _
      exact hall
    · intro hcon
      simp [hkr] at hcon
  | edit =>
    have hv2 : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      (decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))) = true := by
      have h3 : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        (match (r.kind : Kind) with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))) = true := hv
      rw [hkr] at h3
      simp at h3
      simpa using h3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv2
    obtain ⟨⟨hd, ha⟩, hr, hs⟩ := hv2
    refine ⟨hd, ha, ?_, ?_⟩
    · intro hcon
      simp [hkr] at hcon
    · intro _
      exact ⟨hr, hs⟩

theorem req_auth_probe6 (s : State) (r : Request) (he :
      (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = false) :
    (step s r).1 = Outcome.rejected := by simp [step, he]

theorem req_authorization_final_test : Authorized step := by
  intro s r hok
  have heq : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true := by
    cases he : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))
    · have hcon : (step s r).1 = Outcome.rejected := by simp [step, he]
      rw [hcon] at hok
      exact absurd hok Outcome.noConfusion
    · rfl
  have hv := tmp_valid_true4 s r heq
  obtain ⟨_, _, hmove, hedit⟩ := hv
  exact ⟨hmove, hedit⟩

theorem probe_effects_shape (s : State) (r : Request) (hv : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true) :
    (step s r).2.docs = s.docs := by
  simp [step, hv]

theorem fx_effects_aux : Effects step := by
  intro s r hok
  have hv : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true := by
    cases he : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))
    · have hcon : (step s r).1 = Outcome.rejected := by simp [step, he]
      rw [hcon] at hok
      exact absurd hok Outcome.noConfusion
    · rfl
  have e1 : (step s r).2.docs = s.docs := by simp [step, hv]
  have e2 : (step s r).2.users = s.users := by simp [step, hv]
  have e3 : (step s r).2.role = s.role := by simp [step, hv]
  have e4 : ∀ d, (step s r).2.status d = expectedStatus s r d := by intro d; simp [step, hv]
  have e5 : ∀ d, (step s r).2.content d = expectedContent s r d := by intro d; simp [step, hv]
  have e6 : (step s r).2.audit = expectedAudit s r := by simp [step, hv]
  exact ⟨e1, e2, e3, e4, e5, e6⟩

theorem allowed_arch_aux2 (ro : Role) (dst : Status) : allowed ro .archived dst = false := by
  cases ro <;> cases dst <;> rfl

theorem allowed_pub_aux2 (ro : Role) (dst : Status) (h : allowed ro .published dst = true) : dst = .published ∨ dst = .archived := by
  cases ro <;> cases dst <;> simp_all [allowed]

private theorem my_replay_append_aux (l₁ l₂ : List Entry) (d : DocId) (st : Status) :
    replay (l₁ ++ l₂) d st = replay l₂ d (replay l₁ d st) := by
  induction l₁ generalizing st with
  | nil => simp [replay]
  | cons hd tl ih => simp [replay, ih]

private theorem my_replay_single_aux (e : Entry) (d : DocId) (st : Status) :
    replay [e] d st = (if e.doc = d then e.dst else st) := by
  simp [replay]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨hdoc, hactor, hmove, hedit⟩ := h
  show (step s r).1 = _
  simp only [step]
  have e1 : decide (r.doc ∈ s.docs) = true := by simp [hdoc]
  have e2 : decide (r.actor ∈ s.users) = true := by simp [hactor]
  have hv : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      (match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))) = true := by
    cases hkr : r.kind
    · have hm := hmove hkr
      rw [e1, e2]
      simp [hm]
    · have he := hedit hkr
      obtain ⟨hr, hs⟩ := he
      have er : decide (s.role r.actor = .author) = true := by simp [hr]
      have es : decide (s.status r.doc = .draft) = true := by simp [hs]
      rw [e1, e2]
      simp [er, es]
  simp [hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hb : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = false := by
    apply eq_false_of_ne_true
    intro ht
    apply h
    exact tmp_valid_true4 s r ht
  show step s r = _
  unfold step
  simp [hb]

theorem req_authorization : Authorized step := by
  intro s r hok
  have heq : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true := by
    cases he : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))
    · have hcon : (step s r).1 = Outcome.rejected := by simp [step, he]
      rw [hcon] at hok
      exact absurd hok Outcome.noConfusion
    · rfl
  have hv := tmp_valid_true4 s r heq
  obtain ⟨_, _, hmove, hedit⟩ := hv
  exact ⟨hmove, hedit⟩

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  have hv : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true := by
    cases he : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))
    · have hcon : (step s r).1 = Outcome.rejected := by simp [step, he]
      rw [hcon] at hok
      exact absurd hok Outcome.noConfusion
    · rfl
  have hst : (step s r).2.status d = expectedStatus s r d := by
    simp [step, hv]
  have hco : (step s r).2.content d = expectedContent s r d := by
    simp [step, hv]
  have hne2 : ¬ (r.kind = .move ∧ d = r.doc) := fun h => hne h.2
  have hne3 : ¬ (r.kind = .edit ∧ d = r.doc) := fun h => hne h.2
  have es : expectedStatus s r d = s.status d := by
    simp [expectedStatus, hne2]
  have ec : expectedContent s r d = s.content d := by
    simp [expectedContent, hne3]
  rw [hst, hco, es, ec]
  exact ⟨rfl, rfl⟩

theorem req_published_immutable  : PublishedImmutable step := by
  intro s r d hstat
  by_cases hb : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true
  · have hco : (step s r).2.content d = expectedContent s r d := by simp [step, hb]
    rw [hco]
    have hv := tmp_valid_true4 s r hb
    obtain ⟨_, _, _, hedit⟩ := hv
    have hne : ¬ (r.kind = .edit ∧ d = r.doc) := by
      intro hcon
      obtain ⟨hke, hdd⟩ := hcon
      have hdraft : s.status r.doc = .draft := (hedit hke).2
      have hsdraft : s.status d = .draft := by rw [hdd]; exact hdraft
      cases hstat with
      | inl hpub =>
        rw [hsdraft] at hpub
        exact absurd hpub (by decide)
      | inr harch =>
        rw [hsdraft] at harch
        exact absurd harch (by decide)
    simp [expectedContent, hne]
  · have hbF : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = false := by
      cases he : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))
      · rfl
      · exact absurd he hb
    have hst : (step s r).2.content d = s.content d := by simp [step, hbF]
    exact hst

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hb : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true
    · have hst : (step s r).2.status d = expectedStatus s r d := by simp [step, hb]
      rw [hst]
      by_cases hcond : r.kind = .move ∧ d = r.doc
      · obtain ⟨hkm, hdd⟩ := hcond
        have hes : expectedStatus s r d = r.dst := by simp [expectedStatus, hkm, hdd]
        rw [hes]
        have hv := tmp_valid_true4 s r hb
        obtain ⟨_, _, hmove, _⟩ := hv
        have hall := hmove hkm
        have hsr : s.status r.doc = .published := by rw [← hdd]; exact hpub
        rw [hsr] at hall
        exact allowed_pub_aux2 _ _ hall
      · have hes : expectedStatus s r d = s.status d := by simp [expectedStatus, hcond]
        rw [hes, hpub]
        exact Or.inl rfl
    · have hbF : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = false := by
        cases he : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))
        · rfl
        · exact absurd he hb
      have hst : (step s r).2.status d = s.status d := by simp [step, hbF]
      rw [hst, hpub]
      exact Or.inl rfl
  · intro harch
    by_cases hb : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true
    · have hst : (step s r).2.status d = expectedStatus s r d := by simp [step, hb]
      rw [hst]
      by_cases hcond : r.kind = .move ∧ d = r.doc
      · obtain ⟨hkm, hdd⟩ := hcond
        have hv := tmp_valid_true4 s r hb
        obtain ⟨_, _, hmove, _⟩ := hv
        have hall := hmove hkm
        have hsr : s.status r.doc = .archived := by rw [← hdd]; exact harch
        rw [hsr] at hall
        have hfalse : allowed (s.role r.actor) Status.archived r.dst = false :=
          allowed_arch_aux2 (s.role r.actor) r.dst
        rw [hall] at hfalse
        exact Bool.noConfusion hfalse
      · have hes : expectedStatus s r d = s.status d := by simp [expectedStatus, hcond]
        rw [hes, harch]
    · have hbF : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = false := by
        cases he : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))
        · rfl
        · exact absurd he hb
      have hst : (step s r).2.status d = s.status d := by simp [step, hbF]
      rw [hst, harch]

theorem req_effects : Effects step := fx_effects_aux

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  show s.audit <+: (step s r).2.audit
  unfold step
  by_cases hb : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true
  · simp only [hb, ite_true]
    show s.audit <+: expectedAudit s r
    unfold expectedAudit
    by_cases hkm : r.kind = .move
    · simp [hkm]
    · simp [hkm]
  · have hbF : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = false := by
      cases he : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))
      · rfl
      · exact absurd he hb
    simp [hbF]

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hcons
  by_cases hb : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
      match r.kind with
      | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
      | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = true
  · have e_docs : (step s r).2.docs = s.docs := by simp [step, hb]
    have e_status : ∀ d, (step s r).2.status d = expectedStatus s r d := by intro d; simp [step, hb]
    have e_audit : (step s r).2.audit = expectedAudit s r := by simp [step, hb]
    intro d hd
    rw [e_docs] at hd
    rw [e_status, e_audit]
    have hrep : replay s.audit d .draft = s.status d := hcons d hd
    cases hkr : r.kind with
    | edit =>
      have hea : expectedAudit s r = s.audit := by simp [expectedAudit, hkr]
      have hes : expectedStatus s r d = s.status d := by simp [expectedStatus, hkr]
      rw [hea, hes]
      exact hrep
    | move =>
      have hea : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by simp [expectedAudit, hkr]
      have hes : expectedStatus s r d = (if d = r.doc then r.dst else s.status d) := by simp [expectedStatus, hkr]
      rw [hea, hes]
      have happ : replay (s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩]) d .draft =
        replay [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] d (replay s.audit d .draft) :=
        my_replay_append_aux s.audit [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] d .draft
      rw [happ, hrep]
      rw [my_replay_single_aux]
      by_cases heq : d = r.doc
      · subst heq
        simp
      · have heq2 : ¬ (r.doc = d) := fun h => heq (Eq.symm h)
        simp [heq, heq2]
  · have hbF : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)) = false := by
      cases he : (decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
        match r.kind with
        | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft))
      · rfl
      · exact absurd he hb
    have e2 : (step s r).2 = s := by simp [step, hbF]
    rw [e2]
    exact hcons

end Workflow
