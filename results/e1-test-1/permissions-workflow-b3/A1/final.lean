import Workflow.Spec
namespace Workflow

def nextState (s : State) (r : Request) : State :=
  { docs := s.docs
    users := s.users
    status := fun d => expectedStatus s r d
    content := fun d => expectedContent s r d
    role := s.role
    audit := expectedAudit s r }

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest
  infer_instance

def step : Impl := fun s r => if ValidRequest s r then (.ok, nextState s r) else (.rejected, s)

theorem req_authorization_aux : Authorized step := by
  intro s r h
  by_cases hv : ValidRequest s r
  · obtain ⟨_, _, hm, he⟩ := hv
    exact ⟨fun hk => hm hk, fun hk => he hk⟩
  · unfold step at h
    simp [hv] at h

def foo := 1

theorem foo_lemma_test2 : True := by trivial

theorem replay_append_thm (l1 l2 : List Entry) (d : DocId) (st : Status) :
    replay (l1 ++ l2) d st = replay l2 d (replay l1 d st) := by
  induction l1 generalizing st with
  | nil => simp [replay]
  | cons hd tl ih => simp [replay, ih]

theorem replay_singleton_thm (e : Entry) (d : DocId) (st : Status) :
    replay [e] d st = (if e.doc = d then e.dst else st) := by
  simp [replay]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : Authorized step := by
  intro s r h
  by_cases hv : ValidRequest s r
  · obtain ⟨_, _, hm, he⟩ := hv
    exact ⟨fun hk => hm hk, fun hk => he hk⟩
  · unfold step at h
    simp [hv] at h

theorem req_single_doc : SingleDoc step := by
  intro s r h d hd
  by_cases hv : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hv]
    rw [h2]
    have hne : ¬ (r.kind = .move ∧ d = r.doc) := fun ⟨_, heq⟩ => hd heq
    have hne2 : ¬ (r.kind = .edit ∧ d = r.doc) := fun ⟨_, heq⟩ => hd heq
    have hs : (nextState s r).status d = s.status d := by
      unfold nextState expectedStatus
      simp [hne]
    have hc : (nextState s r).content d = s.content d := by
      unfold nextState expectedContent
      simp [hne2]
    exact ⟨hs, hc⟩
  · unfold step at h
    simp [hv] at h

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d h
  by_cases hv : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hv]
    rw [h2]
    obtain ⟨hdoc, huser, hm, he⟩ := hv
    have hne : ¬ (r.kind = .edit ∧ d = r.doc) := by
      rintro ⟨hk, heq⟩
      have hst := (he hk).2
      have : s.status d = .draft := by rw [heq]; exact hst
      rcases h with hpub | harch <;> simp_all
    have hc : (nextState s r).content d = s.content d := by
      unfold nextState expectedContent
      simp [hne]
    exact hc
  · have h2 : (step s r).2 = s := by unfold step; simp [hv]
    rw [h2]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hv : ValidRequest s r
    · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hv]
      rw [h2]
      show (nextState s r).status d = _ ∨ _
      have hs : (nextState s r).status d = expectedStatus s r d := rfl
      rw [hs]
      unfold expectedStatus
      split
      · next hcond =>
        obtain ⟨hkm, heq⟩ := hcond
        have hallow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := by
          obtain ⟨_, _, hm, _⟩ := hv
          exact hm hkm
        have hsrc : s.status r.doc = .published := by rw [← heq]; exact hpub
        rw [hsrc] at hallow
        cases hrole : s.role r.actor <;> cases hdst : r.dst <;> simp [allowed, hrole, hdst] at hallow ⊢
      · next hcond => simp [hpub]
    · have h2 : (step s r).2 = s := by unfold step; simp [hv]
      rw [h2, hpub]
      exact Or.inl rfl
  · intro harch
    by_cases hv : ValidRequest s r
    · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hv]
      rw [h2]
      have hs : (nextState s r).status d = expectedStatus s r d := rfl
      rw [hs]
      unfold expectedStatus
      split
      · next hcond =>
        obtain ⟨hkm, heq⟩ := hcond
        have hallow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := by
          obtain ⟨_, _, hm, _⟩ := hv
          exact hm hkm
        have hsrc : s.status r.doc = .archived := by rw [← heq]; exact harch
        rw [hsrc] at hallow
        cases hrole : s.role r.actor <;> cases hdst : r.dst <;> simp [allowed, hrole, hdst] at hallow
      · next hcond => simp [harch]
    · have h2 : (step s r).2 = s := by unfold step; simp [hv]
      rw [h2, harch]

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hv]
    rw [h2]
    exact ⟨rfl, rfl, rfl, fun d => rfl, fun d => rfl, rfl⟩
  · unfold step at h
    simp [hv] at h

theorem req_audit_append_only    : AuditAppendOnly step := by
  intro s r
  by_cases hv : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hv]
    rw [h2]
    unfold nextState expectedAudit
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  · have h2 : (step s r).2 = s := by unfold step; simp [hv]
    rw [h2]
    exact List.prefix_refl _

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hcons d hmem
  by_cases hv : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hv]
    rw [h2] at hmem
    rw [h2]
    have hdocs : (nextState s r).docs = s.docs := rfl
    rw [hdocs] at hmem
    have haudit : (nextState s r).audit = expectedAudit s r := rfl
    have hstat : (nextState s r).status d = expectedStatus s r d := rfl
    rw [haudit, hstat]
    have hold : replay s.audit d .draft = s.status d := hcons d hmem
    unfold expectedAudit
    by_cases hkm : r.kind = .move
    · have hsplit : (if r.kind = .move then s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] else s.audit) = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by simp [hkm]
      rw [hsplit, replay_append_thm, hold, replay_singleton_thm]
      unfold expectedStatus
      by_cases heq : d = r.doc
      · have e1 : r.doc = d := Eq.symm heq
        have c1 : r.kind = .move ∧ d = r.doc := ⟨hkm, heq⟩
        rw [if_pos e1, if_pos c1]
      · have e1 : ¬ (r.doc = d) := fun h => heq h.symm
        have c1 : ¬ (r.kind = .move ∧ d = r.doc) := fun h => heq h.2
        rw [if_neg e1, if_neg c1]
    · have hsplit : (if r.kind = .move then s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] else s.audit) = s.audit := by simp [hkm]
      rw [hsplit, hold]
      unfold expectedStatus
      have hcond : ¬ (r.kind = .move ∧ d = r.doc) := fun h => hkm h.1
      rw [if_neg hcond]
  · have h2 : (step s r).2 = s := by unfold step; simp [hv]
    rw [h2]
    rw [h2] at hmem
    exact hcons d hmem

end Workflow
