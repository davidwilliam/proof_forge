import Workflow.Spec
namespace Workflow
instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance

def nextState (s : State) (r : Request) : State :=
  { docs := s.docs
    users := s.users
    status := fun d => expectedStatus s r d
    content := fun d => expectedContent s r d
    role := s.role
    audit := expectedAudit s r }

def step : Impl := fun s r =>
  if ValidRequest s r then (.ok, nextState s r) else (.rejected, s)

theorem replay_append_aux3 (l₁ l₂ : List Entry) (d : DocId) (st : Status) :
    replay (l₁ ++ l₂) d st = replay l₂ d (replay l₁ d st) := by
  induction l₁ generalizing st with
  | nil => simp [replay]
  | cons e es ih => simp [replay, ih]

theorem replay_single_aux3 (e : Entry) (d : DocId) (st : Status) :
    replay [e] d st = (if e.doc = d then e.dst else st) := by
  simp [replay]

theorem req_valid_succeeds       : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : Authorized step := by
  intro s r hok
  have hV : ValidRequest s r := by
    by_cases h : ValidRequest s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  exact ⟨fun hm => hV.2.2.1 hm, fun he => hV.2.2.2 he⟩

theorem req_single_doc           : SingleDoc step := by
  intro s r hok d hne
  have hV : ValidRequest s r := by
    by_cases h : ValidRequest s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  have h2 : (step s r).2 = nextState s r := by
    unfold step
    simp [hV]
  rw [h2]
  constructor
  · show (nextState s r).status d = s.status d
    unfold nextState expectedStatus
    simp [hne]
  · show (nextState s r).content d = s.content d
    unfold nextState expectedContent
    simp [hne]

theorem req_published_immutable  : PublishedImmutable step := by
  intro s r d h
  unfold step
  by_cases hV : ValidRequest s r
  · simp only [hV, ↓reduceIte]
    show (nextState s r).content d = s.content d
    simp only [nextState, expectedContent]
    by_cases he : r.kind = .edit ∧ d = r.doc
    · obtain ⟨hk, hdd⟩ := he
      subst hdd
      have hed := hV.2.2.2 hk
      rcases h with hpub | harch
      · rw [hed.2] at hpub; contradiction
      · rw [hed.2] at harch; contradiction
    · simp [he]
  · simp [hV]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hV : ValidRequest s r
    · have h2 : (step s r).2 = nextState s r := by
        unfold step; simp [hV]
      rw [h2]
      have hst : (nextState s r).status d = expectedStatus s r d := rfl
      rw [hst]
      unfold expectedStatus
      by_cases hT : (r.kind = .move ∧ d = r.doc)
      · rw [if_pos hT]
        obtain ⟨hkm, hdd⟩ := hT
        have hpub' : s.status r.doc = .published := hdd ▸ hpub
        have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true :=
          hV.2.2.1 hkm
        rw [hpub'] at hall
        have hdst : r.dst = .published ∨ r.dst = .archived := by
          cases hr : s.role r.actor <;> cases hd : r.dst <;> simp_all [allowed]
        rcases hdst with h | h
        · rw [h]; exact Or.inl rfl
        · rw [h]; exact Or.inr rfl
      · rw [if_neg hT, hpub]; exact Or.inl rfl
    · have h2 : (step s r).2 = s := by
        unfold step; simp [hV]
      rw [h2, hpub]; exact Or.inl rfl
  · intro harch
    by_cases hV : ValidRequest s r
    · have h2 : (step s r).2 = nextState s r := by
        unfold step; simp [hV]
      rw [h2]
      have hst : (nextState s r).status d = expectedStatus s r d := rfl
      rw [hst]
      unfold expectedStatus
      by_cases hT : (r.kind = .move ∧ d = r.doc)
      · rw [if_pos hT]
        obtain ⟨hkm, hdd⟩ := hT
        have harch' : s.status r.doc = .archived := hdd ▸ harch
        have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true :=
          hV.2.2.1 hkm
        rw [harch'] at hall
        cases hr : s.role r.actor <;> cases hd : r.dst <;> simp_all [allowed]
      · rw [if_neg hT, harch]
    · have h2 : (step s r).2 = s := by
        unfold step; simp [hV]
      rw [h2, harch]

theorem req_effects              : Effects step := by
  intro s r hok
  have hV : ValidRequest s r := by
    by_cases h : ValidRequest s r
    · exact h
    · unfold step at hok
      simp [h] at hok
  have h2 : (step s r).2 = nextState s r := by
    unfold step
    simp [hV]
  rw [h2]
  exact ⟨rfl, rfl, rfl, fun d => rfl, fun d => rfl, rfl⟩

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  unfold step
  by_cases hV : ValidRequest s r
  · simp only [if_pos hV]
    show s.audit <+: (nextState s r).audit
    simp only [nextState, expectedAudit]
    by_cases hm : r.kind = .move
    · simp [hm]
    · simp [hm]
  · simp only [if_neg hV]
    exact List.prefix_rfl

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by
      unfold step
      simp [hV]
    rw [h2]
    intro d hd
    have hd' : d ∈ s.docs := by simpa [nextState] using hd
    have hrep := hCons d hd'
    have hstat : (nextState s r).status d = expectedStatus s r d := rfl
    have haud : (nextState s r).audit = expectedAudit s r := rfl
    rw [hstat, haud]
    by_cases hm : r.kind = .move
    · have hAud : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by
        unfold expectedAudit
        rw [if_pos hm]
      have hStat : expectedStatus s r d = (if d = r.doc then r.dst else s.status d) := by
        unfold expectedStatus
        by_cases heq : d = r.doc
        · have hc : (r.kind = .move ∧ d = r.doc) := ⟨hm, heq⟩
          rw [if_pos hc, if_pos heq]
        · have hc : ¬ (r.kind = .move ∧ d = r.doc) := fun h => heq h.2
          rw [if_neg hc, if_neg heq]
      rw [hAud, hStat]
      have h1 : replay (s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩]) d .draft
          = replay [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] d (replay s.audit d .draft) :=
        replay_append_aux3 s.audit [_] d .draft
      rw [h1, hrep]
      have eDoc : (⟨r.doc, r.actor, s.status r.doc, r.dst⟩ : Entry).doc = r.doc := rfl
      rw [replay_single_aux3, eDoc]
      by_cases heq : d = r.doc
      · have h1eq : (r.doc = d) := heq.symm
        rw [if_pos h1eq, if_pos heq]
      · have h1ne : ¬ (r.doc = d) := fun h => heq h.symm
        rw [if_neg h1ne, if_neg heq]
    · have hAud : expectedAudit s r = s.audit := by
        unfold expectedAudit
        rw [if_neg hm]
      have hStat : expectedStatus s r d = s.status d := by
        unfold expectedStatus
        have hc : ¬ (r.kind = .move ∧ d = r.doc) := fun h => hm h.1
        rw [if_neg hc]
      rw [hAud, hStat]
      exact hrep
  · have h2 : (step s r).2 = s := by
      unfold step
      simp [hV]
    rw [h2]
    exact hCons

end Workflow
