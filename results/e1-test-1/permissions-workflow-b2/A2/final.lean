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

theorem req_no_unpublish_aux_test : True := by trivial
#check @allowed
#check (allowed .publisher .published .archived)

def foo : Nat := 3

theorem foo_thm : True := by trivial

theorem replay_append_thm (l1 l2 : List Entry) (d : DocId) (st : Status) : replay (l1 ++ l2) d st = replay l2 d (replay l1 d st) := by induction l1 generalizing st with | nil => simp [replay] | cons e tl ih => simp [replay, ih]

theorem replay_single_thm (e : Entry) (d : DocId) (st : Status) : replay [e] d st = (if e.doc = d then e.dst else st) := by simp [replay]

theorem entry_proj_thm (a : Nat) (b : Nat) (c : Status) (e : Status) : (⟨a, b, c, e⟩ : Entry).doc = a := by rfl

theorem next_docs_thm (s : State) (r : Request) : (nextState s r).docs = s.docs := by rfl

theorem test_ifpos2 (s : State) (r : Request) (d : DocId) (heq : r.doc = d) :
  (if (⟨r.doc, r.actor, s.status r.doc, r.dst⟩ : Entry).doc = d then (⟨r.doc, r.actor, s.status r.doc, r.dst⟩ : Entry).dst else s.status d) = r.dst := by
  have hL : (⟨r.doc, r.actor, s.status r.doc, r.dst⟩ : Entry).doc = d := heq
  rw [if_pos hL]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp only [step, h, ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [if_neg h]

theorem req_authorization : Authorized step := by
  intro s r h
  by_cases hV : ValidRequest s r
  · obtain ⟨_, _, hm, he⟩ := hV
    exact ⟨hm, he⟩
  · exfalso
    have hstep : (step s r).1 = Outcome.rejected := by
      unfold step
      simp [hV]
    rw [hstep] at h
    cases h

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hV]
    rw [h2]
    unfold nextState
    simp only
    constructor
    · unfold expectedStatus
      simp [hne]
    · unfold expectedContent
      simp [hne]
  · exfalso
    have hstep : (step s r).1 = Outcome.rejected := by unfold step; simp [hV]
    rw [hstep] at hok
    cases hok

theorem req_published_immutable  : PublishedImmutable step := by
  intro s r d hstat
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hV]
    rw [h2]
    unfold nextState
    simp only
    unfold expectedContent
    by_cases hcond : (r.kind = .edit ∧ d = r.doc)
    · obtain ⟨hedit, heq⟩ := hcond
      obtain ⟨_, _, _, he⟩ := hV
      have hpair := he hedit
      obtain ⟨_, hdraft⟩ := hpair
      rw [← heq] at hdraft
      rcases hstat with hpub | harch
      · rw [hpub] at hdraft; cases hdraft
      · rw [harch] at hdraft; cases hdraft
    · simp [hcond]
  · have h2 : (step s r).2 = s := by unfold step; simp [hV]
    rw [h2]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hV : ValidRequest s r
    · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hV]
      rw [h2]
      show (nextState s r).status d = .published ∨ (nextState s r).status d = .archived
      have hst : (nextState s r).status d = expectedStatus s r d := rfl
      rw [hst]
      unfold expectedStatus
      by_cases hcond : (r.kind = .move ∧ d = r.doc)
      · have hif : (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = r.dst := if_pos hcond
        rw [hif]
        obtain ⟨hkind, heq⟩ := hcond
        obtain ⟨_, _, hm, _⟩ := hV
        have hall := hm hkind
        have hsd : s.status r.doc = .published := by rw [← heq]; exact hpub
        rw [hsd] at hall
        cases hro : s.role r.actor <;> cases hdst : r.dst <;> simp [allowed, hro, hdst] at hall ⊢ <;> cases hall
      · have hif : (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = s.status d := if_neg hcond
        rw [hif, hpub]
        exact Or.inl rfl
    · have h2 : (step s r).2 = s := by unfold step; simp [hV]
      rw [h2, hpub]
      exact Or.inl rfl
  · intro harch
    by_cases hV : ValidRequest s r
    · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hV]
      rw [h2]
      show (nextState s r).status d = .archived
      have hst : (nextState s r).status d = expectedStatus s r d := rfl
      rw [hst]
      unfold expectedStatus
      by_cases hcond : (r.kind = .move ∧ d = r.doc)
      · have hif : (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = r.dst := if_pos hcond
        rw [hif] at ⊢
        obtain ⟨hkind, heq⟩ := hcond
        obtain ⟨_, _, hm, _⟩ := hV
        have hall := hm hkind
        have hsd : s.status r.doc = .archived := by rw [← heq]; exact harch
        rw [hsd] at hall
        cases hro : s.role r.actor <;> cases hdst : r.dst <;> simp [allowed, hro, hdst] at hall
      · have hif : (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = s.status d := if_neg hcond
        rw [hif, harch]
    · have h2 : (step s r).2 = s := by unfold step; simp [hV]
      rw [h2, harch]

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hV]
    rw [h2]
    exact ⟨rfl, rfl, rfl, fun d => rfl, fun d => rfl, rfl⟩
  · exfalso
    have hstep : (step s r).1 = Outcome.rejected := by unfold step; simp [hV]
    rw [hstep] at hok
    cases hok

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  show s.audit <+: (step s r).2.audit
  unfold step
  by_cases hV : ValidRequest s r
  · simp only [if_pos hV]
    show s.audit <+: (nextState s r).audit
    unfold nextState
    simp only
    unfold expectedAudit
    by_cases hm : r.kind = .move
    · simp [hm]
    · simp [hm]
  · simp only [if_neg hV]
    exact List.prefix_refl s.audit

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons d hd
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by unfold step; simp [hV]
    have hd2 : d ∈ (nextState s r).docs := h2 ▸ hd
    have hd' : d ∈ s.docs := hd2
    have hrep : replay s.audit d .draft = s.status d := hCons d hd'
    have hgoal : replay (nextState s r).audit d .draft = (nextState s r).status d := by
      have ha : (nextState s r).audit = expectedAudit s r := rfl
      have hs : (nextState s r).status d = expectedStatus s r d := rfl
      rw [ha, hs]
      by_cases hmove : r.kind = .move
      · have hEA : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by
          unfold expectedAudit; simp [hmove]
        rw [hEA]
        rw [replay_append_thm]
        rw [hrep]
        rw [replay_single_thm]
        by_cases heq : r.doc = d
        · have heq2 : d = r.doc := Eq.symm heq
          have hcond : (r.kind = .move ∧ d = r.doc) := ⟨hmove, heq2⟩
          have hL : ((⟨r.doc, r.actor, s.status r.doc, r.dst⟩ : Entry).doc = d) := heq
          rw [if_pos hL]
          have hR2 : expectedStatus s r d = r.dst := by
            unfold expectedStatus; rw [if_pos hcond]
          rw [hR2]
        · have heq2 : ¬ (d = r.doc) := fun h => heq (Eq.symm h)
          have hcond : ¬ (r.kind = .move ∧ d = r.doc) := fun h => heq2 h.2
          have hL : ¬ (((⟨r.doc, r.actor, s.status r.doc, r.dst⟩ : Entry).doc) = d) := by
            intro hcontra
            exact heq hcontra
          rw [if_neg hL]
          have hR2 : expectedStatus s r d = s.status d := by
            unfold expectedStatus; rw [if_neg hcond]
          rw [hR2]
      · have hEA : expectedAudit s r = s.audit := by
          unfold expectedAudit; simp [hmove]
        rw [hEA, hrep]
        unfold expectedStatus
        simp [hmove]
    rw [h2]; exact hgoal
  · have h2 : (step s r).2 = s := by unfold step; simp [hV]
    have hd' : d ∈ s.docs := h2 ▸ hd
    rw [h2]
    exact hCons d hd'

end Workflow
