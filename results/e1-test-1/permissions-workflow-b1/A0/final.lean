import Workflow.Spec
namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest
  infer_instance

def nextState (s : State) (r : Request) : State :=
  { docs := s.docs
    users := s.users
    status := fun d => expectedStatus s r d
    content := fun d => expectedContent s r d
    role := s.role
    audit := expectedAudit s r }

def step : Impl := fun s r =>
  if ValidRequest s r then (.ok, nextState s r) else (.rejected, s)

theorem replay_append_single (l : List Entry) (e : Entry) (d : DocId) (st : Status) :
    replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
  induction l generalizing st with
  | nil =>
    simp [replay]
  | cons hd tl ih =>
    simp [replay, ih]

theorem pub_arch (ro : Role) (dst : Status) (h : allowed ro Status.published dst = true) :
    dst = Status.archived := by
  cases ro <;> cases dst <;> simp_all [allowed]

theorem arch_false (ro : Role) (dst : Status) : ¬ (allowed ro Status.archived dst = true) := by
  cases ro <;> cases dst <;> decide

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_authorization : Authorized step := by
  intro s r hok
  by_cases hV : ValidRequest s r
  · have h1 := hV.2.2.1
    have h2 := hV.2.2.2
    exact ⟨h1, h2⟩
  · have hstep : step s r = (.rejected, s) := by simp [step, hV]
    have h1 : (step s r).1 = Outcome.rejected := by rw [hstep]
    rw [h1] at hok
    have hNe : ¬ (Outcome.rejected = Outcome.ok) := by decide
    have hF := hNe hok
    exact False.elim hF

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by simp [step, hV]
    rw [h2]
    have hNotMove : ¬ (r.kind = Kind.move ∧ d = r.doc) := by
      intro h
      exact hne h.2
    have hNotEdit : ¬ (r.kind = Kind.edit ∧ d = r.doc) := by
      intro h
      exact hne h.2
    have hs : expectedStatus s r d = s.status d := by simp [expectedStatus, hNotMove]
    have hc : expectedContent s r d = s.content d := by simp [expectedContent, hNotEdit]
    have hs2 : (nextState s r).status d = s.status d := hs
    have hc2 : (nextState s r).content d = s.content d := hc
    exact ⟨hs2, hc2⟩
  · have hstep : step s r = (.rejected, s) := by simp [step, hV]
    have h1 : (step s r).1 = Outcome.rejected := by rw [hstep]
    rw [h1] at hok
    have hNe : ¬ (Outcome.rejected = Outcome.ok) := by decide
    have hF := hNe hok
    exact False.elim hF

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hpub
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by simp [step, hV]
    rw [h2]
    have hc0 : (nextState s r).content d = expectedContent s r d := rfl
    rw [hc0]
    have hedit := hV.2.2.2
    by_cases hk : r.kind = Kind.edit ∧ d = r.doc
    · have hkk1 : r.kind = Kind.edit := hk.1
      have hkk2 : d = r.doc := hk.2
      have hstat : s.status r.doc = Status.draft := (hedit hkk1).2
      have hstat2 : s.status d = Status.draft := by rw [hkk2]; exact hstat
      cases hpub with
      | inl hp =>
        have hEq := hstat2.symm.trans hp
        have hNe : ¬ (Status.draft = Status.published) := by decide
        have hF := hNe hEq
        exact False.elim hF
      | inr ha =>
        have hEq := hstat2.symm.trans ha
        have hNe : ¬ (Status.draft = Status.archived) := by decide
        have hF := hNe hEq
        exact False.elim hF
    · simp [expectedContent, hk]
  · have h2 : (step s r).2 = s := by simp [step, hV]
    rw [h2]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hV : ValidRequest s r
    · have h2 : (step s r).2 = nextState s r := by simp [step, hV]
      rw [h2]
      have hs0 : (nextState s r).status d = expectedStatus s r d := rfl
      rw [hs0]
      by_cases hm : r.kind = Kind.move ∧ d = r.doc
      · have hk : r.kind = Kind.move := hm.1
        have hdd : d = r.doc := hm.2
        have he : expectedStatus s r d = r.dst := by simp [expectedStatus, hm]
        rw [he]
        have hmove := hV.2.2.1
        have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hk
        have hsr : s.status r.doc = Status.published := by rw [hdd] at hpub; exact hpub
        rw [hsr] at hall
        have hdst := pub_arch (s.role r.actor) r.dst hall
        rw [hdst]
        exact Or.inr rfl
      · have he : expectedStatus s r d = s.status d := by simp [expectedStatus, hm]
        rw [he, hpub]
        exact Or.inl rfl
    · have h2 : (step s r).2 = s := by simp [step, hV]
      rw [h2, hpub]
      exact Or.inl rfl
  · intro harc
    by_cases hV : ValidRequest s r
    · have h2 : (step s r).2 = nextState s r := by simp [step, hV]
      rw [h2]
      have hs0 : (nextState s r).status d = expectedStatus s r d := rfl
      rw [hs0]
      by_cases hm : r.kind = Kind.move ∧ d = r.doc
      · have hk : r.kind = Kind.move := hm.1
        have hdd : d = r.doc := hm.2
        have hmove := hV.2.2.1
        have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hk
        have hsr : s.status r.doc = Status.archived := by rw [hdd] at harc; exact harc
        rw [hsr] at hall
        have hF := arch_false (s.role r.actor) r.dst hall
        exact False.elim hF
      · have he : expectedStatus s r d = s.status d := by simp [expectedStatus, hm]
        rw [he, harc]
    · have h2 : (step s r).2 = s := by simp [step, hV]
      rw [h2, harc]

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by simp [step, hV]
    rw [h2]
    exact ⟨rfl, rfl, rfl, fun d => rfl, fun d => rfl, rfl⟩
  · have hstep : step s r = (.rejected, s) := by simp [step, hV]
    have h1 : (step s r).1 = Outcome.rejected := by rw [hstep]
    rw [h1] at hok
    have hNe : ¬ (Outcome.rejected = Outcome.ok) := by decide
    have hF := hNe hok
    exact False.elim hF

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by simp [step, hV]
    rw [h2]
    have ha : (nextState s r).audit = expectedAudit s r := rfl
    rw [ha]
    by_cases hk : r.kind = Kind.move
    · have he : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by simp [expectedAudit, hk]
      rw [he]
      exact ⟨[⟨r.doc, r.actor, s.status r.doc, r.dst⟩], rfl⟩
    · have he : expectedAudit s r = s.audit := by simp [expectedAudit, hk]
      rw [he]
      exact ⟨[], by simp⟩
  · have h2 : (step s r).2 = s := by simp [step, hV]
    rw [h2]
    exact ⟨[], by simp⟩

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hcons d hdmem
  by_cases hV : ValidRequest s r
  · have h2 : (step s r).2 = nextState s r := by simp [step, hV]
    rw [h2] at hdmem
    rw [h2]
    have hdmem2 : d ∈ s.docs := hdmem
    have hrep : replay s.audit d Status.draft = s.status d := hcons d hdmem2
    have ha : (nextState s r).audit = expectedAudit s r := rfl
    have hs : (nextState s r).status d = expectedStatus s r d := rfl
    rw [ha, hs]
    by_cases hk : r.kind = Kind.move
    · have heAudit : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by simp [expectedAudit, hk]
      have heStatus : expectedStatus s r d = (if d = r.doc then r.dst else s.status d) := by simp [expectedStatus, hk]
      rw [heAudit, heStatus, replay_append_single, hrep]
      by_cases hdd : d = r.doc
      · subst hdd
        simp
      · have h1 : ¬ (r.doc = d) := by intro h; exact hdd h.symm
        simp [hdd, h1]
    · have heAudit : expectedAudit s r = s.audit := by simp [expectedAudit, hk]
      have hNotMove : ¬ (r.kind = Kind.move ∧ d = r.doc) := by intro h; exact hk h.1
      have heStatus : expectedStatus s r d = s.status d := by simp [expectedStatus, hNotMove]
      rw [heAudit, heStatus, hrep]
  · have h2 : (step s r).2 = s := by simp [step, hV]
    rw [h2] at hdmem
    rw [h2]
    exact hcons d hdmem

end Workflow
