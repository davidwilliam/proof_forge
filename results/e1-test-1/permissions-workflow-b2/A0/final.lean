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

theorem aux_valid_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidRequest s r := by
  by_cases hv : ValidRequest s r
  · exact hv
  · have heq : step s r = (.rejected, s) := by
      unfold step
      simp [hv]
    rw [heq] at h
    simp at h

theorem aux_step_eq_next {s : State} {r : Request} (hv : ValidRequest s r) :
    (step s r).2 = nextState s r := by
  unfold step
  simp [hv]

theorem aux_step_eq_self {s : State} {r : Request} (hv : ¬ ValidRequest s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [hv]

theorem aux_step_snd_self {s : State} {r : Request} (hv : ¬ ValidRequest s r) :
    (step s r).2 = s := by
  have heq := aux_step_eq_self hv
  rw [heq]

theorem aux_replay_append_single (l : List Entry) (e : Entry) (d : DocId) (st : Status) :
    replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
  induction l generalizing st with
  | nil =>
    simp [replay]
  | cons hd tl ih =>
    have h1 : replay ((hd :: tl) ++ [e]) d st
        = replay (tl ++ [e]) d (if hd.doc = d then hd.dst else st) := rfl
    rw [h1, ih]
    have h2 : replay (hd :: tl) d st
        = replay tl d (if hd.doc = d then hd.dst else st) := rfl
    rw [h2]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : Authorized step := by
  intro s r hok
  have hv : ValidRequest s r := aux_valid_of_ok hok
  unfold ValidRequest at hv
  obtain ⟨_, _, hmove, hedit⟩ := hv
  constructor
  · intro hm
    exact hmove hm
  · intro he
    exact hedit he

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  have hv : ValidRequest s r := aux_valid_of_ok hok
  have h2 := aux_step_eq_next hv
  rw [h2]
  have hc1 : ¬ (r.kind = .move ∧ d = r.doc) := fun h => hne h.2
  have hc2 : ¬ (r.kind = .edit ∧ d = r.doc) := fun h => hne h.2
  have hs : (nextState s r).status d = s.status d := by
    show expectedStatus s r d = s.status d
    unfold expectedStatus
    rw [if_neg hc1]
  have hct : (nextState s r).content d = s.content d := by
    show expectedContent s r d = s.content d
    unfold expectedContent
    rw [if_neg hc2]
  exact ⟨hs, hct⟩

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hpub
  by_cases hv : ValidRequest s r
  · have h2 := aux_step_eq_next hv
    rw [h2]
    show (nextState s r).content d = s.content d
    show expectedContent s r d = s.content d
    unfold expectedContent
    by_cases heq : (r.kind = .edit ∧ d = r.doc)
    · have hke : r.kind = .edit := heq.1
      have hdd : d = r.doc := heq.2
      unfold ValidRequest at hv
      obtain ⟨_, _, _, hedit⟩ := hv
      have hed := hedit hke
      obtain ⟨_, hst⟩ := hed
      have hsd : s.status d = .draft := by
        rw [hdd]
        exact hst
      cases hpub with
      | inl hp =>
        rw [hsd] at hp
        simp at hp
      | inr ha =>
        rw [hsd] at ha
        simp at ha
    · rw [if_neg heq]
  · have hsnd := aux_step_snd_self hv
    rw [hsnd]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hv : ValidRequest s r
    · have h2 := aux_step_eq_next hv
      rw [h2]
      show (nextState s r).status d = .published ∨ (nextState s r).status d = .archived
      show expectedStatus s r d = .published ∨ expectedStatus s r d = .archived
      unfold expectedStatus
      by_cases hconj : (r.kind = .move ∧ d = r.doc)
      · have hkm : r.kind = .move := hconj.1
        have hdd : d = r.doc := hconj.2
        rw [if_pos hconj]
        unfold ValidRequest at hv
        obtain ⟨_, _, hmove, _⟩ := hv
        have hallow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hkm
        have hsrc : s.status r.doc = .published := by
          rw [← hdd]
          exact hpub
        cases hro : s.role r.actor with
        | guest =>
          cases hdr : r.dst with
          | draft => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | review => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | approved => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | published => exact Or.inl rfl
          | archived => exact Or.inr rfl
        | author =>
          cases hdr : r.dst with
          | draft => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | review => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | approved => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | published => exact Or.inl rfl
          | archived => exact Or.inr rfl
        | reviewer =>
          cases hdr : r.dst with
          | draft => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | review => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | approved => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | published => exact Or.inl rfl
          | archived => exact Or.inr rfl
        | publisher =>
          cases hdr : r.dst with
          | draft => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | review => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | approved => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | published =>
            rw [hro, hsrc, hdr] at hallow
            simp [allowed] at hallow
          | archived => exact Or.inr rfl
      · rw [if_neg hconj, hpub]
        exact Or.inl rfl
    · have hsnd := aux_step_snd_self hv
      rw [hsnd, hpub]
      exact Or.inl rfl
  · intro harc
    by_cases hv : ValidRequest s r
    · have h2 := aux_step_eq_next hv
      rw [h2]
      show (nextState s r).status d = .archived
      show expectedStatus s r d = .archived
      unfold expectedStatus
      by_cases hconj : (r.kind = .move ∧ d = r.doc)
      · have hkm : r.kind = .move := hconj.1
        have hdd : d = r.doc := hconj.2
        rw [if_pos hconj]
        unfold ValidRequest at hv
        obtain ⟨_, _, hmove, _⟩ := hv
        have hallow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hkm
        have hsrc : s.status r.doc = .archived := by
          rw [← hdd]
          exact harc
        cases hro : s.role r.actor with
        | guest =>
          cases hdr : r.dst with
          | draft => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | review => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | approved => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | published => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | archived => rfl
        | author =>
          cases hdr : r.dst with
          | draft => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | review => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | approved => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | published => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | archived => rfl
        | reviewer =>
          cases hdr : r.dst with
          | draft => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | review => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | approved => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | published => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | archived => rfl
        | publisher =>
          cases hdr : r.dst with
          | draft => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | review => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | approved => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | published => rw [hro, hsrc, hdr] at hallow; simp [allowed] at hallow
          | archived => rfl
      · rw [if_neg hconj, harc]
    · have hsnd := aux_step_snd_self hv
      rw [hsnd, harc]

theorem req_effects : Effects step := by
  intro s r hok
  have hv : ValidRequest s r := aux_valid_of_ok hok
  have h2 := aux_step_eq_next hv
  rw [h2]
  exact ⟨rfl, rfl, rfl, fun d => rfl, fun d => rfl, rfl⟩

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  by_cases hv : ValidRequest s r
  · have h2 := aux_step_eq_next hv
    rw [h2]
    show s.audit <+: (nextState s r).audit
    show s.audit <+: expectedAudit s r
    unfold expectedAudit
    by_cases hk : r.kind = .move
    · rw [if_pos hk]
      exact ⟨[_], rfl⟩
    · rw [if_neg hk]
      exact ⟨[], by simp⟩
  · have hsnd := aux_step_snd_self hv
    rw [hsnd]
    exact ⟨[], by simp⟩

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hcons
  by_cases hv : ValidRequest s r
  · have h2 := aux_step_eq_next hv
    rw [h2]
    intro d hd
    have hdmem : d ∈ s.docs := hd
    have hrep : replay s.audit d .draft = s.status d := hcons d hdmem
    show replay (nextState s r).audit d .draft = (nextState s r).status d
    show replay (expectedAudit s r) d .draft = expectedStatus s r d
    unfold expectedAudit expectedStatus
    by_cases hkm : r.kind = .move
    · by_cases hdd : d = r.doc
      · have hpos : (r.kind = .move ∧ d = r.doc) := ⟨hkm, hdd⟩
        rw [if_pos hkm, if_pos hpos, aux_replay_append_single]
        have hcond : (r.doc = d) := hdd.symm
        rw [if_pos hcond]
      · have hneg : ¬ (r.kind = .move ∧ d = r.doc) := fun h => hdd h.2
        rw [if_pos hkm, if_neg hneg, aux_replay_append_single]
        have hcond : ¬ (r.doc = d) := fun h => hdd h.symm
        rw [if_neg hcond]
        exact hrep
    · have hnegS : ¬ (r.kind = .move ∧ d = r.doc) := fun h => hkm h.1
      rw [if_neg hkm, if_neg hnegS]
      exact hrep
  · have hsnd := aux_step_snd_self hv
    rw [hsnd]
    exact hcons

end Workflow
