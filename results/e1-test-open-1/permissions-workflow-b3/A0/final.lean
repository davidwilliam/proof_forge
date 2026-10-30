import Workflow.Spec
namespace Workflow

def validBool (s : State) (r : Request) : Bool :=
  decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) &&
    match r.kind with
    | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
    | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)

theorem validBool_iff (s : State) (r : Request) : validBool s r = true ↔ ValidRequest s r := by
  unfold validBool ValidRequest
  constructor
  · intro h
    have h1 := (Bool.and_eq_true_iff.mp h).1
    have h2 := (Bool.and_eq_true_iff.mp h).2
    have hd := of_decide_eq_true (Bool.and_eq_true_iff.mp h1).1
    have hu := of_decide_eq_true (Bool.and_eq_true_iff.mp h1).2
    cases hk : r.kind with
    | move =>
      refine ⟨hd, hu, fun _ => ?_, fun he => False.elim ?_⟩
      · simpa [hk] using h2
      · have : (Kind.move : Kind) ≠ Kind.edit := by decide
        exact this (hk ▸ he)
    | edit =>
      refine ⟨hd, hu, fun hm => False.elim ?_, fun _ => ?_⟩
      · have : (Kind.edit : Kind) ≠ Kind.move := by decide
        exact this (hk ▸ hm)
      · have h2' : decide (s.role r.actor = .author) && decide (s.status r.doc = .draft) = true := by simpa [hk] using h2
        exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h2').1, of_decide_eq_true (Bool.and_eq_true_iff.mp h2').2⟩
  · intro h
    cases hk : r.kind with
    | move =>
      have hallow := h.2.2.1 hk
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true h.1, decide_eq_true h.2.1⟩, by simpa [hk] using hallow⟩
    | edit =>
      have he := h.2.2.2 hk
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true h.1, decide_eq_true h.2.1⟩, by simp [hk, decide_eq_true he.1, decide_eq_true he.2]⟩

theorem replay_append_single (l : List Entry) (e : Entry) (d : DocId) (st : Status) :
    replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
  induction l generalizing st with
  | nil => simp [replay]
  | cons hd tl ih => simp [replay, ih]

theorem replay_not_affected {l : List Entry} {d d0 : DocId} {a : UserId} {src dst : Status} {st : Status}
    (hne : d ≠ d0) : replay (l ++ [{ doc := d0, actor := a, src := src, dst := dst }]) d st = replay l d st := by
  rw [replay_append_single]
  have h : ¬ (d0 = d) := fun h => hne h.symm
  simp [h]

theorem replay_affected {l : List Entry} {d : DocId} {a : UserId} {src dst : Status} {st : Status} :
    replay (l ++ [{ doc := d, actor := a, src := src, dst := dst }]) d st = dst := by
  rw [replay_append_single]; simp

def step : Impl := fun s r =>
  if validBool s r then
    match r.kind with
    | .move => (.ok, { docs := s.docs, users := s.users, status := fun d => if d = r.doc then r.dst else s.status d, content := s.content, role := s.role, audit := s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] })
    | .edit => (.ok, { docs := s.docs, users := s.users, status := s.status, content := fun d => if d = r.doc then r.body else s.content d, role := s.role, audit := s.audit })
  else (.rejected, s)

theorem step_ok_iff_valid (s : State) (r : Request) : (step s r).1 = .ok ↔ ValidRequest s r := by
  unfold step
  by_cases hvb : validBool s r = true
  · simp only [hvb]
    cases hrk : r.kind
    · simp [(validBool_iff s r).mp hvb]
    · simp [(validBool_iff s r).mp hvb]
  · have hb : validBool s r = false := Bool.eq_false_iff.mpr (fun h => hvb h)
    simp only [hb]
    constructor
    · intro h; cases h
    · intro hv; have := (validBool_iff s r).mpr hv; rw [this] at hb; cases hb

theorem step_state_rejected (s : State) (r : Request) (h : ¬ ValidRequest s r) : step s r = (.rejected, s) := by
  unfold step
  have hb : validBool s r = false := Bool.eq_false_iff.mpr (fun hc => h ((validBool_iff s r).mp hc))
  simp [hb]

theorem step_state_ok_move (s : State) (r : Request) (h : ValidRequest s r) (hm : r.kind = .move) :
    (step s r).2 = { docs := s.docs, users := s.users, status := fun d => if d = r.doc then r.dst else s.status d, content := s.content, role := s.role, audit := s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] } := by
  unfold step
  have hb : validBool s r = true := (validBool_iff s r).mpr h
  simp [hb, hm]

theorem step_state_ok_edit (s : State) (r : Request) (h : ValidRequest s r) (he : r.kind = .edit) :
    (step s r).2 = { docs := s.docs, users := s.users, status := s.status, content := fun d => if d = r.doc then r.body else s.content d, role := s.role, audit := s.audit } := by
  unfold step
  have hb : validBool s r = true := (validBool_iff s r).mpr h
  simp [hb, he]

theorem req_valid_succeeds : ValidSucceeds step := fun s r hv => (step_ok_iff_valid s r).mpr hv

theorem req_invalid_noop : InvalidNoop step := fun s r hn => step_state_rejected s r hn

theorem req_authorization : Authorized step := by
  intro s r hok; have hv := (step_ok_iff_valid s r).mp hok; exact ⟨fun h=>hv.2.2.1 h, fun h=>hv.2.2.2 h⟩

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  have hv := (step_ok_iff_valid s r).mp hok
  cases hrk : r.kind
  · have hs := step_state_ok_move s r hv hrk
    have h1 : (step s r).2.status d = (if d = r.doc then r.dst else s.status d) := by simp only [hs]
    have h2 : (step s r).2.content d = s.content d := by simp only [hs]
    simp [h1, h2, hne]
  · have hs := step_state_ok_edit s r hv hrk
    have h1 : (step s r).2.status d = s.status d := by simp only [hs]
    have h2 : (step s r).2.content d = (if d = r.doc then r.body else s.content d) := by simp only [hs]
    simp [h1, h2, hne]

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hp
  by_cases hv : ValidRequest s r
  · cases hrk : r.kind
    · have hs := step_state_ok_move s r hv hrk
      have : (step s r).2.content = s.content := by simp only [hs]
      simp [this]
    · have hs := step_state_ok_edit s r hv hrk
      have hc : (step s r).2.content = fun x => if x = r.doc then r.body else s.content x := by simp only [hs]
      rw [hc]
      by_cases heq : d = r.doc
      · have hedit := hv.2.2.2 hrk
        have hsd : s.status d = Status.draft := heq ▸ hedit.2
        cases hp with
        | inl hpub => rw [hsd] at hpub; cases hpub
        | inr harc => rw [hsd] at harc; cases harc
      · simp [heq]
  · have : step s r = (.rejected, s) := step_state_rejected s r hv
    simp [this]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d; constructor
  · intro hpub; by_cases hv : ValidRequest s r
    · cases hrk : r.kind
      · have hs := step_state_ok_move s r hv hrk
        have hallow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hv.2.2.1 hrk
        have hst : (step s r).2.status d = if d = r.doc then r.dst else s.status d := by simp only [hs]
        by_cases heq : d = r.doc
        · subst heq
          rw [hst, if_pos rfl]
          rw [hpub] at hallow
          revert hallow
          cases hr : s.role r.actor <;> cases hr2 : r.dst <;> simp [allowed, hr]
        · rw [hst, if_neg heq, hpub]; left; rfl
      · have hs := step_state_ok_edit s r hv hrk
        have hst : (step s r).2.status d = s.status d := by simp only [hs]
        rw [hst, hpub]; left; rfl
    · have hs := step_state_rejected s r hv
      have hst : (step s r).2.status d = s.status d := by simp only [hs]
      rw [hst, hpub]; left; rfl
  · intro harc; by_cases hv : ValidRequest s r
    · cases hrk : r.kind
      · have hs := step_state_ok_move s r hv hrk
        have hallow : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hv.2.2.1 hrk
        have hst : (step s r).2.status d = if d = r.doc then r.dst else s.status d := by simp only [hs]
        by_cases heq : d = r.doc
        · subst heq
          have hall2 : allowed (s.role r.actor) Status.archived r.dst = true := by rw [harc] at hallow; exact hallow
          have hfalse : allowed (s.role r.actor) Status.archived r.dst = false := by cases hr2 : s.role r.actor <;> simp [allowed]
          rw [hfalse] at hall2; cases hall2
        · rw [hst, if_neg heq, harc]
      · have hs := step_state_ok_edit s r hv hrk
        have hst : (step s r).2.status d = s.status d := by simp only [hs]
        rw [hst, harc]
    · have hs := step_state_rejected s r hv
      have hst : (step s r).2.status d = s.status d := by simp only [hs]
      rw [hst, harc]

theorem req_effects : Effects step := by
  intro s r hok
  have hv := (step_ok_iff_valid s r).mp hok
  cases hrk : r.kind with
  | move =>
    have hs := step_state_ok_move s r hv hrk
    refine ⟨by simp only [hs], by simp only [hs], by simp only [hs], ?_, ?_, ?_⟩
    · intro d
      have h1 : (step s r).2.status d = if d = r.doc then r.dst else s.status d := by simp only [hs]
      have hexp : expectedStatus s r d = if d = r.doc then r.dst else s.status d := by
        unfold expectedStatus; simp [hrk]
      rw [h1, hexp]
    · intro d
      have h1 : (step s r).2.content d = s.content d := by simp only [hs]
      have hexp : expectedContent s r d = s.content d := by
        unfold expectedContent; simp [hrk]
      rw [h1, hexp]
    · have h1 : (step s r).2.audit = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by simp only [hs]
      have hexp : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by
        unfold expectedAudit; simp [hrk]
      rw [h1, hexp]
  | edit =>
    have hs := step_state_ok_edit s r hv hrk
    refine ⟨by simp only [hs], by simp only [hs], by simp only [hs], ?_, ?_, ?_⟩
    · intro d
      have h1 : (step s r).2.status d = s.status d := by simp only [hs]
      have hexp : expectedStatus s r d = s.status d := by
        unfold expectedStatus; simp [hrk]
      rw [h1, hexp]
    · intro d
      have h1 : (step s r).2.content d = if d = r.doc then r.body else s.content d := by simp only [hs]
      have hexp : expectedContent s r d = if d = r.doc then r.body else s.content d := by
        unfold expectedContent; simp [hrk]
      rw [h1, hexp]
    · have h1 : (step s r).2.audit = s.audit := by simp only [hs]
      have hexp : expectedAudit s r = s.audit := by
        unfold expectedAudit; simp [hrk]
      rw [h1, hexp]

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  by_cases hv : ValidRequest s r
  · cases hrk : r.kind
    · have hs := step_state_ok_move s r hv hrk
      have ha : (step s r).2.audit = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by simp only [hs]
      rw [ha]; exact ⟨[⟨r.doc, r.actor, s.status r.doc, r.dst⟩], rfl⟩
    · have hs := step_state_ok_edit s r hv hrk
      have ha : (step s r).2.audit = s.audit := by simp only [hs]
      rw [ha]; exact ⟨[], by simp⟩
  · have hs := step_state_rejected s r hv
    have ha : (step s r).2.audit = s.audit := by simp only [hs]
    rw [ha]; exact ⟨[], by simp⟩

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hcons d hd; show replay (step s r).2.audit d Status.draft = (step s r).2.status d
  by_cases hv : ValidRequest s r
  · cases hrk : r.kind
    · have hs := step_state_ok_move s r hv hrk
      have hdocs : (step s r).2.docs = s.docs := by simp only [hs]
      have hd' : d ∈ s.docs := by rw [<-hdocs]; exact hd
      have hmem := hcons d hd'
      have haudit : (step s r).2.audit = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by simp only [hs]
      have hstatus : (step s r).2.status d = if d = r.doc then r.dst else s.status d := by simp only [hs]
      rw [haudit, hstatus]
      by_cases heq : d = r.doc
      · rw [if_pos heq]; subst heq; exact replay_affected
      · rw [if_neg heq, replay_not_affected heq, hmem]
    · have hs := step_state_ok_edit s r hv hrk
      have hdocs : (step s r).2.docs = s.docs := by simp only [hs]
      have hd' : d ∈ s.docs := by rw [<-hdocs]; exact hd
      have hmem := hcons d hd'
      have haudit : (step s r).2.audit = s.audit := by simp only [hs]
      have hstatus : (step s r).2.status = s.status := by simp only [hs]
      rw [haudit, hstatus, hmem]
  · have hs := step_state_rejected s r hv
    have hdocs : (step s r).2.docs = s.docs := by simp only [hs]
    have hd' : d ∈ s.docs := by rw [<-hdocs]; exact hd
    have haudit : (step s r).2.audit = s.audit := by simp only [hs]
    have hstatus : (step s r).2.status = s.status := by simp only [hs]
    rw [haudit, hstatus]; exact hcons d hd'

end Workflow
