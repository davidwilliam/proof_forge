import Workflow.Spec
namespace Workflow
def step : Impl := fun s r =>
  if decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) then
    match r.kind with
    | .move =>
      if allowed (s.role r.actor) (s.status r.doc) r.dst then
        (.ok, { s with
          status := fun d => expectedStatus s r d
          content := fun d => expectedContent s r d
          audit := expectedAudit s r })
      else (.rejected, s)
    | .edit =>
      if decide (s.role r.actor = .author ∧ s.status r.doc = .draft) then
        (.ok, { s with
          status := fun d => expectedStatus s r d
          content := fun d => expectedContent s r d
          audit := expectedAudit s r })
      else (.rejected, s)
  else (.rejected, s)

theorem tmp1 (s : State) (r : Request) (hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users) : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by
  simp [hmem]

theorem tmp2 (s : State) (r : Request) (hmem : ¬ (r.doc ∈ s.docs ∧ r.actor ∈ s.users)) : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by
  simp [hmem]

theorem tmp3 (s : State) (r : Request) (hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true) (hallF : allowed (s.role r.actor) (s.status r.doc) r.dst = false) (hk : r.kind = Kind.move) :
  (if decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) then match r.kind with | .move => if allowed (s.role r.actor) (s.status r.doc) r.dst then (Outcome.ok, s) else (Outcome.rejected, s) | .edit => (Outcome.ok, s) else (Outcome.rejected, s)) = (Outcome.rejected, s) := by
  simp [hdec, hk, hallF]

theorem tmpMatch1 : (match (Kind.move : Kind) with | .move => (1:Nat) | .edit => 2) = 1 := by simp

theorem tmpMatch2 (k : Kind) (h : k = .move) : (match k with | .move => (1:Nat) | .edit => 2) = 1 := by simp [h]

theorem tmpRed (s : State) (r : Request) (hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users) :
  (if decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) then (1:Nat) else 2) = 1 := by
  have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := tmp1 s r hmem
  simp [hdec]

theorem tmp_auth_move3 (s : State) (r : Request) (hok : (step s r).1 = .ok) (hmove : r.kind = Kind.move) :
    allowed (s.role r.actor) (s.status r.doc) r.dst = true := by
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
    by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true
    · exact hall
    · have hdec2 : (decide (allowed (s.role r.actor) (s.status r.doc) r.dst = true) = false) := by simp [hall]
      have hfalse : (step s r).1 = Outcome.rejected := by simp [step, hmove, hdec, hall]
      rw [hfalse] at hok
      simp at hok
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by simp [hmem]
    have hfalse : (step s r).1 = Outcome.rejected := by simp [step, hdec]
    rw [hfalse] at hok
    simp at hok

theorem tmp_auth_edit3 (s : State) (r : Request) (hok : (step s r).1 = .ok) (hedit : r.kind = Kind.edit) :
    s.role r.actor = Role.author ∧ s.status r.doc = Status.draft := by
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
    by_cases hcond : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft
    · exact hcond
    · have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = false := by simp [hcond]
      have hfalse : (step s r).1 = Outcome.rejected := by simp [step, hedit, hdec, hcond]
      rw [hfalse] at hok
      simp at hok
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by simp [hmem]
    have hfalse : (step s r).1 = Outcome.rejected := by simp [step, hdec]
    rw [hfalse] at hok
    simp at hok

theorem helper_single_status : True := trivial

theorem single_exp_status_thm (s : State) (r : Request) (d : DocId) (hne : d ≠ r.doc) : expectedStatus s r d = s.status d := by unfold expectedStatus; simp [hne]

theorem single_exp_content_thm (s : State) (r : Request) (d : DocId) (hne : d ≠ r.doc) : expectedContent s r d = s.content d := by unfold expectedContent; simp [hne]

theorem allowed_pub_helper (ro : Role) (dst : Status) (h : allowed ro .published dst = true) : dst = .archived := by
  cases ro <;> cases dst <;> simp_all [allowed]

theorem allowed_arch_helper (ro : Role) (dst : Status) : allowed ro .archived dst = false := by cases ro <;> cases dst <;> rfl

theorem exp_status_move_eq (s : State) (r : Request) (hkm : r.kind = .move) (heq : r.doc = d) : expectedStatus s r d = r.dst := by simp [expectedStatus, hkm, heq]

theorem exp_status_edit_eq (s : State) (r : Request) (hke : r.kind = .edit) : expectedStatus s r d = s.status d := by simp [expectedStatus, hke]

theorem exp_status_other (s : State) (r : Request) (d : DocId) (hne : d ≠ r.doc) : expectedStatus s r d = s.status d := single_exp_status_thm s r d hne

theorem req_effects_testA : Effects step := by
  intro s r hok
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
    have hkind : r.kind = Kind.move ∨ r.kind = Kind.edit := by cases r.kind <;> simp
    cases hkind with
    | inl hk =>
      have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true :=
        tmp_auth_move3 s r hok hk
      have hstep : step s r = (Outcome.ok, { s with status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, audit := expectedAudit s r }) := by
        simp [step, hdec, hk, hall]
      have h2 : (step s r).2 = { s with status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, audit := expectedAudit s r } := by
        simp [hstep]
      simp [h2]
    | inr hk =>
      have hcond : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft :=
        tmp_auth_edit3 s r hok hk
      have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = true := by simp [hcond]
      have hstep : step s r = (Outcome.ok, { s with status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, audit := expectedAudit s r }) := by
        simp [step, hdec, hk, hdec2]
      have h2 : (step s r).2 = { s with status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, audit := expectedAudit s r } := by
        simp [hstep]
      simp [h2]
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by simp [hmem]
    have hfalse : (step s r).1 = Outcome.rejected := by simp [step, hdec]
    rw [hfalse] at hok
    simp at hok

theorem check_prefix_names (l : List Nat) : l <+: l := by exact List.prefix_refl l

theorem replay_append_single_test (l : List Entry) (e : Entry) (d : DocId) (st : Status) : replay (l ++ [e]) d st = (if e.doc = d then e.dst else replay l d st) := by
  induction l generalizing st with
  | nil => simp [replay]
  | cons hd tl ih => simp [replay, ih]

theorem replay_expected_move_eq (s : State) (r : Request) (d : DocId) (hk : r.kind = .move) :
  replay (expectedAudit s r) d .draft = (if r.doc = d then r.dst else replay s.audit d .draft) := by
  have h1 : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by
    unfold expectedAudit; simp [hk]
  rw [h1]
  have h2 := replay_append_single_test s.audit ⟨r.doc, r.actor, s.status r.doc, r.dst⟩ d .draft
  simp at h2 ⊢
  exact h2

theorem replay_expected_edit_eq (s : State) (r : Request) (hk : r.kind = .edit) :
  expectedAudit s r = s.audit := by
  unfold expectedAudit; simp [hk]

theorem replay_expected_edit_status (s : State) (r : Request) (d : DocId) (hk : r.kind = .edit) :
  expectedStatus s r d = s.status d := by
  unfold expectedStatus; simp [hk]

theorem exp_status_move_hit (s : State) (r : Request) (d : DocId) (hk : r.kind = .move) (heq : d = r.doc) : expectedStatus s r d = r.dst := by unfold expectedStatus; simp [hk, heq]

theorem exp_status_move_miss (s : State) (r : Request) (d : DocId) (hk : r.kind = .move) (hne : d ≠ r.doc) : expectedStatus s r d = s.status d := by unfold expectedStatus; simp [hk, hne]

theorem audit_cons_ok_move3 (s : State) (r : Request) (dd : DocId)
  (hk : r.kind = .move) (hcons : AuditConsistent s) (hd : dd ∈ s.docs)
  (hstat : ∀ e, (step s r).2.status e = expectedStatus s r e)
  (haudit : (step s r).2.audit = expectedAudit s r) :
  replay (step s r).2.audit dd .draft = (step s r).2.status dd := by
  rw [haudit, hstat]
  rw [replay_expected_move_eq s r dd hk]
  by_cases heq : r.doc = dd
  · have hif : (if r.doc = dd then r.dst else replay s.audit dd .draft) = r.dst := by simp [heq]
    rw [hif]
    have hst : expectedStatus s r dd = r.dst := exp_status_move_hit s r dd hk heq.symm
    rw [hst]
  · have heq3 : dd ≠ r.doc := fun h => heq h.symm
    have hif : (if r.doc = dd then r.dst else replay s.audit dd .draft) = replay s.audit dd .draft := by simp [heq]
    rw [hif]
    have hrep : replay s.audit dd .draft = s.status dd := hcons dd hd
    rw [hrep]
    have hst : expectedStatus s r dd = s.status dd := exp_status_move_miss s r dd hk heq3
    rw [hst]

theorem req_valid_succeeds       : ValidSucceeds step := by
  intro s r h
  unfold ValidRequest at h
  obtain ⟨hd, hu, hmove, hedit⟩ := h
  have hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users := ⟨hd, hu⟩
  have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
  cases hk : r.kind with
  | move =>
    have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hk
    simp [step, hdec, hk, hall]
  | edit =>
    have hcond : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft := hedit hk
    have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = true := by simp [hcond]
    simp [step, hdec, hk, hdec2]

theorem req_invalid_noop         : InvalidNoop step := by
  intro s r h
  unfold ValidRequest at h
  obtain ⟨actor, doc, kind, dst, body⟩ := r
  simp only at h ⊢
  by_cases hmem : doc ∈ s.docs ∧ actor ∈ s.users
  · have hdec : decide (doc ∈ s.docs ∧ actor ∈ s.users) = true := by simp [hmem]
    cases kind with
    | move =>
      simp only at h
      have hall_neg : ¬ allowed (s.role actor) (s.status doc) dst = true := by
        intro hall
        apply h
        obtain ⟨hd, hu⟩ := hmem
        refine ⟨hd, hu, ?_, ?_⟩
        · intro _; exact hall
        · intro hedit; cases hedit
      simp [step, hdec, hall_neg]
    | edit =>
      simp only at h
      have hcond_neg : ¬ (s.role actor = Role.author ∧ s.status doc = Status.draft) := by
        intro hcond
        apply h
        obtain ⟨hd, hu⟩ := hmem
        refine ⟨hd, hu, ?_, ?_⟩
        · intro hmove; cases hmove
        · intro _; exact hcond
      have hdec2 : decide (s.role actor = Role.author ∧ s.status doc = Status.draft) = false := by simp [hcond_neg]
      simp [step, hdec, hdec2]
  · have hdec : decide (doc ∈ s.docs ∧ actor ∈ s.users) = false := by simp [hmem]
    simp [step, hdec]

theorem req_authorization : Authorized step := by
  intro s r hok
  exact ⟨fun hmove => tmp_auth_move3 s r hok hmove, fun hedit => tmp_auth_edit3 s r hok hedit⟩

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
    cases hk : r.kind with
    | move =>
      have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true :=
        tmp_auth_move3 s r hok hk
      have hstep2 : (step s r).2.status d = expectedStatus s r d ∧ (step s r).2.content d = expectedContent s r d := by
        simp [step, hdec, hk, hall]
      rw [hstep2.1, hstep2.2, single_exp_status_thm s r d hne, single_exp_content_thm s r d hne]
      exact ⟨rfl, rfl⟩
    | edit =>
      have hcond : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft :=
        tmp_auth_edit3 s r hok hk
      have hstep2 : (step s r).2.status d = expectedStatus s r d ∧ (step s r).2.content d = expectedContent s r d := by
        simp [step, hdec, hk, hcond.1, hcond.2]
      rw [hstep2.1, hstep2.2, single_exp_status_thm s r d hne, single_exp_content_thm s r d hne]
      exact ⟨rfl, rfl⟩
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by simp [hmem]
    have hfalse : (step s r).1 = Outcome.rejected := by simp [step, hdec]
    rw [hfalse] at hok
    simp at hok

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d h
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
    cases hk : r.kind with
    | move =>
      by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true
      · have hcont : (step s r).2.content d = expectedContent s r d := by simp [step, hdec, hk, hall]
        rw [hcont]
        unfold expectedContent
        simp [hk]
      · have hneg : (decide (allowed (s.role r.actor) (s.status r.doc) r.dst = true) = false) := by simp [hall]
        have h2 : (step s r).2 = s := by simp [step, hdec, hk, hall]
        rw [h2]
    | edit =>
      by_cases hcond : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft
      · have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = true := by simp [hcond]
        have hcont : (step s r).2.content d = expectedContent s r d := by simp [step, hdec, hk, hdec2]
        by_cases heq : d = r.doc
        · subst heq
          obtain ⟨_, hdraft⟩ := hcond
          cases h with
          | inl hp => rw [hdraft] at hp; cases hp
          | inr hp => rw [hdraft] at hp; cases hp
        · rw [hcont, single_exp_content_thm s r d heq]
      · have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = false := by simp [hcond]
        have h2 : (step s r).2 = s := by simp [step, hdec, hk, hdec2]
        rw [h2]
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by simp [hmem]
    have h2 : (step s r).2 = s := by simp [step, hdec]
    rw [h2]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
    · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
      cases hk : r.kind with
      | move =>
        by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true
        · have hst : (step s r).2.status d = expectedStatus s r d := by simp [step, hdec, hk, hall]
          rw [hst]
          by_cases heq : d = r.doc
          · subst heq
            have hexp : expectedStatus s r r.doc = r.dst := by simp [expectedStatus, hk]
            rw [hexp]
            have hsrc : s.status r.doc = .published := hpub
            have hall2 : allowed (s.role r.actor) .published r.dst = true := by rw [← hsrc]; exact hall
            have hdst : r.dst = .archived := allowed_pub_helper _ _ hall2
            rw [hdst]; exact Or.inr rfl
          · have h2 : expectedStatus s r d = s.status d := single_exp_status_thm s r d heq
            rw [h2]; exact Or.inl hpub
        · have h2 : (step s r).2 = s := by simp [step, hdec, hk, hall]
          rw [h2]; exact Or.inl hpub
      | edit =>
        by_cases hcond : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft
        · have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = true := by simp [hcond]
          have hst : (step s r).2.status d = expectedStatus s r d := by simp [step, hdec, hk, hdec2]
          rw [hst]; unfold expectedStatus; simp [hk]; exact Or.inl hpub
        · have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = false := by simp [hcond]
          have h2 : (step s r).2 = s := by simp [step, hdec, hk, hdec2]
          rw [h2]; exact Or.inl hpub
    · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by simp [hmem]
      have h2 : (step s r).2 = s := by simp [step, hdec]
      rw [h2]; exact Or.inl hpub
  · intro harch
    by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
    · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
      cases hk : r.kind with
      | move =>
        by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true
        · have hst : (step s r).2.status d = expectedStatus s r d := by simp [step, hdec, hk, hall]
          rw [hst]
          by_cases heq : d = r.doc
          · subst heq
            have hsrc : s.status r.doc = .archived := harch
            have hall2 : allowed (s.role r.actor) .archived r.dst = true := by rw [← hsrc]; exact hall
            rw [allowed_arch_helper] at hall2; cases hall2
          · have h2 : expectedStatus s r d = s.status d := single_exp_status_thm s r d heq
            rw [h2]; exact harch
        · have h2 : (step s r).2 = s := by simp [step, hdec, hk, hall]
          rw [h2]; exact harch
      | edit =>
        by_cases hcond : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft
        · have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = true := by simp [hcond]
          have hst : (step s r).2.status d = expectedStatus s r d := by simp [step, hdec, hk, hdec2]
          rw [hst]; unfold expectedStatus; simp [hk]; exact harch
        · have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = false := by simp [hcond]
          have h2 : (step s r).2 = s := by simp [step, hdec, hk, hdec2]
          rw [h2]; exact harch
    · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by simp [hmem]
      have h2 : (step s r).2 = s := by simp [step, hdec]
      rw [h2]; exact harch

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
    have hkind : r.kind = Kind.move ∨ r.kind = Kind.edit := by cases r.kind <;> simp
    cases hkind with
    | inl hk =>
      have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true :=
        tmp_auth_move3 s r hok hk
      have hstep : step s r = (Outcome.ok, { s with status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, audit := expectedAudit s r }) := by
        simp [step, hdec, hk, hall]
      have h2 : (step s r).2 = { s with status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, audit := expectedAudit s r } := by
        simp [hstep]
      simp [h2]
    | inr hk =>
      have hcond : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft :=
        tmp_auth_edit3 s r hok hk
      have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = true := by simp [hcond]
      have hstep : step s r = (Outcome.ok, { s with status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, audit := expectedAudit s r }) := by
        simp [step, hdec, hk, hdec2]
      have h2 : (step s r).2 = { s with status := fun d => expectedStatus s r d, content := fun d => expectedContent s r d, audit := expectedAudit s r } := by
        simp [hstep]
      simp [h2]
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by simp [hmem]
    have hfalse : (step s r).1 = Outcome.rejected := by simp [step, hdec]
    rw [hfalse] at hok
    simp at hok

theorem req_audit_append_only    : AuditAppendOnly step := by
  intro s r
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = true := by simp [hmem]
    cases hk : r.kind with
    | move =>
      by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true
      · have h2 : (step s r).2.audit = expectedAudit s r := by simp [step, hdec, hk, hall]
        rw [h2]
        unfold expectedAudit
        simp [hk]
      · have h2 : (step s r).2 = s := by simp [step, hdec, hk, hall]
        rw [h2]
        exact List.prefix_refl s.audit
    | edit =>
      by_cases hcond : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft
      · have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = true := by simp [hcond]
        have h2 : (step s r).2.audit = expectedAudit s r := by simp [step, hdec, hk, hdec2]
        rw [h2]
        unfold expectedAudit
        simp [hk]
      · have hdec2 : decide (s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) = false := by simp [hcond]
        have h2 : (step s r).2 = s := by simp [step, hdec, hk, hdec2]
        rw [h2]
        exact List.prefix_refl s.audit
  · have hdec : decide (r.doc ∈ s.docs ∧ r.actor ∈ s.users) = false := by simp [hmem]
    have h2 : (step s r).2 = s := by simp [step, hdec]
    rw [h2]
    exact List.prefix_refl s.audit

theorem req_audit_consistent     : KeepsAuditConsistent step := by
  intro s r hcons dd hdmem
  by_cases hok : (step s r).1 = Outcome.ok
  · have heff := req_effects s r hok
    obtain ⟨hdocs, husers, hrole, hstat, hcont, haudit⟩ := heff
    have hd : dd ∈ s.docs := by rw [← hdocs]; exact hdmem
    -- Actually hdocs : (step s r).2.docs = s.docs, so rw
    cases hk : r.kind with
    | move =>
      exact audit_cons_ok_move3 s r dd hk hcons hd hstat haudit
    | edit =>
      have haudit_eq : (step s r).2.audit = s.audit := by
        rw [haudit, replay_expected_edit_eq s r hk]
      have hstat_eq : (step s r).2.status dd = s.status dd := by
        rw [hstat dd, replay_expected_edit_status s r dd hk]
      rw [haudit_eq, hstat_eq]
      exact hcons dd hd
  · have hinvalid : ¬ ValidRequest s r := by
      intro hv
      have hok2 := req_valid_succeeds s r hv
      rw [hok2] at hok
      simp at hok
    have hnoop := req_invalid_noop s r hinvalid
    have h2 : (step s r).2 = s := by simp [hnoop]
    have hdocs_eq : (step s r).2.docs = s.docs := by rw [h2]
    have hd : dd ∈ s.docs := by rw [← hdocs_eq]; exact hdmem
    rw [h2]
    exact hcons dd hd

end Workflow
