import Workflow.Spec

namespace Workflow

def step : Impl := fun s r =>
  let docMem : Bool := s.docs.contains r.doc
  let userMem : Bool := s.users.contains r.actor
  let authOk : Bool :=
    match r.kind with
    | .move => allowed (s.role r.actor) (s.status r.doc) r.dst
    | .edit => decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)
  if docMem && userMem && authOk then
    (Outcome.ok,
      { docs := s.docs,
        users := s.users,
        status := fun d => expectedStatus s r d,
        content := fun d => expectedContent s r d,
        role := s.role,
        audit := expectedAudit s r })
  else
    (Outcome.rejected, s)

theorem req_single_doc_aux1 (s : State) (r : Request) (d : DocId) (hd : d ≠ r.doc) :
    expectedStatus s r d = s.status d := by
  unfold expectedStatus
  simp [hd]

theorem req_single_doc_aux2 (s : State) (r : Request) (d : DocId) (hd : d ≠ r.doc) :
    expectedContent s r d = s.content d := by
  unfold expectedContent
  have h' : ¬ (r.kind = Kind.edit ∧ d = r.doc) := fun h => hd h.2
  simp [h']

theorem req_no_unpublish_aux_test2 : True := by
  trivial
#check @List.contains
#check @List.elem_eq_mem

theorem probe_contains_mem (s : State) (r : Request) : (s.docs.contains r.doc = true ↔ r.doc ∈ s.docs) := by
  simp [List.contains_eq_mem]
#check @List.contains_eq_mem

theorem probe_unfold_aux : True := by
  trivial
#check (Workflow.allowed .publisher .published .archived)
#check (Workflow.expectedStatus)

theorem helper_pub_allow2 (ro : Role) (dst : Status) (h : allowed ro .published dst = true) :
    dst = .published ∨ dst = .archived := by
  cases ro <;> cases dst <;> simp_all [allowed]

theorem helper_arch_allow (ro : Role) (src dst : Status) (hs : src = .archived) (h : allowed ro src dst = true) : False := by
  subst hs; cases ro <;> cases dst <;> simp [allowed] at h

theorem helper_pub_allow3 (ro : Role) (src dst : Status) (hs : src = .published) (h : allowed ro src dst = true) :
    dst = .published ∨ dst = .archived := by
  subst hs; exact helper_pub_allow2 ro dst h

theorem tmp_eff_rw (s : State) (r : Request) :
    step s r =
      (if ((s.docs.contains r.doc && s.users.contains r.actor &&
        (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft))) = true)
      then (Outcome.ok,
        { docs := s.docs,
          users := s.users,
          status := fun d => expectedStatus s r d,
          content := fun d => expectedContent s r d,
          role := s.role,
          audit := expectedAudit s r })
      else (Outcome.rejected, s)) := by
  unfold step
  simp only

theorem tmp_prefix_test (s : State) (r : Request) : s.audit <+: expectedAudit s r := by
  unfold expectedAudit
  by_cases h : r.kind = Kind.move
  · simp [h]
  · simp [h]

theorem probe_prefix_refl (l : List Entry) : l <+: l := by
  exact ⟨[], by simp⟩

theorem replay_append_lemma : ∀ (l1 l2 : List Entry) (d : DocId) (st : Status), replay (l1 ++ l2) d st = replay l2 d (replay l1 d st) := by
  intro l1
  induction l1 with
  | nil => intro l2 d st; simp [replay]
  | cons hd tl ih => intro l2 d st; simp [replay, ih]
#check replay_append_lemma

theorem replay_single_entry (e : Entry) (d : DocId) (st : Status) :
    replay [e] d st = (if e.doc = d then e.dst else st) := by
  simp [replay]

theorem replay_append_single (l : List Entry) (e : Entry) (d : DocId) (st : Status) :
    replay (l ++ [e]) d st = (if e.doc = d then e.dst else replay l d st) := by
  rw [replay_append_lemma]
  simp [replay]

theorem replay_edit_status (s : State) (r : Request) (h : r.kind = Kind.edit) (d : DocId) :
    expectedStatus s r d = s.status d := by
  unfold expectedStatus
  simp [h]

theorem replay_move_audit (s : State) (r : Request) (h : r.kind = Kind.move) :
    expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by
  unfold expectedAudit
  simp [h]

theorem replay_edit_audit (s : State) (r : Request) (h : r.kind ≠ Kind.move) :
    expectedAudit s r = s.audit := by
  unfold expectedAudit
  simp [h]

theorem tmp_valid_probe2 (s : State) (r : Request) (hmove : r.kind = Kind.move → allowed (s.role r.actor) (s.status r.doc) r.dst = true) (hedit : r.kind = Kind.edit → s.role r.actor = Role.author ∧ s.status r.doc = Status.draft) :
    (match r.kind with | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft)) = true := by
  cases hkr : r.kind with
  | move =>
    simp only
    exact hmove hkr
  | edit =>
    simp only
    have he := hedit hkr
    obtain ⟨h1, h2⟩ := he
    simp [h1, h2]

theorem probe_step_unfold (s : State) (r : Request) :
    True := by
  have h : (step s r).1 = Outcome.ok → True := by
    intro ho
    unfold step at ho
    simp only at ho
    trivial
  trivial

theorem probe_bool_and3 (a b c : Bool) (h : (a && b && c) = true) : a = true := by
  have h2 : ((a && b) && c) = true := h
  have h3 := (Bool.and_eq_true ((a && b)) c).mp h2
  have h4 := (Bool.and_eq_true a b).mp h3.1
  exact h4.1

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold ValidRequest at h
  obtain ⟨hdoc, huser, hmove, hedit⟩ := h
  have hauth := tmp_valid_probe2 s r hmove hedit
  have hdocT : s.docs.contains r.doc = true := by simp [List.contains_eq_mem, hdoc]
  have huserT : s.users.contains r.actor = true := by simp [List.contains_eq_mem, huser]
  unfold step
  simp only [hdocT, huserT, hauth, Bool.true_and, ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hN
  have hstep := tmp_eff_rw s r
  rw [hstep]
  by_cases hC : ((s.docs.contains r.doc && s.users.contains r.actor &&
        (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft))) = true)
  · exfalso
    apply hN
    have hAB : ((s.docs.contains r.doc && s.users.contains r.actor) && (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft))) = true := hC
    have hConj := (Bool.and_eq_true _ _).mp hAB
    have hConj2 := (Bool.and_eq_true _ _).mp hConj.1
    have hdocT : s.docs.contains r.doc = true := hConj2.1
    have huserT : s.users.contains r.actor = true := hConj2.2
    have hauthT : (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft)) = true := hConj.2
    have hdoc : r.doc ∈ s.docs := by
      have hmem : r.doc ∈ s.docs ↔ s.docs.contains r.doc = true := by simp [List.contains_eq_mem]
      rw [hmem]; exact hdocT
    have huser : r.actor ∈ s.users := by
      have hmem : r.actor ∈ s.users ↔ s.users.contains r.actor = true := by simp [List.contains_eq_mem]
      rw [hmem]; exact huserT
    refine ⟨hdoc, huser, ?_, ?_⟩
    · intro hm
      rw [hm] at hauthT
      simp only at hauthT
      exact hauthT
    · intro he
      rw [he] at hauthT
      simp only at hauthT
      simp at hauthT
      exact hauthT
  · rw [if_neg hC]

theorem req_authorization : Authorized step := by
  intro s r h
  unfold step at h
  simp only at h
  by_cases hC : ((r.doc ∈ s.docs ∧ r.actor ∈ s.users) ∧
            (match r.kind with
              | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
              | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft)) = true)
  · simp [hC] at h
    constructor
    · intro hm
      rw [hm] at hC
      simp at hC
      exact hC.2
    · intro he
      rw [he] at hC
      simp at hC
      exact hC.2
  · simp [hC] at h

theorem req_single_doc : SingleDoc step := by
  intro s r h d hd
  have hstep := tmp_eff_rw s r
  by_cases hC : ((s.docs.contains r.doc && s.users.contains r.actor &&
        (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft))) = true)
  · rw [hstep, if_pos hC]
    simp only
    constructor
    · exact req_single_doc_aux1 s r d hd
    · exact req_single_doc_aux2 s r d hd
  · rw [hstep, if_neg hC] at h ⊢
    simp only at h
    -- h : rejected = ok is contradictory; need to derive False
    simp at h

theorem req_published_immutable  : PublishedImmutable step := by
  intro s r d h
  simp only [step] at *
  by_cases hC : ((r.doc ∈ s.docs ∧ r.actor ∈ s.users) ∧
            (match r.kind with
              | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
              | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft)) = true)
  · simp [hC]
    unfold expectedContent
    by_cases he : (r.kind = Kind.edit ∧ d = r.doc)
    · obtain ⟨hk, hd⟩ := he
      subst hd
      have hC2 := hC.2
      rw [hk] at hC2
      simp at hC2
      obtain ⟨_, hdraft⟩ := hC2
      rcases h with hpub | harch
      · rw [hpub] at hdraft
        contradiction
      · rw [harch] at hdraft
        contradiction
    · simp [he]
  · simp [hC]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  have hstep := tmp_eff_rw s r
  by_cases hC : ((s.docs.contains r.doc && s.users.contains r.actor &&
        (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft))) = true)
  · have hAuth : (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft)) = true := by
      have hAB : ((s.docs.contains r.doc && s.users.contains r.actor) &&
        (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft))) = true := hC
      exact ((Bool.and_eq_true _ _).mp hAB).2
    constructor
    · intro hpub
      rw [hstep, if_pos hC]
      simp only
      by_cases hm : (r.kind = Kind.move ∧ d = r.doc)
      · have hkm : r.kind = Kind.move := hm.1
        have heq : d = r.doc := hm.2
        have hAuth2 : allowed (s.role r.actor) (s.status r.doc) r.dst = true := by
          have : (match r.kind with
            | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
            | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft)) = true := hAuth
          simp [hkm] at this
          exact this
        have hsrc : s.status r.doc = Status.published := by rw [← heq]; exact hpub
        have hdst : r.dst = Status.published ∨ r.dst = Status.archived := by
          have h2 : allowed (s.role r.actor) Status.published r.dst = true := by rw [← hsrc]; exact hAuth2
          exact helper_pub_allow2 (s.role r.actor) r.dst h2
        have hExp : expectedStatus s r d = r.dst := by unfold expectedStatus; simp [hm]
        rw [hExp]
        exact hdst
      · have hExp : expectedStatus s r d = s.status d := by unfold expectedStatus; simp [hm]
        rw [hExp, hpub]
        exact Or.inl rfl
    · intro harch
      rw [hstep, if_pos hC]
      simp only
      by_cases hm : (r.kind = Kind.move ∧ d = r.doc)
      · have hkm : r.kind = Kind.move := hm.1
        have heq : d = r.doc := hm.2
        have hAuth2 : allowed (s.role r.actor) (s.status r.doc) r.dst = true := by
          have : (match r.kind with
            | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
            | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft)) = true := hAuth
          simp [hkm] at this
          exact this
        have hsrc : s.status r.doc = Status.archived := by rw [← heq]; exact harch
        have hF : False := by
          have h2 : allowed (s.role r.actor) Status.archived r.dst = true := by rw [← hsrc]; exact hAuth2
          have := helper_arch_allow (s.role r.actor) Status.archived r.dst rfl h2
          exact this
        exact False.elim hF
      · have hExp : expectedStatus s r d = s.status d := by unfold expectedStatus; simp [hm]
        rw [hExp, harch]
  · constructor
    · intro hpub
      rw [hstep, if_neg hC]
      simp only
      exact Or.inl hpub
    · intro harch
      rw [hstep, if_neg hC]
      simp only
      exact harch

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hC : ((r.doc ∈ s.docs ∧ r.actor ∈ s.users) ∧
            (match r.kind with
              | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
              | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft)) = true)
  · simp [hC] at h ⊢
  · simp [hC] at h

theorem req_audit_append_only    : AuditAppendOnly step := by
  intro s r
  have hpre : s.audit <+: expectedAudit s r := tmp_prefix_test s r
  have hstep := tmp_eff_rw s r
  by_cases hC : (((s.docs.contains r.doc && s.users.contains r.actor &&
        (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft))) = true))
  · rw [hstep, if_pos hC]
    simp only
    exact hpre
  · rw [hstep, if_neg hC]
    simp only
    exact probe_prefix_refl s.audit

theorem req_audit_consistent     : KeepsAuditConsistent step := by
  intro s r hCons d hd
  have hstep := tmp_eff_rw s r
  by_cases hC : (((s.docs.contains r.doc && s.users.contains r.actor &&
        (match r.kind with
        | Kind.move => allowed (s.role r.actor) (s.status r.doc) r.dst
        | Kind.edit => decide (s.role r.actor = Role.author) && decide (s.status r.doc = Status.draft))) = true))
  · rw [hstep, if_pos hC] at hd ⊢
    simp only at hd ⊢
    by_cases hm : r.kind = Kind.move
    · have haudit : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] :=
        replay_move_audit s r hm
      have hreplay : replay s.audit d Status.draft = s.status d := hCons d hd
      by_cases heq : r.doc = d
      · subst heq
        rw [haudit, replay_append_single]
        simp only [↓reduceIte]
        have hstat : expectedStatus s r r.doc = r.dst := by
          unfold expectedStatus; simp [hm]
        rw [hstat]
      · have hne : d ≠ r.doc := fun h => heq h.symm
        rw [haudit, replay_append_single]
        simp only [heq, ↓reduceIte]
        rw [hreplay]
        unfold expectedStatus
        simp [hne]
    · have haudit : expectedAudit s r = s.audit := replay_edit_audit s r hm
      have hstat : expectedStatus s r d = s.status d := by
        unfold expectedStatus; simp [hm]
      rw [haudit, hstat]
      exact hCons d hd
  · rw [hstep, if_neg hC] at hd ⊢
    simp only at hd ⊢
    exact hCons d hd

end Workflow
