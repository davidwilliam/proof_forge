import Workflow.Spec
namespace Workflow

def doMove (s : State) (r : Request) : State :=
  { s with status := fun d => if d == r.doc then r.dst else s.status d,
           audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] }

def doEdit (s : State) (r : Request) : State :=
  { s with content := fun d => if d == r.doc then r.body else s.content d }

def step : Impl := fun s r =>
  if _h1 : r.doc ∈ s.docs then
    if _h2 : r.actor ∈ s.users then
      match r.kind with
      | .move => if allowed (s.role r.actor) (s.status r.doc) r.dst then (.ok, doMove s r) else (.rejected, s)
      | .edit => if s.role r.actor == .author && s.status r.doc == .draft then (.ok, doEdit s r) else (.rejected, s)
    else (.rejected, s)
  else (.rejected, s)

theorem req_single_doc_helper : SingleDoc step := by
  intro s r h d hne
  unfold step at h
  by_cases hdoc : r.doc ∈ s.docs
  · simp only [dif_pos hdoc] at h
    by_cases huser : r.actor ∈ s.users
    · simp only [dif_pos huser] at h
      cases hk : r.kind
      · simp only [hk] at h
        by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst
        · simp only [hall] at h
          have hpair : (step s r).2 = doMove s r := by
            unfold step
            simp [hdoc, huser, hk, hall]
          rw [hpair]
          unfold doMove
          have hfalse : (d == r.doc) = false := by
            simp [hne]
          constructor
          · simp [hfalse]
          · simp
        · simp only [hall] at h; simp at h
      · simp only [hk] at h
        by_cases ha : s.role r.actor == Role.author && s.status r.doc == Status.draft
        · simp only [ha] at h
          have hpair : (step s r).2 = doEdit s r := by
            unfold step
            simp [hdoc, huser, hk, ha]
          rw [hpair]
          unfold doEdit
          constructor
          · simp
          · simp [hne]
        · simp only [ha] at h; simp at h
    · simp only [dif_neg huser] at h; simp at h
  · simp only [dif_neg hdoc] at h; simp at h

theorem replay_append_aux : ∀ (l1 l2 : List Entry) (d : DocId) (st : Status),
  replay (l1 ++ l2) d st = replay l2 d (replay l1 d st) := by
  intro l1
  induction l1 with
  | nil => intro l2 d st; simp [replay]
  | cons e es ih => intro l2 d st; simp [replay, ih]

theorem replay_singleton_aux : ∀ (l : List Entry) (e : Entry) (d : DocId) (st : Status),
  replay (l ++ [e]) d st = if e.doc = d then e.dst else replay l d st := by
  intro l e d st
  rw [replay_append_aux]
  simp [replay]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hdoc : r.doc ∈ s.docs := h.1
  have huser : r.actor ∈ s.users := h.2.1
  have hmove : r.kind = Kind.move → allowed (s.role r.actor) (s.status r.doc) r.dst = true := h.2.2.1
  have hedit : r.kind = Kind.edit → s.role r.actor = Role.author ∧ s.status r.doc = Status.draft := h.2.2.2
  unfold step
  simp only [dif_pos hdoc, dif_pos huser]
  cases hk : r.kind with
  | move => simp [hmove hk]
  | edit =>
    have he := hedit hk
    simp [he.1, he.2]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold ValidRequest at h
  unfold step
  by_cases hdoc : r.doc ∈ s.docs
  · simp only [dif_pos hdoc]
    by_cases huser : r.actor ∈ s.users
    · simp only [dif_pos huser]
      cases hk : r.kind with
      | move =>
        by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true
        · exfalso; apply h; refine ⟨hdoc, huser, ?_, ?_⟩
          · intro _; exact hall
          · intro heq; simp [hk] at heq
        · simp [hall]
      | edit =>
        by_cases ha : (s.role r.actor == .author && s.status r.doc == .draft) = true
        · exfalso; apply h
          have hro_true : (s.role r.actor == .author) = true := by
            cases hc : (s.role r.actor == .author) with
            | true => rfl
            | false => simp [hc] at ha
          have hst_true : (s.status r.doc == .draft) = true := by
            cases hc2 : (s.status r.doc == .draft) with
            | true => rfl
            | false =>
              cases hc : (s.role r.actor == .author) with
              | true => simp [hc, hc2] at ha
              | false => simp [hc] at hro_true
          have hro : s.role r.actor = .author := by
            simp [beq_iff_eq] at hro_true; exact hro_true
          have hst : s.status r.doc = .draft := by
            simp [beq_iff_eq] at hst_true; exact hst_true
          refine ⟨hdoc, huser, ?_, ?_⟩
          · intro heq; simp [hk] at heq
          · intro _; exact ⟨hro, hst⟩
        · simp [ha]
    · simp only [dif_neg huser]
  · simp only [dif_neg hdoc]

theorem req_authorization : Authorized step := by
  intro s r h
  constructor
  · intro hm
    unfold step at h
    by_cases hdoc : r.doc ∈ s.docs
    · simp only [dif_pos hdoc] at h
      by_cases huser : r.actor ∈ s.users
      · simp only [dif_pos huser] at h
        have h2 : r.kind = Kind.move := hm
        rw [h2] at h
        simp only at h
        by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true
        · exact hall
        · simp [hall] at h
      · simp only [dif_neg huser] at h
        simp at h
    · simp only [dif_neg hdoc] at h
      simp at h
  · intro he
    unfold step at h
    by_cases hdoc : r.doc ∈ s.docs
    · simp only [dif_pos hdoc] at h
      by_cases huser : r.actor ∈ s.users
      · simp only [dif_pos huser] at h
        have h2 : r.kind = Kind.edit := he
        rw [h2] at h
        simp only at h
        by_cases hauth : s.role r.actor == Role.author
        · simp only [hauth] at h
          by_cases hdraft : s.status r.doc == Status.draft
          · simp only [hdraft] at h
            simp at h
            have h1 : s.role r.actor = Role.author := by
              simp only [beq_iff_eq] at hauth
              exact hauth
            have h2a : s.status r.doc = Status.draft := by
              simp only [beq_iff_eq] at hdraft
              exact hdraft
            exact ⟨h1, h2a⟩
          · simp only [hdraft] at h
            simp at h
        · simp only [hauth] at h
          simp at h
      · simp only [dif_neg huser] at h
        simp at h
    · simp only [dif_neg hdoc] at h
      simp at h

theorem req_single_doc : SingleDoc step := by
  intro s r h d hne
  unfold step at h
  by_cases hdoc : r.doc ∈ s.docs
  · simp only [dif_pos hdoc] at h
    by_cases huser : r.actor ∈ s.users
    · simp only [dif_pos huser] at h
      cases hk : r.kind
      · simp only [hk] at h
        by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst
        · simp only [hall] at h
          have hpair : (step s r).2 = doMove s r := by
            unfold step
            simp [hdoc, huser, hk, hall]
          rw [hpair]
          unfold doMove
          have hfalse : (d == r.doc) = false := by
            simp [hne]
          constructor
          · simp [hfalse]
          · simp
        · simp only [hall] at h; simp at h
      · simp only [hk] at h
        by_cases ha : s.role r.actor == Role.author && s.status r.doc == Status.draft
        · simp only [ha] at h
          have hpair : (step s r).2 = doEdit s r := by
            unfold step
            simp [hdoc, huser, hk, ha]
          rw [hpair]
          unfold doEdit
          constructor
          · simp
          · simp [hne]
        · simp only [ha] at h; simp at h
    · simp only [dif_neg huser] at h; simp at h
  · simp only [dif_neg hdoc] at h; simp at h

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d h
  unfold step
  by_cases hdoc : r.doc ∈ s.docs
  · simp only [dif_pos hdoc]
    by_cases huser : r.actor ∈ s.users
    · simp only [dif_pos huser]
      cases hk : r.kind
      · by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true
        · simp only [hall, ite_true]
          show (doMove s r).content d = s.content d
          unfold doMove; simp
        · have hallF : allowed (s.role r.actor) (s.status r.doc) r.dst = false := by
            cases hv : allowed (s.role r.actor) (s.status r.doc) r.dst with
            | true => simp [hv] at hall
            | false => rfl
          simp only [hallF, Bool.false_eq_true, ite_false]
      · by_cases ha : (s.role r.actor == Role.author && s.status r.doc == Status.draft) = true
        · simp only [ha, ite_true]
          show (doEdit s r).content d = s.content d
          unfold doEdit
          simp only
          by_cases heq : d == r.doc
          · have heq2 : d = r.doc := by simpa [beq_iff_eq] using heq
            subst heq2
            rcases h with hpub | harch <;> simp_all
          · simp [heq]
        · simp only [ha, Bool.false_eq_true, ite_false]
    · simp only [dif_neg huser]
  · simp only [dif_neg hdoc]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    unfold step
    by_cases hdoc : r.doc ∈ s.docs
    · simp only [dif_pos hdoc]
      by_cases huser : r.actor ∈ s.users
      · simp only [dif_pos huser]
        cases hk : r.kind
        · by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst
          · simp only [hall]
            show (doMove s r).status d = .published ∨ (doMove s r).status d = .archived
            unfold doMove
            simp only
            by_cases heq : d == r.doc
            · have heq2 : d = r.doc := by simpa [beq_iff_eq] using heq
              subst heq2
              simp only [beq_self_eq_true, ↓reduceIte]
              have hall' : allowed (s.role r.actor) .published r.dst = true := by
                have : s.status r.doc = .published := hpub
                rw [this] at hall
                exact hall
              have hdst : r.dst = .archived := by
                cases hrole : s.role r.actor with
                | guest => simp [allowed, hrole] at hall'
                | author => simp [allowed, hrole] at hall'
                | reviewer => simp [allowed, hrole] at hall'
                | publisher =>
                  cases hdst : r.dst with
                  | draft => simp [allowed, hrole, hdst] at hall'
                  | review => simp [allowed, hrole, hdst] at hall'
                  | approved => simp [allowed, hrole, hdst] at hall'
                  | published => simp [allowed, hrole, hdst] at hall'
                  | archived => rfl
              rw [hdst]
              exact Or.inr rfl
            · simp [heq, hpub]
          · simp only [hall]
            simp [hpub]
        · by_cases ha : s.role r.actor == Role.author && s.status r.doc == Status.draft
          · simp only [ha]
            show (doEdit s r).status d = .published ∨ (doEdit s r).status d = .archived
            unfold doEdit
            simp [hpub]
          · simp only [ha]
            simp [hpub]
      · simp only [dif_neg huser]
        simp [hpub]
    · simp only [dif_neg hdoc]
      simp [hpub]
  · intro harch
    unfold step
    by_cases hdoc : r.doc ∈ s.docs
    · simp only [dif_pos hdoc]
      by_cases huser : r.actor ∈ s.users
      · simp only [dif_pos huser]
        cases hk : r.kind
        · by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst
          · simp only [hall]
            show (doMove s r).status d = .archived
            unfold doMove
            simp only
            by_cases heq : d == r.doc
            · have heq2 : d = r.doc := by simpa [beq_iff_eq] using heq
              subst heq2
              simp only [beq_self_eq_true, ↓reduceIte]
              have hall' : allowed (s.role r.actor) .archived r.dst = true := by
                have : s.status r.doc = .archived := harch
                rw [this] at hall
                exact hall
              cases hrole : s.role r.actor with
              | guest => simp [allowed, hrole] at hall'
              | author => simp [allowed, hrole] at hall'
              | reviewer => simp [allowed, hrole] at hall'
              | publisher => simp [allowed, hrole] at hall'
            · simp [heq, harch]
          · simp only [hall]
            simp [harch]
        · by_cases ha : s.role r.actor == Role.author && s.status r.doc == Status.draft
          · simp only [ha]
            show (doEdit s r).status d = .archived
            unfold doEdit
            simp [harch]
          · simp only [ha]
            simp [harch]
      · simp only [dif_neg huser]
        simp [harch]
    · simp only [dif_neg hdoc]
      simp [harch]

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h
  by_cases hdoc : r.doc ∈ s.docs
  · simp only [dif_pos hdoc] at h
    by_cases huser : r.actor ∈ s.users
    · simp only [dif_pos huser] at h
      cases hk : r.kind
      · simp only [hk] at h
        by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst
        · simp only [hall] at h
          have hpair : step s r = (.ok, doMove s r) := by
            unfold step
            simp [hdoc, huser, hk, hall]
          have h2eq : (step s r).2 = doMove s r := by rw [hpair]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · show (step s r).2.docs = s.docs
            rw [h2eq]; unfold doMove; simp
          · show (step s r).2.users = s.users
            rw [h2eq]; unfold doMove; simp
          · show (step s r).2.role = s.role
            rw [h2eq]; unfold doMove; simp
          · intro d
            show (step s r).2.status d = expectedStatus s r d
            rw [h2eq]
            unfold doMove
            unfold expectedStatus
            simp only [hk]
            by_cases heq : d = r.doc
            · simp [heq]
            · have hbeq : (d == r.doc) = false := by simp [heq]
              simp [heq, hbeq]
          · intro d
            show (step s r).2.content d = expectedContent s r d
            rw [h2eq]
            unfold doMove
            unfold expectedContent
            have hfalse : (r.kind = Kind.edit ∧ d = r.doc) = False := by simp [hk]
            simp [hfalse]
          · show (step s r).2.audit = expectedAudit s r
            rw [h2eq]
            unfold doMove
            unfold expectedAudit
            simp [hk]
        · simp only [hall] at h
          simp at h
      · simp only [hk] at h
        by_cases ha : s.role r.actor == Role.author && s.status r.doc == Status.draft
        · simp only [ha] at h
          have hpair : step s r = (.ok, doEdit s r) := by
            unfold step
            simp [hdoc, huser, hk, ha]
          have h2eq : (step s r).2 = doEdit s r := by rw [hpair]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · show (step s r).2.docs = s.docs
            rw [h2eq]; unfold doEdit; simp
          · show (step s r).2.users = s.users
            rw [h2eq]; unfold doEdit; simp
          · show (step s r).2.role = s.role
            rw [h2eq]; unfold doEdit; simp
          · intro d
            show (step s r).2.status d = expectedStatus s r d
            rw [h2eq]
            unfold doEdit
            unfold expectedStatus
            have hfalse : (r.kind = Kind.move ∧ d = r.doc) = False := by simp [hk]
            simp [hfalse]
          · intro d
            show (step s r).2.content d = expectedContent s r d
            rw [h2eq]
            unfold doEdit
            unfold expectedContent
            simp only [hk]
            by_cases heq : d = r.doc
            · have hbeq : (d == r.doc) = true := by simp [heq]
              simp [heq, hbeq]
            · have hbeq : (d == r.doc) = false := by simp [heq]
              simp [heq, hbeq]
          · show (step s r).2.audit = expectedAudit s r
            rw [h2eq]
            unfold doEdit
            unfold expectedAudit
            simp [hk]
        · simp only [ha] at h
          simp at h
    · simp only [dif_neg huser] at h; simp at h
  · simp only [dif_neg hdoc] at h; simp at h

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  unfold step
  by_cases hdoc : r.doc ∈ s.docs
  · simp only [dif_pos hdoc]
    by_cases huser : r.actor ∈ s.users
    · simp only [dif_pos huser]
      cases hk : r.kind
      case move =>
        by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst
        · simp only [hall]
          show s.audit <+: (doMove s r).audit
          unfold doMove
          simp
        · simp only [hall]
          simp
      case edit =>
        by_cases ha : s.role r.actor == Role.author && s.status r.doc == Status.draft
        · simp only [ha]
          show s.audit <+: (doEdit s r).audit
          unfold doEdit
          simp
        · simp only [ha]
          simp
    · simp only [dif_neg huser]
      simp
  · simp only [dif_neg hdoc]
    simp

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons d hd
  by_cases hdoc : r.doc ∈ s.docs
  · by_cases huser : r.actor ∈ s.users
    · cases hk : r.kind
      · by_cases hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true
        · have hstep : step s r = (.ok, doMove s r) := by
            unfold step; simp [hdoc, huser, hk, hall]
          have h2 : (step s r).2 = doMove s r := by rw [hstep]
          have hd2 : d ∈ s.docs := by
            have : (step s r).2.docs = s.docs := by rw [h2]; unfold doMove; simp
            rw [this] at hd; exact hd
          rw [h2]
          show replay (doMove s r).audit d .draft = (doMove s r).status d
          have ha : (doMove s r).audit = s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] := by unfold doMove; simp
          have hs : (doMove s r).status d = if d == r.doc then r.dst else s.status d := by unfold doMove; simp
          rw [ha, hs]
          have hrep : replay (s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }]) d .draft
            = if r.doc = d then r.dst else replay s.audit d .draft := by rw [replay_singleton_aux]
          rw [hrep]
          by_cases heq : d == r.doc
          · have heq2 : d = r.doc := by simpa [beq_iff_eq] using heq
            simp [heq2.symm]
          · have hne : r.doc ≠ d := by intro h; simp [h] at heq
            simp [hne, heq, hCons d hd2]
        · have hstep : step s r = (.rejected, s) := by
            unfold step; simp [hdoc, huser, hk, hall]
          have h2 : (step s r).2 = s := by rw [hstep]
          rw [h2] at hd ⊢
          exact hCons d hd
      · by_cases ha : (s.role r.actor == Role.author && s.status r.doc == Status.draft) = true
        · have hstep : step s r = (.ok, doEdit s r) := by
            unfold step; simp [hdoc, huser, hk, ha]
          have h2 : (step s r).2 = doEdit s r := by rw [hstep]
          have hd2 : d ∈ s.docs := by
            have : (step s r).2.docs = s.docs := by rw [h2]; unfold doEdit; simp
            rw [this] at hd; exact hd
          rw [h2]
          show replay (doEdit s r).audit d .draft = (doEdit s r).status d
          have ha2 : (doEdit s r).audit = s.audit := by unfold doEdit; simp
          have hs2 : (doEdit s r).status d = s.status d := by unfold doEdit; simp
          rw [ha2, hs2]
          exact hCons d hd2
        · have hstep : step s r = (.rejected, s) := by
            unfold step; simp [hdoc, huser, hk, ha]
          have h2 : (step s r).2 = s := by rw [hstep]
          rw [h2] at hd ⊢
          exact hCons d hd
    · have hstep : step s r = (.rejected, s) := by
        unfold step; simp [hdoc, huser]
      have h2 : (step s r).2 = s := by rw [hstep]
      rw [h2] at hd ⊢
      exact hCons d hd
  · have hstep : step s r = (.rejected, s) := by
      unfold step; simp [hdoc]
    have h2 : (step s r).2 = s := by rw [hstep]
    rw [h2] at hd ⊢
    exact hCons d hd

end Workflow
