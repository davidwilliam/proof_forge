import Workflow.Spec
namespace Workflow
instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance
def edges : List (Role × Status × Status) :=
  [(.author, .draft, .review), (.author, .draft, .archived), (.author, .review, .draft),
   (.reviewer, .review, .approved), (.reviewer, .review, .draft),
   (.publisher, .approved, .published), (.publisher, .approved, .draft),
   (.publisher, .published, .archived)]

def mayMove (s : State) (r : Request) : Bool :=
  edges.contains (s.role r.actor, s.status r.doc, r.dst)

def mayEdit (s : State) (r : Request) : Bool :=
  s.role r.actor == .author && s.status r.doc == .draft

def doMove (s : State) (r : Request) : State :=
  { s with status := fun d => if d == r.doc then r.dst else s.status d,
           audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] }

def doEdit (s : State) (r : Request) : State :=
  { s with content := fun d => if d == r.doc then r.body else s.content d }

def step : Impl := fun s r =>
  if s.docs.contains r.doc && s.users.contains r.actor then
    match r.kind with
    | .move => if mayMove s r then (.ok, doMove s r) else (.rejected, s)
    | .edit => if mayEdit s r then (.ok, doEdit s r) else (.rejected, s)
  else (.rejected, s)

theorem replayAppend2 (audit : List Entry) (e : Entry) (d : DocId) (st : Status) :
  replay (audit ++ [e]) d st = if e.doc = d then e.dst else replay audit d st := by
  induction audit generalizing st with
  | nil => simp [replay]
  | cons hd tl ih =>
    simp [replay, ih]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hdoc : r.doc ∈ s.docs := h.1
  have huser : r.actor ∈ s.users := h.2.1
  have hmove := h.2.2.1
  have hedit := h.2.2.2
  show (step s r).1 = .ok
  unfold step
  simp [hdoc, huser]
  cases hk : r.kind with
  | move =>
    have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hmove hk
    have hc : mayMove s r = true := by
      unfold mayMove allowed at *
      unfold edges at *
      cases hr : s.role r.actor <;> cases hs : s.status r.doc <;> cases hd : r.dst <;> simp_all
    simp [hk, hc]
  | edit =>
    have he := hedit hk
    have hc : mayEdit s r = true := by unfold mayEdit; simp [he.1, he.2]
    simp [hk, hc]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold ValidRequest at h
  unfold step
  by_cases hdoc : r.doc ∈ s.docs
  · by_cases huser : r.actor ∈ s.users
    · simp [show r.doc ∈ s.docs ∧ r.actor ∈ s.users from ⟨hdoc,huser⟩]
      cases hk : r.kind
      · have hall : allowed (s.role r.actor) (s.status r.doc) r.dst ≠ true := by
          intro hc
          apply h
          refine ⟨hdoc, huser, ?_, ?_⟩
          · intro _; exact hc
          · intro he; simp [hk] at he
        have hm : mayMove s r = false := by
          unfold mayMove allowed edges at *
          cases hr : s.role r.actor <;> cases hs : s.status r.doc <;> cases hd : r.dst <;> simp_all
        simp [hk, hm]
      · have hall : ¬ (s.role r.actor = .author ∧ s.status r.doc = .draft) := by
          intro hc
          apply h
          refine ⟨hdoc, huser, ?_, ?_⟩
          · intro hm; simp [hk] at hm
          · intro _; exact hc
        have hm : mayEdit s r = false := by
          unfold mayEdit
          simp
          intro ha hb
          exact hall ⟨ha, hb⟩
        simp [hk, hm]
    · have hmem : ¬ (r.doc ∈ s.docs ∧ r.actor ∈ s.users) := by
        intro ⟨_, hu⟩; exact huser hu
      simp [hmem]
  · have hmem : ¬ (r.doc ∈ s.docs ∧ r.actor ∈ s.users) := by
      intro ⟨hd, _⟩; exact hdoc hd
    simp [hmem]

theorem req_authorization : Authorized step := by
  intro s r hok
  unfold step at hok
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · simp [hmem] at hok
    cases hk : r.kind
    · simp [hk] at hok
      have hm : mayMove s r = true := by
        cases hc : mayMove s r
        · simp [hc] at hok
        · rfl
      constructor
      · intro _
        unfold mayMove at hm
        unfold allowed
        cases hr : s.role r.actor <;> cases hs : s.status r.doc <;> cases hd : r.dst <;> simp_all [edges]
      · intro he; simp [hk] at he
    · simp [hk] at hok
      have hm : mayEdit s r = true := by
        cases hc : mayEdit s r
        · simp [hc] at hok
        · rfl
      constructor
      · intro hm2; simp [hk] at hm2
      · intro _
        unfold mayEdit at hm
        simp at hm
        have hra : s.role r.actor = .author := by
          cases hr : s.role r.actor <;> simp_all
        have hsd : s.status r.doc = .draft := by
          cases hs : s.status r.doc <;> simp_all
        exact ⟨hra, hsd⟩
  · simp [hmem] at hok

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  unfold step at hok ⊢
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · simp [hmem] at hok ⊢
    cases hk : r.kind
    · simp [hk] at hok ⊢
      cases hm : mayMove s r
      · simp [hm] at hok
      · simp [hm] at hok ⊢
        constructor
        · show (doMove s r).status d = s.status d; simp [doMove, beq_iff_eq, hne]
        · show (doMove s r).content d = s.content d; simp [doMove]
    · simp [hk] at hok ⊢
      cases hm : mayEdit s r
      · simp [hm] at hok
      · simp [hm] at hok ⊢
        constructor
        · show (doEdit s r).status d = s.status d; simp [doEdit]
        · show (doEdit s r).content d = s.content d; simp [doEdit, beq_iff_eq, hne]
  · simp [hmem] at hok

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d hd
  unfold step
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · simp [hmem]
    cases hk : r.kind
    · simp [hk]
      cases hm : mayMove s r
      · simp [hm]
      · simp [hm, doMove]
    · simp [hk]
      cases hm : mayEdit s r
      · simp [hm]
      · simp [hm]
        have hmd : mayEdit s r = true := hm
        unfold mayEdit at hmd
        simp at hmd
        have hsd : s.status r.doc = .draft := by
          cases hs : s.status r.doc <;> simp_all
        by_cases heq : d = r.doc
        · subst heq
          simp_all
        · simp [doEdit, beq_iff_eq, heq]
  · simp [hmem]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    show (step s r).2.status d = .published ∨ (step s r).2.status d = .archived
    unfold step
    by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
    · simp [hmem]
      cases hk : r.kind
      · simp [hk]
        by_cases hm : mayMove s r = true
        · simp only [hm, ↓reduceIte, doMove]
          -- now goal is (fun d => if d == r.doc then r.dst else s.status d) d ...
          simp only [beq_iff_eq]
          by_cases heq : d = r.doc
          · subst heq
            have hm2 : edges.contains (s.role r.actor, s.status r.doc, r.dst) = true := by
              unfold mayMove at hm; exact hm
            rw [hpub] at hm2
            unfold edges at hm2
            cases hr : s.role r.actor <;> cases hd : r.dst <;> simp_all
          · simp [heq, hpub]
        · have hmF : mayMove s r = false := by cases hc : mayMove s r <;> simp_all
          simp [hmF, hpub]
      · simp [hk]
        by_cases hm : mayEdit s r = true
        · simp [hm, doEdit, hpub]
        · have hmF : mayEdit s r = false := by cases hc : mayEdit s r <;> simp_all
          simp [hmF, hpub]
    · simp [hmem, hpub]
  · intro harc
    show (step s r).2.status d = .archived
    unfold step
    by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
    · simp [hmem]
      cases hk : r.kind
      · simp [hk]
        by_cases hm : mayMove s r = true
        · simp only [hm, ↓reduceIte, doMove]
          simp only [beq_iff_eq]
          by_cases heq : d = r.doc
          · subst heq
            have hm2 : edges.contains (s.role r.actor, s.status r.doc, r.dst) = true := by
              unfold mayMove at hm; exact hm
            rw [harc] at hm2
            unfold edges at hm2
            cases hr : s.role r.actor <;> cases hd : r.dst <;> simp_all
          · simp [heq, harc]
        · have hmF : mayMove s r = false := by cases hc : mayMove s r <;> simp_all
          simp [hmF, harc]
      · simp [hk]
        by_cases hm : mayEdit s r = true
        · simp [hm, doEdit, harc]
        · have hmF : mayEdit s r = false := by cases hc : mayEdit s r <;> simp_all
          simp [hmF, harc]
    · simp [hmem, harc]

theorem req_effects : Effects step := by
  intro s r hok
  have hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users := by
    unfold step at hok
    by_cases h : r.doc ∈ s.docs ∧ r.actor ∈ s.users
    · exact h
    · simp [h] at hok
  unfold step at hok ⊢
  simp [hmem] at hok ⊢
  cases hk : r.kind
  · simp [hk] at hok ⊢
    have hm : mayMove s r = true := by
      by_cases hc : mayMove s r = true
      · exact hc
      · have : mayMove s r = false := by cases hc2 : mayMove s r <;> simp_all
        simp [this] at hok
    simp [hm] at hok ⊢
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro d; simp only [doMove, expectedStatus, hk, beq_iff_eq]; by_cases heq : d = r.doc <;> simp [heq]
    · intro d; simp [doMove, expectedContent, hk]
    · simp [doMove, expectedAudit, hk]
  · simp [hk] at hok ⊢
    have hm : mayEdit s r = true := by
      by_cases hc : mayEdit s r = true
      · exact hc
      · have : mayEdit s r = false := by cases hc2 : mayEdit s r <;> simp_all
        simp [this] at hok
    simp [hm] at hok ⊢
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro d; simp [doEdit, expectedStatus, hk]
    · intro d; simp only [doEdit, expectedContent, hk, beq_iff_eq]; by_cases heq : d = r.doc <;> simp [heq]
    · simp [doEdit, expectedAudit, hk]

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  show s.audit <+: (step s r).2.audit
  unfold step
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · simp [hmem]
    cases hk : r.kind
    · cases hm : mayMove s r <;> simp [hk, hm]
      unfold doMove; simp
    · cases hm : mayEdit s r <;> simp [hk, hm]
      unfold doEdit; simp
  · simp [hmem]

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons d hd
  unfold step at hd ⊢
  by_cases hb : s.docs.contains r.doc && s.users.contains r.actor
  · simp only [hb, ↓reduceIte] at hd ⊢
    cases hk : r.kind
    · simp only [hk] at hd ⊢
      by_cases hm : mayMove s r
      · simp only [hm, ↓reduceIte, doMove] at hd ⊢
        have hrep : replay (s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }]) d .draft
            = if r.doc = d then r.dst else replay s.audit d .draft := replayAppend2 _ _ _ _
        by_cases heq : r.doc = d
        · have heq2 : d == r.doc := by simp [beq_iff_eq, heq]
          have h1 : r.doc = d := heq
          rw [hrep, if_pos h1]
          simp [heq2]
        · have heq2 : ¬ (d == r.doc) := by simp [beq_iff_eq]; intro h; exact heq h.symm
          rw [hrep, if_neg heq]
          simp [heq2, hCons d hd]
      · simp only [hm, ↓reduceIte] at hd ⊢
        exact hCons d hd
    · simp only [hk] at hd ⊢
      by_cases hm : mayEdit s r
      · simp only [hm, ↓reduceIte, doEdit] at hd ⊢
        exact hCons d hd
      · simp only [hm, ↓reduceIte] at hd ⊢
        exact hCons d hd
  · simp only [hb, ↓reduceIte] at hd ⊢
    exact hCons d hd

end Workflow
