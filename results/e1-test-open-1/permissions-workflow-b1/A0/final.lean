import Workflow.Spec

namespace Workflow

instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest
  infer_instance

def successState (s : State) (r : Request) : State :=
  { docs := s.docs
    , users := s.users
    , status := fun d => expectedStatus s r d
    , content := fun d => expectedContent s r d
    , role := s.role
    , audit := expectedAudit s r
  }

def step : Impl := fun s r =>
  if _h : ValidRequest s r then
    (.ok, successState s r)
  else
    (.rejected, s)

theorem step_ok_of_valid_aux {s : State} {r : Request} (h : ValidRequest s r) : (step s r).1 = .ok := by
  unfold step
  simp [h]

theorem step_rejected_of_invalid_aux {s : State} {r : Request} (h : ¬ ValidRequest s r) : step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem step_eq_success_of_valid_aux {s : State} {r : Request} (h : ValidRequest s r) : step s r = (.ok, successState s r) := by
  unfold step
  simp [h]

theorem valid_of_ok_aux {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidRequest s r := by
  unfold step at h
  by_cases hv : ValidRequest s r
  · exact hv
  · simp [hv] at h

theorem state_of_ok_aux {s : State} {r : Request} (h : (step s r).1 = .ok) : (step s r).2 = successState s r := by
  have hv : ValidRequest s r := valid_of_ok_aux h
  have heq : step s r = (.ok, successState s r) := step_eq_success_of_valid_aux hv
  have h1 : (step s r).2 = (Prod.mk (.ok : Outcome) (successState s r)).2 := by rw [heq]
  simp at h1
  exact h1

theorem state_of_invalid_aux {s : State} {r : Request} (h : ¬ ValidRequest s r) : (step s r).2 = s := by
  rw [step_rejected_of_invalid_aux h]

theorem replay_append_aux : ∀ (l₁ l₂ : List Entry) (d : DocId) (st : Status),
  replay (l₁ ++ l₂) d st = replay l₂ d (replay l₁ d st)
  | [], _, _, _ => by simp [replay]
  | e :: es, l₂, d, st => by simp [replay, replay_append_aux es l₂]

theorem allowed_published_true_aux (role : Role) (dst : Status) :
  allowed role .published dst = true → dst = .archived := by
  intro h
  cases role <;> cases dst <;> first | rfl | simp [allowed] at h

theorem allowed_archived_false_aux (role : Role) (dst : Status) :
  allowed role .archived dst = false := by
  cases role <;> cases dst <;> rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  exact step_ok_of_valid_aux h

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  exact step_rejected_of_invalid_aux h

theorem req_authorization : Authorized step := by
  unfold Authorized
  intro s r hok
  have hv : ValidRequest s r := valid_of_ok_aux (s:=s) (r:=r) hok
  unfold ValidRequest at hv
  obtain ⟨_, _, hmove, hedit⟩ := hv
  constructor
  · intro hm; exact hmove hm
  · intro he; exact hedit he

theorem req_single_doc : SingleDoc step := by
  unfold SingleDoc
  intro s r hok d hd
  have hst : (step s r).2 = successState s r := state_of_ok_aux hok
  rw [hst]
  unfold successState expectedStatus expectedContent
  have h1 : ¬ (r.kind = .move ∧ d = r.doc) := by intro h; exact hd h.2
  have h2 : ¬ (r.kind = .edit ∧ d = r.doc) := by intro h; exact hd h.2
  simp [h1, h2]

theorem req_published_immutable : PublishedImmutable step := by
  unfold PublishedImmutable
  intro s r d hp
  by_cases hv : ValidRequest s r
  · have hst : (step s r).2 = successState s r := state_of_ok_aux (s:=s) (r:=r) (step_ok_of_valid_aux hv)
    rw [hst]
    unfold successState expectedContent
    simp only
    by_cases heq : r.kind = .edit ∧ d = r.doc
    · obtain ⟨hk, hd_eq⟩ := heq
      have hd' : r.doc = d := hd_eq.symm
      rw [← hd'] at hp
      unfold ValidRequest at hv
      obtain ⟨_, _, _, hedit⟩ := hv
      have h2 := hedit hk
      rw [h2.2] at hp
      simp at hp
    · simp [heq]
  · rw [state_of_invalid_aux hv]

theorem req_no_unpublish : NoUnpublish step := by
  unfold NoUnpublish
  intro s r d
  constructor
  · intro hpub
    by_cases hv : ValidRequest s r
    · have hst : (step s r).2 = successState s r := state_of_ok_aux (s:=s) (r:=r) (step_ok_of_valid_aux hv)
      rw [hst]
      unfold successState expectedStatus
      show (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = .published ∨
           (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = .archived
      by_cases heq : r.kind = .move ∧ d = r.doc
      · have hpub2 : s.status r.doc = .published := by
          have hdr : d = r.doc := heq.2
          rw [hdr] at hpub
          exact hpub
        have hmove : r.kind = .move := heq.1
        unfold ValidRequest at hv
        obtain ⟨_, _, hmoveAllowed, _⟩ := hv
        have hall := hmoveAllowed hmove
        rw [hpub2] at hall
        have hd_eq2 := allowed_published_true_aux _ _ hall
        rw [if_pos heq, hd_eq2]
        right; rfl
      · rw [if_neg heq, hpub]; left; rfl
    · rw [state_of_invalid_aux hv, hpub]; left; rfl
  · intro harch
    by_cases hv : ValidRequest s r
    · have hst : (step s r).2 = successState s r := state_of_ok_aux (s:=s) (r:=r) (step_ok_of_valid_aux hv)
      rw [hst]
      unfold successState expectedStatus
      show (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = .archived
      by_cases heq : r.kind = .move ∧ d = r.doc
      · have harch2 : s.status r.doc = .archived := by
          have hdr : d = r.doc := heq.2
          rw [hdr] at harch
          exact harch
        have hmove : r.kind = .move := heq.1
        unfold ValidRequest at hv
        obtain ⟨_, _, hmoveAllowed, _⟩ := hv
        have hall := hmoveAllowed hmove
        rw [harch2] at hall
        have hall' := allowed_archived_false_aux (s.role r.actor) r.dst
        rw [hall'] at hall
        simp at hall
      · rw [if_neg heq, harch]
    · rw [state_of_invalid_aux hv, harch]

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hok
  have hst : (step s r).2 = successState s r := state_of_ok_aux hok
  rw [hst]
  unfold successState
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro d; rfl
  · intro d; rfl

theorem req_audit_append_only : AuditAppendOnly step := by
  unfold AuditAppendOnly
  intro s r
  by_cases hv : ValidRequest s r
  · have hst : (step s r).2 = successState s r := state_of_ok_aux (s:=s) (r:=r) (step_ok_of_valid_aux hv)
    rw [hst]
    unfold successState
    unfold expectedAudit
    by_cases hk : r.kind = .move
    · simp only [hk, ite_true]
      exact List.prefix_append _ _
    · simp only [hk, ite_false]
      exact List.prefix_refl _
  · rw [state_of_invalid_aux hv]
    exact List.prefix_refl _

theorem req_audit_consistent : KeepsAuditConsistent step := by
  unfold KeepsAuditConsistent AuditConsistent
  intro s r hcons
  by_cases hv : ValidRequest s r
  · have hst : (step s r).2 = successState s r := state_of_ok_aux (s:=s) (r:=r) (step_ok_of_valid_aux hv)
    rw [hst]
    unfold successState
    intro d hd
    show replay (expectedAudit s r) d .draft = expectedStatus s r d
    unfold expectedAudit expectedStatus
    by_cases hk : r.kind = .move
    · simp only [hk, ite_true]
      have h1 : replay (s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }]) d .draft
                = replay [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] d (replay s.audit d .draft) :=
        replay_append_aux _ _ _ _
      rw [h1]
      have hrep : replay s.audit d .draft = s.status d := hcons d hd
      rw [hrep]
      show replay [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] d (s.status d) =
           (if True ∧ d = r.doc then r.dst else s.status d)
      -- evaluate singleton: definitionally replay [e] d st = if e.doc = d then e.dst else st
      have hsingleton : replay [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] d (s.status d)
        = (if r.doc = d then r.dst else s.status d) := rfl
      rw [hsingleton]
      by_cases heq : d = r.doc
      · have heq' : r.doc = d := heq.symm
        have hp : True ∧ d = r.doc := ⟨trivial, heq⟩
        rw [if_pos hp, if_pos heq']
      · have hn : ¬ (True ∧ d = r.doc) := by intro h; exact heq h.2
        have hn' : ¬ (r.doc = d) := by intro h; exact heq h.symm
        rw [if_neg hn, if_neg hn']
    · simp only [hk, ite_false]
      have hrhs : (if False ∧ d = r.doc then r.dst else s.status d) = s.status d := by
        have hn : ¬ (False ∧ d = r.doc) := by intro h; exact h.1
        rw [if_neg hn]
      rw [hrhs]
      exact hcons d hd
  · rw [state_of_invalid_aux hv]
    intro d hd
    exact hcons d hd

end Workflow
