import Workflow.Spec
namespace Workflow

def doMove (s : State) (r : Request) : State :=
  { s with status := fun d => if d == r.doc then r.dst else s.status d,
           audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] }

def doEdit (s : State) (r : Request) : State :=
  { s with content := fun d => if d == r.doc then r.body else s.content d }

def step : Impl := fun s r =>
  if h1 : r.doc ∈ s.docs ∧ r.actor ∈ s.users then
    match h2 : r.kind with
    | .move =>
        if h3 : allowed (s.role r.actor) (s.status r.doc) r.dst = true then
          (.ok, doMove s r)
        else
          (.rejected, s)
    | .edit =>
        if h3 : s.role r.actor = .author ∧ s.status r.doc = .draft then
          (.ok, doEdit s r)
        else
          (.rejected, s)
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r ⟨hd, hu, hm, he⟩
  simp only [step]
  have htrue : r.doc ∈ s.docs ∧ r.actor ∈ s.users := ⟨hd, hu⟩
  rw [dif_pos htrue]
  by_cases hk : r.kind = .move
  · have hall : allowed (s.role r.actor) (s.status r.doc) r.dst = true := hm hk
    rw [hk]
    simp [hall]
  · have hk2 : r.kind = .edit := by cases h : r.kind <;> simp_all
    have hall : s.role r.actor = Role.author ∧ s.status r.doc = Status.draft := he hk2
    rw [hk2]
    simp [hall]

theorem req_invalid_noop         : InvalidNoop step := sorry

theorem req_authorization : Authorized step := by
  intro s r hok
  simp only [step] at hok
  by_cases hmem : r.doc ∈ s.docs ∧ r.actor ∈ s.users
  · rw [dif_pos hmem] at hok
    split at hok
    · next heq =>
      -- heq : r.kind = move
      split at hok
      · next hall =>
        constructor
        · intro _; exact hall
        · intro he; simp_all
      · next hall => simp at hok
    · next heq =>
      split at hok
      · next hauth =>
        constructor
        · intro hm; simp_all
        · intro _; exact hauth
      · next hauth => simp at hok
  · rw [dif_neg hmem] at hok
    simp at hok

theorem req_single_doc           : SingleDoc step := sorry

theorem req_published_immutable : PublishedImmutable step := by
  intro s r d h
  simp only [step, doMove, doEdit]
  split
  next hmem =>
    split
    next hall =>
      split
      next hallowed => simp
      next hallowed => rfl
    next hall =>
      split
      next hauth =>
        simp only
        by_cases hdeq : d = r.doc
        · rw [hdeq] at h
          have hdraft : s.status r.doc = .draft := hauth.2
          rw [hdraft] at h
          simp at h
        · have hbeq : (d == r.doc) = false := by
            simp [hdeq]
          simp [hbeq]
      next hauth => rfl
  next hmem => rfl

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    unfold step doMove doEdit
    split
    next hmem =>
      split
      next hmove =>
        split
        next hall =>
          show (if d == r.doc then r.dst else s.status d) = .published ∨ (if d == r.doc then r.dst else s.status d) = .archived
          by_cases hdd : d = r.doc
          · subst hdd
            have hpub2 : s.status r.doc = .published := hpub
            rw [hpub2] at hall
            have hdst : r.dst = Status.archived := by
              cases hr : s.role r.actor <;> cases hd : r.dst <;> simp_all [allowed]
            rw [hdst]
            simp
          · have hbeq : (d == r.doc) = false := by simp [hdd]
            simp [hbeq, hpub]
        · simp only; simp [hpub]
      next hmove =>
        split
        next hauth => simp only; simp [hpub]
        next hauth => simp only; simp [hpub]
    · simp [hpub]
  · intro harch
    unfold step doMove doEdit
    split
    next hmem =>
      split
      next hmove =>
        split
        next hall =>
          show (if d == r.doc then r.dst else s.status d) = Status.archived
          by_cases hdd : d = r.doc
          · subst hdd
            have harch2 : s.status r.doc = .archived := harch
            rw [harch2] at hall
            have hfalse : False := by
              cases hr : s.role r.actor <;> cases hd : r.dst <;> simp_all [allowed]
            exact False.elim hfalse
          · have hbeq : (d == r.doc) = false := by simp [hdd]
            simp [hbeq, harch]
        · simp [harch]
      next hmove =>
        split
        next hauth => simp [harch]
        next hauth => simp [harch]
    · simp [harch]

theorem req_effects              : Effects step := sorry

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  unfold step doMove doEdit
  split
  next hmem =>
    split
    next hmove =>
      split
      · next hallow =>
        simp only
        apply List.prefix_append
      · next hallow =>
        simp only
        exact List.prefix_rfl
    next hmove =>
      split
      · next hauth =>
        simp only
        exact List.prefix_rfl
      · next hauth =>
        simp only
        exact List.prefix_rfl
  · simp only
    exact List.prefix_rfl

theorem req_audit_consistent     : KeepsAuditConsistent step := sorry

end Workflow
