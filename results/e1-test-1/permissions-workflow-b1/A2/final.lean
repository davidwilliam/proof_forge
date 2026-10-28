import Workflow.Spec
namespace Workflow
instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance

def step : Impl := fun s r =>
  if ValidRequest s r then
    (.ok, { docs := s.docs, users := s.users,
            status := fun d => expectedStatus s r d,
            content := fun d => expectedContent s r d,
            role := s.role,
            audit := expectedAudit s r })
  else (.rejected, s)

theorem req_single_doc_aux : True := trivial
#check @SingleDoc

theorem req_no_unpublish_aux_test : True := trivial
#check @allowed

theorem allow_test1 : allowed .publisher .published .archived = true := by rfl

theorem allow_test2 : allowed .publisher .published .draft = false := by rfl

theorem allow_test3 : allowed .publisher .published .published = false := by rfl

theorem pub_helper : ∀ dst, allowed .publisher .published dst = true → dst = .archived := by
  intro dst h
  cases dst
  · simp [allowed] at h
  · simp [allowed] at h
  · simp [allowed] at h
  · simp [allowed] at h
  · rfl

theorem pub_src_helper2 : ∀ (rl : Role) (dst : Status), allowed rl .published dst = true → dst = .archived := by
  intro rl dst h
  cases rl <;> cases dst <;> simp_all [allowed]

theorem arch_src_helper2 : ∀ (rl : Role) (dst : Status), allowed rl .archived dst = true → False := by
  intro rl dst h
  cases rl <;> cases dst <;> simp_all [allowed]

theorem replay_nil_test (d : DocId) (st : Status) : replay [] d st = st := by simp [replay]

theorem replay_cons_test (e : Entry) (es : List Entry) (d : DocId) (st : Status) : replay (e :: es) d st = replay es d (if e.doc = d then e.dst else st) := by simp [replay]

theorem replay_singleton_aux (e : Entry) (d : DocId) (st : Status) : replay [e] d st = (if e.doc = d then e.dst else st) := by simp [replay]

theorem replay_append_single_aux : ∀ (l : List Entry) (e : Entry) (d : DocId) (st : Status), replay (l ++ [e]) d st = (if e.doc = d then e.dst else replay l d st) := by
  intro l
  induction l with
  | nil => intro e d st; simp [replay]
  | cons hd tl ih => intro e d st; simp only [List.cons_append]; rw [replay_cons_test, replay_cons_test, ih]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : Authorized step := by
  intro s r hOk
  by_cases hV : ValidRequest s r
  · obtain ⟨a, b, c, d⟩ := hV
    exact ⟨c, d⟩
  · have hEq : (step s r).1 = Outcome.rejected := by
      unfold step
      simp [hV]
    rw [hEq] at hOk
    contradiction

theorem req_single_doc : SingleDoc step := by
  intro s r hOk d hne
  have hV : ValidRequest s r := by
    by_cases hN : ValidRequest s r
    · exact hN
    · have hEq : (step s r).1 = Outcome.rejected := by
        unfold step
        simp [hN]
      rw [hEq] at hOk
      contradiction
  have hSt : (step s r).2.status d = expectedStatus s r d := by
    unfold step
    simp [hV]
  have hCo : (step s r).2.content d = expectedContent s r d := by
    unfold step
    simp [hV]
  constructor
  · rw [hSt]
    unfold expectedStatus
    simp [hne]
  · rw [hCo]
    unfold expectedContent
    simp [hne]

theorem req_published_immutable  : PublishedImmutable step := by
  intro s r d hStat
  unfold step
  by_cases hV : ValidRequest s r
  · simp only [hV, ↓reduceIte]
    unfold expectedContent
    by_cases hE : r.kind = .edit ∧ d = r.doc
    · obtain ⟨hk, hdd⟩ := hE
      obtain ⟨_, _, _, hEdit⟩ := hV
      have hAuth := hEdit hk
      have hDraft : s.status d = Status.draft := by rw [hdd]; exact hAuth.2
      rcases hStat with hP | hA
      · rw [hDraft] at hP; cases hP
      · rw [hDraft] at hA; cases hA
    · simp [hE]
  · simp [hV]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hP
    by_cases hV : ValidRequest s r
    · have hSt : (step s r).2.status d = expectedStatus s r d := by
        unfold step; simp [hV]
      rw [hSt]
      unfold expectedStatus
      by_cases hE : r.kind = .move ∧ d = r.doc
      · have hk : r.kind = .move := hE.1
        have hdd : d = r.doc := hE.2
        have hExp : (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = r.dst := by simp [hE]
        rw [hExp]
        obtain ⟨_, _, hMove, _⟩ := hV
        have hAllow := hMove hk
        have hSrc : s.status r.doc = .published := by rw [← hdd]; exact hP
        rw [hSrc] at hAllow
        have hDst := pub_src_helper2 _ _ hAllow
        rw [hDst]; exact Or.inr rfl
      · have hExp : (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = s.status d := by simp [hE]
        rw [hExp, hP]
        exact Or.inl rfl
    · have hSt : (step s r).2.status d = s.status d := by
        unfold step; simp [hV]
      rw [hSt, hP]
      exact Or.inl rfl
  · intro hA
    by_cases hV : ValidRequest s r
    · have hSt : (step s r).2.status d = expectedStatus s r d := by
        unfold step; simp [hV]
      rw [hSt]
      unfold expectedStatus
      by_cases hE : r.kind = .move ∧ d = r.doc
      · have hk : r.kind = .move := hE.1
        have hdd : d = r.doc := hE.2
        obtain ⟨_, _, hMove, _⟩ := hV
        have hAllow := hMove hk
        have hSrc : s.status r.doc = .archived := by rw [← hdd]; exact hA
        rw [hSrc] at hAllow
        exact absurd hAllow (by intro hh; have := arch_src_helper2 _ _ hh; exact this)
      · have hExp : (if r.kind = .move ∧ d = r.doc then r.dst else s.status d) = s.status d := by simp [hE]
        rw [hExp, hA]
    · have hSt : (step s r).2.status d = s.status d := by
        unfold step; simp [hV]
      rw [hSt, hA]

theorem req_effects : Effects step := by
  intro s r hOk
  by_cases hV : ValidRequest s r
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold step; simp [hV]
    · unfold step; simp [hV]
    · unfold step; simp [hV]
    · intro d; unfold step; simp [hV]
    · intro d; unfold step; simp [hV]
    · unfold step; simp [hV]
  · have hEq : (step s r).1 = Outcome.rejected := by unfold step; simp [hV]
    rw [hEq] at hOk
    contradiction

theorem req_audit_append_only : AuditAppendOnly step := by
  intro s r
  unfold step
  by_cases hV : ValidRequest s r
  · simp only [hV, ↓reduceIte]
    unfold expectedAudit
    by_cases hM : r.kind = Kind.move
    · simp only [hM, ↓reduceIte]
      exact ⟨[_], rfl⟩
    · simp only [hM, ↓reduceIte]
      exact ⟨[], by simp⟩
  · simp only [hV, ↓reduceIte]
    exact ⟨[], by simp⟩

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hCons d hd
  by_cases hV : ValidRequest s r
  · have hDocs : (step s r).2.docs = s.docs := by unfold step; simp [hV]
    have hStat : ∀ dd, (step s r).2.status dd = expectedStatus s r dd := by intro dd; unfold step; simp [hV]
    have hAud : (step s r).2.audit = expectedAudit s r := by unfold step; simp [hV]
    rw [hStat, hAud]
    have hd' : d ∈ s.docs := hDocs ▸ hd
    have hBase : replay s.audit d .draft = s.status d := hCons d hd'
    have hExpA : expectedAudit s r = (if r.kind = Kind.move then s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] else s.audit) := by
      unfold expectedAudit; rfl
    by_cases hM : r.kind = Kind.move
    · rw [hExpA, if_pos hM, replay_append_single_aux]
      show (if r.doc = d then r.dst else replay s.audit d .draft) = expectedStatus s r d
      unfold expectedStatus
      by_cases hEq : d = r.doc
      · have h1p : r.doc = d := Eq.symm hEq
        rw [if_pos h1p, if_pos ⟨hM, hEq⟩]
      · have h1 : ¬ (r.doc = d) := fun hh => hEq hh.symm
        have h2n : ¬ (r.kind = Kind.move ∧ d = r.doc) := fun hh => hEq hh.2
        rw [if_neg h1, if_neg h2n]
        exact hBase
    · rw [hExpA, if_neg hM]
      show replay s.audit d .draft = expectedStatus s r d
      unfold expectedStatus
      have hAnd : ¬ (r.kind = Kind.move ∧ d = r.doc) := fun hh => hM hh.1
      rw [if_neg hAnd]
      exact hBase
  · have h2 : (step s r).2 = s := by unfold step; simp [hV]
    have hd' : d ∈ s.docs := h2 ▸ hd
    rw [h2]
    exact hCons d hd'

end Workflow
