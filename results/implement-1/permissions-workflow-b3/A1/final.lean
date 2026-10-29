import Workflow.Spec

namespace Workflow

def validb (s : State) (r : Request) : Bool :=
  match r.kind with
  | .move => decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) && allowed (s.role r.actor) (s.status r.doc) r.dst
  | .edit => decide (r.doc ∈ s.docs) && decide (r.actor ∈ s.users) && decide (s.role r.actor = .author) && decide (s.status r.doc = .draft)

def step : Impl := fun s r =>
  if validb s r then
    (Outcome.ok, { s with status := expectedStatus s r, content := expectedContent s r, audit := expectedAudit s r })
  else
    (Outcome.rejected, s)

theorem explore2 (s : State) (r : Request) (hk : r.kind = .move)
  (h : validb s r = true) : r.doc ∈ s.docs := by
  unfold validb at h
  rw [hk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem explore3 (s : State) (r : Request) (h : validb s r = true) : ValidRequest s r := by
  unfold ValidRequest
  by_cases hk : r.kind = .move
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold validb at h
      rw [hk] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1
    · unfold validb at h
      rw [hk] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.2
    · intro hkm
      unfold validb at h
      rw [hk] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
    · intro hke
      rw [hk] at hke
      simp at hke
  · have hke : r.kind = .edit := by
      cases hrk : r.kind with
      | move => contradiction
      | edit => rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold validb at h
      rw [hke] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.1
    · unfold validb at h
      rw [hke] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.2
    · intro hkm
      rw [hke] at hkm
      simp at hkm
    · intro _
      unfold validb at h
      rw [hke] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.2, h.2⟩

theorem validb_rev_aux (s : State) (r : Request) (h : ValidRequest s r) : validb s r = true := by
  unfold ValidRequest at h
  obtain ⟨hdoc, huser, hmove, hedit⟩ := h
  unfold validb
  by_cases hk : r.kind = .move
  · rw [hk]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hdoc, huser⟩, ?_⟩
    exact hmove hk
  · have hke : r.kind = .edit := by
      cases hrk : r.kind with
      | move => contradiction
      | edit => rfl
    rw [hke]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have he := hedit hke
    refine ⟨⟨⟨hdoc, huser⟩, he.1⟩, he.2⟩

theorem allow_pub_aux2 (rl : Role) (dst : Status) (h : allowed rl .published dst = true) : dst = .archived := by
  cases hr : rl with
  | guest => cases dst <;> simp [allowed, hr] at h
  | author => cases dst <;> simp [allowed, hr] at h
  | reviewer => cases dst <;> simp [allowed, hr] at h
  | publisher => cases dst <;> simp [allowed, hr] at h ⊢ <;> assumption

theorem allow_arch_aux2 (rl : Role) (dst : Status) : allowed rl .archived dst = false := by
  cases rl <;> cases dst <;> rfl

theorem tmp_prefix_refl (l : List Nat) : l <+: l := ⟨[], by simp⟩

theorem tmp_prefix_app (l : List Nat) (x : Nat) : l <+: l ++ [x] := ⟨[x], rfl⟩

theorem tmp_check_prefix : ∀ (l : List Entry), l <+: l := by
  intro l
  exact ⟨[], by simp⟩

theorem tmp_check_prefix2 : ∀ (l : List Entry) (e : Entry), l <+: l ++ [e] := by
  intro l e
  exact ⟨[e], rfl⟩

def foo_test_xyz : Nat := 5

theorem replay_append_thm (l1 l2 : List Entry) (d : DocId) (st : Status) : replay (l1 ++ l2) d st = replay l2 d (replay l1 d st) := by
  induction l1 generalizing st with
  | nil => simp [replay]
  | cons e es ih => simp [replay, ih]

theorem replay_single_thm (e : Entry) (d : DocId) (st : Status) : replay [e] d st = (if e.doc = d then e.dst else st) := by
  simp only [replay]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold ValidRequest at h
  obtain ⟨hdoc, huser, hmove, hedit⟩ := h
  have hv : validb s r = true := by
    cases hkr : r.kind with
    | move =>
      have hm := hmove hkr
      unfold validb
      rw [hkr]
      simp [hdoc, huser, hm]
    | edit =>
      have he := hedit hkr
      obtain ⟨hr, hs⟩ := he
      unfold validb
      rw [hkr]
      simp [hdoc, huser, hr, hs]
  unfold step
  simp [hv]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hv : validb s r = false := by
    cases hb : validb s r with
    | true => exact absurd (explore3 s r hb) h
    | false => rfl
  unfold step
  simp [hv]

theorem req_authorization        : Authorized step := by
  intro s r hok
  have hv : validb s r = true := by
    cases hb : validb s r with
    | true => rfl
    | false =>
      unfold step at hok
      simp [hb] at hok
  have hvr := explore3 s r hv
  unfold ValidRequest at hvr
  obtain ⟨_, _, hmove, hedit⟩ := hvr
  exact ⟨hmove, hedit⟩

theorem req_single_doc : SingleDoc step := by
  intro s r hok d hne
  have hv : validb s r = true := by
    cases hb : validb s r with
    | true => rfl
    | false =>
      unfold step at hok
      simp [hb] at hok
  have hstate : (step s r).2 = { s with status := expectedStatus s r, content := expectedContent s r, audit := expectedAudit s r } := by
    unfold step
    simp [hv]
  have hne' : ¬ (d = r.doc) := fun heq => hne heq
  constructor
  · calc (step s r).2.status d = expectedStatus s r d := by rw [hstate]
      _ = s.status d := by unfold expectedStatus; simp [hne']
  · calc (step s r).2.content d = expectedContent s r d := by rw [hstate]
      _ = s.content d := by unfold expectedContent; simp [hne']

theorem req_published_immutable  : PublishedImmutable step := by
  intro s r d hstat
  cases hb : validb s r with
  | true =>
    have hstate : (step s r).2 = { s with status := expectedStatus s r, content := expectedContent s r, audit := expectedAudit s r } := by
      unfold step
      simp [hb]
    have hvr := explore3 s r hb
    unfold ValidRequest at hvr
    obtain ⟨_, _, _, hedit⟩ := hvr
    have hcont : (step s r).2.content d = expectedContent s r d := by rw [hstate]
    rw [hcont]
    unfold expectedContent
    by_cases hcond : r.kind = .edit ∧ d = r.doc
    · obtain ⟨hkedit, hdeq⟩ := hcond
      have he := hedit hkedit
      have hsdraft : s.status r.doc = Status.draft := he.2
      have hsd2 : s.status d = s.status r.doc := by rw [hdeq]
      rw [hsd2, hsdraft] at hstat
      rcases hstat with h | h <;> simp at h
    · simp [hcond]
  | false =>
    have hstate2 : (step s r).2 = s := by
      unfold step
      simp [hb]
    rw [hstate2]

theorem req_no_unpublish : NoUnpublish step := by
  intro s r d
  constructor
  · intro hpub
    cases hb : validb s r with
    | false =>
      have hstate2 : (step s r).2 = s := by unfold step; simp [hb]
      rw [hstate2, hpub]; exact Or.inl rfl
    | true =>
      have hstate : (step s r).2 = { s with status := expectedStatus s r, content := expectedContent s r, audit := expectedAudit s r } := by
        unfold step; simp [hb]
      rw [hstate]
      simp only
      unfold expectedStatus
      by_cases hcond : (r.kind = .move ∧ d = r.doc)
      · have hkm : r.kind = .move := hcond.1
        have hdeq : d = r.doc := hcond.2
        rw [if_pos hcond]
        have hvr := explore3 s r hb
        unfold ValidRequest at hvr
        obtain ⟨_, _, hmove, _⟩ := hvr
        have hallow := hmove hkm
        have hsrc : s.status r.doc = .published := by rw [← hdeq]; exact hpub
        rw [hsrc] at hallow
        have hdst : r.dst = .archived := allow_pub_aux2 _ _ hallow
        rw [hdst]; exact Or.inr rfl
      · rw [if_neg hcond, hpub]; exact Or.inl rfl
  · intro harch
    cases hb : validb s r with
    | false =>
      have hstate2 : (step s r).2 = s := by unfold step; simp [hb]
      rw [hstate2, harch]
    | true =>
      have hstate : (step s r).2 = { s with status := expectedStatus s r, content := expectedContent s r, audit := expectedAudit s r } := by
        unfold step; simp [hb]
      rw [hstate]
      simp only
      unfold expectedStatus
      by_cases hcond : (r.kind = .move ∧ d = r.doc)
      · have hkm : r.kind = .move := hcond.1
        have hdeq : d = r.doc := hcond.2
        rw [if_pos hcond]
        have hvr := explore3 s r hb
        unfold ValidRequest at hvr
        obtain ⟨_, _, hmove, _⟩ := hvr
        have hallow := hmove hkm
        have hsrc : s.status r.doc = .archived := by rw [← hdeq]; exact harch
        rw [hsrc, allow_arch_aux2] at hallow
        simp at hallow
      · rw [if_neg hcond, harch]

theorem req_effects : Effects step := by
  intro s r hok
  have hv : validb s r = true := by
    cases hb : validb s r with
    | true => rfl
    | false =>
      unfold step at hok
      simp [hb] at hok
  have hstate : (step s r).2 = { s with status := expectedStatus s r, content := expectedContent s r, audit := expectedAudit s r } := by
    unfold step
    simp [hv]
  have hstate1 : (step s r).2.docs = s.docs := by rw [hstate]
  have hstate2 : (step s r).2.users = s.users := by rw [hstate]
  have hstate3 : (step s r).2.role = s.role := by rw [hstate]
  have hstat : ∀ d, (step s r).2.status d = expectedStatus s r d := by intro d; rw [hstate]
  have hcont : ∀ d, (step s r).2.content d = expectedContent s r d := by intro d; rw [hstate]
  have haud : (step s r).2.audit = expectedAudit s r := by rw [hstate]
  exact ⟨hstate1, hstate2, hstate3, hstat, hcont, haud⟩

theorem req_audit_append_only    : AuditAppendOnly step := by
  intro s r
  show s.audit <+: (step s r).2.audit
  unfold step
  by_cases hb : validb s r = true
  · simp only [hb, ↓reduceIte]
    show s.audit <+: expectedAudit s r
    unfold expectedAudit
    by_cases hk : r.kind = .move
    · simp only [hk, ↓reduceIte]
      exact ⟨[_], rfl⟩
    · simp only [hk, ↓reduceIte]
      exact ⟨[], by simp⟩
  · have hb' : validb s r = false := by
      cases h : validb s r with
      | true => contradiction
      | false => rfl
    simp only [hb']
    show s.audit <+: s.audit
    exact ⟨[], by simp⟩

theorem req_audit_consistent : KeepsAuditConsistent step := by
  intro s r hcons d hd
  cases hbv : validb s r with
  | true =>
    have hstate : (step s r).2 = { s with status := expectedStatus s r, content := expectedContent s r, audit := expectedAudit s r } := by
      unfold step; simp [hbv]
    have hdocs : (step s r).2.docs = s.docs := by rw [hstate]
    have haud : (step s r).2.audit = expectedAudit s r := by rw [hstate]
    have hst : (step s r).2.status d = expectedStatus s r d := by rw [hstate]
    have hdmem : d ∈ s.docs := by rw [hdocs] at hd; exact hd
    have hreplay : replay s.audit d .draft = s.status d := hcons d hdmem
    have hgoal1 : replay (step s r).2.audit d .draft = replay (expectedAudit s r) d .draft := by rw [haud]
    rw [hgoal1, hst]
    show replay (expectedAudit s r) d .draft = expectedStatus s r d
    by_cases hk : r.kind = Kind.move
    · have hea : expectedAudit s r = s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] := by
        unfold expectedAudit; rw [if_pos hk]
      have hes : expectedStatus s r d = (if d = r.doc then r.dst else s.status d) := by
        unfold expectedStatus; by_cases hdd : d = r.doc <;> simp [hk, hdd]
      rw [hea, hes]
      have happ : replay (s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩]) d .draft = replay [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] d (replay s.audit d .draft) := replay_append_thm s.audit _ d _
      rw [happ, hreplay]
      rw [replay_single_thm]
      by_cases hdd : r.doc = d
      · have hdd' : d = r.doc := hdd.symm
        rw [if_pos hdd, if_pos hdd']
      · have hdd2 : ¬ (d = r.doc) := fun h => hdd h.symm
        rw [if_neg hdd, if_neg hdd2]
    · have hea2 : expectedAudit s r = s.audit := by
        unfold expectedAudit; rw [if_neg hk]
      have hes2 : expectedStatus s r d = s.status d := by
        unfold expectedStatus; rw [if_neg (by simp [hk])]
      rw [hea2, hes2, hreplay]
  | false =>
    have hstate2 : (step s r).2 = s := by unfold step; simp [hbv]
    have hdocs2 : (step s r).2.docs = s.docs := by rw [hstate2]
    have haud2 : (step s r).2.audit = s.audit := by rw [hstate2]
    have hst2 : (step s r).2.status d = s.status d := by rw [hstate2]
    have hdmem2 : d ∈ s.docs := by rw [hdocs2] at hd; exact hd
    have hreplay2 : replay s.audit d .draft = s.status d := hcons d hdmem2
    rw [haud2, hst2]
    exact hreplay2

end Workflow
