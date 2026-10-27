import Acl.Spec
/-!
# Reference solution A (build team; hidden from agents)

One recursive pass computes the depth of the most specific matching allow entry and of the
most specific matching deny entry; access is granted when the allow is strictly deeper.
-/

namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance

def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

/-- Raise an optional maximum to at least `k`. -/
def bump (m : Option Nat) (k : Nat) : Option Nat :=
  match m with
  | none => some k
  | some j => some (max j k)

/-- Depths of the most specific matching allow and deny entries. -/
def scan (r : Request) : List Entry → Option Nat × Option Nat
  | [] => (none, none)
  | e :: es =>
    let (a, d) := scan r es
    if matchesB e r then
      match e.effect with
      | .allow => (bump a (depth e), d)
      | .deny => (a, bump d (depth e))
    else (a, d)

def decide2 : Option Nat × Option Nat → Bool
  | (some a, none) => true
  | (some a, some d) => d < a
  | _ => false

def decision (l : List Entry) (r : Request) : Bool := decide2 (scan r l)

def step : Impl := fun s r =>
  if ValidQuery s r then
    let g := decision s.entries r
    let rec_ : Record := { user := r.user, path := r.path, granted := g }
    (if g then .granted else .denied, { s with log := s.log ++ [rec_] })
  else (.rejected, s)

theorem matchesB_iff (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  simp only [matchesB, Matches, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.isPrefixOf_iff_prefix]

/-- The greatest depth of an entry with effect `eff` matching `r`, specified relationally. -/
def IsMax (eff : Effect) (r : Request) (l : List Entry) : Option Nat → Prop
  | none => ∀ e ∈ l, Matches e r → e.effect ≠ eff
  | some k => (∃ e ∈ l, Matches e r ∧ e.effect = eff ∧ depth e = k) ∧
      ∀ e ∈ l, Matches e r → e.effect = eff → depth e ≤ k

theorem isMax_bump {eff : Effect} {r : Request} {l : List Entry} {m : Option Nat} (x : Entry)
    (hm : IsMax eff r l m) (hx : Matches x r) (he : x.effect = eff) :
    IsMax eff r (x :: l) (bump m (depth x)) := by
  cases m with
  | none =>
    refine ⟨⟨x, List.mem_cons_self, hx, he, rfl⟩, fun e he' hme hee => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact Nat.le_refl _
    · exact absurd hee (hm e he' hme)
  | some j =>
    obtain ⟨⟨w, hw, hmw, hew, hdw⟩, hall⟩ := hm
    refine ⟨?_, fun e he' hme hee => ?_⟩
    · by_cases hjk : depth x ≤ j
      · exact ⟨w, List.mem_cons_of_mem _ hw, hmw, hew, by show depth w = max j (depth x); omega⟩
      · exact ⟨x, List.mem_cons_self, hx, he, by show depth x = max j (depth x); omega⟩
    · rcases List.mem_cons.1 he' with rfl | he'
      · show depth e ≤ max j (depth e); omega
      · have := hall e he' hme hee; show depth e ≤ max j (depth x); omega

theorem isMax_skip {eff : Effect} {r : Request} {l : List Entry} {m : Option Nat} (x : Entry)
    (hm : IsMax eff r l m) (hx : ¬ (Matches x r ∧ x.effect = eff)) :
    IsMax eff r (x :: l) m := by
  cases m with
  | none =>
    intro e he hme hee
    rcases List.mem_cons.1 he with rfl | he
    · exact hx ⟨hme, hee⟩
    · exact hm e he hme hee
  | some j =>
    obtain ⟨⟨w, hw, hmw, hew, hdw⟩, hall⟩ := hm
    refine ⟨⟨w, List.mem_cons_of_mem _ hw, hmw, hew, hdw⟩, fun e he hme hee => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact absurd ⟨hme, hee⟩ hx
    · exact hall e he hme hee

/-- The scan computes both maxima. -/
theorem scan_spec (r : Request) : ∀ l : List Entry,
    IsMax .allow r l (scan r l).1 ∧ IsMax .deny r l (scan r l).2 := by
  intro l
  induction l with
  | nil =>
    show IsMax .allow r [] none ∧ IsMax .deny r [] none
    exact ⟨fun e he => (by cases he), fun e he => (by cases he)⟩
  | cons x xs ih =>
    obtain ⟨ha, hd⟩ := ih
    simp only [scan]
    by_cases hm : matchesB x r = true
    · have hx := (matchesB_iff x r).1 hm
      simp only [hm, ite_true]
      cases he : x.effect with
      | allow =>
        refine ⟨isMax_bump x ha hx he, isMax_skip x hd ?_⟩
        intro h; rw [he] at h; cases h.2
      | deny =>
        refine ⟨isMax_skip x ha ?_, isMax_bump x hd hx he⟩
        intro h; rw [he] at h; cases h.2
    · have hx : ¬ Matches x r := fun h => hm ((matchesB_iff x r).2 h)
      have hm' : matchesB x r = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ite_false]
      exact ⟨isMax_skip x ha (fun h => hx h.1), isMax_skip x hd (fun h => hx h.1)⟩

theorem decision_iff (l : List Entry) (r : Request) : decision l r = true ↔ Permitted l r := by
  obtain ⟨ha, hd⟩ := scan_spec r l
  unfold decision
  generalize scan r l = p at ha hd
  obtain ⟨ma, md⟩ := p
  constructor
  · intro h
    cases ma with
    | none => cases md <;> simp [decide2] at h
    | some A =>
      obtain ⟨⟨w, hw, hmw, hew, hdw⟩, _⟩ := ha
      refine ⟨w, hw, hmw, hew, fun d hdl hmd hed => ?_⟩
      cases md with
      | none => exact absurd hed (hd d hdl hmd)
      | some D =>
        have hlt : D < A := by simpa [decide2] using h
        have := hd.2 d hdl hmd hed
        omega
  · rintro ⟨a, hal, hma, hea, hden⟩
    cases ma with
    | none => exact absurd hea (ha a hal hma)
    | some A =>
      have hle := ha.2 a hal hma hea
      cases md with
      | none => rfl
      | some D =>
        obtain ⟨⟨w, hw, hmw, hew, hdw⟩, _⟩ := hd
        have := hden w hw hmw hew
        simp [decide2]; omega

theorem decision_false (l : List Entry) (r : Request) (h : decision l r = false) :
    ¬ HasAllow l r ∨ Overridden l r := by
  obtain ⟨ha, hd⟩ := scan_spec r l
  unfold decision at h
  generalize scan r l = p at ha hd h
  obtain ⟨ma, md⟩ := p
  cases ma with
  | none => exact Or.inl (fun ⟨a, hal, hma, hea⟩ => ha a hal hma hea)
  | some A =>
    cases md with
    | none => simp [decide2] at h
    | some D =>
      have hge : A ≤ D := by simpa [decide2] using h
      obtain ⟨⟨w, hw, hmw, hew, hdw⟩, _⟩ := hd
      right
      exact ⟨w, hw, hmw, hew, fun a hal hma hea => by have := ha.2 a hal hma hea; omega⟩

theorem permitted_perm {l l' : List Entry} (hp : l.Perm l') (r : Request) :
    Permitted l r ↔ Permitted l' r := by
  unfold Permitted
  constructor
  · rintro ⟨a, ha, h1, h2, h3⟩
    exact ⟨a, hp.mem_iff.1 ha, h1, h2, fun d hd => h3 d (hp.mem_iff.2 hd)⟩
  · rintro ⟨a, ha, h1, h2, h3⟩
    exact ⟨a, hp.mem_iff.2 ha, h1, h2, fun d hd => h3 d (hp.mem_iff.1 hd)⟩

theorem decision_perm {l l' : List Entry} (hp : l.Perm l') (r : Request) :
    decision l r = decision l' r := by
  have h := (decision_iff l r).trans ((permitted_perm hp r).trans (decision_iff l' r).symm)
  cases h1 : decision l r <;> cases h2 : decision l' r <;> simp_all

theorem step_of_valid {s : State} {r : Request} (h : ValidQuery s r) :
    step s r = ((if decision s.entries r then .granted else .denied),
      { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
  simp [step, h]

theorem step_of_invalid {s : State} {r : Request} (h : ¬ ValidQuery s r) :
    step s r = (.rejected, s) := by
  simp [step, h]

theorem answered_valid {s : State} {r : Request} (h : (step s r).1 ≠ .rejected) : ValidQuery s r := by
  by_cases hv : ValidQuery s r
  · exact hv
  · rw [step_of_invalid hv] at h; exact absurd rfl h

theorem granted_iff (s : State) (r : Request) :
    (step s r).1 = .granted ↔ ValidQuery s r ∧ decision s.entries r = true := by
  by_cases hv : ValidQuery s r
  · rw [step_of_valid hv]; cases decision s.entries r <;> simp [hv]
  · rw [step_of_invalid hv]; simp [hv]

theorem denied_iff (s : State) (r : Request) :
    (step s r).1 = .denied ↔ ValidQuery s r ∧ decision s.entries r = false := by
  by_cases hv : ValidQuery s r
  · rw [step_of_valid hv]; cases decision s.entries r <;> simp [hv]
  · rw [step_of_invalid hv]; simp [hv]

theorem req_valid_answered : ValidAnswered step := by
  intro s r h
  rw [step_of_valid h]
  cases decision s.entries r <;> simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_invalid h

theorem req_effects : Effects step := by
  intro s r h
  rw [step_of_valid (answered_valid h)]
  cases decision s.entries r <;> simp

theorem req_grant_justified : GrantJustified step := by
  intro s r h
  exact (decision_iff _ _).1 ((granted_iff s r).1 h).2

theorem req_default_deny : DefaultDeny step := by
  intro s r hno h
  obtain ⟨a, ha, hm, he, _⟩ := req_grant_justified s r h
  exact hno ⟨a, ha, hm, he⟩

theorem req_deny_overrides : DenyOverrides step := by
  intro s r ⟨d, hd, hmd, hed, hall⟩ h
  obtain ⟨a, ha, hma, hea, hden⟩ := req_grant_justified s r h
  have h1 := hall a ha hma hea
  have h2 := hden d hd hmd hed
  omega

theorem req_specific_allow : SpecificAllow step := by
  intro s r hv hp
  exact (granted_iff s r).2 ⟨hv, (decision_iff _ _).2 hp⟩

theorem req_order_independent : OrderIndependent step := by
  intro s r l hp
  have hv : ValidQuery { s with entries := l } r ↔ ValidQuery s r := Iff.rfl
  by_cases h : ValidQuery s r
  · rw [step_of_valid h, step_of_valid (hv.2 h)]
    simp only [decision_perm hp r]
  · rw [step_of_invalid h, step_of_invalid (fun h' => h (hv.1 h'))]

theorem req_denial_explained : DenialExplained step := by
  intro s r h
  exact decision_false _ _ ((denied_iff s r).1 h).2

end Acl
