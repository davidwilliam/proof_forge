import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

/-- Depth of the most specific matching entry with effect `eff`. -/
def best (eff : Effect) (r : Request) (l : List Entry) : Option Nat :=
  (l.filter (fun e => matchesB e r && e.effect == eff)).foldl
    (fun m e => some (max (m.getD 0) (depth e))) none

def decision (l : List Entry) (r : Request) : Bool :=
  match best .allow r l, best .deny r l with
  | some _, none => true
  | some a, some d => d < a
  | none, _ => false

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem req_effects_aux1 : True := trivial

theorem foo_test : True := trivial

theorem probe_lemmas : True := trivial
#check @List.isPrefixOf_iff_prefix
#check @List.prefix_append

theorem probe2 : True := trivial
#check Acl.Matches
#check Acl.HasAllow

def helloTestDeny : Nat := 5
#check List.isPrefixOf
#check BEq.beq
#check decide

def testX : Bool := true

def dummyDeny1 : Nat := 0

theorem matchesB_true_iff_test (e : Entry) (r : Request) :
    (matchesB e r = true) ↔ Matches e r := by
  unfold matchesB Matches
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.isPrefixOf_iff_prefix]

theorem best_nil_test (eff : Effect) (r : Request) : best eff r [] = none := by
  unfold best
  simp

theorem fold_some_isSome (m : Nat) (L : List Entry)
    (g : Option Nat → Entry → Option Nat)
    (hg : ∀ m e, ∃ n, g m e = some n) :
    ∃ n, L.foldl g (some m) = some n := by
  induction L generalizing m with
  | nil => exact ⟨m, rfl⟩
  | cons x xs ih =>
    obtain ⟨n, hn⟩ := hg (some m) x
    rw [List.foldl_cons, hn]
    exact ih n

theorem mem_filt_iff_allow (e : Entry) (l : List Entry) (r : Request) :
    e ∈ l.filter (fun x => matchesB x r && x.effect == .allow) ↔
    (e ∈ l ∧ Matches e r ∧ e.effect = .allow) := by
  rw [List.mem_filter]
  constructor
  · intro ⟨hmem, hcond⟩
    have h1 : matchesB e r = true := by
      have : ((matchesB e r && e.effect == .allow) = true) := hcond
      exact (Bool.and_eq_true_iff.mp this).1
    have h2 : (e.effect == .allow) = true := (Bool.and_eq_true_iff.mp hcond).2
    refine ⟨hmem, (matchesB_true_iff_test e r).mp h1, (beq_iff_eq.mp h2)⟩
  · intro ⟨hmem, hm, heff⟩
    refine ⟨hmem, ?_⟩
    rw [Bool.and_eq_true_iff]
    constructor
    · exact (matchesB_true_iff_test e r).mpr hm
    · rw [heff]; rfl

theorem mem_filt_iff_deny (e : Entry) (l : List Entry) (r : Request) :
    e ∈ l.filter (fun x => matchesB x r && x.effect == .deny) ↔
    (e ∈ l ∧ Matches e r ∧ e.effect = .deny) := by
  rw [List.mem_filter]
  constructor
  · intro ⟨hmem, hcond⟩
    have h1 : matchesB e r = true := (Bool.and_eq_true_iff.mp hcond).1
    have h2 : (e.effect == .deny) = true := (Bool.and_eq_true_iff.mp hcond).2
    exact ⟨hmem, (matchesB_true_iff_test e r).mp h1, (beq_iff_eq.mp h2)⟩
  · intro ⟨hmem, hm, heff⟩
    refine ⟨hmem, ?_⟩
    rw [Bool.and_eq_true_iff]
    constructor
    · exact (matchesB_true_iff_test e r).mpr hm
    · rw [heff]; rfl

theorem fold_g_ge (F : List Entry) (m : Option Nat) :
    m.getD 0 ≤ ((F.foldl (fun m e => some (max (m.getD 0) (depth e))) m).getD 0) := by
  induction F generalizing m with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h1 : m.getD 0 ≤ ((some (max (m.getD 0) (depth x)) : Option Nat).getD 0) := by
      simp only [Option.getD_some]
      exact Nat.le_max_left _ _
    have h2 := ih (some (max (m.getD 0) (depth x)))
    simp only [Option.getD_some] at h2
    -- h2 : (max ... ) ≤ fold result
    exact Nat.le_trans h1 h2

theorem tmpP : True := trivial

theorem tmpQ : True := trivial

theorem tmpS : True := trivial

theorem mem_filt_generic (e : Entry) (l : List Entry) (r : Request) (eff : Effect) :
    e ∈ l.filter (fun x => matchesB x r && x.effect == eff) ↔
    (e ∈ l ∧ Matches e r ∧ e.effect = eff) := by
  rw [List.mem_filter]
  constructor
  · intro ⟨hmem, hcond⟩
    have h1 : matchesB e r = true := (Bool.and_eq_true_iff.mp hcond).1
    have h2 : (e.effect == eff) = true := (Bool.and_eq_true_iff.mp hcond).2
    exact ⟨hmem, (matchesB_true_iff_test e r).mp h1, (beq_iff_eq.mp h2)⟩
  · intro ⟨hmem, hm, heff⟩
    refine ⟨hmem, ?_⟩
    rw [Bool.and_eq_true_iff]
    constructor
    · exact (matchesB_true_iff_test e r).mpr hm
    · rw [heff]; exact beq_self_eq_true eff

theorem denyExp_mem_le5 : ∀ (F : List Entry) (m : Option Nat) (e : Entry), e ∈ F → depth e ≤ ((F.foldl (fun o en => some (max (o.getD 0) (depth en))) m).getD 0) := by
  intro F
  induction F with
  | nil => intro m e h; simp at h
  | cons x xs ih =>
    intro m e hm
    simp only [List.foldl_cons]
    have hmem : e = x ∨ e ∈ xs := List.mem_cons.mp hm
    cases hmem with
    | inl heq =>
      rw [heq]
      have h1 : depth x ≤ (some (max (m.getD 0) (depth x)) : Option Nat).getD 0 := by
        simp only [Option.getD_some]
        exact Nat.le_max_right _ _
      have h2 := fold_g_ge xs (some (max (m.getD 0) (depth x)))
      exact Nat.le_trans h1 h2
    | inr hmem2 =>
      exact ih (some (max (m.getD 0) (depth x))) e hmem2

theorem probe_contains (s : State) (r : Request) : (s.users.contains r.user = true) ↔ r.user ∈ s.users := by
  simp [List.contains_eq_mem]
#check @List.contains_eq_mem

theorem fold_max_disj : ∀ (F : List Entry) (m : Option Nat) (n : Nat),
    (F.foldl (fun o en => some (max (o.getD 0) (depth en))) m) = some n →
    (n = m.getD 0 ∨ ∃ e ∈ F, depth e = n) := by
  intro F
  induction F with
  | nil =>
    intro m n h
    simp at h
    subst h
    exact Or.inl rfl
  | cons x xs ih =>
    intro m n h
    simp only [List.foldl_cons] at h
    have hIH := ih (some (max (m.getD 0) (depth x))) n h
    cases hIH with
    | inl heq =>
      have hmax : (some (max (m.getD 0) (depth x)) : Option Nat).getD 0 = max (m.getD 0) (depth x) := by
        simp only [Option.getD_some]
      rw [hmax] at heq
      have hcases : max (m.getD 0) (depth x) = m.getD 0 ∨ max (m.getD 0) (depth x) = depth x := by
        omega
      cases hcases with
      | inl hl => rw [heq, hl]; exact Or.inl rfl
      | inr hr => rw [heq, hr]; exact Or.inr ⟨x, List.mem_cons_self, rfl⟩
    | inr hex =>
      obtain ⟨e, hmem, hdepth⟩ := hex
      exact Or.inr ⟨e, List.mem_cons_of_mem x hmem, hdepth⟩

theorem step_cond_of_denied2 (s : State) (r : Request) (h : (step s r).1 = .denied) :
    (s.users.contains r.user && r.user != 0) = true := by
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · exact hc
  · have hcF : (s.users.contains r.user && r.user != 0) = false := by
      cases heq : (s.users.contains r.user && r.user != 0)
      · rfl
      · exact absurd heq hc
    have hstep : step s r = (.rejected, s) := by
      unfold step
      simp only [hcF, Bool.false_eq_true, ↓reduceIte]
    have hfst : (step s r).1 = .rejected := by rw [hstep]
    rw [hfst] at h
    simp at h

theorem tmp_probe_valid : True := trivial

theorem tmp_bneD : True := trivial

theorem tmp_onlyA (s : State) (r : Request) (hmem : r.user ∈ s.users) : s.users.contains r.user = true :=
  (probe_contains s r).mpr hmem











theorem plan0_contains_true_of_mem (users : List UserId) (u : UserId)
    (h : u ∈ users) : users.contains u = true := by
  rw [List.contains_eq_mem]
  simp [h]

theorem plan0_bne_true_of_ne (u : UserId) (h : u ≠ 0) :
    (u != 0) = true := by
  simp [h]

theorem plan0_valid_guard_true (s : State) (r : Request)
    (h : ValidQuery s r) :
    (s.users.contains r.user && r.user != 0) = true := by
  unfold ValidQuery at h
  obtain ⟨hmem, hne⟩ := h
  have hc : s.users.contains r.user = true :=
    plan0_contains_true_of_mem s.users r.user hmem
  have hb : (r.user != 0) = true :=
    plan0_bne_true_of_ne r.user hne
  rw [hc, hb, Bool.and_self]

theorem plan0_step_fst_granted_or_denied (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = true) :
    (step s r).1 = .granted ∨ (step s r).1 = .denied := by
  have h2 : (step s r).1 = (if decision s.entries r = true then Outcome.granted else Outcome.denied) := by
    unfold step
    rw [h]
    simp
  rw [h2]
  by_cases hdec : decision s.entries r = true <;> simp [hdec]

theorem plan0_valid_answered_step : ValidAnswered step := by
  intro s r hvalid
  have hguard := plan0_valid_guard_true s r hvalid
  have hdisj := plan0_step_fst_granted_or_denied s r hguard
  cases hdisj with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

theorem myValidAnswered_pf : ValidAnswered step := plan0_valid_answered_step

theorem plan1_bne_ne (u : UserId) (h : (u != 0) = true) : u ≠ 0 := by
  intro hc
  subst hc
  simp at h

theorem plan1_contains_of_true2 (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = true) :
    r.user ∈ s.users := (probe_contains s r).mp (Bool.and_eq_true_iff.mp h).1

theorem plan1_ne_of_true2 (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = true) :
    r.user ≠ 0 := plan1_bne_ne r.user (Bool.and_eq_true_iff.mp h).2

theorem plan1_guard_false (s : State) (r : Request) (hnv : ¬ ValidQuery s r) :
    (s.users.contains r.user && r.user != 0) = false := by
  cases heq : (s.users.contains r.user && r.user != 0) with
  | true =>
    exfalso
    apply hnv
    constructor
    · exact plan1_contains_of_true2 s r heq
    · exact plan1_ne_of_true2 s r heq
  | false => rfl

theorem eff_guard_true (s : State) (r : Request) (hne : (step s r).1 ≠ .rejected) :
    (s.users.contains r.user && r.user != 0) = true := by
  cases heq : (s.users.contains r.user && r.user != 0) with
  | true => rfl
  | false =>
    exfalso
    apply hne
    unfold step
    simp only [heq, Bool.false_eq_true, ↓reduceIte]

theorem eff_probe5 (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    (step s r).2.users = s.users := by
  have hmem : r.user ∈ s.users := plan1_contains_of_true2 s r hguard
  have hne : r.user ≠ 0 := plan1_ne_of_true2 s r hguard
  unfold step
  simp [hmem, hne]

theorem eff_probe6 (s : State) (r : Request)
    (hmem : r.user ∈ s.users) (hne : r.user ≠ 0) :
    step s r = ((if decision s.entries r then .granted else .denied),
      { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
  unfold step
  simp [hmem, hne]

theorem eff_users (s : State) (r : Request)
    (hmem : r.user ∈ s.users) (hne : r.user ≠ 0) :
    (step s r).2.users = s.users := eff_probe5 s r ((plan0_valid_guard_true s r ⟨hmem, hne⟩))





theorem plan1_effects_state_parts_of_guard (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    (step s r).2.users = s.users ∧
    (step s r).2.entries = s.entries ∧
    (step s r).2.log = s.log ++ [⟨r.user, r.path, decision s.entries r⟩] := by
  have hmem : r.user ∈ s.users := plan1_contains_of_true2 s r hguard
  have hne : r.user ≠ 0 := plan1_ne_of_true2 s r hguard
  have hstep := eff_probe6 s r hmem hne
  rw [hstep]
  simp


theorem plan1_effects_holds (s : State) (r : Request)
    (hne : (step s r).1 ≠ .rejected) :
    (step s r).2.users = s.users ∧
    (step s r).2.entries = s.entries ∧
    (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩] := by
  have hguard : (s.users.contains r.user && r.user != 0) = true :=
    eff_guard_true s r hne
  have hmem : r.user ∈ s.users := plan1_contains_of_true2 s r hguard
  have hne2 : r.user ≠ 0 := plan1_ne_of_true2 s r hguard
  have hstep := eff_probe6 s r hmem hne2
  have hfst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) := by
    rw [hstep]
  have hdec : decide ((step s r).1 = .granted) = decision s.entries r := by
    rw [hfst]
    cases hde : decision s.entries r <;> simp
  have hparts1 : (step s r).2.users = s.users := by rw [hstep]
  have hparts2 : (step s r).2.entries = s.entries := by rw [hstep]
  have hparts3 : (step s r).2.log = s.log ++ [⟨r.user, r.path, decision s.entries r⟩] := by
    rw [hstep]
  refine ⟨hparts1, hparts2, ?_⟩
  rw [hparts3, hdec]


theorem plan1_effects_step_eq_of_guard_aux (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    step s r = (if decision s.entries r then .granted else .denied,
      { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
  have hmem : r.user ∈ s.users := plan1_contains_of_true2 s r hguard
  have hne : r.user ≠ 0 := plan1_ne_of_true2 s r hguard
  exact eff_probe6 s r hmem hne

theorem plan1_effects_step_eq_of_guard (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    step s r = (if decision s.entries r then .granted else .denied,
      { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) :=
  plan1_effects_step_eq_of_guard_aux s r hguard

theorem probe_decide_aux (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    True := by
  have hstep := plan1_effects_step_eq_of_guard s r hguard
  have hfst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) := by
    rw [hstep]
  have h2 : (step s r).1 = (if decision s.entries r = true then Outcome.granted else Outcome.denied) := by
    rw [hstep]
  trivial





theorem plan2_decide_if_granted (b : Bool) :
    decide ((if b then Outcome.granted else Outcome.denied) = Outcome.granted) = b := by
  cases b <;> simp


theorem plan2_decide_step_of_guard (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    decide ((step s r).1 = Outcome.granted) = decision s.entries r := by
  have hstep := plan1_effects_step_eq_of_guard s r hguard
  have hfst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) := by
    rw [hstep]
  rw [hfst]
  exact plan2_decide_if_granted (decision s.entries r)


theorem plan2_step_eq_of_guard (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    step s r = (if decision s.entries r then Outcome.granted else Outcome.denied,
      { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) :=
  plan1_effects_step_eq_of_guard s r hguard

theorem plan2_step_fst_of_guard (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied := by
  have hstep := plan1_effects_step_eq_of_guard s r hguard
  rw [hstep]

theorem plan2_decide_if_granted_aux (b : Bool) :
    decide ((if b then Outcome.granted else Outcome.denied) = Outcome.granted) = b := by
  cases b <;> simp

def myTest123 : Nat := 5

theorem myTestLemma : True := trivial

theorem plan2_decide_test2 (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    decide ((step s r).1 = Outcome.granted) = decision s.entries r := by
  have hfst := plan2_step_fst_of_guard s r hguard
  rw [hfst]
  exact plan2_decide_if_granted_aux (decision s.entries r)

theorem plan2_decide_early_ok (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    decide ((step s r).1 = Outcome.granted) = decision s.entries r := by
  have hstep := plan1_effects_step_eq_of_guard s r hguard
  have hfst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) := by
    rw [hstep]
  rw [hfst]
  exact plan2_decide_if_granted (decision s.entries r)

theorem plan1_effects_decide_eq_of_guard (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    decide ((step s r).1 = .granted) = decision s.entries r :=
  plan2_decide_step_of_guard s r hguard

theorem plan1_effects_state_parts_of_guard_fix2 (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    (step s r).2.users = s.users ∧
    (step s r).2.entries = s.entries ∧
    (step s r).2.log = s.log ++ [⟨r.user, r.path, decision s.entries r⟩] := by
  have hstep := plan1_effects_step_eq_of_guard s r hguard
  rw [hstep]
  simp

theorem plan1_effects_state_parts_of_guard_check (s : State) (r : Request)
    (hguard : (s.users.contains r.user && r.user != 0) = true) :
    (step s r).2.users = s.users ∧
    (step s r).2.entries = s.entries ∧
    (step s r).2.log = s.log ++ [⟨r.user, r.path, decision s.entries r⟩] := by
  have hmem : r.user ∈ s.users := plan1_contains_of_true2 s r hguard
  have hne : r.user ≠ 0 := plan1_ne_of_true2 s r hguard
  have hstep := eff_probe6 s r hmem hne
  rw [hstep]
  simp

theorem plan1_effects_holds_check2 (s : State) (r : Request)
    (hne : (step s r).1 ≠ .rejected) :
    (step s r).2.users = s.users ∧
    (step s r).2.entries = s.entries ∧
    (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩] := by
  have hguard : (s.users.contains r.user && r.user != 0) = true :=
    eff_guard_true s r hne
  have hparts := plan1_effects_state_parts_of_guard_fix2 s r hguard
  have hdec : decide ((step s r).1 = .granted) = decision s.entries r :=
    plan1_effects_decide_eq_of_guard s r hguard
  obtain ⟨hu, he, hl⟩ := hparts
  refine ⟨hu, he, ?_⟩
  rw [hl, hdec]

theorem plan1_effects_holds_fixA (s : State) (r : Request)
    (hne : (step s r).1 ≠ .rejected) :
    (step s r).2.users = s.users ∧
    (step s r).2.entries = s.entries ∧
    (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩] := by
  have hguard : (s.users.contains r.user && r.user != 0) = true :=
    eff_guard_true s r hne
  have hmem : r.user ∈ s.users := plan1_contains_of_true2 s r hguard
  have hne2 : r.user ≠ 0 := plan1_ne_of_true2 s r hguard
  have hstep := eff_probe6 s r hmem hne2
  have hfst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) := by
    rw [hstep]
  have hdec : decide ((step s r).1 = .granted) = decision s.entries r := by
    rw [hfst]
    cases hde : decision s.entries r <;> simp
  have hparts1 : (step s r).2.users = s.users := by rw [hstep]
  have hparts2 : (step s r).2.entries = s.entries := by rw [hstep]
  have hparts3 : (step s r).2.log = s.log ++ [⟨r.user, r.path, decision s.entries r⟩] := by
    rw [hstep]
  refine ⟨hparts1, hparts2, ?_⟩
  rw [hparts3, hdec]

theorem myEffects_final : Effects step := fun s r hne => plan1_effects_holds_fixA s r hne

theorem dd3_step_ne (s : State) (r : Request)
    (hdec : decision s.entries r = false) : (step s r).1 ≠ .granted := by
  intro hgr
  cases hguard : (s.users.contains r.user && r.user != 0) with
  | false =>
    have hstep : step s r = (.rejected, s) := by
      unfold step
      simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hfst : (step s r).1 = .rejected := by rw [hstep]
    rw [hfst] at hgr
    simp at hgr
  | true =>
    have hfst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) :=
      plan2_step_fst_of_guard s r hguard
    rw [hfst, hdec] at hgr
    simp at hgr

theorem dd3_filter_empty_iff (l : List Entry) (r : Request) :
    (l.filter (fun x => matchesB x r && x.effect == .allow) = []) ↔ ¬ HasAllow l r := by
  constructor
  · intro hnil hAllow
    obtain ⟨a, hmem, hm, heff⟩ := hAllow
    have hmemF : a ∈ l.filter (fun x => matchesB x r && x.effect == .allow) := by
      rw [mem_filt_iff_allow]
      exact ⟨hmem, hm, heff⟩
    rw [hnil] at hmemF
    simp at hmemF
  · intro hno
    cases hF : (l.filter (fun x => matchesB x r && x.effect == .allow)) with
    | nil => rfl
    | cons y ys =>
      exfalso
      apply hno
      have hmem : y ∈ l.filter (fun x => matchesB x r && x.effect == .allow) := by
        rw [hF]; exact List.mem_cons_self
      rw [mem_filt_iff_allow] at hmem
      obtain ⟨hmemL, hm, heff⟩ := hmem
      exact ⟨y, hmemL, hm, heff⟩

theorem dd3_fold_some_ne_none2 (F : List Entry) (m : Nat) :
    (F.foldl (fun o en => some (max (o.getD 0) (depth en))) (some m)) ≠ none := by
  obtain ⟨n, hn⟩ := fold_some_isSome m F (fun m e => some (max (m.getD 0) (depth e))) (fun m e => ⟨_, rfl⟩)
  rw [hn]
  simp

theorem dd3_best_none_iff2 (l : List Entry) (r : Request) (eff : Effect) :
    best eff r l = none ↔ (l.filter (fun x => matchesB x r && x.effect == eff) = []) := by
  unfold best
  constructor
  · intro hnone
    cases hF : (l.filter (fun x => matchesB x r && x.effect == eff)) with
    | nil => rfl
    | cons y ys =>
      exfalso
      have hfold : ((y :: ys).foldl (fun o en => some (max (o.getD 0) (depth en))) none) ≠ none := by
        simp only [List.foldl_cons]
        exact dd3_fold_some_ne_none2 ys (max (Option.getD none 0) (depth y))
      rw [hF] at hnone
      exact absurd hnone hfold
  · intro hnil
    simp [hnil]

theorem dd3_best_allow_none2 (l : List Entry) (r : Request)
    (h : ¬ HasAllow l r) : best .allow r l = none := by
  rw [dd3_best_none_iff2]
  exact (dd3_filter_empty_iff l r).mpr h

theorem dd3_dec_false2a (l : List Entry) (r : Request)
    (h : best .allow r l = none) : decision l r = false := by
  simp [decision, h]

theorem fold_le_bound_aux : ∀ (F : List Entry) (m : Option Nat) (B : Nat),
    (∀ e ∈ F, depth e ≤ B) → m.getD 0 ≤ B →
    ((F.foldl (fun o en => some (max (o.getD 0) (depth en))) m).getD 0) ≤ B := by
  intro F
  induction F with
  | nil => intro m B _ hm; exact hm
  | cons x xs ih =>
    intro m B hall hm
    simp only [List.foldl_cons]
    have hx : depth x ≤ B := hall x List.mem_cons_self
    have hxs : ∀ e ∈ xs, depth e ≤ B := fun e h => hall e (List.mem_cons_of_mem x h)
    have hm' : ((some (max (m.getD 0) (depth x)) : Option Nat).getD 0) ≤ B := by
      simp only [Option.getD_some]
      omega
    exact ih _ _ hxs hm'

theorem best_some_bound_aux3 (l : List Entry) (r : Request) (eff : Effect) (A : Nat)
    (h : best eff r l = some A) :
    ∀ e ∈ l.filter (fun x => matchesB x r && x.effect == eff), depth e ≤ A := by
  intro e he
  have hle := denyExp_mem_le5 (l.filter (fun x => matchesB x r && x.effect == eff)) none e he
  have h2 : (l.filter (fun x => matchesB x r && x.effect == eff)).foldl (fun o en => some (max (o.getD 0) (depth en))) none = some A := h
  have hEq : Option.getD ((l.filter (fun x => matchesB x r && x.effect == eff)).foldl (fun o en => some (max (o.getD 0) (depth en))) none) 0 = A := by
    rw [h2]; rfl
  rw [hEq] at hle
  exact hle

theorem best_some_witness_aux3 (l : List Entry) (r : Request) (eff : Effect) (A : Nat)
    (h : best eff r l = some A) :
    ∃ e ∈ l.filter (fun x => matchesB x r && x.effect == eff), depth e = A := by
  have hdisj := fold_max_disj (l.filter (fun x => matchesB x r && x.effect == eff)) none A h
  cases hdisj with
  | inl heq =>
    have hA0 : A = 0 := by simpa using heq
    subst hA0
    have hFne : l.filter (fun x => matchesB x r && x.effect == eff) ≠ [] := by
      intro hnil
      have hnone : best eff r l = none := (dd3_best_none_iff2 l r eff).mpr hnil
      rw [h] at hnone
      simp at hnone
    obtain ⟨y, ys, hEq⟩ : ∃ y ys, l.filter (fun x => matchesB x r && x.effect == eff) = y :: ys :=
      List.exists_cons_of_ne_nil hFne
    have hy : y ∈ l.filter (fun x => matchesB x r && x.effect == eff) := by
      rw [hEq]; exact List.mem_cons_self
    have hle : depth y ≤ 0 := best_some_bound_aux3 l r eff 0 h y hy
    have hdy : depth y = 0 := by omega
    exact ⟨y, hy, hdy⟩
  | inr hex => exact hex

theorem grant_step_dec_true_aux (s : State) (r : Request)
    (hgr : (step s r).1 = .granted) : decision s.entries r = true := by
  have hne : (step s r).1 ≠ .rejected := by rw [hgr]; decide
  have hguard : (s.users.contains r.user && r.user != 0) = true :=
    eff_guard_true s r hne
  have hfst : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied :=
    plan2_step_fst_of_guard s r hguard
  rw [hgr] at hfst
  cases hdec : decision s.entries r with
  | true => rfl
  | false =>
    simp [hdec] at hfst

theorem grant_probe_shape (A D : Nat) (l : List Entry) (r : Request)
    (hA : best .allow r l = some A) (hD : best .deny r l = some D)
    (hdec : decision l r = true) : D < A := by
  unfold decision at hdec
  rw [hA, hD] at hdec
  exact of_decide_eq_true hdec

theorem tmp_perm_mem (l1 l2 : List Entry) (h : l1.Perm l2) (e : Entry) : (e ∈ l1 ↔ e ∈ l2) := h.mem_iff
#check @List.Perm.mem_iff

theorem tmp_perm_filter_test (l1 l2 : List Entry) (h : l1.Perm l2) (p : Entry → Bool) : (l1.filter p).Perm (l2.filter p) := h.filter p

theorem tmp_perm_induct (P : List Entry → List Entry → Prop)
    (hnil : P [] [])
    (hcons : ∀ (x : Entry) (l1 l2 : List Entry), l1.Perm l2 → P l1 l2 → P (x :: l1) (x :: l2))
    (hswap : ∀ (x y : Entry) (l : List Entry), P (y :: x :: l) (x :: y :: l))
    (htrans : ∀ (l1 l2 l3 : List Entry), l1.Perm l2 → l2.Perm l3 → P l1 l2 → P l2 l3 → P l1 l3)
    (l1 l2 : List Entry) (h : l1.Perm l2) : P l1 l2 := by
  induction h with
  | nil => exact hnil
  | cons x h1 ih => exact hcons x _ _ h1 ih
  | swap x y l => exact hswap x y l
  | trans h1 h2 ih1 ih2 => exact htrans _ _ _ h1 h2 ih1 ih2

theorem tmp_len_test (l1 l2 : List Entry) (h : l1.Perm l2) : l1.length = l2.length := h.length_eq

theorem plan3_fold_max_swap (x y : Entry) (F : List Entry) (m : Option Nat) :
    (y :: x :: F).foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m =
    (x :: y :: F).foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m := by
  simp only [List.foldl_cons, Option.getD_some]
  have h : max (max (m.getD 0) (depth y)) (depth x) = max (max (m.getD 0) (depth x)) (depth y) := by
    omega
  rw [h]


theorem plan3_fold_max_perm {F1 F2 : List Entry} (h : F1.Perm F2) :
    F1.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) none =
    F2.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) none := by
  have gen : ∀ (A B : List Entry), A.Perm B → ∀ (m : Option Nat),
      A.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m =
      B.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m := by
    intro A B hAB
    induction hAB with
    | nil => intro m; rfl
    | cons x h1 ih => intro m; simp only [List.foldl_cons]; exact ih _
    | swap x y l => intro m; exact plan3_fold_max_swap x y l m
    | trans h1 h2 ih1 ih2 => intro m; exact Eq.trans (ih1 m) (ih2 m)
  exact gen F1 F2 h none


theorem plan3_best_perm (eff : Effect) (r : Request) {l1 l2 : List Entry}
    (h : l1.Perm l2) : best eff r l1 = best eff r l2 := by
  unfold best
  have hFilt : (l1.filter (fun x => matchesB x r && x.effect == eff)).Perm
      (l2.filter (fun x => matchesB x r && x.effect == eff)) :=
    tmp_perm_filter_test l1 l2 h _
  exact plan3_fold_max_perm hFilt



theorem plan3_decision_perm (r : Request) {l1 l2 : List Entry}
    (h : l1.Perm l2) : decision l1 r = decision l2 r := by
  have hA : best .allow r l1 = best .allow r l2 := plan3_best_perm .allow r h
  have hD : best .deny r l1 = best .deny r l2 := plan3_best_perm .deny r h
  unfold decision
  rw [hA, hD]




theorem plan3_fold_max_swap_test (x y : Entry) (F : List Entry) (m : Option Nat) :
    (y :: x :: F).foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m =
    (x :: y :: F).foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m := by
  simp only [List.foldl_cons, Option.getD_some]
  have h : max (max (m.getD 0) (depth y)) (depth x) = max (max (m.getD 0) (depth x)) (depth y) := by
    omega
  rw [h]

theorem plan3_fold_max_perm_gen (F1 F2 : List Entry) (h : F1.Perm F2) (m : Option Nat) :
    F1.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m =
    F2.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m := by
  induction h generalizing m with
  | nil => rfl
  | cons x h1 ih => simp only [List.foldl_cons]; exact ih _
  | swap x y l => exact plan3_fold_max_swap x y l m
  | trans h1 h2 ih1 ih2 => exact Eq.trans (ih1 m) (ih2 m)

theorem plan3_fold_max_perm_proof {F1 F2 : List Entry} (h : F1.Perm F2) :
    F1.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) none =
    F2.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) none :=
  plan3_fold_max_perm_gen F1 F2 h none

theorem plan3_fold_max_perm_selfcontained {F1 F2 : List Entry} (h : F1.Perm F2) :
    F1.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) none =
    F2.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) none := by
  have gen : ∀ (A B : List Entry), A.Perm B → ∀ (m : Option Nat),
      A.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m =
      B.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m := by
    intro A B hAB
    induction hAB with
    | nil => intro m; rfl
    | cons x h1 ih => intro m; simp only [List.foldl_cons]; exact ih _
    | swap x y l => intro m; exact plan3_fold_max_swap x y l m
    | trans h1 h2 ih1 ih2 => intro m; exact Eq.trans (ih1 m) (ih2 m)
  exact gen F1 F2 h none

theorem plan3_best_perm_proof (eff : Effect) (r : Request) {l1 l2 : List Entry}
    (h : l1.Perm l2) : best eff r l1 = best eff r l2 := by
  unfold best
  have hFilt : (l1.filter (fun x => matchesB x r && x.effect == eff)).Perm
      (l2.filter (fun x => matchesB x r && x.effect == eff)) :=
    tmp_perm_filter_test l1 l2 h _
  exact plan3_fold_max_perm_gen _ _ hFilt none

theorem plan3_best_perm_alt (eff : Effect) (r : Request) {l1 l2 : List Entry}
    (h : l1.Perm l2) : best eff r l1 = best eff r l2 := by
  unfold best
  have hFilt : (l1.filter (fun x => matchesB x r && x.effect == eff)).Perm
      (l2.filter (fun x => matchesB x r && x.effect == eff)) :=
    tmp_perm_filter_test l1 l2 h _
  exact plan3_fold_max_perm hFilt

theorem plan3_decision_perm_aux_unique123 (r : Request) {l1 l2 : List Entry}
    (h : l1.Perm l2) : decision l1 r = decision l2 r := by
  have hA : best .allow r l1 = best .allow r l2 :=
    plan3_best_perm_proof .allow r h
  have hD : best .deny r l1 = best .deny r l2 :=
    plan3_best_perm_proof .deny r h
  unfold decision
  rw [hA, hD]

theorem plan3_decision_perm_check2 (r : Request) {l1 l2 : List Entry}
    (h : l1.Perm l2) : decision l1 r = decision l2 r := by
  have hA : best .allow r l1 = best .allow r l2 :=
    plan3_best_perm .allow r h
  have hD : best .deny r l1 = best .deny r l2 :=
    plan3_best_perm .deny r h
  unfold decision
  rw [hA, hD]

theorem plan3_perm_helper_unique99 : True := trivial

theorem plan3_step_fst_of_perm (s : State) (r : Request) (l : List Entry)
    (h : l.Perm s.entries) :
    (step { s with entries := l } r).1 = (step s r).1 := by
  have hdec : decision l r = decision s.entries r :=
    plan3_decision_perm_aux_unique123 r h
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · have h1 : (step { s with entries := l } r).1 =
        (if decision l r then Outcome.granted else Outcome.denied) := by
      have hguard : (({ s with entries := l }.users.contains r.user && r.user != 0) = true) := by
        simpa using hc
      exact plan2_step_fst_of_guard _ _ hguard
    have h2 : (step s r).1 =
        (if decision s.entries r then Outcome.granted else Outcome.denied) :=
      plan2_step_fst_of_guard s r hc
    rw [h1, h2, hdec]
  · have hF : (s.users.contains r.user && r.user != 0) = false := by
      cases heq : (s.users.contains r.user && r.user != 0)
      · rfl
      · exact absurd heq hc
    have hF2 : ((({ s with entries := l }.users.contains r.user && r.user != 0)) = false) := by
      simpa using hF
    have h1 : (step { s with entries := l } r).1 = Outcome.rejected := by
      unfold step
      simp only [hF2, Bool.false_eq_true, ↓reduceIte]
    have h2 : (step s r).1 = Outcome.rejected := by
      unfold step
      simp only [hF, Bool.false_eq_true, ↓reduceIte]
    rw [h1, h2]

theorem denied_dec_false_aux (s : State) (r : Request)
    (hden : (step s r).1 = .denied) : decision s.entries r = false := by
  have hne : (step s r).1 ≠ .rejected := by rw [hden]; decide
  have hguard : (s.users.contains r.user && r.user != 0) = true :=
    eff_guard_true s r hne
  have hfst : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied :=
    plan2_step_fst_of_guard s r hguard
  rw [hden] at hfst
  cases hde : decision s.entries r with
  | true => simp [hde] at hfst
  | false => rfl

theorem denied_best_allow_none_hasNoAllow (l : List Entry) (r : Request)
    (h : best .allow r l = none) : ¬ HasAllow l r := by
  intro hA
  obtain ⟨a, hmem, hm, heff⟩ := hA
  have haF : a ∈ l.filter (fun x => matchesB x r && x.effect == .allow) := by
    rw [mem_filt_generic]
    exact ⟨hmem, hm, heff⟩
  have hnil : l.filter (fun x => matchesB x r && x.effect == .allow) = [] :=
    (dd3_best_none_iff2 l r .allow).mp h
  rw [hnil] at haF
  simp at haF

theorem req_valid_answered     : ValidAnswered step := plan0_valid_answered_step

theorem req_invalid_noop       : InvalidNoop step := by
  unfold InvalidNoop
  intro s r hnv
  have hF := plan1_guard_false s r hnv
  unfold step
  simp only [hF, Bool.false_eq_true, ↓reduceIte]

theorem req_effects : Effects step := fun s r hne => plan1_effects_holds_fixA s r hne

theorem req_default_deny : DefaultDeny step := by
  unfold DefaultDeny
  intro s r hno hgr
  have hbest : best .allow r s.entries = none :=
    dd3_best_allow_none2 s.entries r hno
  have hdec : decision s.entries r = false :=
    dd3_dec_false2a s.entries r hbest
  exact (dd3_step_ne s r hdec) hgr

theorem req_deny_overrides : DenyOverrides step := by
  unfold DenyOverrides
  intro s r hov
  obtain ⟨d, hdmem, hdmatch, hdeff, hbound⟩ := hov
  have hdmF : d ∈ s.entries.filter (fun x => matchesB x r && x.effect == .deny) := by
    rw [mem_filt_generic]
    exact ⟨hdmem, hdmatch, hdeff⟩
  have hdeny_ne : best .deny r s.entries ≠ none := by
    intro hnone
    have hnil := (dd3_best_none_iff2 s.entries r .deny).mp hnone
    rw [hnil] at hdmF
    simp at hdmF
  have hdec_false : decision s.entries r = false := by
    by_cases hAllowNone : best .allow r s.entries = none
    · exact dd3_dec_false2a s.entries r hAllowNone
    · obtain ⟨A, hA⟩ : ∃ A, best .allow r s.entries = some A := Option.ne_none_iff_exists'.mp hAllowNone
      obtain ⟨D, hD⟩ : ∃ D, best .deny r s.entries = some D := Option.ne_none_iff_exists'.mp hdeny_ne
      -- bound A ≤ depth d
      have hAllowFilt : ∀ e ∈ s.entries.filter (fun x => matchesB x r && x.effect == .allow), depth e ≤ depth d := by
        intro e he
        rw [mem_filt_generic] at he
        obtain ⟨hmem, hm, heff⟩ := he
        exact hbound e hmem hm heff
      have hA_le : A ≤ depth d := by
        have hgen := fold_le_bound_aux (s.entries.filter (fun x => matchesB x r && x.effect == .allow)) none (depth d) hAllowFilt (by simp)
        unfold best at hA
        rw [hA] at hgen
        simpa using hgen
      have hD_ge : depth d ≤ D := by
        have hgen := denyExp_mem_le5 (s.entries.filter (fun x => matchesB x r && x.effect == .deny)) none d hdmF
        unfold best at hD
        rw [hD] at hgen
        simpa using hgen
      have hle : A ≤ D := Nat.le_trans hA_le hD_ge
      unfold decision
      rw [hA, hD]
      simp
      omega
  exact dd3_step_ne s r hdec_false

theorem req_specific_allow     : SpecificAllow step := by
  unfold SpecificAllow
  intro s r hvalid hperm
  obtain ⟨a, hamem, hamatch, haeff, hbound⟩ := hperm
  have hguard : (s.users.contains r.user && r.user != 0) = true :=
    plan0_valid_guard_true s r hvalid
  have hfst : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied :=
    plan2_step_fst_of_guard s r hguard
  have haF : a ∈ s.entries.filter (fun x => matchesB x r && x.effect == .allow) := by
    rw [mem_filt_generic]
    exact ⟨hamem, hamatch, haeff⟩
  have hallow_ne : best .allow r s.entries ≠ none := by
    intro hnone
    have hnil := (dd3_best_none_iff2 s.entries r .allow).mp hnone
    rw [hnil] at haF
    simp at haF
  obtain ⟨A, hA⟩ : ∃ A, best .allow r s.entries = some A := Option.ne_none_iff_exists'.mp hallow_ne
  have hA_ge : depth a ≤ A := by
    have hgen := denyExp_mem_le5 (s.entries.filter (fun x => matchesB x r && x.effect == .allow)) none a haF
    unfold best at hA
    rw [hA] at hgen
    simpa using hgen
  by_cases hdenyNone : best .deny r s.entries = none
  · have hdec : decision s.entries r = true := by
      simp only [decision, hA, hdenyNone]
    rw [hfst, hdec]
    rfl
  · obtain ⟨D, hD⟩ : ∃ D, best .deny r s.entries = some D := Option.ne_none_iff_exists'.mp hdenyNone
    have hD_lt : D < A := by
      have hall : ∀ e ∈ s.entries.filter (fun x => matchesB x r && x.effect == .deny), depth e < depth a := by
        intro e he
        rw [mem_filt_generic] at he
        obtain ⟨hmem, hm, heff⟩ := he
        exact hbound e hmem hm heff
      cases hda : depth a with
      | zero =>
        exfalso
        have hdisj := fold_max_disj (s.entries.filter (fun x => matchesB x r && x.effect == .deny)) none D (by unfold best at hD; exact hD)
        cases hdisj with
        | inl heq =>
          simp at heq
          have hempty : s.entries.filter (fun x => matchesB x r && x.effect == .deny) = [] := by
            cases hF : (s.entries.filter (fun x => matchesB x r && x.effect == .deny)) with
            | nil => rfl
            | cons y ys =>
              exfalso
              have hy : y ∈ s.entries.filter (fun x => matchesB x r && x.effect == .deny) := by rw [hF]; exact List.mem_cons_self
              have hlt := hall y hy
              rw [hda] at hlt
              omega
          have hnil2 : best .deny r s.entries = none := (dd3_best_none_iff2 s.entries r .deny).mpr hempty
          rw [hnil2] at hD
          simp at hD
        | inr hex =>
          obtain ⟨e, hmem, hdepth⟩ := hex
          have hlt := hall e hmem
          rw [hda, hdepth] at hlt
          omega
      | succ n =>
        have hle : D ≤ n := by
          have hgen := fold_le_bound_aux (s.entries.filter (fun x => matchesB x r && x.effect == .deny)) none n (fun e he => by have hlt := hall e he; omega) (by simp)
          unfold best at hD
          rw [hD] at hgen
          simpa using hgen
        omega
    have hdec : decision s.entries r = true := by
      unfold decision
      rw [hA, hD]
      simp [hD_lt]
    rw [hfst, hdec]
    rfl

theorem req_grant_justified : GrantJustified step := by
  unfold GrantJustified
  intro s r hgr
  have hdec : decision s.entries r = true := grant_step_dec_true_aux s r hgr
  cases hA : best .allow r s.entries with
  | none =>
    unfold decision at hdec
    rw [hA] at hdec
    cases hDn : best .deny r s.entries with
    | none => simp at hdec
    | some D => simp at hdec
  | some A =>
    obtain ⟨a, hmemF, hdepthA⟩ := best_some_witness_aux3 s.entries r .allow A hA
    rw [mem_filt_generic] at hmemF
    obtain ⟨hmem, hm, heff⟩ := hmemF
    refine ⟨a, hmem, hm, heff, ?_⟩
    intro d hdmem hdmatch hdeff
    have hdF : d ∈ s.entries.filter (fun x => matchesB x r && x.effect == .deny) := by
      rw [mem_filt_generic]
      exact ⟨hdmem, hdmatch, hdeff⟩
    cases hD : best .deny r s.entries with
    | none =>
      have hnil : s.entries.filter (fun x => matchesB x r && x.effect == .deny) = [] :=
        (dd3_best_none_iff2 s.entries r .deny).mp hD
      rw [hnil] at hdF
      simp at hdF
    | some D =>
      have hlt : D < A := grant_probe_shape A D s.entries r hA hD hdec
      have hd_le : depth d ≤ D := best_some_bound_aux3 s.entries r .deny D hD d hdF
      omega

theorem req_order_independent  : OrderIndependent step := by
  unfold OrderIndependent
  intro s r l h
  exact plan3_step_fst_of_perm s r l h

theorem req_denial_explained : DenialExplained step := by
  unfold DenialExplained
  intro s r hden
  have hdec : decision s.entries r = false := denied_dec_false_aux s r hden
  cases hA : best .allow r s.entries with
  | none =>
    exact Or.inl (denied_best_allow_none_hasNoAllow s.entries r hA)
  | some A =>
    cases hD : best .deny r s.entries with
    | none =>
      exfalso
      unfold decision at hdec
      rw [hA, hD] at hdec
      simp at hdec
    | some D =>
      have hle : A ≤ D := by
        unfold decision at hdec
        rw [hA, hD] at hdec
        simp at hdec
        omega
      obtain ⟨d, hmemF, hdepthD⟩ := best_some_witness_aux3 s.entries r .deny D hD
      rw [mem_filt_generic] at hmemF
      obtain ⟨hdmem, hdmatch, hdeff⟩ := hmemF
      refine Or.inr ⟨d, hdmem, hdmatch, hdeff, ?_⟩
      intro a hamem hamatch haeff
      have haF : a ∈ s.entries.filter (fun x => matchesB x r && x.effect == .allow) := by
        rw [mem_filt_generic]
        exact ⟨hamem, hamatch, haeff⟩
      have ha_le : depth a ≤ A := best_some_bound_aux3 s.entries r .allow A hA a haF
      omega

end Acl
