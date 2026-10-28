import Acl.Spec
namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery
  infer_instance

def prefixB : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if decide (x = y) then prefixB xs ys else false

theorem cons_prefix_iff {x y : Nat} {xs ys : List Nat} :
    (x :: xs <+: y :: ys) ↔ x = y ∧ xs <+: ys := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h
    have h2 : x :: (xs ++ t) = y :: ys := ht
    injection h2 with hxy hrest
    exact ⟨hxy, ⟨_, hrest⟩⟩
  · intro h
    obtain ⟨heq, ⟨t, ht⟩⟩ := h
    subst heq
    exact ⟨t, by simp [ht]⟩

theorem prefixB_correct (p q : List Nat) : prefixB p q = true ↔ p <+: q := by
  induction p generalizing q with
  | nil =>
    constructor
    · intro _; exact ⟨q, by simp⟩
    · intro _; simp [prefixB]
  | cons x xs ih =>
    cases q with
    | nil =>
      constructor
      · intro h; simp [prefixB] at h
      · intro h
        obtain ⟨t, ht⟩ := h
        simp at ht
    | cons y ys =>
      have hdec : (if decide (x = y) then prefixB xs ys else false) = true ↔ (x = y ∧ prefixB xs ys = true) := by
        by_cases heq : x = y
        · simp [heq]
        · simp [heq]
      have hpb : prefixB (x :: xs) (y :: ys) = (if decide (x = y) then prefixB xs ys else false) := by
        simp [prefixB]
      rw [hpb, hdec, ih, cons_prefix_iff]

def matchesB (e : Entry) (r : Request) : Bool :=
  decide (e.subject = 0 ∨ e.subject = r.user) && prefixB e.path r.path

theorem matchesB_true (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  simp [prefixB_correct]

def allowMatchB (e : Entry) (r : Request) : Bool :=
  matchesB e r && decide (e.effect = .allow)

def denyMatchB (e : Entry) (r : Request) : Bool :=
  matchesB e r && decide (e.effect = .deny)

theorem allow_true (e : Entry) (r : Request) :
    allowMatchB e r = true ↔ Matches e r ∧ e.effect = .allow := by
  unfold allowMatchB
  simp [matchesB_true]

theorem deny_true (e : Entry) (r : Request) :
    denyMatchB e r = true ↔ Matches e r ∧ e.effect = .deny := by
  unfold denyMatchB
  simp [matchesB_true]

def beatsAll (l : List Entry) (r : Request) (a : Entry) : Bool :=
  l.all (fun d => (!denyMatchB d r) || decide (depth d < depth a))

theorem deny_or_lt_true (d : Entry) (r : Request) (a : Entry) :
    ((!denyMatchB d r) || decide (depth d < depth a)) = true ↔
      (Matches d r → d.effect = .deny → depth d < depth a) := by
  have h1 : ((!denyMatchB d r) || decide (depth d < depth a)) = true ↔
      (denyMatchB d r = true → decide (depth d < depth a) = true) := by
    cases denyMatchB d r <;> simp
  rw [h1]
  constructor
  · intro himp hM hE
    have hb : denyMatchB d r = true := (deny_true d r).mpr ⟨hM, hE⟩
    have hc := himp hb
    exact of_decide_eq_true hc
  · intro himp hb
    obtain ⟨hM, hE⟩ := (deny_true d r).mp hb
    have hlt := himp hM hE
    simp [hlt]

theorem beatsAll_true (l : List Entry) (r : Request) (a : Entry) :
    beatsAll l r a = true ↔ ∀ d ∈ l, Matches d r → d.effect = .deny → depth d < depth a := by
  unfold beatsAll
  rw [List.all_eq_true]
  constructor
  · intro h d hdM hM hE
    have hp := h d hdM
    exact (deny_or_lt_true d r a).mp hp hM hE
  · intro h d hdM
    exact (deny_or_lt_true d r a).mpr (h d hdM)

theorem any_true_iff (l : List Entry) (p : Entry → Bool) :
    l.any p = true ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil =>
    simp
  | cons b bs ih =>
    have hcons : (b :: bs).any p = (p b || bs.any p) := by rfl
    have hor : ∀ x y : Bool, (x || y) = true ↔ x = true ∨ y = true := by
      intro x y
      cases x <;> cases y <;> simp
    rw [hcons, hor, ih]
    constructor
    · intro h
      cases h with
      | inl hb => exact ⟨b, List.mem_cons.mpr (Or.inl rfl), hb⟩
      | inr hex =>
        obtain ⟨a, haM, haT⟩ := hex
        exact ⟨a, List.mem_cons.mpr (Or.inr haM), haT⟩
    · intro h
      obtain ⟨a, haM, haT⟩ := h
      have haC := List.mem_cons.mp haM
      cases haC with
      | inl heq =>
        subst heq
        exact Or.inl haT
      | inr hmem =>
        exact Or.inr ⟨a, hmem, haT⟩

theorem and_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

def decision (l : List Entry) (r : Request) : Bool :=
  l.any (fun a => allowMatchB a r && beatsAll l r a)

theorem decision_true (l : List Entry) (r : Request) :
    decision l r = true ↔ Permitted l r := by
  unfold decision Permitted
  rw [any_true_iff]
  constructor
  · intro h
    obtain ⟨a, haM, haT⟩ := h
    have hconj := (and_true_iff _ _).mp haT
    obtain ⟨h1, h2⟩ := hconj
    obtain ⟨hM, hE⟩ := (allow_true a r).mp h1
    obtain hall := (beatsAll_true l r a).mp h2
    exact ⟨a, haM, hM, hE, hall⟩
  · intro h
    obtain ⟨a, haM, hM, hE, hall⟩ := h
    have h1 : allowMatchB a r = true := (allow_true a r).mpr ⟨hM, hE⟩
    have h2 : beatsAll l r a = true := (beatsAll_true l r a).mpr hall
    have haT : (allowMatchB a r && beatsAll l r a) = true := (and_true_iff _ _).mpr ⟨h1, h2⟩
    exact ⟨a, haM, haT⟩

def step : Impl := fun s r =>
  if ValidQuery s r then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem perm_mem_iff {l₁ l₂ : List Entry} (h : l₁.Perm l₂) (x : Entry) : x ∈ l₁ ↔ x ∈ l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ =>
    simp only [List.mem_cons]
    constructor
    · intro hh
      cases hh with
      | inl heq => exact Or.inr (Or.inl heq)
      | inr hh2 =>
        cases hh2 with
        | inl heq => exact Or.inl heq
        | inr hmem => exact Or.inr (Or.inr hmem)
    · intro hh
      cases hh with
      | inl heq => exact Or.inr (Or.inl heq)
      | inr hh2 =>
        cases hh2 with
        | inl heq => exact Or.inl heq
        | inr hmem => exact Or.inr (Or.inr hmem)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem permitted_of_perm {l₁ l₂ : List Entry} (h : l₁.Perm l₂) (r : Request) :
    Permitted l₁ r ↔ Permitted l₂ r := by
  unfold Permitted
  constructor
  · intro hp
    obtain ⟨a, haM, hM, hE, hall⟩ := hp
    refine ⟨a, (perm_mem_iff h a).mp haM, hM, hE, fun d hdM hMd hEd => hall d ((perm_mem_iff h d).mpr hdM) hMd hEd⟩
  · intro hp
    obtain ⟨a, haM, hM, hE, hall⟩ := hp
    refine ⟨a, (perm_mem_iff h a).mpr haM, hM, hE, fun d hdM hMd hEd => hall d ((perm_mem_iff h d).mp hdM) hMd hEd⟩

theorem permitted_hasAllow {l : List Entry} {r : Request} (h : Permitted l r) : HasAllow l r := by
  unfold Permitted HasAllow at *
  obtain ⟨a, haM, hM, hE, _⟩ := h
  exact ⟨a, haM, hM, hE⟩

theorem overridden_not_permitted {l : List Entry} {r : Request}
    (ho : Overridden l r) (hp : Permitted l r) : False := by
  unfold Overridden Permitted at *
  obtain ⟨d, hdM, hMd, hEd, hallD⟩ := ho
  obtain ⟨a, haM, hMa, hEa, hallA⟩ := hp
  have h1 := hallD a haM hMa hEa
  have h2 := hallA d hdM hMd hEd
  omega

theorem maximal_allow_exists (l : List Entry) (r : Request) (h : HasAllow l r) :
    ∃ a ∈ l, Matches a r ∧ a.effect = .allow ∧
      ∀ a' ∈ l, Matches a' r → a'.effect = .allow → depth a' ≤ depth a := by
  induction l with
  | nil =>
    have hF : ¬ HasAllow ([] : List Entry) r := by simp [HasAllow]
    exact absurd h hF
  | cons b bs ih =>
    have hdisj : (Matches b r ∧ b.effect = .allow) ∨ HasAllow bs r := by
      unfold HasAllow at h
      obtain ⟨a, ha, hMa, hEa⟩ := h
      have ha' := List.mem_cons.mp ha
      cases ha' with
      | inl heq =>
        subst heq
        exact Or.inl ⟨hMa, hEa⟩
      | inr hmem =>
        exact Or.inr ⟨a, hmem, hMa, hEa⟩
    by_cases htl : HasAllow bs r
    · obtain ⟨a, haM, hMa, hEa, hmax⟩ := ih htl
      by_cases hb : Matches b r ∧ b.effect = .allow
      · obtain ⟨hMb, hEb⟩ := hb
        by_cases hle : depth a ≤ depth b
        · refine ⟨b, List.mem_cons.mpr (Or.inl rfl), hMb, hEb, fun a' ha' hMa' hEa' => ?_⟩
          have ha'c := List.mem_cons.mp ha'
          cases ha'c with
          | inl heq =>
            subst heq
            exact Nat.le_refl _
          | inr hmem =>
            have h1 := hmax a' hmem hMa' hEa'
            omega
        · refine ⟨a, List.mem_cons.mpr (Or.inr haM), hMa, hEa, fun a' ha' hMa' hEa' => ?_⟩
          have ha'c := List.mem_cons.mp ha'
          cases ha'c with
          | inl heq =>
            subst heq
            omega
          | inr hmem => exact hmax a' hmem hMa' hEa'
      · refine ⟨a, List.mem_cons.mpr (Or.inr haM), hMa, hEa, fun a' ha' hMa' hEa' => ?_⟩
        have ha'c := List.mem_cons.mp ha'
        cases ha'c with
        | inl heq =>
          subst heq
          exfalso
          exact hb ⟨hMa', hEa'⟩
        | inr hmem => exact hmax a' hmem hMa' hEa'
    · have hb2 : Matches b r ∧ b.effect = .allow := by
        cases hdisj with
        | inl hh => exact hh
        | inr hh => exact absurd hh htl
      obtain ⟨hMb, hEb⟩ := hb2
      refine ⟨b, List.mem_cons.mpr (Or.inl rfl), hMb, hEb, fun a' ha' hMa' hEa' => ?_⟩
      have ha'c := List.mem_cons.mp ha'
      cases ha'c with
      | inl heq =>
        subst heq
        exact Nat.le_refl _
      | inr hmem =>
        exfalso
        exact htl ⟨a', hmem, hMa', hEa'⟩

theorem find_deny_or_all' (l : List Entry) (r : Request) (a : Entry) :
    (∀ d ∈ l, Matches d r → d.effect = .deny → depth d < depth a) ∨
    (∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧ depth a ≤ depth d) := by
  induction l with
  | nil =>
    exact Or.inl (fun d hdM _ _ => by simp at hdM)
  | cons b bs ih =>
    cases ih with
    | inr hex =>
      right
      obtain ⟨d, hdM, hM, hE, hle⟩ := hex
      exact ⟨d, List.mem_cons.mpr (Or.inr hdM), hM, hE, hle⟩
    | inl hall =>
      cases hdec : denyMatchB b r with
      | true =>
        have hDM := (deny_true b r).mp hdec
        obtain ⟨hM, hE⟩ := hDM
        by_cases hlt : depth b < depth a
        · left
          intro d hdM hMd hEd
          have hc := List.mem_cons.mp hdM
          cases hc with
          | inl heq =>
            cases heq
            exact hlt
          | inr hmem => exact hall d hmem hMd hEd
        · right
          have hle : depth a ≤ depth b := by omega
          exact ⟨b, List.mem_cons.mpr (Or.inl rfl), hM, hE, hle⟩
      | false =>
        left
        intro d hdM hMd hEd
        have hc := List.mem_cons.mp hdM
        cases hc with
        | inl heq =>
          have hD' : denyMatchB d r = true := (deny_true d r).mpr ⟨hMd, hEd⟩
          rw [heq] at hD'
          rw [hD'] at hdec
          contradiction
        | inr hmem => exact hall d hmem hMd hEd

theorem not_permitted_elim (l : List Entry) (r : Request) (h : ¬ Permitted l r) :
    ¬ HasAllow l r ∨ Overridden l r := by
  by_cases hA : HasAllow l r
  · have hex : ∃ a ∈ l, Matches a r ∧ a.effect = .allow ∧
        ∀ a' ∈ l, Matches a' r → a'.effect = .allow → depth a' ≤ depth a :=
      maximal_allow_exists l r hA
    obtain ⟨a, haM, hMa, hEa, hmax⟩ := hex
    cases hOr : find_deny_or_all' l r a with
    | inl hall =>
      exfalso
      apply h
      exact ⟨a, haM, hMa, hEa, hall⟩
    | inr hex2 =>
      right
      obtain ⟨d, hdM, hMd, hEd, hle⟩ := hex2
      refine ⟨d, hdM, hMd, hEd, fun a' ha'M hMa' hEa' => ?_⟩
      have h1 := hmax a' ha'M hMa' hEa'
      omega
  · exact Or.inl hA

theorem step_of_valid (s : State) (r : Request) (h : ValidQuery s r) :
    step s r = ((if decision s.entries r then .granted else .denied),
      { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
  unfold step
  simp only [h, ↓reduceIte]

theorem step_of_invalid (s : State) (r : Request) (h : ¬ ValidQuery s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp only [h, ↓reduceIte]

theorem step_valid_true (s : State) (r : Request) (h : ValidQuery s r) :
    (step s r).1 = .granted ∨ (step s r).1 = .denied := by
  have h2 := step_of_valid s r h
  rw [h2]
  cases hD : decision s.entries r <;> simp [hD]

theorem granted_of_decision_true (s : State) (r : Request) (h : ValidQuery s r)
    (hd2 : decision s.entries r = true) : (step s r).1 = .granted := by
  rw [step_of_valid s r h, hd2]
  simp

theorem denied_of_decision_false (s : State) (r : Request) (h : ValidQuery s r)
    (hd2 : decision s.entries r = false) : (step s r).1 = .denied := by
  rw [step_of_valid s r h, hd2]
  simp

theorem decision_of_granted (s : State) (r : Request) (h : (step s r).1 = .granted) :
    ValidQuery s r ∧ decision s.entries r = true := by
  by_cases hv : ValidQuery s r
  · refine ⟨hv, ?_⟩
    rw [step_of_valid s r hv] at h
    cases hD : decision s.entries r <;> simp_all
  · rw [step_of_invalid s r hv] at h
    simp at h

theorem decision_of_denied (s : State) (r : Request) (h : (step s r).1 = .denied) :
    ValidQuery s r ∧ decision s.entries r = false := by
  by_cases hv : ValidQuery s r
  · refine ⟨hv, ?_⟩
    rw [step_of_valid s r hv] at h
    cases hD : decision s.entries r <;> simp_all
  · rw [step_of_invalid s r hv] at h
    simp at h

theorem valid_update (s : State) (l : List Entry) (r : Request) :
    ValidQuery { s with entries := l } r ↔ ValidQuery s r := by
  simp [ValidQuery]

theorem req_valid_answered : ValidAnswered step := by
  unfold ValidAnswered
  intro s r hv
  have h := step_valid_true s r hv
  cases h with
  | inl hg => simp [hg]
  | inr hd2 => simp [hd2]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r hv
  exact step_of_invalid s r hv

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hne
  by_cases hv : ValidQuery s r
  · rw [step_of_valid s r hv]
    cases hD : decision s.entries r <;> simp_all
  · exfalso
    exact hne (by simp [step_of_invalid s r hv])

theorem req_default_deny : DefaultDeny step := by
  unfold DefaultDeny
  intro s r hno hg
  have ⟨_, hd2⟩ := decision_of_granted s r hg
  have hp : Permitted s.entries r := (decision_true _ _).mp hd2
  have ha := permitted_hasAllow hp
  exact hno ha

theorem req_deny_overrides : DenyOverrides step := by
  unfold DenyOverrides
  intro s r ho hg
  have ⟨_, hd2⟩ := decision_of_granted s r hg
  have hp : Permitted s.entries r := (decision_true _ _).mp hd2
  exact overridden_not_permitted ho hp

theorem req_specific_allow : SpecificAllow step := by
  unfold SpecificAllow
  intro s r hv hp
  have hd2 : decision s.entries r = true := (decision_true _ _).mpr hp
  exact granted_of_decision_true s r hv hd2

theorem req_grant_justified : GrantJustified step := by
  unfold GrantJustified
  intro s r hg
  have ⟨_, hd2⟩ := decision_of_granted s r hg
  exact (decision_true _ _).mp hd2

theorem req_order_independent : OrderIndependent step := by
  unfold OrderIndependent
  intro s r l hperm
  by_cases hv : ValidQuery s r
  · have hv2 : ValidQuery { s with entries := l } r := (valid_update s l r).mpr hv
    have hP2 : Permitted l r ↔ Permitted s.entries r := permitted_of_perm hperm r
    have hdeq : decision l r = decision s.entries r := by
      by_cases hp : Permitted l r
      · have hp2 : Permitted s.entries r := hP2.mp hp
        have d1 : decision l r = true := (decision_true _ _).mpr hp
        have d2 : decision s.entries r = true := (decision_true _ _).mpr hp2
        rw [d1, d2]
      · have hp2 : ¬ Permitted s.entries r := fun hc => hp (hP2.mpr hc)
        have d1 : decision l r = false := by
          cases hD : decision l r with
          | true =>
            have hc := (decision_true _ _).mp hD
            exfalso
            exact hp hc
          | false => rfl
        have d2 : decision s.entries r = false := by
          cases hD : decision s.entries r with
          | true =>
            have hc := (decision_true _ _).mp hD
            exfalso
            exact hp2 hc
          | false => rfl
        rw [d1, d2]
    have h1 := step_of_valid s r hv
    have h2 := step_of_valid { s with entries := l } r hv2
    simp only [h1, h2, hdeq]
  · have hv2 : ¬ ValidQuery { s with entries := l } r := by
      rw [valid_update]
      exact hv
    have h1 := step_of_invalid s r hv
    have h2 := step_of_invalid { s with entries := l } r hv2
    simp [h1, h2]

theorem req_denial_explained : DenialExplained step := by
  unfold DenialExplained
  intro s r hd2
  have ⟨_, hdec⟩ := decision_of_denied s r hd2
  have hnp : ¬ Permitted s.entries r := by
    intro hp
    have hdt := (decision_true _ _).mpr hp
    rw [hdec] at hdt
    contradiction
  exact not_permitted_elim s.entries r hnp

end Acl
