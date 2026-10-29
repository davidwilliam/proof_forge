import Acl.Spec

namespace Acl

def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def isValidB (s : State) (r : Request) : Bool :=
  s.users.contains r.user && !(r.user == 0)

def permittedB (l : List Entry) (r : Request) : Bool :=
  let allows := l.filter (fun e => matchesB e r && decide (e.effect = .allow))
  let denies := l.filter (fun e => matchesB e r && decide (e.effect = .deny))
  allows.any (fun a => denies.all (fun d => decide (d.path.length < a.path.length)))

def step : Impl := fun s r =>
  if !isValidB s r then (.rejected, s)
  else if permittedB s.entries r then
    (.granted, { users := s.users, entries := s.entries, log := s.log ++ [{ user := r.user, path := r.path, granted := true }] })
  else
    (.denied, { users := s.users, entries := s.entries, log := s.log ++ [{ user := r.user, path := r.path, granted := false }] })

def foo : Nat := 3
#check List.contains
#check List.elem

theorem isValidB_correct_aux (s : State) (r : Request) : (isValidB s r = true ↔ ValidQuery s r) := by
  simp [isValidB, ValidQuery]

theorem matchesB_correct_test (e : Entry) (r : Request) : (matchesB e r = true ↔ Matches e r) := by
  simp [matchesB, Matches]

theorem probe_matches (e : Entry) (r : Request) : (matchesB e r = true ↔ Matches e r) := by
  simp [matchesB, Matches]

theorem t_all (l : List Entry) (p : Entry → Bool) : (l.all p = true ↔ ∀ x ∈ l, p x = true) :=
  List.all_eq_true

theorem t_any (l : List Entry) (p : Entry → Bool) : (l.any p = true ↔ ∃ x, x ∈ l ∧ p x = true) :=
  List.any_eq_true

theorem probe2 (l1 l2 : List Nat) : (l1.isPrefixOf l2 = true ↔ l1 <+: l2) := by simp
#check List.isPrefixOf
#check BEq Nat

theorem probe1b (a b : Nat) (h : (a == b) = true) : a = b := by simpa using h

theorem probe_dec1 (p : Prop) [Decidable p] : (decide p = true ↔ p) := by simp

theorem probe_dec2 (a : Entry) (h : a.effect = .allow) : decide (a.effect = .allow) = true := by simp [h]

theorem probe_dec3 (d a : Entry) (h : d.path.length < a.path.length) : decide (d.path.length < a.path.length) = true := by simp [h]

theorem probe_memfilt (l : List Entry) (r : Request) (x : Entry) : (x ∈ l.filter (fun e => matchesB e r && decide (e.effect = .allow)) ↔ x ∈ l ∧ ((matchesB x r && decide (x.effect = .allow)) = true)) := by simp [List.mem_filter]

theorem allow_mem_aux (l : List Entry) (r : Request) (a : Entry) :
    (a ∈ l.filter (fun e => matchesB e r && decide (e.effect = .allow)) ↔
     a ∈ l ∧ Matches a r ∧ a.effect = .allow) := by
  constructor
  · intro h
    have hm := (List.mem_filter.mp h)
    obtain ⟨hL, hB⟩ := hm
    have hB2 : (matchesB a r && decide (a.effect = .allow)) = true := hB
    have h1 : matchesB a r = true := (Bool.and_eq_true_iff.mp hB2).1
    have h2 : decide (a.effect = .allow) = true := (Bool.and_eq_true_iff.mp hB2).2
    exact ⟨hL, (matchesB_correct_test a r).mp h1, of_decide_eq_true h2⟩
  · rintro ⟨hL, hm, heff⟩
    apply List.mem_filter.mpr
    refine ⟨hL, ?_⟩
    rw [Bool.and_eq_true_iff]
    exact ⟨(matchesB_correct_test a r).mpr hm, by simp [heff]⟩

theorem deny_mem_aux (l : List Entry) (r : Request) (d : Entry) :
    (d ∈ l.filter (fun e => matchesB e r && decide (e.effect = .deny)) ↔
     d ∈ l ∧ Matches d r ∧ d.effect = .deny) := by
  constructor
  · intro h
    have hm := (List.mem_filter.mp h)
    obtain ⟨hL, hB⟩ := hm
    have h1 : matchesB d r = true := (Bool.and_eq_true_iff.mp hB).1
    have h2 : decide (d.effect = .deny) = true := (Bool.and_eq_true_iff.mp hB).2
    exact ⟨hL, (matchesB_correct_test d r).mp h1, of_decide_eq_true h2⟩
  · rintro ⟨hL, hm, heff⟩
    apply List.mem_filter.mpr
    refine ⟨hL, ?_⟩
    rw [Bool.and_eq_true_iff]
    exact ⟨(matchesB_correct_test d r).mpr hm, by simp [heff]⟩

theorem permittedB_correct_aux2 (l : List Entry) (r : Request) : (permittedB l r = true ↔ Permitted l r) := by
  unfold permittedB Permitted depth
  simp only
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, ha, hinner⟩
    rw [allow_mem_aux] at ha
    obtain ⟨haL, haM, haE⟩ := ha
    have hall : ∀ x ∈ l.filter (fun e => matchesB e r && decide (e.effect = .deny)), decide (x.path.length < a.path.length) = true :=
      List.all_eq_true.mp hinner
    refine ⟨a, haL, haM, haE, ?_⟩
    intro d hd hmd hdeff
    have hdF : d ∈ l.filter (fun e => matchesB e r && decide (e.effect = .deny)) :=
      (deny_mem_aux l r d).mpr ⟨hd, hmd, hdeff⟩
    exact of_decide_eq_true (hall d hdF)
  · rintro ⟨a, haL, haM, haE, hall⟩
    refine ⟨a, (allow_mem_aux l r a).mpr ⟨haL, haM, haE⟩, ?_⟩
    rw [List.all_eq_true]
    intro x hx
    have hxm := (deny_mem_aux l r x).mp hx
    obtain ⟨hxL, hxM, hxE⟩ := hxm
    exact probe_dec3 x a (hall x hxL hxM hxE)

theorem foo_test : foo = 3 := rfl

theorem denied_isValidB (s : State) (r : Request) (h : (step s r).1 = .denied) : isValidB s r = true := by
  unfold step at h
  by_cases hv : isValidB s r = true
  · exact hv
  · have hvf : (!isValidB s r) = true := by simp [hv]
    simp [hvf] at h

theorem probe_mem_head (hd : Entry) (tl : List Entry) : hd ∈ hd :: tl := by
  simp
#check List.mem_cons
#check List.Mem.head
#check List.not_mem_nil

theorem probe_mem_lemmas (hd : Entry) (tl : List Entry) (x : Entry) (h : x ∈ hd :: tl) : x = hd ∨ x ∈ tl := List.mem_cons.mp h
#check List.mem_cons_self
#check List.mem_cons_of_mem

theorem any_false_spec (l : List Entry) (p : Entry → Bool) (h : l.any p = false) (x : Entry) (hx : x ∈ l) : p x = false := by
  cases hp : p x with
  | true =>
    have htrue : l.any p = true := by
      rw [List.any_eq_true]
      exact ⟨x, hx, hp⟩
    rw [htrue] at h
    contradiction
  | false => rfl
#check List.any_eq_true
#check List.all_eq_true

theorem probe_cases_or2 (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem req_valid_answered_aux2 : True := trivial

theorem req_valid_answered_tmpB : ValidAnswered step := by
  intro s r hv
  have hvB : isValidB s r = true := (isValidB_correct_aux s r).mpr hv
  unfold step
  have h1 : ((!isValidB s r) = false) := by simp [hvB]
  rw [h1]
  cases h : permittedB s.entries r
  · simp
  · simp

theorem denies_dominating_aux : ∀ (allows denies : List Entry),
    (∀ a ∈ allows, ∃ d ∈ denies, a.path.length ≤ d.path.length) →
    allows = [] ∨ ∃ d ∈ denies, ∀ a ∈ allows, a.path.length ≤ d.path.length := by
  intro allows
  induction allows with
  | nil => intro denies h; exact Or.inl rfl
  | cons hd tl ih =>
    intro denies hcond
    have hhd : ∃ d ∈ denies, hd.path.length ≤ d.path.length := hcond hd (by simp)
    obtain ⟨d1, hd1mem, hd1le⟩ := hhd
    have htl : ∀ a ∈ tl, ∃ d ∈ denies, a.path.length ≤ d.path.length := by
      intro a ha
      exact hcond a (List.mem_cons_of_mem hd ha)
    have iht := ih denies htl
    cases iht with
    | inl htlNil =>
      subst htlNil
      refine Or.inr ⟨d1, hd1mem, fun a ha => ?_⟩
      have heq : a = hd := by simpa using (List.mem_cons.mp ha)
      rw [heq]
      exact hd1le
    | inr hEx =>
      obtain ⟨d2, hd2mem, hd2dom⟩ := hEx
      by_cases hle : d1.path.length ≤ d2.path.length
      · exact Or.inr ⟨d2, hd2mem, fun a ha => by
          have hcases := List.mem_cons.mp ha
          cases hcases with
          | inl heq => rw [heq]; exact Nat.le_trans hd1le hle
          | inr hmem => exact hd2dom a hmem⟩
      · have hlt : d2.path.length < d1.path.length := Nat.lt_of_not_ge hle
        have hle' : d2.path.length ≤ d1.path.length := Nat.le_of_lt hlt
        exact Or.inr ⟨d1, hd1mem, fun a ha => by
          have hcases := List.mem_cons.mp ha
          cases hcases with
          | inl heq => rw [heq]; exact hd1le
          | inr hmem => exact Nat.le_trans (hd2dom a hmem) hle'⟩

theorem overridden_not_permitted (l : List Entry) (r : Request) :
    Overridden l r → ¬ Permitted l r := by
  rintro ⟨d, hdL, hdM, hdE, hdom⟩ ⟨a, haL, haM, haE, hall⟩
  have h1 : depth a ≤ depth d := hdom a haL haM haE
  have h2 : depth d < depth a := hall d hdL hdM hdE
  exact absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)

theorem req_deny_overrides_selfcontained : DenyOverrides step := by
  intro s r hOver hGrant
  have hP : permittedB s.entries r = true := by
    unfold step at hGrant
    by_cases hv : isValidB s r = true
    · simp [hv] at hGrant
      by_cases hp : permittedB s.entries r = true
      · exact hp
      · simp [hp] at hGrant
    · have hvf : (!isValidB s r) = true := by simp [hv]
      simp [hvf] at hGrant
  have hPerm : Permitted s.entries r := (permittedB_correct_aux2 s.entries r).mp hP
  exact (overridden_not_permitted s.entries r hOver) hPerm

theorem notPerm_of_denied_aux2 (s : State) (r : Request) (h : (step s r).1 = .denied) : ¬ Permitted s.entries r := by
  intro hP
  have hpT : permittedB s.entries r = true := (permittedB_correct_aux2 s.entries r).mpr hP
  have hv : isValidB s r = true := denied_isValidB s r h
  unfold step at h
  simp [hv, hpT] at h

theorem notPerm_hasAllow_imp_overridden_aux2 (l : List Entry) (r : Request) (hNP : ¬ Permitted l r) (hHas : HasAllow l r) : Overridden l r := by
  unfold Overridden
  unfold depth
  have hBound : ∀ a ∈ l.filter (fun e => matchesB e r && decide (e.effect = .allow)), ∃ d ∈ l.filter (fun e => matchesB e r && decide (e.effect = .deny)), a.path.length ≤ d.path.length := by
    intro a haF
    have hmem := (allow_mem_aux l r a).mp haF
    obtain ⟨haL, haM, haE⟩ := hmem
    by_cases hEx : ∃ d ∈ l.filter (fun e => matchesB e r && decide (e.effect = .deny)), a.path.length ≤ d.path.length
    · exact hEx
    · exfalso
      apply hNP
      refine ⟨a, haL, haM, haE, ?_⟩
      intro d hdL hdM hdE
      have hdF : d ∈ l.filter (fun e => matchesB e r && decide (e.effect = .deny)) :=
        (deny_mem_aux l r d).mpr ⟨hdL, hdM, hdE⟩
      have hNot : ¬ (a.path.length ≤ d.path.length) := fun hle => hEx ⟨d, hdF, hle⟩
      exact Nat.lt_of_not_ge hNot
  have hDom := denies_dominating_aux (l.filter (fun e => matchesB e r && decide (e.effect = .allow))) (l.filter (fun e => matchesB e r && decide (e.effect = .deny))) hBound
  cases hDom with
  | inl hNil =>
    exfalso
    obtain ⟨a, haL, haM, haE⟩ := hHas
    have haF : a ∈ l.filter (fun e => matchesB e r && decide (e.effect = .allow)) :=
      (allow_mem_aux l r a).mpr ⟨haL, haM, haE⟩
    rw [hNil] at haF
    exact List.not_mem_nil haF
  | inr hEx =>
    obtain ⟨d, hdFmem, hdDom⟩ := hEx
    have hdm := (deny_mem_aux l r d).mp hdFmem
    obtain ⟨hdL, hdM, hdE⟩ := hdm
    refine ⟨d, hdL, hdM, hdE, ?_⟩
    intro a haL haM haE
    have haF : a ∈ l.filter (fun e => matchesB e r && decide (e.effect = .allow)) :=
      (allow_mem_aux l r a).mpr ⟨haL, haM, haE⟩
    exact hdDom a haF

theorem req_valid_answered : ValidAnswered step := by
  intro s r hv
  have hvB : isValidB s r = true := (isValidB_correct_aux s r).mpr hv
  unfold step
  have h1 : ((!isValidB s r) = false) := by simp [hvB]
  rw [h1]
  cases h : permittedB s.entries r
  · simp
  · simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hfalse : isValidB s r = false := by
    have hiff := isValidB_correct_aux s r
    by_cases hb : isValidB s r = true
    · exfalso; exact h (hiff.mp hb)
    · cases h2 : isValidB s r
      · rfl
      · simp_all
  unfold step
  simp [hfalse]

theorem req_effects : Effects step := by
  intro s r hne
  have hv : isValidB s r = true := by
    cases hb : isValidB s r
    · exfalso
      have hstep : step s r = (.rejected, s) := by unfold step; simp [hb]
      rw [hstep] at hne
      simp at hne
    · rfl
  have hsimp : step s r =
    (if permittedB s.entries r then
      (.granted, ({ users := s.users, entries := s.entries, log := s.log ++ [{ user := r.user, path := r.path, granted := true }] } : State))
    else
      (.denied, ({ users := s.users, entries := s.entries, log := s.log ++ [{ user := r.user, path := r.path, granted := false }] } : State))) := by
    unfold step
    simp [hv]
  cases hpb : permittedB s.entries r
  · have h1 : (step s r).1 = .denied := by rw [hsimp]; simp [hpb]
    have hU : (step s r).2.users = s.users := by rw [hsimp]; simp [hpb]
    have hE : (step s r).2.entries = s.entries := by rw [hsimp]; simp [hpb]
    have hL : (step s r).2.log = s.log ++ [{ user := r.user, path := r.path, granted := false }] := by rw [hsimp]; simp [hpb]
    have hd : decide ((step s r).1 = .granted) = false := by simp [h1]
    refine ⟨hU, hE, ?_⟩
    have hgoal : (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩] := by
      rw [hd, hL]
    exact hgoal
  · have h1 : (step s r).1 = .granted := by rw [hsimp]; simp [hpb]
    have hU : (step s r).2.users = s.users := by rw [hsimp]; simp [hpb]
    have hE : (step s r).2.entries = s.entries := by rw [hsimp]; simp [hpb]
    have hL : (step s r).2.log = s.log ++ [{ user := r.user, path := r.path, granted := true }] := by rw [hsimp]; simp [hpb]
    have hd : decide ((step s r).1 = .granted) = true := by simp [h1]
    refine ⟨hU, hE, ?_⟩
    have hgoal : (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩] := by
      rw [hd, hL]
    exact hgoal

theorem req_default_deny : DefaultDeny step := by
  intro s r hNo hGrant
  have hP : permittedB s.entries r = true := by
    unfold step at hGrant
    by_cases hv : isValidB s r = true
    · simp [hv] at hGrant
      by_cases hp : permittedB s.entries r = true
      · exact hp
      · simp [hp] at hGrant
    · have hvf : (!isValidB s r) = true := by simp [hv]
      simp [hvf] at hGrant
  have hPerm : Permitted s.entries r := (permittedB_correct_aux2 s.entries r).mp hP
  obtain ⟨a, haL, haM, haE, _⟩ := hPerm
  exact hNo ⟨a, haL, haM, haE⟩

theorem req_deny_overrides : DenyOverrides step := by
  intro s r hOver hGrant
  have hP : permittedB s.entries r = true := by
    unfold step at hGrant
    by_cases hv : isValidB s r = true
    · simp [hv] at hGrant
      by_cases hp : permittedB s.entries r = true
      · exact hp
      · simp [hp] at hGrant
    · have hvf : (!isValidB s r) = true := by simp [hv]
      simp [hvf] at hGrant
  have hPerm : Permitted s.entries r := (permittedB_correct_aux2 s.entries r).mp hP
  exact (overridden_not_permitted s.entries r hOver) hPerm

theorem req_specific_allow : SpecificAllow step := by
  intro s r hv hperm
  have hvB : isValidB s r = true := (isValidB_correct_aux s r).mpr hv
  have hpB : permittedB s.entries r = true := (permittedB_correct_aux2 s.entries r).mpr hperm
  unfold step
  simp [hvB, hpB]

theorem req_grant_justified    : GrantJustified step := by
  intro s r h
  have hP : permittedB s.entries r = true := by
    unfold step at h
    by_cases hv : isValidB s r = true
    · simp [hv] at h
      by_cases hp : permittedB s.entries r = true
      · exact hp
      · simp [hp] at h
    · have hvf : (!isValidB s r) = true := by simp [hv]
      simp [hvf] at h
  exact (permittedB_correct_aux2 s.entries r).mp hP

theorem req_order_independent  : OrderIndependent step := by
  intro s r l hPerm
  have hV : isValidB { s with entries := l } r = isValidB s r := by simp [isValidB]
  have hPermitted_iff : Permitted l r ↔ Permitted s.entries r := by
    constructor
    · rintro ⟨a, haL, haM, haE, hall⟩
      exact ⟨a, hPerm.mem_iff.mp haL, haM, haE, fun d hd hmd hdeff => hall d (hPerm.mem_iff.mpr hd) hmd hdeff⟩
    · rintro ⟨a, haL, haM, haE, hall⟩
      exact ⟨a, hPerm.mem_iff.mpr haL, haM, haE, fun d hd hmd hdeff => hall d (hPerm.mem_iff.mp hd) hmd hdeff⟩
  have hPB : permittedB l r = permittedB s.entries r := by
    have e1 : (permittedB l r = true) ↔ Permitted l r := permittedB_correct_aux2 l r
    have e2 : (permittedB s.entries r = true) ↔ Permitted s.entries r := permittedB_correct_aux2 s.entries r
    cases hb1 : permittedB l r <;> cases hb2 : permittedB s.entries r
    · rfl
    · exfalso
      have h1 : Permitted s.entries r := e2.mp hb2
      have h2 : Permitted l r := hPermitted_iff.mpr h1
      have h3 : permittedB l r = true := e1.mpr h2
      simp [hb1] at h3
    · exfalso
      have h1 : Permitted l r := e1.mp hb1
      have h2 : Permitted s.entries r := hPermitted_iff.mp h1
      have h3 : permittedB s.entries r = true := e2.mpr h2
      simp [hb2] at h3
    · rfl
  show (step { s with entries := l } r).1 = (step s r).1
  unfold step
  simp only [hV, hPB]
  by_cases hv : ((!isValidB s r) = true)
  · simp [hv]
  · simp [hv]
    by_cases hp : (permittedB s.entries r = true)
    · simp [hp]
    · simp [hp]

theorem req_denial_explained : DenialExplained step := by
  intro s r hden
  have hNP : ¬ Permitted s.entries r := notPerm_of_denied_aux2 s r hden
  by_cases hHas : HasAllow s.entries r
  · exact Or.inr (notPerm_hasAllow_imp_overridden_aux2 s.entries r hNP hHas)
  · exact Or.inl hHas

end Acl
