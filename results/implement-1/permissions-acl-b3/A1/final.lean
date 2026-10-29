import Acl.Spec

namespace Acl

def matchesB (e : Entry) (r : Request) : Bool :=
  (decide (e.subject = 0) || decide (e.subject = r.user)) && e.path.isPrefixOf r.path

def permittedB (l : List Entry) (r : Request) : Bool :=
  l.any fun a =>
    matchesB a r && decide (a.effect = .allow) &&
    l.all fun d =>
      !(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length)

def validB (s : State) (r : Request) : Bool :=
  s.users.contains r.user && decide (r.user ≠ 0)

def step : Impl := fun s r =>
  if !validB s r then (.rejected, s)
  else if permittedB s.entries r then
    (.granted, { s with log := s.log ++ [{ user := r.user, path := r.path, granted := true }] })
  else
    (.denied, { s with log := s.log ++ [{ user := r.user, path := r.path, granted := false }] })

theorem validB_of_ValidQuery2 (s : State) (r : Request) (h : ValidQuery s r) : validB s r = true := by
  unfold ValidQuery at h
  obtain ⟨hmem, hne⟩ := h
  unfold validB
  have hc : s.users.contains r.user = true := (List.contains_iff_mem).mpr hmem
  have hd : decide (r.user ≠ 0) = true := decide_eq_true hne
  rw [hc, hd]
  rfl

theorem helper_validB_true (s : State) (r : Request) (h : validB s r = true) : ValidQuery s r := by
  unfold ValidQuery
  unfold validB at h
  have h1 : s.users.contains r.user = true ∧ decide (r.user ≠ 0) = true := by
    have h2 : ((s.users.contains r.user && decide (r.user ≠ 0)) = true) = (s.users.contains r.user = true ∧ decide (r.user ≠ 0) = true) := Bool.and_eq_true _ _
    rw [h2] at h
    exact h
  constructor
  · exact (List.contains_iff_mem).mp h1.1
  · exact of_decide_eq_true h1.2

theorem req_effects_tmp2 : Effects step := by
  unfold Effects
  intro s r hne
  unfold step at hne ⊢
  by_cases hv : validB s r = true
  · have hif : ((!validB s r) = false) := by simp [hv]
    by_cases hp : permittedB s.entries r = true
    · simp [hif, hp]
    · have hpF : permittedB s.entries r = false := by
        cases h : permittedB s.entries r with
        | true => simp [h] at hp
        | false => rfl
      simp [hif, hpF]
  · have hvF : validB s r = false := by
      cases h : validB s r with
      | true => simp [h] at hv
      | false => rfl
    have hif : ((!validB s r) = true) := by simp [hvF]
    simp [hif] at hne

theorem t1 (l : List Nat) (p : Nat → Bool) : l.any p = true ↔ ∃ x ∈ l, p x = true := List.any_eq_true

theorem t2 (l : List Nat) (p : Nat → Bool) : l.all p = true ↔ ∀ x ∈ l, p x = true := List.all_eq_true

theorem matchesB_iff (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  constructor
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨hor, hpref⟩ := h
    rw [Bool.or_eq_true] at hor
    have hsub : e.subject = 0 ∨ e.subject = r.user := by
      cases hor with
      | inl hl => exact Or.inl (of_decide_eq_true hl)
      | inr hr => exact Or.inr (of_decide_eq_true hr)
    have hp : e.path <+: r.path := by
      have := (List.isPrefixOf_iff_prefix).mp hpref
      exact this
    exact ⟨hsub, hp⟩
  · intro h
    rw [Bool.and_eq_true]
    obtain ⟨hsub, hpref⟩ := h
    constructor
    · rw [Bool.or_eq_true]
      cases hsub with
      | inl hl => exact Or.inl (decide_eq_true hl)
      | inr hr => exact Or.inr (decide_eq_true hr)
    · exact (List.isPrefixOf_iff_prefix).mpr hpref

theorem innerB_iff2 (l : List Entry) (r : Request) (a : Entry) :
  (l.all fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length)) = true
  ↔ ∀ d ∈ l, Matches d r → d.effect = .deny → d.path.length < a.path.length := by
  rw [List.all_eq_true]
  constructor
  · intro h d hm hr he
    have hd := h d hm
    have hmb : matchesB d r = true := (matchesB_iff d r).mpr hr
    have hed : decide (d.effect = .deny) = true := decide_eq_true he
    rw [hmb, hed] at hd
    simpa using hd
  · intro h d hm
    by_cases hr : Matches d r
    · by_cases he : d.effect = .deny
      · have hlt := h d hm hr he
        have hdec : decide (d.path.length < a.path.length) = true := decide_eq_true hlt
        have hmb : matchesB d r = true := (matchesB_iff d r).mpr hr
        have hed : decide (d.effect = .deny) = true := decide_eq_true he
        simp [hmb, hed, hdec]
      · have hed : decide (d.effect = .deny) = false := decide_eq_false he
        have hmb : matchesB d r = true := (matchesB_iff d r).mpr hr
        simp [hmb, hed]
    · have hmb : matchesB d r = false := by
        cases hmb : matchesB d r with
        | true => exact absurd ((matchesB_iff d r).mp hmb) hr
        | false => rfl
      simp [hmb]

theorem permittedB_iff_perm (l : List Entry) (r : Request) :
  permittedB l r = true ↔ Permitted l r := by
  unfold permittedB Permitted depth
  rw [List.any_eq_true]
  constructor
  · intro h
    obtain ⟨a, hmem, ha⟩ := h
    have h1 : (matchesB a r && decide (a.effect = .allow) && l.all fun d => !(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length)) = true := ha
    rw [Bool.and_eq_true] at h1
    obtain ⟨hab, hall⟩ := h1
    rw [Bool.and_eq_true] at hab
    obtain ⟨hmb, heff⟩ := hab
    refine ⟨a, hmem, (matchesB_iff a r).mp hmb, of_decide_eq_true heff, ?_⟩
    intro d hdm hr he
    have := (innerB_iff2 l r a).mp hall d hdm hr he
    exact this
  · intro h
    obtain ⟨a, hmem, hr, heff, hall⟩ := h
    refine ⟨a, hmem, ?_⟩
    rw [Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      exact ⟨(matchesB_iff a r).mpr hr, decide_eq_true heff⟩
    · exact (innerB_iff2 l r a).mpr hall

theorem Permitted_perm_test (l1 l2 : List Entry) (r : Request) (h : l1.Perm l2) : Permitted l1 r ↔ Permitted l2 r := by
  unfold Permitted
  constructor
  · rintro ⟨a, hm, hr, he, hall⟩
    refine ⟨a, (h.mem_iff.mp hm), hr, he, fun d hd hr2 he2 => hall d (h.mem_iff.mpr hd) hr2 he2⟩
  · rintro ⟨a, hm, hr, he, hall⟩
    refine ⟨a, (h.mem_iff.mpr hm), hr, he, fun d hd hr2 he2 => hall d (h.mem_iff.mp hd) hr2 he2⟩

theorem permittedB_perm_inv2 (s : State) (r : Request) (l : List Entry) (hperm : l.Perm s.entries) :
  permittedB l r = permittedB s.entries r := by
  by_cases hl : permittedB l r = true
  · have hp : Permitted l r := (permittedB_iff_perm l r).mp hl
    have hp2 : Permitted s.entries r := (Permitted_perm_test l s.entries r hperm).mp hp
    have hs : permittedB s.entries r = true := (permittedB_iff_perm s.entries r).mpr hp2
    rw [hl, hs]
  · have hlF : permittedB l r = false := by
      cases hh : permittedB l r with
      | true => simp [hh] at hl
      | false => rfl
    by_cases hs : permittedB s.entries r = true
    · have hp : Permitted s.entries r := (permittedB_iff_perm s.entries r).mp hs
      have hp2 : Permitted l r := (Permitted_perm_test l s.entries r hperm).mpr hp
      have hl2 : permittedB l r = true := (permittedB_iff_perm l r).mpr hp2
      rw [hl2] at hlF
      simp at hlF
    · have hsF : permittedB s.entries r = false := by
        cases hh : permittedB s.entries r with
        | true => simp [hh] at hs
        | false => rfl
      rw [hlF, hsF]

theorem my_ord_helper (s : State) (r : Request) (l : List Entry)
  (hvalid : validB ({ s with entries := l } : State) r = validB s r)
  (hpermB : permittedB l r = permittedB s.entries r) :
  (step { s with entries := l } r).1 = (step s r).1 := by
  have he : (({ s with entries := l } : State).entries) = l := rfl
  unfold step
  rw [hvalid, he, hpermB]
  by_cases hv : ((!validB s r) = true)
  · simp [hv]
  · have hvF : ((!validB s r) = false) := by
      cases hh : (!validB s r) with
      | true => simp [hh] at hv
      | false => rfl
    simp [hvF]
    by_cases hp : (permittedB s.entries r = true)
    · simp [hp]
    · have hpF : (permittedB s.entries r = false) := by
        cases hh : permittedB s.entries r with
        | true => simp [hh] at hp
        | false => rfl
      simp [hpF]

theorem foo_test_tmp : True := trivial

theorem check_nat_lemmas : True := by
  have h1 : ∀ (a b : Nat), ¬ a ≤ b → b < a := fun a b h => Nat.lt_of_not_le h
  trivial

theorem check_nat_lemmas2 : True := by
  have h1 : ∀ (a b : Nat), ¬ a ≤ b → b < a := fun a b h => Nat.lt_of_not_ge h
  have h2 : ∀ (a b : Nat), a < b → a ≤ b := fun a b h => Nat.le_of_lt h
  have h3 : ∀ (a b c : Nat), a ≤ b → b ≤ c → a ≤ c := fun a b c h1 h2 => Nat.le_trans h1 h2
  have h4 : ∀ (a b : Nat), a ≤ b ∨ b ≤ a := fun a b => Nat.le_total a b
  trivial

theorem check_avail_1 : True := by
  have h : ∀ (a b : Nat), ¬ a < b → b ≤ a := fun a b hh => Nat.le_of_not_lt hh
  trivial

theorem req_default_deny_aux : DefaultDeny step := by
  unfold DefaultDeny
  intro s r hna hgr
  have hperm : Permitted s.entries r := by
    have hpb : permittedB s.entries r = true := by
      unfold step at hgr
      by_cases hv : validB s r = true
      · have hnb : ((!validB s r) = false) := by simp [hv]
        simp [hnb] at hgr ⊢
        by_cases hpb : permittedB s.entries r = true
        · exact hpb
        · have hpbF : permittedB s.entries r = false := by
            cases hh : permittedB s.entries r with
            | true => simp [hh] at hpb
            | false => rfl
          simp [hpbF] at hgr
      · have hvF : validB s r = false := by
          cases hh : validB s r with
          | true => simp [hh] at hv
          | false => rfl
        have hnb : ((!validB s r) = true) := by simp [hvF]
        simp [hnb] at hgr
    exact (permittedB_iff_perm s.entries r).mp hpb
  obtain ⟨a, hm, hmatch, heff, _⟩ := hperm
  exact hna ⟨a, hm, hmatch, heff⟩

theorem overridden_not_permitted_aux (l : List Entry) (r : Request) (hov : Overridden l r) (hperm : Permitted l r) : False := by
  obtain ⟨d, hdm, hmatchd, heffd, hle⟩ := hov
  obtain ⟨a, ham, hmatcha, heffa, hlt⟩ := hperm
  have h1 : depth a ≤ depth d := hle a ham hmatcha heffa
  have h2 : depth d < depth a := hlt d hdm hmatchd heffd
  have h3 : depth a < depth a := Nat.lt_of_le_of_lt h1 h2
  exact Nat.lt_irrefl _ h3

theorem granted_perm_aux2 (s : State) (r : Request) (h : (step s r).1 = .granted) : Permitted s.entries r := by
  have hp : permittedB s.entries r = true := by
    unfold step at h
    by_cases hv : validB s r = true
    · have hnb : (!validB s r) = false := by simp [hv]
      simp [hnb] at h ⊢
      by_cases hpb : permittedB s.entries r = true
      · exact hpb
      · have hpbF : permittedB s.entries r = false := by cases hh : permittedB s.entries r with | true => simp [hh] at hpb | false => rfl
        simp [hpbF] at h
    · have hvF : validB s r = false := by cases hh : validB s r with | true => simp [hh] at hv | false => rfl
      have hnb : (!validB s r) = true := by simp [hvF]
      simp [hnb] at h
  exact (permittedB_iff_perm s.entries r).mp hp

theorem maxAllow_exists_aux (l : List Entry) (r : Request) : HasAllow l r → ∃ a ∈ l, Matches a r ∧ a.effect = .allow ∧ ∀ a' ∈ l, Matches a' r → a'.effect = .allow → depth a' ≤ depth a := by
  induction l with
  | nil =>
    intro h
    obtain ⟨a, hm, _, _⟩ := h
    simp at hm
  | cons x xs ih =>
    intro h
    by_cases hx : (Matches x r ∧ x.effect = .allow)
    · by_cases hxs : HasAllow xs r
      · obtain ⟨a0, hm0, hmatch0, heff0, hmax0⟩ := ih hxs
        have htot : depth x ≤ depth a0 ∨ depth a0 ≤ depth x := Nat.le_total _ _
        cases htot with
        | inl hle =>
          refine ⟨a0, List.mem_cons.mpr (Or.inr hm0), hmatch0, heff0, ?_⟩
          intro a' hm' hmatch' heff'
          rw [List.mem_cons] at hm'
          cases hm' with
          | inl heq =>
            rw [heq]
            exact hle
          | inr hmem =>
            exact hmax0 a' hmem hmatch' heff'
        | inr hge =>
          refine ⟨x, List.mem_cons.mpr (Or.inl rfl), hx.1, hx.2, ?_⟩
          intro a' hm' hmatch' heff'
          rw [List.mem_cons] at hm'
          cases hm' with
          | inl heq =>
            rw [heq]
            exact Nat.le_refl _
          | inr hmem =>
            exact Nat.le_trans (hmax0 a' hmem hmatch' heff') hge
      · refine ⟨x, List.mem_cons.mpr (Or.inl rfl), hx.1, hx.2, ?_⟩
        intro a' hm' hmatch' heff'
        rw [List.mem_cons] at hm'
        cases hm' with
        | inl heq =>
          rw [heq]
          exact Nat.le_refl _
        | inr hmem =>
          exfalso
          exact hxs ⟨a', hmem, hmatch', heff'⟩
    · by_cases hxs : HasAllow xs r
      · obtain ⟨a0, hm0, hmatch0, heff0, hmax0⟩ := ih hxs
        refine ⟨a0, List.mem_cons.mpr (Or.inr hm0), hmatch0, heff0, ?_⟩
        intro a' hm' hmatch' heff'
        rw [List.mem_cons] at hm'
        cases hm' with
        | inl heq =>
          rw [heq] at hmatch' heff'
          exfalso
          exact hx ⟨hmatch', heff'⟩
        | inr hmem =>
          exact hmax0 a' hmem hmatch' heff'
      · exfalso
        apply hxs
        obtain ⟨a, hm, hmatch, heff⟩ := h
        rw [List.mem_cons] at hm
        cases hm with
        | inl heq =>
          rw [heq] at hmatch heff
          exact absurd ⟨hmatch, heff⟩ hx
        | inr hmem =>
          exact ⟨a, hmem, hmatch, heff⟩

theorem permFalse_blocks_aux2 (l : List Entry) (r : Request) (a : Entry)
  (hmem : a ∈ l) (hmatch : Matches a r) (heff : a.effect = .allow)
  (hfalse : permittedB l r = false) :
  ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧ depth a ≤ depth d := by
  by_cases hex : ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧ depth a ≤ depth d
  · exact hex
  · exfalso
    have hperm : Permitted l r := by
      refine ⟨a, hmem, hmatch, heff, ?_⟩
      intro d hdm hmatchd heffd
      have hnot : ¬ depth a ≤ depth d := by
        intro hle
        exact hex ⟨d, hdm, hmatchd, heffd, hle⟩
      exact Nat.lt_of_not_le hnot
    have htrue : permittedB l r = true := (permittedB_iff_perm l r).mpr hperm
    rw [htrue] at hfalse
    simp at hfalse

theorem req_valid_answered     : ValidAnswered step := by
  unfold ValidAnswered
  intro s r h
  have hb : validB s r = true := validB_of_ValidQuery2 s r h
  have hnb : (!validB s r) = false := by simp [hb]
  unfold step
  simp [hnb]
  by_cases hpb : permittedB s.entries r = true
  · simp [hpb]
  · have hpbF : permittedB s.entries r = false := by
      cases hh : permittedB s.entries r with
      | true => simp [hh] at hpb
      | false => rfl
    simp [hpbF]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  have hv : validB s r = false := by
    cases hb : validB s r with
    | true => exact absurd (helper_validB_true s r hb) h
    | false => rfl
  unfold step
  simp [hv]

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hne
  unfold step at hne ⊢
  by_cases hv : validB s r = true
  · have hif : ((!validB s r) = false) := by simp [hv]
    by_cases hp : permittedB s.entries r = true
    · simp [hif, hp]
    · have hpF : permittedB s.entries r = false := by
        cases h : permittedB s.entries r with
        | true => simp [h] at hp
        | false => rfl
      simp [hif, hpF]
  · have hvF : validB s r = false := by
      cases h : validB s r with
      | true => simp [h] at hv
      | false => rfl
    have hif : ((!validB s r) = true) := by simp [hvF]
    simp [hif] at hne

theorem req_default_deny       : DefaultDeny step := by
  unfold DefaultDeny
  intro s r hna hgr
  have hperm : Permitted s.entries r := by
    have hpb : permittedB s.entries r = true := by
      unfold step at hgr
      by_cases hv : validB s r = true
      · have hnb : ((!validB s r) = false) := by simp [hv]
        simp [hnb] at hgr ⊢
        by_cases hpb : permittedB s.entries r = true
        · exact hpb
        · have hpbF : permittedB s.entries r = false := by
            cases hh : permittedB s.entries r with
            | true => simp [hh] at hpb
            | false => rfl
          simp [hpbF] at hgr
      · have hvF : validB s r = false := by
          cases hh : validB s r with
          | true => simp [hh] at hv
          | false => rfl
        have hnb : ((!validB s r) = true) := by simp [hvF]
        simp [hnb] at hgr
    exact (permittedB_iff_perm s.entries r).mp hpb
  obtain ⟨a, hm, hmatch, heff, _⟩ := hperm
  exact hna ⟨a, hm, hmatch, heff⟩

theorem req_deny_overrides     : DenyOverrides step := by
  unfold DenyOverrides
  intro s r hov hgr
  have hperm : Permitted s.entries r := by
    have hp : permittedB s.entries r = true := by
      unfold step at hgr
      by_cases hv : validB s r = true
      · have hnb : (!validB s r) = false := by simp [hv]
        simp [hnb] at hgr ⊢
        by_cases hpb : permittedB s.entries r = true
        · exact hpb
        · have hpbF : permittedB s.entries r = false := by cases hh : permittedB s.entries r with | true => simp [hh] at hpb | false => rfl
          simp [hpbF] at hgr
      · have hvF : validB s r = false := by cases hh : validB s r with | true => simp [hh] at hv | false => rfl
        have hnb : (!validB s r) = true := by simp [hvF]
        simp [hnb] at hgr
    exact (permittedB_iff_perm s.entries r).mp hp
  exact overridden_not_permitted_aux s.entries r hov hperm

theorem req_specific_allow     : SpecificAllow step := by
  unfold SpecificAllow
  intro s r hv hperm
  have hb : validB s r = true := validB_of_ValidQuery2 s r hv
  have hp : permittedB s.entries r = true := (permittedB_iff_perm s.entries r).mpr hperm
  unfold step
  have hnb : (!validB s r) = false := by simp [hb]
  simp [hnb, hp]

theorem req_grant_justified    : GrantJustified step := by
  unfold GrantJustified
  intro s r h
  have hp : permittedB s.entries r = true := by
    unfold step at h
    by_cases hv : validB s r = true
    · have hnb : (!validB s r) = false := by simp [hv]
      simp [hnb] at h ⊢
      -- h : (if permittedB ... then granted else denied) = granted
      by_cases hpb : permittedB s.entries r = true
      · exact hpb
      · have hpbF : permittedB s.entries r = false := by cases hh : permittedB s.entries r with | true => simp [hh] at hpb | false => rfl
        simp [hpbF] at h
    · have hvF : validB s r = false := by cases hh : validB s r with | true => simp [hh] at hv | false => rfl
      have hnb : (!validB s r) = true := by simp [hvF]
      simp [hnb] at h
  exact (permittedB_iff_perm s.entries r).mp hp

theorem req_order_independent  : OrderIndependent step := by
  unfold OrderIndependent
  intro s r l hperm
  have hvalid : validB ({ s with entries := l } : State) r = validB s r := by simp [validB]
  have hpermB : permittedB l r = permittedB s.entries r :=
    permittedB_perm_inv2 s r l hperm
  exact my_ord_helper s r l hvalid hpermB

theorem req_denial_explained : DenialExplained step := by
  unfold DenialExplained
  intro s r hden
  by_cases hallow : HasAllow s.entries r
  · right
    obtain ⟨amax, hmaxmem, hmaxmatch, hmaxeff, hmaxle⟩ := maxAllow_exists_aux s.entries r hallow
    have hfalse : permittedB s.entries r = false := by
      unfold step at hden
      by_cases hv : validB s r = true
      · have hnb : (!validB s r) = false := by simp [hv]
        rw [hnb] at hden
        simp at hden
        by_cases hpb : permittedB s.entries r = true
        · simp [hpb] at hden
        · cases hh : permittedB s.entries r with
          | true => simp [hh] at hpb
          | false => rfl
      · have hvF : validB s r = false := by cases hh : validB s r with | true => simp [hh] at hv | false => rfl
        have hnb : (!validB s r) = true := by simp [hvF]
        rw [hnb] at hden
        simp at hden
    obtain ⟨d, hdmem, hdmatch, hdeff, hle⟩ := permFalse_blocks_aux2 s.entries r amax hmaxmem hmaxmatch hmaxeff hfalse
    refine ⟨d, hdmem, hdmatch, hdeff, ?_⟩
    intro a' ha'mem ha'match ha'eff
    exact Nat.le_trans (hmaxle a' ha'mem ha'match ha'eff) hle
  · left
    exact hallow

end Acl
