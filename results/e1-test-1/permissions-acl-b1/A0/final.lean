import Acl.Spec
namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery
  infer_instance

def subjB (e : Entry) (r : Request) : Bool :=
  decide (e.subject = 0) || decide (e.subject = r.user)

def prefixB : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a = b) && prefixB as bs

def matchesB (e : Entry) (r : Request) : Bool :=
  subjB e r && prefixB e.path r.path

def isAllowB (e : Entry) (r : Request) : Bool :=
  matchesB e r && decide (e.effect = .allow)

def isDenyB (e : Entry) (r : Request) : Bool :=
  matchesB e r && decide (e.effect = .deny)

theorem subjB_correct (e : Entry) (r : Request) :
    subjB e r = true ↔ (e.subject = 0 ∨ e.subject = r.user) := by
  unfold subjB
  rw [Bool.or_eq_true_iff]
  constructor
  · intro h
    cases h with
    | inl hl => exact Or.inl (of_decide_eq_true hl)
    | inr hr => exact Or.inr (of_decide_eq_true hr)
  · intro h
    cases h with
    | inl hl => simp [hl]
    | inr hr => simp [hr]

theorem prefixB_correct : ∀ (p q : List Nat), prefixB p q = true ↔ p <+: q
  | [], q => ⟨fun _ => ⟨q, by simp⟩, fun _ => rfl⟩
  | _ :: _, [] =>
    ⟨fun h => by simp [prefixB] at h,
     fun h => by obtain ⟨t, ht⟩ := h; simp at ht⟩
  | a :: as, b :: bs =>
    ⟨fun h => by
        simp only [prefixB, Bool.and_eq_true_iff] at h
        obtain ⟨hab, hpre⟩ := h
        have hab' : a = b := of_decide_eq_true hab
        have hI := (prefixB_correct as bs).mp hpre
        obtain ⟨t, ht⟩ := hI
        subst hab'
        exact ⟨t, by simp [ht]⟩,
     fun h => by
        obtain ⟨t, ht⟩ := h
        have ht2 : a :: (as ++ t) = b :: bs := by simpa using ht
        have hab : a = b := by injection ht2
        subst hab
        have htail : as ++ t = bs := by injection ht2
        simp only [prefixB]
        rw [Bool.and_eq_true_iff]
        constructor
        · simp
        · exact (prefixB_correct as bs).mpr ⟨t, htail⟩⟩

theorem matchesB_correct (e : Entry) (r : Request) :
    matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  rw [Bool.and_eq_true_iff, subjB_correct, prefixB_correct]

theorem isAllowB_correct (e : Entry) (r : Request) :
    isAllowB e r = true ↔ Matches e r ∧ e.effect = .allow := by
  unfold isAllowB
  rw [Bool.and_eq_true_iff, matchesB_correct]
  constructor
  · intro h
    obtain ⟨hm, he⟩ := h
    exact ⟨hm, of_decide_eq_true he⟩
  · intro h
    obtain ⟨hm, he⟩ := h
    exact ⟨hm, by simp [he]⟩

theorem isDenyB_correct (e : Entry) (r : Request) :
    isDenyB e r = true ↔ Matches e r ∧ e.effect = .deny := by
  unfold isDenyB
  rw [Bool.and_eq_true_iff, matchesB_correct]
  constructor
  · intro h
    obtain ⟨hm, he⟩ := h
    exact ⟨hm, of_decide_eq_true he⟩
  · intro h
    obtain ⟨hm, he⟩ := h
    exact ⟨hm, by simp [he]⟩

def allDeniesLess (l : List Entry) (r : Request) (n : Nat) : Bool :=
  match l with
  | [] => true
  | e :: es =>
    if isDenyB e r then
      if decide (depth e < n) then allDeniesLess es r n else false
    else allDeniesLess es r n

theorem allDeniesLess_correct (l : List Entry) (r : Request) (n : Nat) :
    allDeniesLess l r n = true ↔ ∀ d ∈ l, Matches d r → d.effect = .deny → depth d < n := by
  induction l with
  | nil => simp [allDeniesLess]
  | cons e es ih =>
    by_cases hD : isDenyB e r = true
    · have hm : Matches e r ∧ e.effect = .deny := (isDenyB_correct e r).mp hD
      by_cases hn : depth e < n
      · have hdn : decide (depth e < n) = true := by simp [hn]
        have heq : allDeniesLess (e :: es) r n = allDeniesLess es r n := by
          simp [allDeniesLess, hD, hdn]
        rw [heq, ih]
        constructor
        · intro hall d hdmem hmatch hdeny
          have hor : d = e ∨ d ∈ es := by simpa using hdmem
          cases hor with
          | inl heq2 => subst heq2; exact hn
          | inr hmem => exact hall d hmem hmatch hdeny
        · intro hall d hmem hmatch hdeny
          exact hall d (by simp [hmem]) hmatch hdeny
      · have hdn : decide (depth e < n) = false := by simp [hn]
        have heq : allDeniesLess (e :: es) r n = false := by
          simp [allDeniesLess, hD, hdn]
        rw [heq]
        constructor
        · intro h
          simp at h
        · intro hall
          exact absurd (hall e (by simp) hm.1 hm.2) hn
    · have hDf : isDenyB e r = false := by
        cases hB : isDenyB e r with
        | true => simp [hB] at hD
        | false => rfl
      have hnot : ¬ (Matches e r ∧ e.effect = .deny) := by
        intro hcon
        have ht := (isDenyB_correct e r).mpr hcon
        rw [ht] at hD
        simp at hD
      have heq2 : allDeniesLess (e :: es) r n = allDeniesLess es r n := by
        simp [allDeniesLess, hDf]
      rw [heq2, ih]
      constructor
      · intro hall d hdmem hmatch hdeny
        have hor : d = e ∨ d ∈ es := by simpa using hdmem
        cases hor with
        | inl heq3 => subst heq3; exact False.elim (hnot ⟨hmatch, hdeny⟩)
        | inr hmem => exact hall d hmem hmatch hdeny
      · intro hall d hmem hmatch hdeny
        exact hall d (by simp [hmem]) hmatch hdeny

theorem allDeniesLess_false_ex (l : List Entry) (r : Request) (n : Nat) :
    allDeniesLess l r n = false → ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧ ¬ depth d < n := by
  induction l with
  | nil =>
    intro h
    simp [allDeniesLess] at h
  | cons e es ih =>
    intro h
    by_cases hD : isDenyB e r = true
    · have hm := (isDenyB_correct e r).mp hD
      by_cases hn : depth e < n
      · have hdn : decide (depth e < n) = true := by simp [hn]
        have heq : allDeniesLess (e :: es) r n = allDeniesLess es r n := by
          simp [allDeniesLess, hD, hdn]
        rw [heq] at h
        obtain ⟨d, hmem, hmatch, heff, hnge⟩ := ih h
        exact ⟨d, by simp [hmem], hmatch, heff, hnge⟩
      · exact ⟨e, by simp, hm.1, hm.2, hn⟩
    · have hDf : isDenyB e r = false := by
        cases hB : isDenyB e r with
        | true => simp [hB] at hD
        | false => rfl
      have heq : allDeniesLess (e :: es) r n = allDeniesLess es r n := by
        simp [allDeniesLess, hDf]
      rw [heq] at h
      obtain ⟨d, hmem, hmatch, heff, hnge⟩ := ih h
      exact ⟨d, by simp [hmem], hmatch, heff, hnge⟩

def permittedGo (l : List Entry) (r : Request) (cs : List Entry) : Bool :=
  match cs with
  | [] => false
  | a :: as =>
    if isAllowB a r && allDeniesLess l r (depth a) then true
    else permittedGo l r as

def permittedB (l : List Entry) (r : Request) : Bool :=
  permittedGo l r l

theorem permittedGo_correct (l : List Entry) (r : Request) (cs : List Entry) :
    permittedGo l r cs = true ↔
      ∃ a ∈ cs, Matches a r ∧ a.effect = .allow ∧
        ∀ d ∈ l, Matches d r → d.effect = .deny → depth d < depth a := by
  induction cs with
  | nil => simp [permittedGo]
  | cons a as ih =>
    by_cases h : (isAllowB a r && allDeniesLess l r (depth a)) = true
    · have hgo : permittedGo l r (a :: as) = true := by simp [permittedGo, h]
      rw [hgo]
      simp only [true_iff]
      have hAnd := (Bool.and_eq_true_iff.mp h)
      have hAllow : Matches a r ∧ a.effect = .allow := (isAllowB_correct a r).mp hAnd.1
      have hall := (allDeniesLess_correct l r (depth a)).mp hAnd.2
      exact ⟨a, by simp, hAllow.1, hAllow.2, hall⟩
    · have hF : (isAllowB a r && allDeniesLess l r (depth a)) = false := by
        cases hB : (isAllowB a r && allDeniesLess l r (depth a)) with
        | true => simp [hB] at h
        | false => rfl
      have hgo : permittedGo l r (a :: as) = permittedGo l r as := by
        simp [permittedGo, hF]
      rw [hgo, ih]
      constructor
      · intro hex
        obtain ⟨b, hmem, hmatch, heff, huniv⟩ := hex
        exact ⟨b, by simp [hmem], hmatch, heff, huniv⟩
      · intro hex
        obtain ⟨b, hmem, hmatch, heff, huniv⟩ := hex
        have hor : b = a ∨ b ∈ as := by simpa using hmem
        cases hor with
        | inl heqba =>
          subst heqba
          have hA : isAllowB b r = true := (isAllowB_correct b r).mpr ⟨hmatch, heff⟩
          have hAll : allDeniesLess l r (depth b) = true :=
            (allDeniesLess_correct l r (depth b)).mpr huniv
          have ht : (isAllowB b r && allDeniesLess l r (depth b)) = true := by
            simp [hA, hAll]
          exact False.elim (h ht)
        | inr hmem2 => exact ⟨b, hmem2, hmatch, heff, huniv⟩

theorem permittedB_correct (l : List Entry) (r : Request) :
    permittedB l r = true ↔ Permitted l r := by
  unfold permittedB Permitted
  exact permittedGo_correct l r l

theorem permitted_implies_hasAllow (l : List Entry) (r : Request) :
    Permitted l r → HasAllow l r := by
  intro h
  unfold Permitted HasAllow at *
  obtain ⟨a, hmem, hmatch, heff, _⟩ := h
  exact ⟨a, hmem, hmatch, heff⟩

theorem overridden_and_permitted_exclusive (l : List Entry) (r : Request) :
    Overridden l r → Permitted l r → False := by
  intro hov hperm
  unfold Overridden Permitted at *
  obtain ⟨d, hdmem, hdmatch, hdeff, hle⟩ := hov
  obtain ⟨a, hamem, hamatch, haeff, hlt⟩ := hperm
  have h1 : depth a ≤ depth d := hle a hamem hamatch haeff
  have h2 : depth d < depth a := hlt d hdmem hdmatch hdeff
  omega

theorem maxAllowExists (l : List Entry) (r : Request) :
    HasAllow l r →
      ∃ a ∈ l, Matches a r ∧ a.effect = .allow ∧
        ∀ a' ∈ l, Matches a' r → a'.effect = .allow → depth a' ≤ depth a := by
  induction l with
  | nil =>
    intro h
    unfold HasAllow at h
    obtain ⟨a, hmem, _, _⟩ := h
    simp at hmem
  | cons hd tl ih =>
    intro h
    by_cases htl : HasAllow tl r
    · obtain ⟨a0, hmem0, hmatch0, heff0, hmax0⟩ := ih htl
      by_cases hhd : Matches hd r ∧ hd.effect = .allow
      · by_cases hle : depth a0 ≤ depth hd
        · refine ⟨hd, by simp, hhd.1, hhd.2, ?_⟩
          intro a' hmem' hmatch' heff'
          have hor : a' = hd ∨ a' ∈ tl := by simpa using hmem'
          cases hor with
          | inl heq => subst heq; exact Nat.le_refl _
          | inr hmemTl =>
            have hle' := hmax0 a' hmemTl hmatch' heff'
            omega
        · have hlt : depth hd < depth a0 := by omega
          refine ⟨a0, by simp [hmem0], hmatch0, heff0, ?_⟩
          intro a' hmem' hmatch' heff'
          have hor : a' = hd ∨ a' ∈ tl := by simpa using hmem'
          cases hor with
          | inl heq => subst heq; omega
          | inr hmemTl => exact hmax0 a' hmemTl hmatch' heff'
      · refine ⟨a0, by simp [hmem0], hmatch0, heff0, ?_⟩
        intro a' hmem' hmatch' heff'
        have hor : a' = hd ∨ a' ∈ tl := by simpa using hmem'
        cases hor with
        | inl heq => subst heq; exact False.elim (hhd ⟨hmatch', heff'⟩)
        | inr hmemTl => exact hmax0 a' hmemTl hmatch' heff'
    · have hhd : Matches hd r ∧ hd.effect = .allow := by
        unfold HasAllow at h
        obtain ⟨a, hmem, hmatch, heff⟩ := h
        have hor : a = hd ∨ a ∈ tl := by simpa using hmem
        cases hor with
        | inl heq => subst heq; exact ⟨hmatch, heff⟩
        | inr hmemTl =>
          have hcon : HasAllow tl r := ⟨a, hmemTl, hmatch, heff⟩
          exact False.elim (htl hcon)
      refine ⟨hd, by simp, hhd.1, hhd.2, ?_⟩
      intro a' hmem' hmatch' heff'
      have hor : a' = hd ∨ a' ∈ tl := by simpa using hmem'
      cases hor with
      | inl heq => subst heq; exact Nat.le_refl _
      | inr hmemTl =>
        have hcon : HasAllow tl r := ⟨a', hmemTl, hmatch', heff'⟩
        exact False.elim (htl hcon)

theorem hasAllow_notPermitted_implies_overridden (l : List Entry) (r : Request) :
    HasAllow l r → ¬ Permitted l r → Overridden l r := by
  intro hhas hnperm
  obtain ⟨amax, hmemMax, hmatchMax, heffMax, hmax⟩ := maxAllowExists l r hhas
  have hAllF : allDeniesLess l r (depth amax) = false := by
    cases hX : allDeniesLess l r (depth amax) with
    | true =>
      have hall := (allDeniesLess_correct l r (depth amax)).mp hX
      have hperm : Permitted l r := ⟨amax, hmemMax, hmatchMax, heffMax, hall⟩
      exact False.elim (hnperm hperm)
    | false => rfl
  obtain ⟨d, hdmem, hdmatch, hdeff, hnge⟩ := allDeniesLess_false_ex l r (depth amax) hAllF
  have hle : depth amax ≤ depth d := by omega
  exact ⟨d, hdmem, hdmatch, hdeff, fun a hamem hamatch haeff => by
    have h1 := hmax a hamem hamatch haeff
    omega⟩

def step : Impl := fun s r =>
  if _h : ValidQuery s r then
    let g := permittedB s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem step_valid_eq (s : State) (r : Request) (h : ValidQuery s r) :
    step s r = (if permittedB s.entries r then .granted else .denied,
      { s with log := s.log ++ [⟨r.user, r.path, permittedB s.entries r⟩] }) := by
  unfold step
  simp [h]

theorem step_invalid_eq (s : State) (r : Request) (h : ¬ ValidQuery s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem valid_of_not_rejected (s : State) (r : Request) :
    (step s r).1 ≠ .rejected → ValidQuery s r := by
  intro hne
  by_cases h : ValidQuery s r
  · exact h
  · have heq := step_invalid_eq s r h
    rw [heq] at hne
    simp at hne

theorem granted_of_step_valid_true (s : State) (r : Request) (h : ValidQuery s r)
    (hg : permittedB s.entries r = true) : (step s r).1 = .granted := by
  rw [step_valid_eq s r h, hg]
  simp

theorem permittedB_of_granted (s : State) (r : Request) :
    (step s r).1 = .granted → permittedB s.entries r = true := by
  intro hgr
  by_cases h : ValidQuery s r
  · rw [step_valid_eq s r h] at hgr
    simp at hgr
    cases hg : permittedB s.entries r with
    | true => rfl
    | false => simp [hg] at hgr
  · rw [step_invalid_eq s r h] at hgr
    simp at hgr

theorem permittedB_of_denied_valid (s : State) (r : Request) :
    (step s r).1 = .denied → permittedB s.entries r = false := by
  intro hden
  by_cases h : ValidQuery s r
  · rw [step_valid_eq s r h] at hden
    simp at hden
    cases hg : permittedB s.entries r with
    | true => simp [hg] at hden
    | false => rfl
  · rw [step_invalid_eq s r h] at hden
    simp at hden

theorem req_valid_answered : ValidAnswered step := by
  intro s r hvalid
  rw [step_valid_eq s r hvalid]
  simp
  by_cases hg : permittedB s.entries r <;> simp [hg]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hinvalid
  exact step_invalid_eq s r hinvalid

theorem req_effects : Effects step := by
  intro s r hne
  have hvalid := valid_of_not_rejected s r hne
  rw [step_valid_eq s r hvalid]
  refine ⟨rfl, rfl, ?_⟩
  cases hg : permittedB s.entries r with
  | true => simp [hg]
  | false => simp [hg]

theorem req_default_deny : DefaultDeny step := by
  intro s r hno
  by_cases h : ValidQuery s r
  · rw [step_valid_eq s r h]
    simp only
    by_cases hg : permittedB s.entries r
    · have hperm := (permittedB_correct s.entries r).mp hg
      have hhas := permitted_implies_hasAllow s.entries r hperm
      exact absurd hhas hno
    · simp [hg]
  · rw [step_invalid_eq s r h]
    simp

theorem req_deny_overrides : DenyOverrides step := by
  intro s r hov
  by_cases h : ValidQuery s r
  · rw [step_valid_eq s r h]
    simp only
    by_cases hg : permittedB s.entries r
    · have hperm := (permittedB_correct s.entries r).mp hg
      have hfalse := overridden_and_permitted_exclusive s.entries r hov hperm
      exact False.elim hfalse
    · simp [hg]
  · rw [step_invalid_eq s r h]
    simp

theorem req_specific_allow : SpecificAllow step := by
  intro s r hvalid hperm
  have hg : permittedB s.entries r = true := (permittedB_correct s.entries r).mpr hperm
  exact granted_of_step_valid_true s r hvalid hg

theorem req_grant_justified : GrantJustified step := by
  intro s r hgr
  have hg := permittedB_of_granted s r hgr
  exact (permittedB_correct s.entries r).mp hg

theorem req_order_independent : OrderIndependent step := by
  intro s r l hperm
  have hvalid_iff : ValidQuery { s with entries := l } r ↔ ValidQuery s r := by
    unfold ValidQuery
    simp
  have hpermiff : Permitted l r ↔ Permitted s.entries r := by
    unfold Permitted
    constructor
    · intro hex
      obtain ⟨a, hmem, hmatch, heff, huniv⟩ := hex
      have hmem2 : a ∈ s.entries := (List.Perm.mem_iff hperm).mp hmem
      refine ⟨a, hmem2, hmatch, heff, ?_⟩
      intro d hdmem hdmatch hdeff
      have hdmem2 : d ∈ l := (List.Perm.mem_iff hperm).mpr hdmem
      exact huniv d hdmem2 hdmatch hdeff
    · intro hex
      obtain ⟨a, hmem, hmatch, heff, huniv⟩ := hex
      have hmem2 : a ∈ l := (List.Perm.mem_iff hperm).mpr hmem
      refine ⟨a, hmem2, hmatch, heff, ?_⟩
      intro d hdmem hdmatch hdeff
      have hdmem2 : d ∈ s.entries := (List.Perm.mem_iff hperm).mp hdmem
      exact huniv d hdmem2 hdmatch hdeff
  have hgiff : permittedB l r = true ↔ permittedB s.entries r = true := by
    rw [permittedB_correct, permittedB_correct, hpermiff]
  have hg_eq : permittedB l r = permittedB s.entries r := by
    cases h1 : permittedB l r
    · cases h2 : permittedB s.entries r
      · rfl
      · have hT : permittedB s.entries r = true := by simp [h2]
        have hT2 : permittedB l r = true := hgiff.mpr hT
        rw [h1] at hT2
        simp at hT2
    · cases h2 : permittedB s.entries r
      · have hT : permittedB l r = true := by simp [h1]
        have hT2 : permittedB s.entries r = true := hgiff.mp hT
        rw [h2] at hT2
        simp at hT2
      · rfl
  by_cases h : ValidQuery s r
  · have h2 : ValidQuery { s with entries := l } r := hvalid_iff.mpr h
    rw [step_valid_eq s r h, step_valid_eq { s with entries := l } r h2]
    simp [hg_eq]
  · have h2 : ¬ ValidQuery { s with entries := l } r := by
      rw [hvalid_iff]
      exact h
    rw [step_invalid_eq s r h, step_invalid_eq { s with entries := l } r h2]

theorem req_denial_explained : DenialExplained step := by
  intro s r hden
  have hg := permittedB_of_denied_valid s r hden
  have hnperm : ¬ Permitted s.entries r := by
    intro hperm
    have ht := (permittedB_correct s.entries r).mpr hperm
    rw [hg] at ht
    simp at ht
  by_cases hhas : HasAllow s.entries r
  · have hov := hasAllow_notPermitted_implies_overridden s.entries r hhas hnperm
    exact Or.inr hov
  · exact Or.inl hhas

end Acl
