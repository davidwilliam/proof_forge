import Acl.Spec
namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance

def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def permittedB (l : List Entry) (r : Request) : Bool :=
  l.any fun a =>
    matchesB a r && decide (a.effect = .allow) &&
    l.all fun d =>
      (!(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length))

def hasAllowB (l : List Entry) (r : Request) : Bool :=
  l.any fun e => matchesB e r && decide (e.effect = .allow)

def step : Impl := fun s r =>
  if _h : ValidQuery s r then
    let g := permittedB s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else
    (.rejected, s)

theorem matchesB_true_iff_aux (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.isPrefixOf_iff_prefix]

theorem hasAllowB_true_iff (l : List Entry) (r : Request) : hasAllowB l r = true ↔ HasAllow l r := by
  unfold hasAllowB HasAllow
  rw [List.any_eq_true]
  constructor
  · intro h
    obtain ⟨a, ha_mem, ha_cond⟩ := h
    simp only [Bool.and_eq_true] at ha_cond
    obtain ⟨hmB, heq⟩ := ha_cond
    exact ⟨a, ha_mem, (matchesB_true_iff_aux a r).mp hmB, by simp at heq; exact heq⟩
  · intro h
    obtain ⟨a, ha_mem, hmA, heA⟩ := h
    exact ⟨a, ha_mem, by simp only [Bool.and_eq_true]; exact ⟨(matchesB_true_iff_aux a r).mpr hmA, by simp [heA]⟩⟩

theorem permittedB_of_Permitted_aux (l : List Entry) (r : Request) (h : Permitted l r) : permittedB l r = true := by
  obtain ⟨a, ha_mem, hmA, heA, ha_dom⟩ := h
  unfold permittedB
  rw [List.any_eq_true]
  refine ⟨a, ha_mem, ?_⟩
  have hmB : matchesB a r = true := (matchesB_true_iff_aux a r).mpr hmA
  have heB : decide (a.effect = Effect.allow) = true := by simp [heA]
  simp only [hmB, heB, Bool.true_and, Bool.and_self]
  rw [List.all_eq_true]
  intro d hd
  by_cases hmd : matchesB d r = true
  · by_cases hed : decide (d.effect = Effect.deny) = true
    · have hmD : Matches d r := (matchesB_true_iff_aux d r).mp hmd
      have heD : d.effect = Effect.deny := by simp at hed; exact hed
      have hlt : d.path.length < a.path.length := ha_dom d hd hmD heD
      simp [hmd, hed, hlt]
    · simp [hmd, hed]
  · simp [hmd]

theorem permittedB_true_implies_Permitted_aux (l : List Entry) (r : Request) (h : permittedB l r = true) : Permitted l r := by
  unfold permittedB at h
  rw [List.any_eq_true] at h
  obtain ⟨a, ha_mem, ha_cond⟩ := h
  simp only [Bool.and_eq_true] at ha_cond
  obtain ⟨⟨hmB, heqB⟩, hall⟩ := ha_cond
  have hmA : Matches a r := (matchesB_true_iff_aux a r).mp hmB
  have heA : a.effect = .allow := by simp at heqB; exact heqB
  refine ⟨a, ha_mem, hmA, heA, ?_⟩
  intro d hd hmD heD
  rw [List.all_eq_true] at hall
  have hdP := hall d hd
  have hmBd : matchesB d r = true := (matchesB_true_iff_aux d r).mpr hmD
  have heDb : decide (d.effect = .deny) = true := by simp [heD]
  simp [hmBd, heDb] at hdP
  exact hdP

theorem max_deny_exists2 (l : List Entry) (r : Request) (h : ∃ d ∈ l, Matches d r ∧ d.effect = .deny) :
  ∃ dmax ∈ l, Matches dmax r ∧ dmax.effect = .deny ∧ ∀ d ∈ l, Matches d r → d.effect = .deny → depth d ≤ depth dmax := by
  induction l with
  | nil => simp at h
  | cons head tl ih =>
    simp only [List.mem_cons] at h ⊢
    by_cases hHd : Matches head r ∧ head.effect = .deny
    · by_cases hTlExists : ∃ d ∈ tl, Matches d r ∧ d.effect = .deny
      · obtain ⟨dmax, hdmax_mem, hM, hE, hLe⟩ := ih hTlExists
        by_cases hle2 : depth head ≤ depth dmax
        · refine ⟨dmax, Or.inr hdmax_mem, hM, hE, ?_⟩
          intro d hdmem hMd hEd
          rcases hdmem with rfl | hmemTl
          · exact hle2
          · exact hLe d hmemTl hMd hEd
        · have hlt : depth dmax < depth head := Nat.lt_of_not_ge hle2
          refine ⟨head, Or.inl rfl, hHd.1, hHd.2, ?_⟩
          intro d hdmem hMd hEd
          rcases hdmem with rfl | hmemTl
          · exact Nat.le_refl _
          · have hle_d := hLe d hmemTl hMd hEd
            exact Nat.le_trans hle_d (Nat.le_of_lt hlt)
      · refine ⟨head, Or.inl rfl, hHd.1, hHd.2, ?_⟩
        intro d hdmem hMd hEd
        rcases hdmem with rfl | hmemTl
        · exact Nat.le_refl _
        · exfalso; exact hTlExists ⟨d, hmemTl, hMd, hEd⟩
    · have hTlExists : ∃ d ∈ tl, Matches d r ∧ d.effect = .deny := by
        rcases h with ⟨d, hdmem, hMr, hEr⟩
        rcases hdmem with rfl | hmemTl
        · exfalso; exact hHd ⟨hMr, hEr⟩
        · exact ⟨d, hmemTl, hMr, hEr⟩
      obtain ⟨dmax, hdmax_mem, hM, hE, hLe⟩ := ih hTlExists
      refine ⟨dmax, Or.inr hdmax_mem, hM, hE, ?_⟩
      intro d hdmem hMd hEd
      rcases hdmem with rfl | hmemTl
      · exfalso; exact hHd ⟨hMd, hEd⟩
      · exact hLe d hmemTl hMd hEd

theorem any_false_forall {α : Type} (l : List α) (p : α → Bool) (h : l.any p = false) (x : α) (hx : x ∈ l) : p x = false := by
  cases hp : p x with
  | true =>
    have hAny : l.any p = true := List.any_eq_true.mpr ⟨x, hx, hp⟩
    simp [hAny] at h
  | false => rfl

theorem all_false_exists {α : Type} (l : List α) (p : α → Bool) (h : l.all p = false) : ∃ x ∈ l, p x = false := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    cases hp : p hd with
    | false =>
      exact ⟨hd, List.mem_cons_self, hp⟩
    | true =>
      have htl : tl.all p = false := by
        cases htl2 : tl.all p with
        | true =>
          have hTrue : (hd :: tl).all p = true := by simp [hp, htl2]
          simp [hTrue] at h
        | false => rfl
      obtain ⟨x, hx, hpx⟩ := ih htl
      exact ⟨x, List.mem_cons_of_mem hd hx, hpx⟩

theorem req_valid_answered : ValidAnswered step := by
  intro s r h
  simp only [step, h, dite_true]
  split
  · simp
  · simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_effects : Effects step := by
  intro s r h
  have hV : ValidQuery s r := by
    by_cases hv : ValidQuery s r
    · exact hv
    · exfalso; apply h; simp [step, hv]
  have hsimp : step s r = (if permittedB s.entries r then Outcome.granted else Outcome.denied, { s with log := s.log ++ [{ user := r.user, path := r.path, granted := permittedB s.entries r }] }) := by
    simp [step, hV]
  rw [hsimp] at h ⊢
  simp at h
  constructor
  · rfl
  constructor
  · rfl
  · cases hg : permittedB s.entries r <;> simp_all

theorem req_default_deny : DefaultDeny step := by
  intro s r hNo hGr
  have hO : (step s r).1 = if _h : ValidQuery s r then (if permittedB s.entries r then Outcome.granted else Outcome.denied) else Outcome.rejected := by
    unfold step; by_cases hv : ValidQuery s r <;> simp [hv]
  rw [hO] at hGr
  by_cases hv : ValidQuery s r
  · simp [hv] at hGr
    have hPT : permittedB s.entries r = true := by cases hb : permittedB s.entries r <;> simp_all
    have hHas : HasAllow s.entries r := by
      unfold permittedB at hPT
      rw [List.any_eq_true] at hPT
      obtain ⟨a, ha_mem, ha_cond⟩ := hPT
      simp only [Bool.and_eq_true] at ha_cond
      obtain ⟨⟨hmB, heq⟩, _⟩ := ha_cond
      have hm : Matches a r := (matchesB_true_iff_aux a r).mp hmB
      have heff : a.effect = Effect.allow := by cases he : a.effect <;> simp_all
      exact ⟨a, ha_mem, hm, heff⟩
    exact hNo hHas
  · simp [hv] at hGr

theorem req_deny_overrides : DenyOverrides step := by
  intro s r hOv hGr
  have hM : ∀ e, matchesB e r = true ↔ Matches e r := fun e => matchesB_true_iff_aux e r
  have hStep : (step s r).1 = if hv : ValidQuery s r then (if permittedB s.entries r then Outcome.granted else Outcome.denied) else Outcome.rejected := by
    unfold step; by_cases hv : ValidQuery s r <;> simp [hv]
  rw [hStep] at hGr
  by_cases hv : ValidQuery s r
  · simp [hv] at hGr
    have hPermTrue : permittedB s.entries r = true := by cases hb : permittedB s.entries r <;> simp_all
    have hPerm : Permitted s.entries r := by
      unfold permittedB at hPermTrue
      rw [List.any_eq_true] at hPermTrue
      obtain ⟨a, ha_mem, ha_cond⟩ := hPermTrue
      simp only [Bool.and_eq_true] at ha_cond
      obtain ⟨⟨hmB, heffB⟩, hallB⟩ := ha_cond
      have hm : Matches a r := (hM a).mp hmB
      have heff : a.effect = .allow := by cases he : a.effect <;> simp_all
      refine ⟨a, ha_mem, hm, heff, ?_⟩
      intro d hd hmD heD
      have hmBd : matchesB d r = true := (hM d).mpr hmD
      have heDb : decide (d.effect = .deny) = true := by simp [heD]
      rw [List.all_eq_true] at hallB
      have hdP := hallB d hd
      simp [hmBd, heDb] at hdP
      exact Nat.lt_of_lt_of_eq hdP rfl
    obtain ⟨a, ha_mem, hmA, heA, ha_dom⟩ := hPerm
    obtain ⟨d, hd_mem, hmD, heD, hd_dom⟩ := hOv
    have hle := hd_dom a ha_mem hmA heA
    have hlt := ha_dom d hd_mem hmD heD
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle hlt)
  · simp [hv] at hGr

theorem req_specific_allow : SpecificAllow step := by
  intro s r hV hP
  have hPB : permittedB s.entries r = true := permittedB_of_Permitted_aux s.entries r hP
  simp [step, hV, hPB]

theorem req_grant_justified : GrantJustified step := by
  intro s r hGr
  have hStep : (step s r).1 = if hv : ValidQuery s r then (if permittedB s.entries r then Outcome.granted else Outcome.denied) else Outcome.rejected := by
    unfold step; by_cases hv : ValidQuery s r <;> simp [hv]
  rw [hStep] at hGr
  by_cases hv : ValidQuery s r
  · simp [hv] at hGr
    have hPB : permittedB s.entries r = true := by cases hb : permittedB s.entries r <;> simp_all
    exact permittedB_true_implies_Permitted_aux s.entries r hPB
  · simp [hv] at hGr

theorem req_order_independent : OrderIndependent step := by
  intro s r l hperm
  have hPermB : permittedB l r = permittedB s.entries r := by
    have hIff1 : permittedB l r = true ↔ Permitted l r := ⟨permittedB_true_implies_Permitted_aux l r, permittedB_of_Permitted_aux l r⟩
    have hIff2 : permittedB s.entries r = true ↔ Permitted s.entries r := ⟨permittedB_true_implies_Permitted_aux s.entries r, permittedB_of_Permitted_aux s.entries r⟩
    have hPermIff : Permitted l r ↔ Permitted s.entries r := by
      constructor
      · intro h
        obtain ⟨a, ha1, hm, he, hdom⟩ := h
        have ha2 : a ∈ s.entries := hperm.mem_iff.mp ha1
        refine ⟨a, ha2, hm, he, ?_⟩
        intro d hd2 hmD heD
        have hd1 : d ∈ l := hperm.mem_iff.mpr hd2
        exact hdom d hd1 hmD heD
      · intro h
        obtain ⟨a, ha2, hm, he, hdom⟩ := h
        have ha1 : a ∈ l := hperm.mem_iff.mpr ha2
        refine ⟨a, ha1, hm, he, ?_⟩
        intro d hd1 hmD heD
        have hd2 : d ∈ s.entries := hperm.mem_iff.mp hd1
        exact hdom d hd2 hmD heD
    by_cases h1 : permittedB l r = true
    · have hp1 : Permitted l r := hIff1.mp h1
      have hp2 : Permitted s.entries r := hPermIff.mp hp1
      have h2 : permittedB s.entries r = true := hIff2.mpr hp2
      simp [h1, h2]
    · have h1f : permittedB l r = false := by cases hb : permittedB l r <;> simp_all
      by_cases h2 : permittedB s.entries r = true
      · have hp2 : Permitted s.entries r := hIff2.mp h2
        have hp1 : Permitted l r := hPermIff.mpr hp2
        have h1t : permittedB l r = true := hIff1.mpr hp1
        simp [h1t] at h1
      · have h2f : permittedB s.entries r = false := by cases hb : permittedB s.entries r <;> simp_all
        simp [h1f, h2f]
  simp only [step]
  have hV : ValidQuery { s with entries := l } r ↔ ValidQuery s r := by simp [ValidQuery]
  by_cases hv : ValidQuery s r
  · have hv2 : ValidQuery { s with entries := l } r := hV.mpr hv
    simp [hv, hv2, hPermB]
  · have hv2 : ¬ ValidQuery { s with entries := l } r := fun h => hv (hV.mp h)
    simp [hv, hv2]

theorem req_denial_explained : DenialExplained step := by
  intro s r hDen
  have hStepOut : (step s r).1 = if hv : ValidQuery s r then (if permittedB s.entries r then Outcome.granted else Outcome.denied) else Outcome.rejected := by
    unfold step; by_cases hv : ValidQuery s r <;> simp [hv]
  rw [hStepOut] at hDen
  by_cases hv : ValidQuery s r
  · simp [hv] at hDen
    have hPBf : permittedB s.entries r = false := by cases hb : permittedB s.entries r <;> simp_all
    have hHasB_eq : hasAllowB s.entries r = true ↔ HasAllow s.entries r := hasAllowB_true_iff s.entries r
    by_cases hHasB : hasAllowB s.entries r = true
    · right
      have hHas : HasAllow s.entries r := hHasB_eq.mp hHasB
      have hDom : ∀ a ∈ s.entries, Matches a r → a.effect = .allow → ∃ d ∈ s.entries, Matches d r ∧ d.effect = .deny ∧ depth a ≤ depth d := by
        intro a ha_mem hmA heA
        have hAnyFalse : s.entries.any (fun a => matchesB a r && decide (a.effect = .allow) && s.entries.all fun d => (!(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length))) = false := by
          unfold permittedB at hPBf; exact hPBf
        have hPredFalse : (matchesB a r && decide (a.effect = .allow) && s.entries.all fun d => (!(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length))) = false :=
          any_false_forall s.entries _ hAnyFalse a ha_mem
        have hmB : matchesB a r = true := (matchesB_true_iff_aux a r).mpr hmA
        have heB : decide (a.effect = .allow) = true := by simp [heA]
        have hAllFalse : (s.entries.all fun d => (!(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length))) = false := by
          have hEq : (matchesB a r && decide (a.effect = .allow) && s.entries.all fun d => (!(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length))) = ((s.entries.all fun d => (!(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length)))) := by simp [hmB, heB]
          rw [hEq] at hPredFalse
          exact hPredFalse
        obtain ⟨d, hd_mem, hd_false⟩ := all_false_exists s.entries _ hAllFalse
        have hOrFalse : (!(matchesB d r && decide (d.effect = .deny)) || decide (d.path.length < a.path.length)) = false := hd_false
        simp only [Bool.or_eq_false_iff] at hOrFalse
        obtain ⟨hNotMatchDenyFalse, hDepthFalse⟩ := hOrFalse
        have hMatchDenyTrue : (matchesB d r && decide (d.effect = .deny)) = true := by
          cases hc : (matchesB d r && decide (d.effect = .deny)) with
          | true => rfl
          | false => simp [hc] at hNotMatchDenyFalse
        simp only [Bool.and_eq_true] at hMatchDenyTrue
        obtain ⟨hmBd, heDb⟩ := hMatchDenyTrue
        have hmD : Matches d r := (matchesB_true_iff_aux d r).mp hmBd
        have heD : d.effect = .deny := by simp at heDb; exact heDb
        have hLe : depth a ≤ depth d := by
          unfold depth
          have hNotLt : ¬ d.path.length < a.path.length := by
            intro hlt
            have : decide (d.path.length < a.path.length) = true := by simp [hlt]
            simp [this] at hDepthFalse
          exact Nat.le_of_not_gt hNotLt
        exact ⟨d, hd_mem, hmD, heD, hLe⟩
      obtain ⟨a0, ha0_mem, hmA0, heA0⟩ := hHas
      obtain ⟨d0, hd0_mem, hmD0, heD0, _hle0⟩ := hDom a0 ha0_mem hmA0 heA0
      have hExistsDeny : ∃ d ∈ s.entries, Matches d r ∧ d.effect = .deny := ⟨d0, hd0_mem, hmD0, heD0⟩
      obtain ⟨dmax, hdmax_mem, hmDmax, heDmax, hmax_le⟩ := max_deny_exists2 s.entries r hExistsDeny
      refine ⟨dmax, hdmax_mem, hmDmax, heDmax, ?_⟩
      intro a ha_mem hmA heA
      obtain ⟨d, hd_mem, hmD, heD, hle⟩ := hDom a ha_mem hmA heA
      have hle2 : depth d ≤ depth dmax := hmax_le d hd_mem hmD heD
      exact Nat.le_trans hle hle2
    · left
      intro hHas
      have : hasAllowB s.entries r = true := hHasB_eq.mpr hHas
      simp [this] at hHasB
  · simp [hv] at hDen

end Acl
