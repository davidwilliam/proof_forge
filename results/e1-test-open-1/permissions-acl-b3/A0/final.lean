import Acl.Spec
namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by unfold ValidQuery; infer_instance
instance instDecidableMatches (e : Entry) (r : Request) : Decidable (Matches e r) := by unfold Matches; infer_instance
instance instDecidableHasAllow (l : List Entry) (r : Request) : Decidable (HasAllow l r) := by unfold HasAllow; infer_instance
instance instDecidableOverridden (l : List Entry) (r : Request) : Decidable (Overridden l r) := by unfold Overridden; infer_instance
instance instDecidablePermitted (l : List Entry) (r : Request) : Decidable (Permitted l r) := by unfold Permitted; infer_instance

def validB (s : State) (r : Request) : Bool := decide (ValidQuery s r)
def matchesB (e : Entry) (r : Request) : Bool := decide (Matches e r)
def decision (l : List Entry) (r : Request) : Bool := decide (Permitted l r)

theorem validB_true_iff (s : State) (r : Request) : validB s r = true ↔ ValidQuery s r := by simp [validB]
theorem validB_false_iff (s : State) (r : Request) : validB s r = false ↔ ¬ ValidQuery s r := by simp [validB]
theorem matchesB_true_iff (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by simp [matchesB]
theorem decision_true_iff (l : List Entry) (r : Request) : decision l r = true ↔ Permitted l r := by simp [decision]
theorem decision_false_iff (l : List Entry) (r : Request) : decision l r = false ↔ ¬ Permitted l r := by simp [decision]

def step : Impl := fun s r =>
  if validB s r then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem step_valid_eq (s : State) (r : Request) (h : ValidQuery s r) :
    step s r = ((if decision s.entries r then .granted else .denied),
                { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] }) := by
  unfold step; have hv : validB s r = true := (validB_true_iff s r).mpr h; simp [hv]

theorem step_valid_fst (s : State) (r : Request) (h : ValidQuery s r) :
    (step s r).1 = if decision s.entries r then .granted else .denied := by
  rw [step_valid_eq s r h]

theorem step_invalid_eq (s : State) (r : Request) (h : ¬ ValidQuery s r) :
    step s r = (.rejected, s) := by
  unfold step; have hv : validB s r = false := (validB_false_iff s r).mpr h; simp [hv]

def maxDenyOpt : List Entry → Request → Option Entry
| [], _ => none
| hd :: tl, r =>
  let t := maxDenyOpt tl r
  if (matchesB hd r && hd.effect == Effect.deny) then
    match t with
    | none => some hd
    | some q => if decide (depth q < depth hd) then some hd else some q
  else t

theorem maxDenyOpt_exists_aux (l : List Entry) (r : Request) :
    ∀ e ∈ l, Matches e r → e.effect = Effect.deny → ∃ e', maxDenyOpt l r = some e' := by
  induction l with
  | nil => intro e h _ _; simp at h
  | cons hd tl ih =>
    intro e hmem hm heff
    by_cases hc : (matchesB hd r && hd.effect == Effect.deny)
    · have h1 : maxDenyOpt (hd :: tl) r =
          match maxDenyOpt tl r with
          | none => some hd
          | some q => if decide (depth q < depth hd) then some hd else some q := by
        simp [maxDenyOpt, hc]
      rw [h1]
      cases ht : maxDenyOpt tl r with
      | none => exact ⟨hd, by simp [ht]⟩
      | some q => exact ⟨_, by simp [ht]; split <;> rfl⟩
    · have h1 : maxDenyOpt (hd :: tl) r = maxDenyOpt tl r := by simp [maxDenyOpt, hc]
      rw [h1]
      have hmem' : e = hd ∨ e ∈ tl := by simpa using hmem
      rcases hmem' with rfl | hmem2
      · have hmb : matchesB hd r = true := (matchesB_true_iff hd r).mpr hm
        have hcb : (hd.effect == Effect.deny) = true := by rw [heff]
        have : (matchesB hd r && hd.effect == Effect.deny) = true := by simp [hmb, hcb]
        simp [this] at hc
      · exact ih e hmem2 hm heff

theorem maxDenyOpt_exists_of_deny (l : List Entry) (r : Request) :
    (∃ d ∈ l, Matches d r ∧ d.effect = Effect.deny) → ∃ d, maxDenyOpt l r = some d := by
  intro h; rcases h with ⟨d, hd1, hm, he⟩; exact maxDenyOpt_exists_aux l r d hd1 hm he

theorem maxDenyOpt_mem (l : List Entry) (r : Request) (e : Entry)
    (h : maxDenyOpt l r = some e) : e ∈ l ∧ Matches e r ∧ e.effect = Effect.deny := by
  induction l generalizing e with
  | nil => simp [maxDenyOpt] at h
  | cons hd tl ih =>
    by_cases hc : (matchesB hd r && hd.effect == Effect.deny)
    · have h1 : maxDenyOpt (hd :: tl) r =
          match maxDenyOpt tl r with
          | none => some hd
          | some q => if decide (depth q < depth hd) then some hd else some q := by simp [maxDenyOpt, hc]
      rw [h1] at h
      cases ht : maxDenyOpt tl r with
      | none =>
        simp [ht] at h
        have heq : hd = e := Option.some_inj.mp h
        subst heq
        have hm : Matches hd r := (matchesB_true_iff hd r).mp (Bool.and_eq_true_iff.mp hc).1
        have he : hd.effect = Effect.deny := by
          have hx := (Bool.and_eq_true_iff.mp hc).2
          cases heq : hd.effect with
          | allow => simp_all
          | deny => rfl
        exact ⟨List.Mem.head tl, hm, he⟩
      | some q =>
        simp only [ht] at h
        split at h
        · have heq : hd = e := Option.some_inj.mp h
          subst heq
          have hm : Matches hd r := (matchesB_true_iff hd r).mp (Bool.and_eq_true_iff.mp hc).1
          have he : hd.effect = Effect.deny := by
            have hx := (Bool.and_eq_true_iff.mp hc).2
            cases heq : hd.effect with
            | allow => simp_all
            | deny => rfl
          exact ⟨List.Mem.head tl, hm, he⟩
        · have heq : q = e := Option.some_inj.mp h
          subst heq
          have heq2 : maxDenyOpt tl r = some e := ht
          have ihRes := ih _ heq2
          exact ⟨List.Mem.tail hd ihRes.1, ihRes.2.1, ihRes.2.2⟩
    · have h1 : maxDenyOpt (hd :: tl) r = maxDenyOpt tl r := by simp [maxDenyOpt, hc]
      rw [h1] at h
      have ihRes := ih _ h
      exact ⟨List.Mem.tail hd ihRes.1, ihRes.2.1, ihRes.2.2⟩

theorem maxDenyOpt_le (l : List Entry) (r : Request) :
    ∀ (d : Entry), maxDenyOpt l r = some d →
      ∀ (x : Entry), x ∈ l → Matches x r → x.effect = Effect.deny → depth x ≤ depth d := by
  induction l with
  | nil => intro d h; simp [maxDenyOpt] at h
  | cons hd0 tl ih =>
    intro d h x hx hm he
    by_cases hc : (matchesB hd0 r && hd0.effect == Effect.deny)
    · have h1 : maxDenyOpt (hd0 :: tl) r =
            match maxDenyOpt tl r with
            | none => some hd0
            | some q => if decide (depth q < depth hd0) then some hd0 else some q := by simp [maxDenyOpt, hc]
      rw [h1] at h
      cases ht : maxDenyOpt tl r with
      | none =>
        simp [ht] at h
        have heqd : hd0 = d := Option.some_inj.mp h
        subst heqd
        rcases (show x = hd0 ∨ x ∈ tl from by simpa using hx) with rfl | hmem2
        · exact Nat.le_refl _
        · exfalso
          have hex : ∃ y, maxDenyOpt tl r = some y := maxDenyOpt_exists_aux tl r x hmem2 hm he
          rcases hex with ⟨y, hy⟩; rw [ht] at hy; contradiction
      | some q =>
        simp only [ht] at h
        split at h
        · have heqd : hd0 = d := Option.some_inj.mp h
          subst heqd
          rcases (show x = hd0 ∨ x ∈ tl from by simpa using hx) with rfl | hmem2
          · exact Nat.le_refl _
          · have hle := ih q ht x hmem2 hm he
            have hlt : depth q < depth hd0 := of_decide_eq_true ‹_›
            exact Nat.le_trans hle (Nat.le_of_lt hlt)
        · have heqq : q = d := Option.some_inj.mp h
          subst heqq
          have heq : maxDenyOpt tl r = some d := ht
          rcases (show x = hd0 ∨ x ∈ tl from by simpa using hx) with rfl | hmem2
          · have hNotLt : ¬ depth q < depth hd0 := by intro hc2; simp [hc2] at ‹_›
            -- need to use original d before subst? We already subst q=d, need hNotLt with q=d
            -- use q=d now so goal depth hd0 ≤ depth d  i.e. depth hd0 ≤ depth q
            -- hNotLt is ¬ depth d < depth hd0  => depth hd0 ≤ depth d
            exact Nat.le_of_not_gt hNotLt
          · exact ih d heq x hmem2 hm he
    · have h1 : maxDenyOpt (hd0 :: tl) r = maxDenyOpt tl r := by simp [maxDenyOpt, hc]
      rw [h1] at h
      rcases (show x = hd0 ∨ x ∈ tl from by simpa using hx) with rfl | hmem2
      · exfalso
        have hmb : matchesB x r = true := (matchesB_true_iff x r).mpr hm
        have hcb : (x.effect == Effect.deny) = true := by simp [he]
        have : (matchesB hd0 r && hd0.effect == Effect.deny) = true := by
          have : hd0 = x := rfl; rw [this]; simp [hmb, hcb]
        simp [this] at hc
      · exact ih d h x hmem2 hm he

theorem req_valid_answered : ValidAnswered step := by
  intro s r hv
  have h := step_valid_fst s r hv
  rw [h]
  cases h2 : decision s.entries r <;> simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hv; exact step_invalid_eq s r hv

theorem req_effects : Effects step := by
  intro s r hne
  have hv : ValidQuery s r := by
    by_cases h : ValidQuery s r
    · exact h
    · have heq := step_invalid_eq s r h
      rw [heq] at hne; simp at hne
  have heq := step_valid_eq s r hv
  have hfst : (step s r).1 = if decision s.entries r then .granted else .denied := step_valid_fst s r hv
  have hsnd : (step s r).2 = { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] } := by rw [heq]
  constructor
  · rw [hsnd]
  constructor
  · rw [hsnd]
  · rw [hsnd]
    have hdec : decide ((if decision s.entries r then Outcome.granted else Outcome.denied) = Outcome.granted) = decision s.entries r := by
      cases h : decision s.entries r <;> simp [h]
    have h1 : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied := hfst
    calc s.log ++ [⟨r.user, r.path, decision s.entries r⟩]
        = s.log ++ [⟨r.user, r.path, decide ((if decision s.entries r then Outcome.granted else Outcome.denied) = Outcome.granted)⟩] := by rw [hdec]
      _ = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = Outcome.granted)⟩] := by rw [← h1]

theorem req_default_deny : DefaultDeny step := by
  intro s r hna hg
  have hv : ValidQuery s r := by
    by_cases h : ValidQuery s r
    · exact h
    · have heq := step_invalid_eq s r h; rw [heq] at hg; simp at hg
  have hf := step_valid_fst s r hv
  rw [hf] at hg
  cases hd : decision s.entries r with
  | true =>
    have hp := (decision_true_iff s.entries r).mp hd
    rcases hp with ⟨a, ha1, hm, heff, _⟩
    exact hna ⟨a, ha1, hm, heff⟩
  | false => simp [hd] at hg

theorem req_deny_overrides : DenyOverrides step := by
  intro s r hov hg
  have hv : ValidQuery s r := by
    by_cases h : ValidQuery s r
    · exact h
    · have heq := step_invalid_eq s r h; rw [heq] at hg; simp at hg
  have hf := step_valid_fst s r hv
  rw [hf] at hg
  cases hd : decision s.entries r with
  | true =>
    have hp := (decision_true_iff s.entries r).mp hd
    rcases hov with ⟨d, hd1, hmD, heD, hleD⟩
    rcases hp with ⟨a, ha1, hmA, heA, hltA⟩
    have h1 := hleD a ha1 hmA heA
    have h2 := hltA d hd1 hmD heD
    omega
  | false => simp [hd] at hg

theorem req_specific_allow : SpecificAllow step := by
  intro s r hv hp
  have hf := step_valid_fst s r hv; rw [hf]
  have ht : decision s.entries r = true := (decision_true_iff s.entries r).mpr hp
  simp [ht]

theorem req_grant_justified : GrantJustified step := by
  intro s r hg
  have hv : ValidQuery s r := by
    by_cases h : ValidQuery s r
    · exact h
    · have heq := step_invalid_eq s r h; rw [heq] at hg; simp at hg
  have hf := step_valid_fst s r hv; rw [hf] at hg
  cases hd : decision s.entries r with
  | true => exact (decision_true_iff s.entries r).mp hd
  | false => simp [hd] at hg

theorem req_order_independent : OrderIndependent step := by
  intro s r l hp
  have hv1 : ValidQuery s r ↔ ValidQuery { s with entries := l } r := by unfold ValidQuery; simp
  by_cases hv : ValidQuery s r
  · have hv2 : ValidQuery { s with entries := l } r := hv1.mp hv
    have hf1 := step_valid_fst s r hv
    have hf2 := step_valid_fst { s with entries := l } r hv2
    rw [hf1, hf2]; simp only
    have permEq : Permitted s.entries r ↔ Permitted l r := by
      unfold Permitted; constructor
      · intro h; rcases h with ⟨a, ha1, hm, he, hall⟩
        exact ⟨a, hp.symm.mem_iff.mp ha1, hm, he, fun d hd1 hm2 he2 => hall d (hp.symm.mem_iff.mpr hd1) hm2 he2⟩
      · intro h; rcases h with ⟨a, ha1, hm, he, hall⟩
        exact ⟨a, hp.mem_iff.mp ha1, hm, he, fun d hd1 hm2 he2 => hall d (hp.mem_iff.mpr hd1) hm2 he2⟩
    have h1 : decision s.entries r = true ↔ Permitted s.entries r := decision_true_iff s.entries r
    have h2 : decision l r = true ↔ Permitted l r := decision_true_iff l r
    by_cases hd : decision s.entries r = true
    · have hd2 : decision l r = true := h2.mpr (permEq.mp (h1.mp hd)); simp [hd, hd2]
    · have hdF : decision s.entries r = false := by simp_all
      have hnp1 : ¬ Permitted s.entries r := fun h => by have := h1.mpr h; contradiction
      have hnp2 : ¬ Permitted l r := fun h => hnp1 (permEq.mpr h)
      have hd2 : decision l r = false := (decision_false_iff l r).mpr hnp2; simp [hdF, hd2]
  · have hv2 : ¬ ValidQuery { s with entries := l } r := by rw [← hv1]; exact hv
    rw [step_invalid_eq s r hv, step_invalid_eq { s with entries := l } r hv2]

theorem req_denial_explained : DenialExplained step := by
  intro s r hden
  by_cases hv : ValidQuery s r
  · have hfst : (step s r).1 = (if decision s.entries r then Outcome.granted else Outcome.denied) := step_valid_fst s r hv
    rw [hfst] at hden
    have hdF : decision s.entries r = false := by
      cases h : decision s.entries r with
      | true => simp [h] at hden
      | false => rfl
    have hnp : ¬ Permitted s.entries r := (decision_false_iff s.entries r).mp hdF
    by_cases ha : HasAllow s.entries r
    · right
      have hExistsDeny : ∃ d ∈ s.entries, Matches d r ∧ d.effect = Effect.deny := by
        by_cases hex : ∃ d ∈ s.entries, Matches d r ∧ d.effect = Effect.deny
        · exact hex
        · exfalso
          have hnone' : ∀ d ∈ s.entries, Matches d r → d.effect = Effect.deny → False := by
            intro d hd hm he; apply hex; exact ⟨d, hd, hm, he⟩
          rcases ha with ⟨a, ha1, hmA, heA⟩
          have hall : ∀ d ∈ s.entries, Matches d r → d.effect = Effect.deny → depth d < depth a := by
            intro d hd hm he; exfalso; exact hnone' d hd hm he
          exact hnp ⟨a, ha1, hmA, heA, hall⟩
      obtain ⟨dmax, hdmaxEq⟩ := maxDenyOpt_exists_of_deny s.entries r hExistsDeny
      have hmemMax := (maxDenyOpt_mem s.entries r dmax hdmaxEq).1
      have hmMax := (maxDenyOpt_mem s.entries r dmax hdmaxEq).2.1
      have heMax := (maxDenyOpt_mem s.entries r dmax hdmaxEq).2.2
      refine ⟨dmax, hmemMax, hmMax, heMax, fun a ha1 hmA heA => ?_⟩
      by_cases hle : depth a ≤ depth dmax
      · exact hle
      · exfalso
        have hlt' : depth dmax < depth a := Nat.lt_of_not_ge hle
        have hall : ∀ d ∈ s.entries, Matches d r → d.effect = Effect.deny → depth d < depth a := by
          intro d hd hm he
          have hle2 := maxDenyOpt_le s.entries r dmax hdmaxEq d hd hm he
          exact Nat.lt_of_le_of_lt hle2 hlt'
        exact hnp ⟨a, ha1, hmA, heA, hall⟩
    · left; exact ha
  · have heq := step_invalid_eq s r hv
    have : (step s r).1 = Outcome.rejected := by rw [heq]
    rw [this] at hden; contradiction

end Acl
