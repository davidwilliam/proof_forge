import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by unfold ValidQuery; infer_instance
noncomputable instance instDecMatches (e : Entry) (r : Request) : Decidable (Matches e r) := Classical.propDecidable _
noncomputable instance instDecPermitted (l : List Entry) (r : Request) : Decidable (Permitted l r) := Classical.propDecidable _
noncomputable instance instDecHasAllow (l : List Entry) (r : Request) : Decidable (HasAllow l r) := Classical.propDecidable _
noncomputable instance instDecExistsDeny (l : List Entry) (r : Request) (n : Nat) : Decidable (∃ d ∈ l, Matches d r ∧ d.effect = Effect.deny ∧ n ≤ depth d) := Classical.propDecidable _

noncomputable def decision (l : List Entry) (r : Request) : Bool := decide (Permitted l r)

noncomputable def step : Impl := fun s r =>
  if _h : ValidQuery s r then
    ((if decision s.entries r then Outcome.granted else Outcome.denied),
     { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] })
  else (Outcome.rejected, s)

theorem overridden_not_permitted {l : List Entry} {r : Request} (h : Overridden l r) : ¬ Permitted l r := by
  intro hp
  obtain ⟨d, hdmem, hdmat, hdeff, hall⟩ := h
  obtain ⟨a, hamem, hamat, haeff, hall2⟩ := hp
  have hle : depth a ≤ depth d := hall a hamem hamat haeff
  have hlt : depth d < depth a := hall2 d hdmem hdmat hdeff
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle hlt)

theorem hasAllow_of_permitted {l : List Entry} {r : Request} (h : Permitted l r) : HasAllow l r := by
  obtain ⟨a, ha, hm, he, _⟩ := h
  exact ⟨a, ha, hm, he⟩

theorem not_permitted_of_not_hasAllow {l : List Entry} {r : Request} (h : ¬ HasAllow l r) : ¬ Permitted l r :=
  fun hp => h (hasAllow_of_permitted hp)

theorem exists_max_allow {l : List Entry} {r : Request} (hHas : HasAllow l r) : ∃ a₀ ∈ l, Matches a₀ r ∧ a₀.effect = Effect.allow ∧ ∀ a ∈ l, Matches a r → a.effect = Effect.allow → depth a ≤ depth a₀ := by
  induction l with
  | nil => simp [HasAllow] at hHas
  | cons hd tl ih =>
    by_cases hhd : Matches hd r ∧ hd.effect = Effect.allow
    · by_cases htl : HasAllow tl r
      · obtain ⟨a₁, ha₁, hm₁, he₁, hmax₁⟩ := ih htl
        by_cases hle : depth a₁ ≤ depth hd
        · exact ⟨hd, by simp, hhd.1, hhd.2, fun a ha hm he => by
            rcases List.mem_cons.mp ha with heq | hmem
            · subst heq; exact Nat.le_refl _
            · exact Nat.le_trans (hmax₁ a hmem hm he) hle⟩
        · exact ⟨a₁, List.mem_cons_of_mem _ ha₁, hm₁, he₁, fun a ha hm he => by
            rcases List.mem_cons.mp ha with heq | hmem
            · subst heq; exact Nat.le_of_not_le hle
            · exact hmax₁ a hmem hm he⟩
      · exact ⟨hd, by simp, hhd.1, hhd.2, fun a ha hm he => by
          rcases List.mem_cons.mp ha with heq | hmem
          · subst heq; exact Nat.le_refl _
          · exact absurd (⟨a, hmem, hm, he⟩ : HasAllow tl r) htl⟩
    · have htl : HasAllow tl r := by
        obtain ⟨a, ha, hm, he⟩ := hHas
        rcases List.mem_cons.mp ha with heq | hmem
        · subst heq; exact absurd ⟨hm, he⟩ hhd
        · exact ⟨a, hmem, hm, he⟩
      obtain ⟨a₁, ha₁, hm₁, he₁, hmax₁⟩ := ih htl
      exact ⟨a₁, List.mem_cons_of_mem _ ha₁, hm₁, he₁, fun a ha hm he => by
        rcases List.mem_cons.mp ha with heq | hmem
        · subst heq; exact absurd ⟨hm, he⟩ hhd
        · exact hmax₁ a hmem hm he⟩

theorem covering_of_max {l : List Entry} {r : Request} (hNotPerm : ¬ Permitted l r) {a₀ : Entry} (ha₀ : a₀ ∈ l) (hm₀ : Matches a₀ r) (he₀ : a₀.effect = Effect.allow) (hmax₀ : ∀ a ∈ l, Matches a r → a.effect = Effect.allow → depth a ≤ depth a₀) : ∃ d ∈ l, Matches d r ∧ d.effect = Effect.deny ∧ depth a₀ ≤ depth d := by
  by_cases hEx : ∃ d ∈ l, Matches d r ∧ d.effect = Effect.deny ∧ depth a₀ ≤ depth d
  · exact hEx
  · exfalso
    apply hNotPerm
    refine ⟨a₀, ha₀, hm₀, he₀, fun d hd hm he => ?_⟩
    have hNotLe : ¬ depth a₀ ≤ depth d := fun hle => hEx ⟨d, hd, hm, he, hle⟩
    exact Nat.lt_of_not_le hNotLe

theorem not_hasAllow_or_overridden_of_not_permitted {l : List Entry} {r : Request} (h : ¬ Permitted l r) (hHas : HasAllow l r) : Overridden l r := by
  obtain ⟨a₀, ha₀, hm₀, he₀, hmax₀⟩ := exists_max_allow (l:=l) (r:=r) hHas
  obtain ⟨d₀, hd₀, hmD₀, heD₀, hle₀⟩ := covering_of_max h ha₀ hm₀ he₀ hmax₀
  exact ⟨d₀, hd₀, hmD₀, heD₀, fun a ha hm he => Nat.le_trans (hmax₀ a ha hm he) hle₀⟩

theorem permitted_perm {l₁ l₂ : List Entry} (hperm : l₁.Perm l₂) (r : Request) : Permitted l₁ r ↔ Permitted l₂ r := by
  unfold Permitted
  constructor
  · rintro ⟨a, ha, hm, he, hall⟩
    exact ⟨a, hperm.mem_iff.mp ha, hm, he, fun d hd hm2 he2 => hall d (hperm.mem_iff.mpr hd) hm2 he2⟩
  · rintro ⟨a, ha, hm, he, hall⟩
    exact ⟨a, hperm.mem_iff.mpr ha, hm, he, fun d hd hm2 he2 => hall d (hperm.mem_iff.mp hd) hm2 he2⟩

theorem decision_perm {l₁ l₂ : List Entry} (hperm : l₁.Perm l₂) (r : Request) : decision l₁ r = decision l₂ r := by
  unfold decision
  have hiff := permitted_perm hperm r
  by_cases h : Permitted l₁ r <;> by_cases h2 : Permitted l₂ r <;> simp_all

theorem decision_true_iff (l : List Entry) (r : Request) : decision l r = true ↔ Permitted l r := by
  unfold decision; simp

theorem decision_false_iff (l : List Entry) (r : Request) : decision l r = false ↔ ¬ Permitted l r := by
  unfold decision; simp

theorem req_valid_answered : ValidAnswered step := by
  intro s r hv
  simp only [step, dif_pos hv]
  split
  · simp
  · simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hv
  simp only [step, dif_neg hv]

theorem req_effects : Effects step := by
  intro s r hrej
  have hv : ValidQuery s r := by
    by_cases h : ValidQuery s r
    · exact h
    · exfalso
      have : (step s r).1 = Outcome.rejected := by simp only [step, dif_neg h]
      rw [this] at hrej
      exact hrej rfl
  have h1 : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied := by simp only [step, dif_pos hv]
  have h2 : (step s r).2 = { s with log := s.log ++ [⟨r.user, r.path, decision s.entries r⟩] } := by simp only [step, dif_pos hv]
  have hg : decide ((step s r).1 = Outcome.granted) = decision s.entries r := by
    rw [h1]
    cases h : decision s.entries r <;> simp [h]
  rw [h2, hg]
  exact ⟨rfl, rfl, rfl⟩

theorem req_default_deny : DefaultDeny step := by
  intro s r hna hg
  by_cases hv : ValidQuery s r
  · have hf : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied := by simp only [step, dif_pos hv]
    rw [hf] at hg
    have hnp : ¬ Permitted s.entries r := not_permitted_of_not_hasAllow hna
    have hdec : decision s.entries r = false := (decision_false_iff _ _).mpr hnp
    simp [hdec] at hg
  · have hf : (step s r).1 = Outcome.rejected := by simp only [step, dif_neg hv]
    rw [hf] at hg
    simp at hg

theorem req_deny_overrides : DenyOverrides step := by
  intro s r hover hg
  by_cases hv : ValidQuery s r
  · have hf : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied := by simp only [step, dif_pos hv]
    rw [hf] at hg
    have hnp : ¬ Permitted s.entries r := overridden_not_permitted hover
    have hdec : decision s.entries r = false := (decision_false_iff _ _).mpr hnp
    simp [hdec] at hg
  · have hf : (step s r).1 = Outcome.rejected := by simp only [step, dif_neg hv]
    rw [hf] at hg
    simp at hg

theorem req_specific_allow : SpecificAllow step := by
  intro s r hv hperm
  have hf : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied := by simp only [step, dif_pos hv]
  rw [hf]
  have hdec : decision s.entries r = true := (decision_true_iff _ _).mpr hperm
  simp [hdec]

theorem req_grant_justified : GrantJustified step := by
  intro s r hg
  by_cases hv : ValidQuery s r
  · have hf : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied := by simp only [step, dif_pos hv]
    rw [hf] at hg
    have hdec : decision s.entries r = true := by
      cases h : decision s.entries r with
      | true => rfl
      | false => simp [h] at hg
    exact (decision_true_iff _ _).mp hdec
  · have hf : (step s r).1 = Outcome.rejected := by simp only [step, dif_neg hv]
    rw [hf] at hg
    simp at hg

theorem req_order_independent : OrderIndependent step := by
  intro s r l hperm
  have hiff : ValidQuery { s with entries := l } r ↔ ValidQuery s r := by
    constructor <;> intro h <;> unfold ValidQuery at * <;> simpa using h
  by_cases hv : ValidQuery s r
  · have hv2 : ValidQuery { s with entries := l } r := hiff.mpr hv
    have h1 : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied := by simp only [step, dif_pos hv]
    have h2 : (step { s with entries := l } r).1 = if decision l r then Outcome.granted else Outcome.denied := by simp only [step, dif_pos hv2]
    rw [h1, h2, decision_perm hperm r]
  · have hv2 : ¬ ValidQuery { s with entries := l } r := fun h => hv (hiff.mp h)
    have h1 : (step s r).1 = Outcome.rejected := by simp only [step, dif_neg hv]
    have h2 : (step { s with entries := l } r).1 = Outcome.rejected := by simp only [step, dif_neg hv2]
    rw [h1, h2]

theorem req_denial_explained : DenialExplained step := by
  intro s r hden
  by_cases hv : ValidQuery s r
  · have hf : (step s r).1 = if decision s.entries r then Outcome.granted else Outcome.denied := by simp only [step, dif_pos hv]
    rw [hf] at hden
    have hnp : ¬ Permitted s.entries r := by
      intro hp
      have hdec : decision s.entries r = true := (decision_true_iff _ _).mpr hp
      simp [hdec] at hden
    by_cases hHas : HasAllow s.entries r
    · exact Or.inr (not_hasAllow_or_overridden_of_not_permitted hnp hHas)
    · exact Or.inl hHas
  · have hf : (step s r).1 = Outcome.rejected := by simp only [step, dif_neg hv]
    rw [hf] at hden
    simp at hden

end Acl
