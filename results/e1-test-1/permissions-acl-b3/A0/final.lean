import Acl.Spec
namespace Acl

instance decValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery
  infer_instance

private theorem decide_true_iff (P : Prop) [Decidable P] :
    (decide P = true) ↔ P := by
  cases h : decide P with
  | true =>
    have hp : P := of_decide_eq_true h
    simp [h, hp]
  | false =>
    have hn : ¬ P := of_decide_eq_false h
    simp [h, hn]

def prefixB (p q : Path) : Bool := decide (p <+: q)

theorem prefixB_correct (p q : Path) : (prefixB p q = true) ↔ p <+: q := by
  unfold prefixB
  exact decide_true_iff _

private theorem bool_and_eq_true (a b : Bool) :
    ((a && b) = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_or_eq_true (a b : Bool) :
    ((a || b) = true) ↔ (a = true ∨ b = true) := by
  cases a <;> cases b <;> decide

def matchesB (e : Entry) (r : Request) : Bool :=
  ((decide (e.subject = 0) || decide (e.subject = r.user)) && prefixB e.path r.path)

theorem matchesB_eq_true (e : Entry) (r : Request) :
    (matchesB e r = true) ↔ Matches e r := by
  unfold matchesB Matches
  rw [bool_and_eq_true]
  have hOr : ((decide (e.subject = 0) || decide (e.subject = r.user)) = true)
      ↔ (e.subject = 0 ∨ e.subject = r.user) := by
    rw [bool_or_eq_true, decide_true_iff, decide_true_iff]
  rw [hOr, prefixB_correct]

instance decMatches (e : Entry) (r : Request) : Decidable (Matches e r) :=
  decidable_of_iff (matchesB e r = true) (matchesB_eq_true e r)

-- Decidable universal: all matching denies are strictly less specific.
private def decAllDeny : (l : List Entry) → (r : Request) → (a : Entry) →
    Decidable (∀ d ∈ l, Matches d r → d.effect = Effect.deny → depth d < depth a)
  | [], _, _ => .isTrue (fun d h => absurd h (by simp))
  | d :: rest, r, a =>
    match decMatches d r with
    | .isFalse hmF =>
      match decAllDeny rest r a with
      | .isTrue ihT =>
        .isTrue (fun x hx hm he => by
          have hx2 : x = d ∨ x ∈ rest := List.mem_cons.mp hx
          cases hx2 with
          | inl heq =>
            subst heq
            exact absurd hm hmF
          | inr hmem =>
            exact ihT x hmem hm he)
      | .isFalse ihF =>
        .isFalse (fun hAll => ihF (fun x hmem hm he =>
          hAll x (List.mem_cons.mpr (Or.inr hmem)) hm he))
    | .isTrue hmT =>
      match decEq d.effect Effect.deny with
      | .isFalse heF =>
        match decAllDeny rest r a with
        | .isTrue ihT =>
          .isTrue (fun x hx hm he => by
            have hx2 : x = d ∨ x ∈ rest := List.mem_cons.mp hx
            cases hx2 with
            | inl heq =>
              subst heq
              exact absurd he heF
            | inr hmem =>
              exact ihT x hmem hm he)
        | .isFalse ihF =>
          .isFalse (fun hAll => ihF (fun x hmem hm he =>
            hAll x (List.mem_cons.mpr (Or.inr hmem)) hm he))
      | .isTrue heT =>
        match (inferInstance : Decidable (depth d < depth a)) with
        | .isFalse hlF =>
          .isFalse (fun hAll =>
            hlF (hAll d (List.mem_cons.mpr (Or.inl rfl)) hmT heT))
        | .isTrue hlT =>
          match decAllDeny rest r a with
          | .isTrue ihT =>
            .isTrue (fun x hx hm he => by
              have hx2 : x = d ∨ x ∈ rest := List.mem_cons.mp hx
              cases hx2 with
              | inl heq =>
                subst heq
                exact hlT
              | inr hmem =>
                exact ihT x hmem hm he)
          | .isFalse ihF =>
            .isFalse (fun hAll => ihF (fun x hmem hm he =>
              hAll x (List.mem_cons.mpr (Or.inr hmem)) hm he))

-- Decidable existential: some matching allow beats every matching deny.
private def decPermAux (full : List Entry) : (cur : List Entry) → (r : Request) →
    Decidable (∃ a ∈ cur, Matches a r ∧ a.effect = Effect.allow ∧
      ∀ d ∈ full, Matches d r → d.effect = Effect.deny → depth d < depth a)
  | [], _ => .isFalse (fun h => by
      obtain ⟨a, ha_mem, _⟩ := h
      cases ha_mem)
  | a :: rest, r =>
    match decPermAux full rest r with
    | .isTrue ihT =>
      .isTrue (by
        obtain ⟨x, hmem, hm, he, hall⟩ := ihT
        exact ⟨x, List.mem_cons.mpr (Or.inr hmem), hm, he, hall⟩)
    | .isFalse ihF =>
      match decMatches a r with
      | .isFalse hmF =>
        .isFalse (fun h => by
          obtain ⟨x, hx_mem, hx_m, hx_e, hx_all⟩ := h
          have hx2 : x = a ∨ x ∈ rest := List.mem_cons.mp hx_mem
          cases hx2 with
          | inl heq =>
            subst heq
            exact absurd hx_m hmF
          | inr hmem =>
            exact ihF ⟨x, hmem, hx_m, hx_e, hx_all⟩)
      | .isTrue hmT =>
        match decEq a.effect Effect.allow with
        | .isFalse heF =>
          .isFalse (fun h => by
            obtain ⟨x, hx_mem, hx_m, hx_e, hx_all⟩ := h
            have hx2 : x = a ∨ x ∈ rest := List.mem_cons.mp hx_mem
            cases hx2 with
            | inl heq =>
              subst heq
              exact absurd hx_e heF
            | inr hmem =>
              exact ihF ⟨x, hmem, hx_m, hx_e, hx_all⟩)
        | .isTrue heT =>
          match decAllDeny full r a with
          | .isFalse hdF =>
            .isFalse (fun h => by
              obtain ⟨x, hx_mem, hx_m, hx_e, hx_all⟩ := h
              have hx2 : x = a ∨ x ∈ rest := List.mem_cons.mp hx_mem
              cases hx2 with
              | inl heq =>
                subst heq
                exact hdF hx_all
              | inr hmem =>
                exact ihF ⟨x, hmem, hx_m, hx_e, hx_all⟩)
          | .isTrue hdT =>
            .isTrue ⟨a, List.mem_cons.mpr (Or.inl rfl), hmT, heT, hdT⟩

instance decPermitted (l : List Entry) (r : Request) : Decidable (Permitted l r) := by
  unfold Permitted
  exact decPermAux l l r

-- Deny wins ties: grant iff some allow is strictly more specific than every deny.
def step : Impl := fun s r =>
  if _hv : ValidQuery s r then
    if _hp : Permitted s.entries r then
      (Outcome.granted, { s with log := s.log ++ [⟨r.user, r.path, true⟩] })
    else
      (Outcome.denied, { s with log := s.log ++ [⟨r.user, r.path, false⟩] })
  else
    (Outcome.rejected, s)

private theorem permitted_hasAllow {l : List Entry} {r : Request}
    (h : Permitted l r) : HasAllow l r := by
  obtain ⟨a, ha_mem, ha_m, ha_e, _⟩ := h
  exact ⟨a, ha_mem, ha_m, ha_e⟩

private theorem mem_cons_cases {a e : Entry} {rest : List Entry}
    (h : a ∈ e :: rest) : a = e ∨ a ∈ rest :=
  List.mem_cons.mp h

private theorem exists_max_allow (l : List Entry) (r : Request) (h : HasAllow l r) :
    ∃ a ∈ l, Matches a r ∧ a.effect = .allow ∧
      ∀ b ∈ l, Matches b r → b.effect = .allow → depth b ≤ depth a := by
  induction l with
  | nil =>
    obtain ⟨a, ha_mem, _⟩ := h
    cases ha_mem
  | cons e rest ih =>
    by_cases he : Matches e r ∧ e.effect = .allow
    · by_cases hr : HasAllow rest r
      · obtain ⟨m, hm_mem, hm_match, hm_eff, hm_max⟩ := ih hr
        by_cases hle : depth e ≤ depth m
        · refine ⟨m, List.mem_cons.mpr (Or.inr hm_mem), hm_match, hm_eff, ?_⟩
          intro b hb hb_match hb_eff
          rcases mem_cons_cases hb with rfl | hmem
          · exact hle
          · exact hm_max b hmem hb_match hb_eff
        · refine ⟨e, List.mem_cons.mpr (Or.inl rfl), he.1, he.2, ?_⟩
          intro b hb hb_match hb_eff
          rcases mem_cons_cases hb with rfl | hmem
          · exact Nat.le_refl _
          · have h1 := hm_max b hmem hb_match hb_eff
            omega
      · refine ⟨e, List.mem_cons.mpr (Or.inl rfl), he.1, he.2, ?_⟩
        intro b hb hb_match hb_eff
        rcases mem_cons_cases hb with rfl | hmem
        · exact Nat.le_refl _
        · exfalso
          exact hr ⟨b, hmem, hb_match, hb_eff⟩
    · have hr : HasAllow rest r := by
        obtain ⟨x, hx_mem, hx_match, hx_eff⟩ := h
        rcases mem_cons_cases hx_mem with rfl | hmem
        · exfalso
          exact he ⟨hx_match, hx_eff⟩
        · exact ⟨x, hmem, hx_match, hx_eff⟩
      obtain ⟨m, hm_mem, hm_match, hm_eff, hm_max⟩ := ih hr
      refine ⟨m, List.mem_cons.mpr (Or.inr hm_mem), hm_match, hm_eff, ?_⟩
      intro b hb hb_match hb_eff
      rcases mem_cons_cases hb with rfl | hmem
      · exfalso
        exact he ⟨hb_match, hb_eff⟩
      · exact hm_max b hmem hb_match hb_eff

private theorem exists_max_deny (l : List Entry) (r : Request)
    (h : ∃ d ∈ l, Matches d r ∧ d.effect = .deny) :
    ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧
      ∀ b ∈ l, Matches b r → b.effect = .deny → depth b ≤ depth d := by
  induction l with
  | nil =>
    obtain ⟨a, ha_mem, _⟩ := h
    cases ha_mem
  | cons e rest ih =>
    by_cases he : Matches e r ∧ e.effect = .deny
    · by_cases hr : (∃ d ∈ rest, Matches d r ∧ d.effect = .deny)
      · obtain ⟨m, hm_mem, hm_match, hm_eff, hm_max⟩ := ih hr
        by_cases hle : depth e ≤ depth m
        · refine ⟨m, List.mem_cons.mpr (Or.inr hm_mem), hm_match, hm_eff, ?_⟩
          intro b hb hb_match hb_eff
          rcases mem_cons_cases hb with rfl | hmem
          · exact hle
          · exact hm_max b hmem hb_match hb_eff
        · refine ⟨e, List.mem_cons.mpr (Or.inl rfl), he.1, he.2, ?_⟩
          intro b hb hb_match hb_eff
          rcases mem_cons_cases hb with rfl | hmem
          · exact Nat.le_refl _
          · have h1 := hm_max b hmem hb_match hb_eff
            omega
      · refine ⟨e, List.mem_cons.mpr (Or.inl rfl), he.1, he.2, ?_⟩
        intro b hb hb_match hb_eff
        rcases mem_cons_cases hb with rfl | hmem
        · exact Nat.le_refl _
        · exfalso
          exact hr ⟨b, hmem, hb_match, hb_eff⟩
    · have hr : (∃ d ∈ rest, Matches d r ∧ d.effect = .deny) := by
        obtain ⟨x, hx_mem, hx_match, hx_eff⟩ := h
        rcases mem_cons_cases hx_mem with rfl | hmem
        · exfalso
          exact he ⟨hx_match, hx_eff⟩
        · exact ⟨x, hmem, hx_match, hx_eff⟩
      obtain ⟨m, hm_mem, hm_match, hm_eff, hm_max⟩ := ih hr
      refine ⟨m, List.mem_cons.mpr (Or.inr hm_mem), hm_match, hm_eff, ?_⟩
      intro b hb hb_match hb_eff
      rcases mem_cons_cases hb with rfl | hmem
      · exfalso
        exact he ⟨hb_match, hb_eff⟩
      · exact hm_max b hmem hb_match hb_eff

private theorem dichotomy {l : List Entry} {r : Request}
    (h : HasAllow l r) : Permitted l r ∨ Overridden l r := by
  obtain ⟨a_max, ha_mem, ha_match, ha_eff, ha_max⟩ := exists_max_allow l r h
  by_cases hd : (∃ d ∈ l, Matches d r ∧ d.effect = .deny)
  · obtain ⟨d_max, hd_mem, hd_match, hd_eff, hd_max⟩ := exists_max_deny l r hd
    by_cases hle : depth a_max ≤ depth d_max
    · right
      refine ⟨d_max, hd_mem, hd_match, hd_eff, ?_⟩
      intro a ha_mem2 ha_match2 ha_eff2
      have h1 := ha_max a ha_mem2 ha_match2 ha_eff2
      omega
    · left
      refine ⟨a_max, ha_mem, ha_match, ha_eff, ?_⟩
      intro d hd_mem2 hd_match2 hd_eff2
      have h1 := hd_max d hd_mem2 hd_match2 hd_eff2
      omega
  · left
    refine ⟨a_max, ha_mem, ha_match, ha_eff, ?_⟩
    intro d hd_mem2 hd_match2 hd_eff2
    exfalso
    exact hd ⟨d, hd_mem2, hd_match2, hd_eff2⟩

private theorem not_both {l : List Entry} {r : Request}
    (hp : Permitted l r) (ho : Overridden l r) : False := by
  obtain ⟨a, ha_mem, ha_m, ha_e, ha_all⟩ := hp
  obtain ⟨d, hd_mem, hd_m, hd_e, hd_all⟩ := ho
  have hlt := ha_all d hd_mem hd_m hd_e
  have hle := hd_all a ha_mem ha_m ha_e
  omega

private theorem step_fst_granted (s : State) (r : Request)
    (hv : ValidQuery s r) (hp : Permitted s.entries r) :
    (step s r).1 = Outcome.granted := by
  unfold step
  simp [hv, hp]

private theorem step_fst_denied (s : State) (r : Request)
    (hv : ValidQuery s r) (hp : ¬ Permitted s.entries r) :
    (step s r).1 = Outcome.denied := by
  unfold step
  simp [hv, hp]

private theorem step_fst_rejected (s : State) (r : Request)
    (hv : ¬ ValidQuery s r) :
    (step s r).1 = Outcome.rejected := by
  unfold step
  simp [hv]

private theorem step_eq_granted (s : State) (r : Request)
    (hv : ValidQuery s r) (hp : Permitted s.entries r) :
    step s r = (Outcome.granted, { s with log := s.log ++ [⟨r.user, r.path, true⟩] }) := by
  unfold step
  simp [hv, hp]

private theorem step_eq_denied (s : State) (r : Request)
    (hv : ValidQuery s r) (hp : ¬ Permitted s.entries r) :
    step s r = (Outcome.denied, { s with log := s.log ++ [⟨r.user, r.path, false⟩] }) := by
  unfold step
  simp [hv, hp]

private theorem step_eq_rejected (s : State) (r : Request)
    (hv : ¬ ValidQuery s r) :
    step s r = (Outcome.rejected, s) := by
  unfold step
  simp [hv]

private theorem perm_mem_iff {l₁ l₂ : List Entry} (h : l₁.Perm l₂) (x : Entry) :
    x ∈ l₁ ↔ x ∈ l₂ := by
  induction h with
  | nil =>
    exact Iff.rfl
  | cons y h ih =>
    constructor
    · intro hx
      cases List.mem_cons.mp hx with
      | inl heq => exact List.mem_cons.mpr (Or.inl heq)
      | inr hmem => exact List.mem_cons.mpr (Or.inr (ih.mp hmem))
    · intro hx
      cases List.mem_cons.mp hx with
      | inl heq => exact List.mem_cons.mpr (Or.inl heq)
      | inr hmem => exact List.mem_cons.mpr (Or.inr (ih.mpr hmem))
  | swap y z l =>
    constructor
    · intro hx
      cases List.mem_cons.mp hx with
      | inl heq =>
        exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl heq)))
      | inr hmem =>
        cases List.mem_cons.mp hmem with
        | inl heq2 =>
          exact List.mem_cons.mpr (Or.inl heq2)
        | inr hmem3 =>
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hmem3)))
    · intro hx
      cases List.mem_cons.mp hx with
      | inl heq =>
        exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl heq)))
      | inr hmem =>
        cases List.mem_cons.mp hmem with
        | inl heq2 =>
          exact List.mem_cons.mpr (Or.inl heq2)
        | inr hmem3 =>
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hmem3)))
  | trans h1 h2 ih1 ih2 =>
    exact Iff.trans ih1 ih2

theorem req_valid_answered : ValidAnswered step := by
  intro s r hv
  by_cases hp : Permitted s.entries r
  · rw [step_fst_granted s r hv hp]
    decide
  · rw [step_fst_denied s r hv hp]
    decide

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hn
  exact step_eq_rejected s r hn

theorem req_effects : Effects step := by
  intro s r hne
  by_cases hv : ValidQuery s r
  · by_cases hp : Permitted s.entries r
    · rw [step_eq_granted s r hv hp]
      refine ⟨rfl, rfl, ?_⟩
      simp
    · rw [step_eq_denied s r hv hp]
      refine ⟨rfl, rfl, ?_⟩
      simp
  · have h1 : (step s r).1 = Outcome.rejected := step_fst_rejected s r hv
    exact (hne h1).elim

theorem req_default_deny : DefaultDeny step := by
  intro s r hno hEq
  by_cases hv : ValidQuery s r
  · by_cases hp : Permitted s.entries r
    · exfalso
      exact hno (permitted_hasAllow hp)
    · have e := step_fst_denied s r hv hp
      rw [e] at hEq
      contradiction
  · have e := step_fst_rejected s r hv
    rw [e] at hEq
    contradiction

theorem req_deny_overrides : DenyOverrides step := by
  intro s r ho hEq
  by_cases hv : ValidQuery s r
  · by_cases hp : Permitted s.entries r
    · exfalso
      exact not_both hp ho
    · have e := step_fst_denied s r hv hp
      rw [e] at hEq
      contradiction
  · have e := step_fst_rejected s r hv
    rw [e] at hEq
    contradiction

theorem req_specific_allow : SpecificAllow step := by
  intro s r hv hp
  exact step_fst_granted s r hv hp

theorem req_grant_justified : GrantJustified step := by
  intro s r hEq
  by_cases hv : ValidQuery s r
  · by_cases hp : Permitted s.entries r
    · exact hp
    · have e := step_fst_denied s r hv hp
      rw [e] at hEq
      contradiction
  · have e := step_fst_rejected s r hv
    rw [e] at hEq
    contradiction

theorem req_order_independent : OrderIndependent step := by
  intro s r l hperm
  have hP : Permitted l r ↔ Permitted s.entries r := by
    constructor
    · intro hp
      obtain ⟨a, ha_mem, ha_m, ha_e, ha_all⟩ := hp
      have ha_mem2 : a ∈ s.entries := (perm_mem_iff hperm a).mp ha_mem
      refine ⟨a, ha_mem2, ha_m, ha_e, ?_⟩
      intro d hd_mem hd_m hd_e
      have hd_mem2 : d ∈ l := (perm_mem_iff hperm d).mpr hd_mem
      exact ha_all d hd_mem2 hd_m hd_e
    · intro hp
      obtain ⟨a, ha_mem, ha_m, ha_e, ha_all⟩ := hp
      have ha_mem2 : a ∈ l := (perm_mem_iff hperm a).mpr ha_mem
      refine ⟨a, ha_mem2, ha_m, ha_e, ?_⟩
      intro d hd_mem hd_m hd_e
      have hd_mem2 : d ∈ s.entries := (perm_mem_iff hperm d).mp hd_mem
      exact ha_all d hd_mem2 hd_m hd_e
  have hV : ValidQuery { s with entries := l } r ↔ ValidQuery s r := by
    simp [ValidQuery]
  by_cases hv : ValidQuery s r
  · have hv2 : ValidQuery { s with entries := l } r := hV.mpr hv
    by_cases hp : Permitted s.entries r
    · have hp2 : Permitted l r := hP.mpr hp
      have e1 : (step { s with entries := l } r).1 = Outcome.granted := by
        unfold step
        simp [hv2, hp2]
      have e2 : (step s r).1 = Outcome.granted := step_fst_granted s r hv hp
      rw [e1, e2]
    · have hp2 : ¬ Permitted l r := fun h => hp (hP.mp h)
      have e1 : (step { s with entries := l } r).1 = Outcome.denied := by
        unfold step
        simp [hv2, hp2]
      have e2 : (step s r).1 = Outcome.denied := step_fst_denied s r hv hp
      rw [e1, e2]
  · have hv2 : ¬ ValidQuery { s with entries := l } r := fun h => hv (hV.mp h)
    have e1 : (step { s with entries := l } r).1 = Outcome.rejected := by
      unfold step
      simp [hv2]
    have e2 : (step s r).1 = Outcome.rejected := step_fst_rejected s r hv
    rw [e1, e2]

theorem req_denial_explained : DenialExplained step := by
  intro s r hd
  by_cases hv : ValidQuery s r
  · by_cases hp : Permitted s.entries r
    · have e := step_fst_granted s r hv hp
      rw [e] at hd
      contradiction
    · by_cases hA : HasAllow s.entries r
      · right
        have h := dichotomy hA
        cases h with
        | inl hP => contradiction
        | inr hO => exact hO
      · left
        exact hA
  · have e := step_fst_rejected s r hv
    rw [e] at hd
    contradiction

end Acl
