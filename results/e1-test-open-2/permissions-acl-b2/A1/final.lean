import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance

def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def maxDepth (l : List Entry) : Nat :=
  l.foldl (fun acc e => max acc e.path.length) 0

def decision (l : List Entry) (r : Request) : Bool :=
  let allows := l.filter (fun e => matchesB e r && decide (e.effect = .allow))
  let denies := l.filter (fun e => matchesB e r && decide (e.effect = .deny))
  if allows.isEmpty then false
  else if denies.isEmpty then true
  else decide (maxDepth denies < maxDepth allows)

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem helper_maxDepth_cons3 (hd : Entry) (tl : List Entry) : maxDepth (hd :: tl) = max hd.path.length (maxDepth tl) := by
  unfold maxDepth
  simp only [List.foldl_cons]
  have key : ∀ (init : Nat) (l : List Entry), List.foldl (fun acc e => max acc e.path.length) (max init hd.path.length) l = max hd.path.length (List.foldl (fun acc e => max acc e.path.length) init l) := by
    intro init l
    induction l generalizing init with
    | nil => simp [Nat.max_comm]
    | cons y ys ih =>
      simp only [List.foldl_cons]
      calc List.foldl (fun acc e => max acc e.path.length) (max (max init hd.path.length) y.path.length) ys
          = List.foldl (fun acc e => max acc e.path.length) (max (max init y.path.length) hd.path.length) ys := by
            have : max (max init hd.path.length) y.path.length = max (max init y.path.length) hd.path.length := by
              simp [Nat.max_comm, Nat.max_left_comm]
            rw [this]
        _ = max hd.path.length (List.foldl (fun acc e => max acc e.path.length) (max init y.path.length) ys) := ih (max init y.path.length)
        _ = max hd.path.length (List.foldl (fun acc e => max acc e.path.length) init (y :: ys)) := by simp [List.foldl_cons]
  have h := key 0 tl
  simp at h
  exact h

theorem helper_maxDepth_le3 (l : List Entry) (e : Entry) : e ∈ l → e.path.length ≤ maxDepth l := by
  intro he
  induction l with
  | nil => simp at he
  | cons hd tl ih =>
    rcases List.mem_cons.mp he with rfl | hmem
    · rw [helper_maxDepth_cons3]; exact Nat.le_max_left _ _
    · rw [helper_maxDepth_cons3]; exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem helper_maxDepth_exists3 (l : List Entry) : l ≠ [] → ∃ e ∈ l, e.path.length = maxDepth l := by
  intro hne
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    by_cases htl : tl = []
    · subst htl
      exact ⟨hd, by simp, by rw [helper_maxDepth_cons3]; simp [maxDepth]⟩
    · have htl_ne : tl ≠ [] := htl
      obtain ⟨e0, he0, heq⟩ := ih htl_ne
      by_cases hle : decide (hd.path.length ≤ maxDepth tl) = true
      · have hle' : hd.path.length ≤ maxDepth tl := of_decide_eq_true hle
        refine ⟨e0, List.Mem.tail _ he0, ?_⟩
        rw [helper_maxDepth_cons3, Nat.max_eq_right hle', heq]
      · have hle_false : decide (hd.path.length ≤ maxDepth tl) = false := by
          cases hc : decide (hd.path.length ≤ maxDepth tl) <;> simp_all
        have hlt : maxDepth tl < hd.path.length := by
          have h' : ¬ hd.path.length ≤ maxDepth tl := by intro h; simp [h] at hle_false
          exact Nat.lt_of_not_ge h'
        refine ⟨hd, by simp, ?_⟩
        rw [helper_maxDepth_cons3, Nat.max_eq_left (Nat.le_of_lt hlt)]

private theorem test_search : True := by
  have h : [1,2].isPrefixOf [1,2,3] = true := by rfl
  trivial
-- check what lemmas exist

theorem matchesB_correct4 (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  simp

theorem mem_filter_matches_allow4 (l : List Entry) (r : Request) (e : Entry) :
  e ∈ l.filter (fun e => matchesB e r && decide (e.effect = .allow)) ↔ e ∈ l ∧ Matches e r ∧ e.effect = .allow := by
  simp [List.mem_filter, matchesB_correct4, Bool.and_eq_true, decide_eq_true_eq]

theorem mem_filter_matches_deny4 (l : List Entry) (r : Request) (e : Entry) :
  e ∈ l.filter (fun e => matchesB e r && decide (e.effect = .deny)) ↔ e ∈ l ∧ Matches e r ∧ e.effect = .deny := by
  simp [List.mem_filter, matchesB_correct4, Bool.and_eq_true, decide_eq_true_eq]

theorem maxDepth_le_of_forall_mem4 (l : List Entry) (M : Nat) (h : ∀ e ∈ l, e.path.length ≤ M) : maxDepth l ≤ M := by
  induction l with
  | nil => simp [maxDepth]
  | cons hd tl ih =>
    rw [helper_maxDepth_cons3]
    exact Nat.max_le.mpr ⟨h hd (by simp), ih (fun e he => h e (List.Mem.tail _ he))⟩

theorem maxDepth_allows_bound4 (l : List Entry) (r : Request) (d : Entry) (hall : ∀ a ∈ l, Matches a r → a.effect = .allow → depth a ≤ depth d) :
  maxDepth (l.filter (fun e => matchesB e r && decide (e.effect = .allow))) ≤ depth d := by
  apply maxDepth_le_of_forall_mem4
  intro e he
  have h := (mem_filter_matches_allow4 l r e).mp he
  exact hall e h.1 h.2.1 h.2.2

theorem perm_filter3 (p : Entry → Bool) {l₁ l₂ : List Entry} (h : l₁.Perm l₂) : (l₁.filter p).Perm (l₂.filter p) := by
  induction h with
  | nil => exact List.Perm.rfl
  | cons x _ ih =>
    by_cases hx : p x <;> simp [hx, ih]
  | swap x y l =>
    by_cases hx : p x <;> by_cases hy : p y <;> simp [hx, hy]
    · exact (List.Perm.swap x y (List.filter p l))
  | trans ha hb iha ihb => exact iha.trans ihb

theorem perm_isEmpty4 {l₁ l₂ : List Entry} (h : l₁.Perm l₂) : l₁.isEmpty = l₂.isEmpty := by
  have hlen : l₁.length = l₂.length := h.length_eq
  cases l₁ <;> cases l₂ <;> simp_all [List.isEmpty]

theorem perm_maxDepth4 {l₁ l₂ : List Entry} (h : l₁.Perm l₂) : maxDepth l₁ = maxDepth l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [helper_maxDepth_cons3, helper_maxDepth_cons3, ih]
  | swap x y l =>
      rw [helper_maxDepth_cons3, helper_maxDepth_cons3, helper_maxDepth_cons3, helper_maxDepth_cons3]
      simp only [Nat.max_comm, Nat.max_left_comm]
  | trans ha hb iha ihb => rw [iha, ihb]

theorem decision_perm4 {l₁ l₂ : List Entry} (h : l₁.Perm l₂) (r : Request) : decision l₁ r = decision l₂ r := by
  unfold decision
  have hA : (l₁.filter (fun e => matchesB e r && decide (e.effect = .allow))).Perm (l₂.filter (fun e => matchesB e r && decide (e.effect = .allow))) := perm_filter3 _ h
  have hD : (l₁.filter (fun e => matchesB e r && decide (e.effect = .deny))).Perm (l₂.filter (fun e => matchesB e r && decide (e.effect = .deny))) := perm_filter3 _ h
  have hAemp : (l₁.filter (fun e => matchesB e r && decide (e.effect = .allow))).isEmpty = (l₂.filter (fun e => matchesB e r && decide (e.effect = .allow))).isEmpty := perm_isEmpty4 hA
  have hDemp : (l₁.filter (fun e => matchesB e r && decide (e.effect = .deny))).isEmpty = (l₂.filter (fun e => matchesB e r && decide (e.effect = .deny))).isEmpty := perm_isEmpty4 hD
  by_cases hAE : (l₁.filter (fun e => matchesB e r && decide (e.effect = .allow))).isEmpty = true
  · have hAE2 : (l₂.filter (fun e => matchesB e r && decide (e.effect = .allow))).isEmpty = true := hAemp ▸ hAE
    simp [hAE, hAE2]
  · have hAE2 : (l₂.filter (fun e => matchesB e r && decide (e.effect = .allow))).isEmpty = false := by
      have h1 : (l₁.filter (fun e => matchesB e r && decide (e.effect = .allow))).isEmpty = false := by
        cases hc : (l₁.filter (fun e => matchesB e r && decide (e.effect = .allow))).isEmpty <;> simp_all
      exact hAemp ▸ h1
    simp only [hAE, hAE2, ↓reduceIte, Bool.false_eq_true]
    by_cases hDE : (l₁.filter (fun e => matchesB e r && decide (e.effect = .deny))).isEmpty = true
    · have hDE2 : (l₂.filter (fun e => matchesB e r && decide (e.effect = .deny))).isEmpty = true := hDemp ▸ hDE
      simp [hDE, hDE2]
    · have hDE2 : (l₂.filter (fun e => matchesB e r && decide (e.effect = .deny))).isEmpty = false := by
        have h1 : (l₁.filter (fun e => matchesB e r && decide (e.effect = .deny))).isEmpty = false := by
          cases hc : (l₁.filter (fun e => matchesB e r && decide (e.effect = .deny))).isEmpty <;> simp_all
        exact hDemp ▸ h1
      simp only [hDE, hDE2]
      have hmax : maxDepth (l₁.filter (fun e => matchesB e r && decide (e.effect = .deny))) = maxDepth (l₂.filter (fun e => matchesB e r && decide (e.effect = .deny))) := perm_maxDepth4 hD
      have hmax2 : maxDepth (l₁.filter (fun e => matchesB e r && decide (e.effect = .allow))) = maxDepth (l₂.filter (fun e => matchesB e r && decide (e.effect = .allow))) := perm_maxDepth4 hA
      simp [hmax, hmax2]

theorem helper_maxDepth_lt_of_forall_lt3 (l : List Entry) (M : Nat) (hne : l ≠ []) (h : ∀ e ∈ l, e.path.length < M) : maxDepth l < M := by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    rw [helper_maxDepth_cons3]
    have hhd : hd.path.length < M := h hd (by simp)
    by_cases htl_empty : tl = []
    · subst htl_empty
      simp [maxDepth] at *
      omega
    · have htl_ne : tl ≠ [] := htl_empty
      have htl_forall : ∀ e ∈ tl, e.path.length < M := fun e he => h e (List.Mem.tail _ he)
      have ih' : maxDepth tl < M := ih htl_ne htl_forall
      omega

theorem req_valid_answered : ValidAnswered step := by
  intro s r h
  have h1 : r.user ∈ s.users := h.1
  have h2 : r.user ≠ 0 := h.2
  unfold step
  simp [h1, h2]
  -- Now need to show if ... then granted else denied ≠ rejected
  by_cases hg : decision s.entries r = true
  · simp [hg]
  · simp [hg]

theorem req_invalid_noop       : InvalidNoop step := sorry

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  by_cases hv : s.users.contains r.user && r.user != 0
  · simp only [hv] at h ⊢
    simp at h ⊢
  · simp only [hv] at h
    simp at h

theorem req_default_deny : DefaultDeny step := by
  intro s r hNoAllow
  unfold step
  by_cases hv : s.users.contains r.user && r.user != 0
  · simp only [hv, ↓reduceIte]
    have hdec_false : decision s.entries r = false := by
      unfold decision
      have hallows_nil : List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he hfi
        have hb : (matchesB e r && decide (e.effect = .allow)) = true := hfi
        have h1 : matchesB e r = true := by
          have := Bool.and_eq_true_iff.mp hb; exact this.1
        have h2 : decide (e.effect = .allow) = true := by
          have := Bool.and_eq_true_iff.mp hb; exact this.2
        have hm : Matches e r := (matchesB_correct4 e r).mp h1
        have heq : e.effect = .allow := of_decide_eq_true h2
        exact hNoAllow ⟨e, he, hm, heq⟩
      simp [hallows_nil]
    simp only [hdec_false]
    simp
  · simp only [hv, ↓reduceIte]
    simp

theorem req_deny_overrides : DenyOverrides step := by
  intro s r ⟨d, hd_mem, hd_match, hd_eff, hd_max⟩
  unfold step
  by_cases hv : s.users.contains r.user && r.user != 0
  · simp only [hv, ↓reduceIte, ne_eq]
    have hdec_false : decision s.entries r = false := by
      unfold decision
      simp only
      by_cases hallows_empty : (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries).isEmpty = true
      · simp only [hallows_empty, ↓reduceIte]
      · simp only [hallows_empty, ↓reduceIte]
        have hden_mem : d ∈ List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries := by
          rw [mem_filter_matches_deny4]; exact ⟨hd_mem, hd_match, hd_eff⟩
        have hden_ne : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) ≠ [] :=
          List.ne_nil_of_mem hden_mem
        have hden_not_empty : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries).isEmpty = false := by
          simp [hden_ne]
        simp only [hden_not_empty, ↓reduceIte]
        -- decision = decide (maxDenies < maxAllows) . Show it's false.
        have h1 : maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries) ≤ depth d :=
          maxDepth_allows_bound4 s.entries r d hd_max
        have h2 : depth d ≤ maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) := by
          exact helper_maxDepth_le3 _ d hden_mem
        have hle : maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries) ≤ maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) := Nat.le_trans h1 h2
        have hnot : ¬ maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) < maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries) := by omega
        simp [hnot]
    simp [hdec_false]
  · simp only [hv, ↓reduceIte]
    simp

theorem req_specific_allow : SpecificAllow step := by
  intro s r hvalid hperm
  obtain ⟨a, ha_mem, ha_match, ha_eff, ha_spec⟩ := hperm
  have hmem : r.user ∈ s.users := hvalid.1
  have hne : r.user ≠ 0 := hvalid.2
  have hv : (s.users.contains r.user && r.user != 0) = true := by simp [List.contains_eq_mem, hmem, hne]
  unfold step
  simp only [hv, ↓reduceIte]
  suffices hdec : decision s.entries r = true by simp [hdec]
  unfold decision
  have ha_filt : a ∈ List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries := by
    rw [mem_filter_matches_allow4]; exact ⟨ha_mem, ha_match, ha_eff⟩
  have hallows_ne : List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries ≠ [] :=
    List.ne_nil_of_mem ha_filt
  have hallows_notEmpty : (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries).isEmpty = false := by
    simp [hallows_ne]
  simp only [hallows_notEmpty]
  by_cases hden_empty : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries).isEmpty = true
  · simp [hden_empty]
  · have hden_nf : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries).isEmpty = false := by
      have : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries).isEmpty = false := by
        cases h : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries).isEmpty <;> simp_all
      exact this
    simp only [hden_nf]
    have ha_le_max : a.path.length ≤ maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries) :=
      helper_maxDepth_le3 _ a ha_filt
    have hden_ne : List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries ≠ [] := by
      intro heq; simp [heq] at hden_nf
    have hmax_den_lt : maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) < a.path.length := by
      apply helper_maxDepth_lt_of_forall_lt3 _ a.path.length hden_ne
      intro e he
      have hmem2 := (mem_filter_matches_deny4 s.entries r e).mp he
      exact ha_spec e hmem2.1 hmem2.2.1 hmem2.2.2
    have hlt : maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) < maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries) := by omega
    simp [hlt]

theorem req_grant_justified : GrantJustified step := by
  intro s r hgranted
  unfold step at hgranted
  by_cases hv : s.users.contains r.user && r.user != 0
  · simp only [hv] at hgranted
    have hg : decision s.entries r = true := by
      cases hd : decision s.entries r with
      | true => rfl
      | false => simp [hd] at hgranted
    unfold decision at hg
    have hallows_notEmpty : (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries).isEmpty = false := by
      cases he : (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries).isEmpty with
      | true => simp [he] at hg
      | false => rfl
    have hallows_ne : (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries) ≠ [] := by
      intro heq; simp [heq] at hallows_notEmpty
    obtain ⟨a0, ha0_mem, ha0_eq⟩ := helper_maxDepth_exists3 _ hallows_ne
    have ha0_decomp := (mem_filter_matches_allow4 s.entries r a0).mp ha0_mem
    refine ⟨a0, ha0_decomp.1, ha0_decomp.2.1, ha0_decomp.2.2, ?_⟩
    intro d hd_mem hd_match hd_eff
    have hden_mem : d ∈ List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries := by
      rw [mem_filter_matches_deny4]; exact ⟨hd_mem, hd_match, hd_eff⟩
    have hden_ne : List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries ≠ [] := List.ne_nil_of_mem hden_mem
    have hden_notEmpty : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries).isEmpty = false := by simp [hden_ne]
    simp only [hallows_notEmpty, hden_notEmpty] at hg
    have hlt : maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) < maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries) := of_decide_eq_true hg
    rw [← ha0_eq] at hlt
    have hd_le : d.path.length ≤ maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) := helper_maxDepth_le3 _ d hden_mem
    show d.path.length < a0.path.length
    omega
  · have hvF : (s.users.contains r.user && r.user != 0) = false := by
      cases h : s.users.contains r.user && r.user != 0 <;> simp_all
    simp only [hvF] at hgranted
    simp at hgranted

theorem req_order_independent : OrderIndependent step := by
  intro s r l hperm
  unfold step
  simp only
  have hperm_symm : s.entries.Perm l := hperm.symm
  have hdec : decision s.entries r = decision l r := decision_perm4 hperm_symm r
  by_cases hmem : r.user ∈ s.users
  · by_cases hzero : r.user = 0
    · have hv : (s.users.contains r.user && r.user != 0) = false := by simp [List.contains_eq_mem, hmem, hzero]
      simp [hv, hmem, hzero, hdec]
    · have hv : (s.users.contains r.user && r.user != 0) = true := by simp [List.contains_eq_mem, hmem, hzero]
      have hv2 : r.user ∈ s.users ∧ r.user ≠ 0 := ⟨hmem, hzero⟩
      simp [hv, hv2, hdec]
  · by_cases hzero : r.user = 0
    · have hv : (s.users.contains r.user && r.user != 0) = false := by simp [List.contains_eq_mem, hzero]
      have hnot : ¬ (r.user ∈ s.users ∧ r.user ≠ 0) := by simp [hmem]
      simp [hv, hnot]
    · have hv : (s.users.contains r.user && r.user != 0) = false := by simp [List.contains_eq_mem, hmem]
      have hnot : ¬ (r.user ∈ s.users ∧ r.user ≠ 0) := by simp [hmem]
      simp [hv, hnot]

theorem req_denial_explained : DenialExplained step := by
  intro s r hden
  unfold step at hden
  by_cases hv : s.users.contains r.user && r.user != 0
  · simp only [hv] at hden
    have hdec_false : decision s.entries r = false := by
      cases hd : decision s.entries r with
      | true => simp [hd] at hden
      | false => rfl
    unfold decision at hdec_false
    by_cases hallows_empty : (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries).isEmpty = true
    · simp only [hallows_empty] at hdec_false
      left
      intro ⟨a, ha_mem, ha_match, ha_eq⟩
      have ha_filt : a ∈ List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries := by
        rw [mem_filter_matches_allow4]; exact ⟨ha_mem, ha_match, ha_eq⟩
      have hne : List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries ≠ [] := List.ne_nil_of_mem ha_filt
      simp [hne] at hallows_empty
    · have hallows_notEmpty : (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries).isEmpty = false := by
        cases h : (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries).isEmpty <;> simp_all
      simp only [hallows_notEmpty] at hdec_false
      right
      have hden_nemp : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) ≠ [] := by
        intro heq
        have h1 : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries).isEmpty = true := by simp [heq]
        simp [h1] at hdec_false
      have hden_notEmpty : (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries).isEmpty = false := by simp [hden_nemp]
      simp only [hden_notEmpty] at hdec_false
      have hge : ¬ (maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) < maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries)) := by
        intro hlt
        simp [hlt] at hdec_false
      have hle : maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries) ≤ maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) := by omega
      obtain ⟨d0, hd0_mem, hd0_eq⟩ := helper_maxDepth_exists3 _ hden_nemp
      have hd0_decomp := (mem_filter_matches_deny4 s.entries r d0).mp hd0_mem
      refine ⟨d0, hd0_decomp.1, hd0_decomp.2.1, hd0_decomp.2.2, ?_⟩
      intro a ha_mem ha_match ha_eff
      have ha_filt : a ∈ List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries := by
        rw [mem_filter_matches_allow4]; exact ⟨ha_mem, ha_match, ha_eff⟩
      have ha_le : a.path.length ≤ maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .allow)) s.entries) := helper_maxDepth_le3 _ a ha_filt
      have hd_eq : d0.path.length = maxDepth (List.filter (fun e => matchesB e r && decide (e.effect = .deny)) s.entries) := hd0_eq
      show depth a ≤ depth d0
      unfold depth
      omega
  · simp only [hv] at hden
    simp at hden

end Acl
