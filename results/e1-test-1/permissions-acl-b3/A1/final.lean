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
  | some a, some d => decide (d < a)
  | none, _ => false

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem dummy_prope : True := trivial
#check dummy_prope

theorem matchesB_iff (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  constructor
  · intro h
    have h1 : ((e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path) = true := h
    have hand := (Bool.and_eq_true_iff.mp h1)
    obtain ⟨hor, hpref⟩ := hand
    have hor' : (e.subject == 0 || e.subject == r.user) = true := hor
    have hpref' : e.path.isPrefixOf r.path = true := hpref
    have hp : e.path <+: r.path := (List.isPrefixOf_iff_prefix.mp hpref')
    constructor
    · have hOr := (Bool.or_eq_true_iff.mp hor')
      cases hOr with
      | inl h0 =>
        have := (beq_iff_eq.mp h0)
        exact Or.inl this
      | inr h1 =>
        have := (beq_iff_eq.mp h1)
        exact Or.inr this
    · exact hp
  · intro h
    obtain ⟨hsubj, hpref⟩ := h
    have hpref' : e.path.isPrefixOf r.path = true := (List.isPrefixOf_iff_prefix.mpr hpref)
    have hor : (e.subject == 0 || e.subject == r.user) = true := by
      have hOr := (Bool.or_eq_true_iff.mpr (hsubj.elim (fun hh => Or.inl (beq_iff_eq.mpr hh)) (fun hh => Or.inr (beq_iff_eq.mpr hh))))
      exact hOr
    exact (Bool.and_eq_true_iff.mpr ⟨hor, hpref'⟩)
#check @matchesB_iff

theorem filter_allow_mem2 (e : Entry) (r : Request) (l : List Entry) :
  e ∈ l.filter (fun e => matchesB e r && e.effect == .allow) ↔ e ∈ l ∧ Matches e r ∧ e.effect = .allow := by
  constructor
  · intro h
    have hp := (List.mem_filter.mp h)
    obtain ⟨hmem, hpred⟩ := hp
    have hand := (Bool.and_eq_true_iff.mp hpred)
    obtain ⟨hm, heff⟩ := hand
    have hMatches : Matches e r := (matchesB_iff e r).mp hm
    have heff' : e.effect = .allow := (beq_iff_eq.mp heff)
    exact ⟨hmem, hMatches, heff'⟩
  · intro h
    obtain ⟨hmem, hMatches, heff⟩ := h
    apply (List.mem_filter.mpr)
    constructor
    · exact hmem
    · have hm : matchesB e r = true := (matchesB_iff e r).mpr hMatches
      have heff' : (e.effect == .allow) = true := beq_iff_eq.mpr heff
      exact (Bool.and_eq_true_iff.mpr ⟨hm, heff'⟩)

def foldF (m : Option Nat) (e : Entry) : Option Nat :=
  some (max (m.getD 0) (depth e))

theorem foldF_comm_aux (m : Option Nat) (a b : Entry) :
    foldF (foldF m a) b = foldF (foldF m b) a := by
  unfold foldF
  simp only [Option.getD_some]
  have h : max (max (m.getD 0) (depth a)) (depth b)
         = max (max (m.getD 0) (depth b)) (depth a) := by
    rw [Nat.max_assoc, Nat.max_assoc, Nat.max_comm (depth a) (depth b)]
  rw [h]

theorem foldF_getD_thm (m : Option Nat) (e : Entry) : (foldF m e).getD 0 = max (m.getD 0) (depth e) := by unfold foldF; simp

theorem foldl_ge_base (L : List Entry) (m : Option Nat) : m.getD 0 ≤ (L.foldl foldF m).getD 0 := by
  induction L generalizing m with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    calc m.getD 0 ≤ (foldF m hd).getD 0 := by rw [foldF_getD_thm]; exact Nat.le_max_left _ _
      _ ≤ ((tl.foldl foldF (foldF m hd)).getD 0) := ih _

theorem foldl_mem_le (L : List Entry) (m : Option Nat) (e : Entry) (hmem : e ∈ L) : depth e ≤ (L.foldl foldF m).getD 0 := by
  induction L generalizing m with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.foldl_cons] at ⊢
    simp at hmem
    cases hmem with
    | inl heq =>
      rw [heq]
      calc depth hd ≤ (foldF m hd).getD 0 := by rw [foldF_getD_thm]; exact Nat.le_max_right _ _
        _ ≤ ((tl.foldl foldF (foldF m hd)).getD 0) := foldl_ge_base _ _
    | inr hmem2 => exact ih _ hmem2

theorem best_eq_foldF (eff : Effect) (r : Request) (l : List Entry) : best eff r l = ((l.filter (fun e => matchesB e r && e.effect == eff)).foldl foldF none) := by unfold best foldF; rfl

theorem foldl_some_preserved2 (L : List Entry) (n : Nat) : ∃ k, L.foldl foldF (some n) = some k := by
  induction L generalizing n with
  | nil => exact ⟨n, rfl⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hfold : foldF (some n) hd = some (max n (depth hd)) := by unfold foldF; simp
    rw [hfold]
    exact ih _

theorem filter_deny_mem2 (e : Entry) (r : Request) (l : List Entry) :
  e ∈ l.filter (fun e => matchesB e r && e.effect == .deny) ↔ e ∈ l ∧ Matches e r ∧ e.effect = .deny := by
  constructor
  · intro h
    have hp := (List.mem_filter.mp h)
    obtain ⟨hmem, hpred⟩ := hp
    have hand := (Bool.and_eq_true_iff.mp hpred)
    obtain ⟨hm, heff⟩ := hand
    exact ⟨hmem, (matchesB_iff e r).mp hm, (beq_iff_eq.mp heff)⟩
  · intro h
    obtain ⟨hmem, hMatches, heff⟩ := h
    apply (List.mem_filter.mpr)
    constructor
    · exact hmem
    · have hm : matchesB e r = true := (matchesB_iff e r).mpr hMatches
      have heff' : (e.effect == .deny) = true := beq_iff_eq.mpr heff
      exact (Bool.and_eq_true_iff.mpr ⟨hm, heff'⟩)

theorem tmp_check_bne (a b : Nat) (h : a ≠ b) : (a != b) = true := by
  simp [h]
#check bne_iff_ne
#check beq_iff_eq
#check ne_eq

theorem tmp_valid_contains (s : State) (r : Request) (hmem : r.user ∈ s.users) : s.users.contains r.user = true := by
  have h : s.users.contains r.user = decide (r.user ∈ s.users) := List.contains_eq_mem r.user s.users
  rw [h]
  simp [hmem]

theorem tmp_probe2 : (∀ (a : Nat), ¬ a ∈ ([1,2] : List Nat)) → ([1,2] : List Nat) = [] := by
  intro h
  have := List.eq_nil_iff_forall_not_mem.mpr h
  exact this
#check List.eq_nil_iff_forall_not_mem
#check List.mem_filter
#check Option.getD

theorem best_allow_none_of_no_allow (r : Request) (l : List Entry) (h : ¬ HasAllow l r) : best .allow r l = none := by
  unfold HasAllow at h
  have hmem : ∀ e, e ∉ l.filter (fun e => matchesB e r && e.effect == .allow) := by
    intro e he
    apply h
    have h2 := (filter_allow_mem2 e r l).mp he
    obtain ⟨hm, hM, hE⟩ := h2
    exact ⟨e, hm, hM, hE⟩
  have hnil : l.filter (fun e => matchesB e r && e.effect == .allow) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    exact hmem
  unfold best
  rw [hnil]
  rfl

theorem decision_false_of_no_allow3 (r : Request) (l : List Entry) (h : ¬ HasAllow l r) : decision l r = false := by
  have hb := best_allow_none_of_no_allow r l h
  simp [decision, hb]

theorem tmp_foo : True := trivial

theorem deny_fold_upper_thm (L : List Entry) (m : Option Nat) (B : Nat)
    (hB : ∀ e ∈ L, depth e ≤ B) : (L.foldl foldF m).getD 0 ≤ max (m.getD 0) B := by
  induction L generalizing m with
  | nil => simp; exact Nat.le_max_left _ _
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hd_le : depth hd ≤ B := hB hd (by simp)
    have h1 : (foldF m hd).getD 0 ≤ max (m.getD 0) B := by
      rw [foldF_getD_thm]
      omega
    have hB' : ∀ e ∈ tl, depth e ≤ B := fun e he => hB e (List.mem_cons_of_mem hd he)
    have ih' := ih (foldF m hd) hB'
    omega

theorem deny_fold_isSome_of_mem_thm (L : List Entry) (m : Option Nat) (e : Entry) (hm : e ∈ L) :
    ∃ k, L.foldl foldF m = some k := by
  induction L generalizing m with
  | nil => simp at hm
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    by_cases heq : hd = e
    · subst heq
      have h : foldF m hd = some ((foldF m hd).getD 0) := by
        unfold foldF
        simp
      rw [h]
      exact foldl_some_preserved2 _ _
    · have hmem : e ∈ tl := by
        simp at hm
        cases hm with
        | inl h => exact absurd h.symm heq
        | inr h => exact h
      exact ih _ hmem

theorem deny_best_deny_isSome_thm (r : Request) (l : List Entry) (d : Entry)
    (hd : d ∈ l.filter (fun e => matchesB e r && e.effect == .deny)) :
    ∃ kd, best .deny r l = some kd := by
  rw [best_eq_foldF]
  have h := deny_fold_isSome_of_mem_thm _ none d hd
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk⟩

theorem deny_step_granted_imp_decision_thm (s : State) (r : Request) (hg : (step s r).1 = .granted) :
    decision s.entries r = true := by
  unfold step at hg
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · rw [if_pos hc] at hg
    simp only at hg
    cases hgd : decision s.entries r with
    | true => rfl
    | false =>
      simp [hgd] at hg
  · rw [if_neg hc] at hg
    simp at hg

theorem req_specific_allow_aux_test : True := trivial
#check (inferInstance : Decidable (True))

theorem spec_allow_end_helper (s : State) (r : Request) (hc : (s.users.contains r.user && r.user != 0) = true) (hd : decision s.entries r = true) : (step s r).1 = .granted := by
  unfold step
  rw [if_pos hc]
  simp [hd]

theorem req_specific_allow2 : SpecificAllow step := by
  unfold SpecificAllow
  intro s r hValid hPerm
  obtain ⟨a, hamem, hMatch_a, hEff_a, hLt⟩ := hPerm
  have ha_filt : a ∈ s.entries.filter (fun e => matchesB e r && e.effect == .allow) := by
    rw [filter_allow_mem2]
    exact ⟨hamem, hMatch_a, hEff_a⟩
  have hbest_allow_eq : best .allow r s.entries =
      ((s.entries.filter (fun e => matchesB e r && e.effect == .allow)).foldl foldF none) := best_eq_foldF _ _ _
  have hallow_some : ∃ ka, best .allow r s.entries = some ka := by
    rw [hbest_allow_eq]
    exact deny_fold_isSome_of_mem_thm _ none a ha_filt
  obtain ⟨ka, hka⟩ := hallow_some
  have h_a_le_ka : depth a ≤ ka := by
    have hmem_le := foldl_mem_le (s.entries.filter (fun e => matchesB e r && e.effect == .allow)) none a ha_filt
    rw [← hbest_allow_eq, hka] at hmem_le
    simpa using hmem_le
  have hbest_deny_eq : best .deny r s.entries =
      ((s.entries.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none) := best_eq_foldF _ _ _
  have hdeny_lt : ∀ e ∈ s.entries.filter (fun e => matchesB e r && e.effect == .deny), depth e < depth a := by
    intro e he
    have h2 := (filter_deny_mem2 e r s.entries).mp he
    obtain ⟨hmem, hM, hE⟩ := h2
    exact hLt e hmem hM hE
  obtain ⟨hmemU, hneU⟩ := hValid
  have hc1 : s.users.contains r.user = true := tmp_valid_contains s r hmemU
  have hc2 : (r.user != 0) = true := tmp_check_bne r.user 0 hneU
  have hc : (s.users.contains r.user && r.user != 0) = true := by rw [hc1, hc2]; rfl
  have hdec_true : decision s.entries r = true := by
    unfold decision
    rw [hka]
    cases hkd : best .deny r s.entries with
    | none => rfl
    | some kd =>
      simp only
      have hfold_eq : ((s.entries.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none) = some kd := by
        rw [← hbest_deny_eq, hkd]
      have hkd_eq : kd = (((s.entries.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none).getD 0) := by
        rw [hfold_eq]; simp
      by_cases h0 : depth a = 0
      · exfalso
        have hempty : s.entries.filter (fun e => matchesB e r && e.effect == .deny) = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro e he
          have hlt := hdeny_lt e he
          omega
        rw [hempty] at hbest_deny_eq
        simp at hbest_deny_eq
        rw [hkd] at hbest_deny_eq
        contradiction
      · have hB : ∀ e ∈ s.entries.filter (fun e => matchesB e r && e.effect == .deny), depth e ≤ depth a - 1 := by
          intro e he
          have hlt := hdeny_lt e he
          omega
        have hupper := deny_fold_upper_thm (s.entries.filter (fun e => matchesB e r && e.effect == .deny)) none (depth a - 1) hB
        simp at hupper
        have hlt2 : kd < depth a := by omega
        have hdec2 : decide (kd < ka) = true := by simp; omega
        rw [hdec2]
  exact spec_allow_end_helper s r hc hdec_true

theorem grant_test_foo : True := trivial

theorem grant_fold_achieved_aux2 (L : List Entry) (m : Option Nat) :
    (L.foldl foldF m).getD 0 = m.getD 0 ∨ ∃ e ∈ L, depth e = (L.foldl foldF m).getD 0 := by
  induction L generalizing m with
  | nil => exact Or.inl rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hIH := ih (foldF m hd)
    cases hIH with
    | inl hEq =>
      have hFold : (foldF m hd).getD 0 = max (m.getD 0) (depth hd) := foldF_getD_thm m hd
      by_cases hle : depth hd ≤ m.getD 0
      · have hmax : max (m.getD 0) (depth hd) = m.getD 0 := Nat.max_eq_left hle
        have hm' : (foldF m hd).getD 0 = m.getD 0 := by
          rw [hFold, hmax]
        have hgoal : (tl.foldl foldF (foldF m hd)).getD 0 = m.getD 0 := by
          rw [hEq, hm']
        exact Or.inl hgoal
      · have hlt : m.getD 0 < depth hd := by omega
        have hmax : max (m.getD 0) (depth hd) = depth hd := Nat.max_eq_right (Nat.le_of_lt hlt)
        have hm' : (foldF m hd).getD 0 = depth hd := by
          rw [hFold, hmax]
        have hgoal : (tl.foldl foldF (foldF m hd)).getD 0 = depth hd := by
          rw [hEq, hm']
        have hmem : hd ∈ hd :: tl := List.mem_cons_self
        exact Or.inr ⟨hd, hmem, hgoal.symm⟩
    | inr hEx =>
      obtain ⟨e, hmem, heq⟩ := hEx
      exact Or.inr ⟨e, List.mem_cons_of_mem hd hmem, heq⟩

theorem grant_probe_ne (l : List Nat) (h : l ≠ []) : ∃ a, a ∈ l := by
  exact ⟨l.head h, List.head_mem h⟩

theorem grant_probe_cons (l : List Entry) (h : l ≠ []) : ∃ hd tl, l = hd :: tl := by
  exact List.exists_cons_of_ne_nil h

theorem grant_allow_achiever6 (r : Request) (l : List Entry) (ka : Nat)
    (hka : best .allow r l = some ka) :
    ∃ a ∈ l.filter (fun e => matchesB e r && e.effect == .allow), depth a = ka := by
  have hEq := best_eq_foldF .allow r l
  rw [hka] at hEq
  have hFold : ((l.filter (fun e => matchesB e r && e.effect == .allow)).foldl foldF none) = some ka := hEq.symm
  have hGet : (((l.filter (fun e => matchesB e r && e.effect == .allow)).foldl foldF none).getD 0) = ka := by
    simp [hFold]
  have hAch := grant_fold_achieved_aux2 (l.filter (fun e => matchesB e r && e.effect == .allow)) none
  have hAch2 : ((((l.filter (fun e => matchesB e r && e.effect == .allow)).foldl foldF none).getD 0) = 0) ∨
      (∃ e ∈ (l.filter (fun e => matchesB e r && e.effect == .allow)),
        depth e = (((l.filter (fun e => matchesB e r && e.effect == .allow)).foldl foldF none).getD 0)) := by
    simpa using hAch
  cases hAch2 with
  | inl h0 =>
    have hka0 : ka = 0 := by
      rw [← hGet]
      exact h0
    obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil (l := (l.filter (fun e => matchesB e r && e.effect == .allow))) (by
      intro hnil
      rw [hnil] at hFold
      simp at hFold)
    have hmem : hd ∈ l.filter (fun e => matchesB e r && e.effect == .allow) := by
      rw [hcons]
      exact List.mem_cons_self
    have hle := foldl_mem_le (l.filter (fun e => matchesB e r && e.effect == .allow)) none hd hmem
    rw [hFold] at hle
    simp at hle
    have hdepth : depth hd = ka := by omega
    exact ⟨hd, hmem, hdepth⟩
  | inr hEx =>
    obtain ⟨e, hmem, heq⟩ := hEx
    have heq2 : depth e = ka := by
      rw [heq, hGet]
    exact ⟨e, hmem, heq2⟩

theorem foldF_perm_aux {L1 L2 : List Entry} (h : L1.Perm L2) (m : Option Nat) :
    L1.foldl foldF m = L2.foldl foldF m := by
  induction h generalizing m with
  | nil => rfl
  | cons x h ih => simp only [List.foldl_cons]; exact ih _
  | swap x y l => simp only [List.foldl_cons]; rw [foldF_comm_aux]
  | trans h1 h2 ih1 ih2 => rw [ih1, ih2]
#check @foldF_perm_aux

theorem best_perm_thm (eff : Effect) (r : Request) {L1 L2 : List Entry} (h : L1.Perm L2) :
    best eff r L1 = best eff r L2 := by
  unfold best
  have hFilt : (L1.filter (fun e => matchesB e r && e.effect == eff)).Perm
      (L2.filter (fun e => matchesB e r && e.effect == eff)) := h.filter _
  exact foldF_perm_aux hFilt none

theorem decision_perm_thm (r : Request) {L1 L2 : List Entry} (h : L1.Perm L2) :
    decision L1 r = decision L2 r := by
  unfold decision
  rw [best_perm_thm .allow r h, best_perm_thm .deny r h]

theorem denial_deny_achiever_aux2 (r : Request) (l : List Entry) (kd : Nat)
    (hkd : best .deny r l = some kd) :
    ∃ e ∈ l.filter (fun e => matchesB e r && e.effect == .deny), depth e = kd := by
  have hEq := best_eq_foldF .deny r l
  rw [hkd] at hEq
  have hFold : ((l.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none) = some kd := hEq.symm
  have hGet : (((l.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none).getD 0) = kd := by
    simp [hFold]
  have hAch := grant_fold_achieved_aux2 (l.filter (fun e => matchesB e r && e.effect == .deny)) none
  have hAch2 : ((((l.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none).getD 0) = 0) ∨
      (∃ e ∈ (l.filter (fun e => matchesB e r && e.effect == .deny)),
        depth e = (((l.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none).getD 0)) := by
    simpa using hAch
  cases hAch2 with
  | inl h0 =>
    have hkd0 : kd = 0 := by rw [← hGet]; exact h0
    obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil (l := (l.filter (fun e => matchesB e r && e.effect == .deny))) (by
      intro hnil
      rw [hnil] at hFold
      simp at hFold)
    have hmem : hd ∈ l.filter (fun e => matchesB e r && e.effect == .deny) := by
      rw [hcons]; exact List.mem_cons_self
    have hle := foldl_mem_le (l.filter (fun e => matchesB e r && e.effect == .deny)) none hd hmem
    rw [hFold] at hle
    simp at hle
    have hdepth : depth hd = kd := by omega
    exact ⟨hd, hmem, hdepth⟩
  | inr hEx =>
    obtain ⟨e, hmem, heq⟩ := hEx
    have heq2 : depth e = kd := by rw [heq, hGet]
    exact ⟨e, hmem, heq2⟩

theorem denial_hdec_aux (s : State) (r : Request) (hc : (s.users.contains r.user && r.user != 0) = true)
    (hden : (step s r).1 = .denied) : decision s.entries r = false := by
  unfold step at hden
  rw [if_pos hc] at hden
  simp only at hden
  cases hgd : decision s.entries r
  · rfl
  · simp [hgd] at hden

theorem probe_dec_none (s : State) (r : Request) (hall : best .allow r s.entries = none) :
    decision s.entries r = false := by
  simp [decision, hall]

theorem req_valid_answered     : ValidAnswered step := by
  unfold ValidAnswered ValidQuery step
  intro s r h
  obtain ⟨hmem, hne⟩ := h
  have hc1 : s.users.contains r.user = true := tmp_valid_contains s r hmem
  have hc2 : (r.user != 0) = true := tmp_check_bne r.user 0 hne
  have hc : (s.users.contains r.user && r.user != 0) = true := by
    rw [hc1, hc2]; rfl
  rw [if_pos hc]
  cases hdec : decision s.entries r <;> simp

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop ValidQuery step
  intro s r h
  have hcond : ((s.users.contains r.user && r.user != 0) = true) -> False := by
    intro ht
    have hand := (Bool.and_eq_true_iff.mp ht)
    obtain ⟨hc1, hc2⟩ := hand
    have hmem : r.user ∈ s.users := by
      have heq : s.users.contains r.user = decide (r.user ∈ s.users) := List.contains_eq_mem r.user s.users
      rw [heq] at hc1
      exact of_decide_eq_true hc1
    have hne : r.user ≠ 0 := (bne_iff_ne.mp hc2)
    exact h ⟨hmem, hne⟩
  have hneg : ¬ ((s.users.contains r.user && r.user != 0) = true) := hcond
  rw [if_neg hneg]

theorem req_effects : Effects step := by
  intro s r h
  have hstep : step s r =
    (if s.users.contains r.user && r.user != 0 then
      let g := decision s.entries r
      (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
    else (.rejected, s)) := rfl
  rw [hstep] at h ⊢
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · rw [if_pos hc]
    refine ⟨rfl, rfl, ?_⟩
    cases hgd : decision s.entries r <;> simp_all
  · rw [if_neg hc] at h ⊢
    simp_all

theorem req_default_deny : DefaultDeny step := by
  unfold DefaultDeny
  intro s r h hg
  have hdec : decision s.entries r = false := decision_false_of_no_allow3 r s.entries h
  have h1 : (step s r).1 = .denied ∨ (step s r).1 = .rejected := by
    unfold step
    by_cases hc : (s.users.contains r.user && r.user != 0) = true
    · rw [if_pos hc]
      simp only
      rw [hdec]
      exact Or.inl rfl
    · rw [if_neg hc]
      exact Or.inr rfl
  cases h1 with
  | inl hd => rw [hd] at hg; contradiction
  | inr hr => rw [hr] at hg; contradiction

theorem req_deny_overrides : DenyOverrides step := by
  unfold DenyOverrides
  intro s r hOver hgrant
  obtain ⟨d, hdmem, hMatch_d, hEff_d, hLe⟩ := hOver
  have hd_filt : d ∈ s.entries.filter (fun e => matchesB e r && e.effect == .deny) := by
    rw [filter_deny_mem2]
    exact ⟨hdmem, hMatch_d, hEff_d⟩
  obtain ⟨kd, hkd⟩ := deny_best_deny_isSome_thm r s.entries d hd_filt
  have hdec_true : decision s.entries r = true := deny_step_granted_imp_decision_thm s r hgrant
  have hbest_allow_eq : best .allow r s.entries =
      ((s.entries.filter (fun e => matchesB e r && e.effect == .allow)).foldl foldF none) := best_eq_foldF _ _ _
  have hbest_deny_eq : best .deny r s.entries =
      ((s.entries.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none) := best_eq_foldF _ _ _
  have h_d_le_kd : depth d ≤ kd := by
    have hmem_le := foldl_mem_le (s.entries.filter (fun e => matchesB e r && e.effect == .deny)) none d hd_filt
    rw [← hbest_deny_eq, hkd] at hmem_le
    simpa using hmem_le
  cases hallow : best .allow r s.entries with
  | none =>
    simp [decision, hallow, hkd] at hdec_true
  | some ka =>
    simp [decision, hallow, hkd] at hdec_true
    have hLa_bound : ∀ e ∈ s.entries.filter (fun e => matchesB e r && e.effect == .allow), depth e ≤ depth d := by
      intro e he
      have h2 := (filter_allow_mem2 e r s.entries).mp he
      obtain ⟨hmem, hM, hE⟩ := h2
      exact hLe e hmem hM hE
    have hupper := deny_fold_upper_thm (s.entries.filter (fun e => matchesB e r && e.effect == .allow)) none (depth d) hLa_bound
    rw [← hbest_allow_eq, hallow] at hupper
    simp at hupper
    omega

theorem req_specific_allow     : SpecificAllow step := by
  unfold SpecificAllow
  intro s r hValid hPerm
  obtain ⟨a, hamem, hMatch_a, hEff_a, hLt⟩ := hPerm
  have ha_filt : a ∈ s.entries.filter (fun e => matchesB e r && e.effect == .allow) := by
    rw [filter_allow_mem2]
    exact ⟨hamem, hMatch_a, hEff_a⟩
  have hbest_allow_eq : best .allow r s.entries =
      ((s.entries.filter (fun e => matchesB e r && e.effect == .allow)).foldl foldF none) := best_eq_foldF _ _ _
  have hallow_some : ∃ ka, best .allow r s.entries = some ka := by
    rw [hbest_allow_eq]
    exact deny_fold_isSome_of_mem_thm _ none a ha_filt
  obtain ⟨ka, hka⟩ := hallow_some
  have h_a_le_ka : depth a ≤ ka := by
    have hmem_le := foldl_mem_le (s.entries.filter (fun e => matchesB e r && e.effect == .allow)) none a ha_filt
    rw [← hbest_allow_eq, hka] at hmem_le
    simpa using hmem_le
  have hbest_deny_eq : best .deny r s.entries =
      ((s.entries.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none) := best_eq_foldF _ _ _
  have hdeny_lt : ∀ e ∈ s.entries.filter (fun e => matchesB e r && e.effect == .deny), depth e < depth a := by
    intro e he
    have h2 := (filter_deny_mem2 e r s.entries).mp he
    obtain ⟨hmem, hM, hE⟩ := h2
    exact hLt e hmem hM hE
  obtain ⟨hmemU, hneU⟩ := hValid
  have hc1 : s.users.contains r.user = true := tmp_valid_contains s r hmemU
  have hc2 : (r.user != 0) = true := tmp_check_bne r.user 0 hneU
  have hc : (s.users.contains r.user && r.user != 0) = true := by rw [hc1, hc2]; rfl
  have hdec_true : decision s.entries r = true := by
    unfold decision
    rw [hka]
    cases hkd : best .deny r s.entries with
    | none => rfl
    | some kd =>
      simp only
      have hfold_eq : ((s.entries.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none) = some kd := by
        rw [← hbest_deny_eq, hkd]
      have hkd_eq : kd = (((s.entries.filter (fun e => matchesB e r && e.effect == .deny)).foldl foldF none).getD 0) := by
        rw [hfold_eq]; simp
      by_cases h0 : depth a = 0
      · exfalso
        have hempty : s.entries.filter (fun e => matchesB e r && e.effect == .deny) = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro e he
          have hlt := hdeny_lt e he
          omega
        rw [hempty] at hbest_deny_eq
        simp at hbest_deny_eq
        rw [hkd] at hbest_deny_eq
        contradiction
      · have hB : ∀ e ∈ s.entries.filter (fun e => matchesB e r && e.effect == .deny), depth e ≤ depth a - 1 := by
          intro e he
          have hlt := hdeny_lt e he
          omega
        have hupper := deny_fold_upper_thm (s.entries.filter (fun e => matchesB e r && e.effect == .deny)) none (depth a - 1) hB
        simp at hupper
        have hlt2 : kd < depth a := by omega
        have hdec2 : decide (kd < ka) = true := by simp; omega
        rw [hdec2]
  exact spec_allow_end_helper s r hc hdec_true

theorem req_grant_justified : GrantJustified step := by
  unfold GrantJustified
  intro s r hg
  have hdec : decision s.entries r = true := deny_step_granted_imp_decision_thm s r hg
  cases hall : best .allow r s.entries with
  | none =>
    have hfalse : decision s.entries r = false := probe_dec_none s r hall
    rw [hfalse] at hdec
    contradiction
  | some ka =>
    cases hkd : best .deny r s.entries with
    | none =>
      obtain ⟨a, haf_mem, hdepth_eq⟩ := grant_allow_achiever6 r s.entries ka hall
      have ha := (filter_allow_mem2 a r s.entries).mp haf_mem
      obtain ⟨hamem, hMatch_a, hEff_a⟩ := ha
      refine ⟨a, hamem, hMatch_a, hEff_a, ?_⟩
      intro d hdmem hMatch_d hEff_d
      have hdfilt : d ∈ s.entries.filter (fun e => matchesB e r && e.effect == .deny) := by
        rw [filter_deny_mem2]; exact ⟨hdmem, hMatch_d, hEff_d⟩
      have hsome : ∃ kd, best .deny r s.entries = some kd := by
        rw [best_eq_foldF]; exact deny_fold_isSome_of_mem_thm _ none d hdfilt
      obtain ⟨kd, hkd2⟩ := hsome
      rw [hkd] at hkd2
      contradiction
    | some kd =>
      have hdec2 : decision s.entries r = decide (kd < ka) := by unfold decision; rw [hall, hkd]
      rw [hdec2] at hdec
      have hlt : kd < ka := of_decide_eq_true hdec
      obtain ⟨a, haf_mem, hdepth_eq⟩ := grant_allow_achiever6 r s.entries ka hall
      have ha := (filter_allow_mem2 a r s.entries).mp haf_mem
      obtain ⟨hamem, hMatch_a, hEff_a⟩ := ha
      have hEqD := best_eq_foldF .deny r s.entries
      refine ⟨a, hamem, hMatch_a, hEff_a, ?_⟩
      intro d hdmem hMatch_d hEff_d
      have hdfilt : d ∈ s.entries.filter (fun e => matchesB e r && e.effect == .deny) := by
        rw [filter_deny_mem2]; exact ⟨hdmem, hMatch_d, hEff_d⟩
      have hmem_le := foldl_mem_le (s.entries.filter (fun e => matchesB e r && e.effect == .deny)) none d hdfilt
      rw [← hEqD, hkd] at hmem_le
      simp at hmem_le
      omega

theorem req_order_independent  : OrderIndependent step := by
  unfold OrderIndependent step
  intro s r l hPerm
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · have hc' : (({ s with entries := l }).users.contains r.user && r.user != 0) = true := by
      simp only [hc]
    rw [if_pos hc, if_pos hc']
    have hdec : decision l r = decision s.entries r := decision_perm_thm r hPerm
    simp only [hdec]
  · have hc' : ¬ ((({ s with entries := l }).users.contains r.user && r.user != 0) = true) := by
      simpa using hc
    rw [if_neg hc, if_neg hc']

theorem req_denial_explained : DenialExplained step := by
  unfold DenialExplained
  intro s r hden
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · have hdec : decision s.entries r = false := denial_hdec_aux s r hc hden
    cases hall : best .allow r s.entries with
    | none =>
      apply Or.inl
      intro hAllow
      obtain ⟨a, hamem, hMatch, hEff⟩ := hAllow
      have haf : a ∈ s.entries.filter (fun e => matchesB e r && e.effect == .allow) := by
        rw [filter_allow_mem2]; exact ⟨hamem, hMatch, hEff⟩
      have hsome : ∃ ka, best .allow r s.entries = some ka := by
        rw [best_eq_foldF]; exact deny_fold_isSome_of_mem_thm _ none a haf
      obtain ⟨ka, hka⟩ := hsome
      rw [hka] at hall; contradiction
    | some ka =>
      cases hkd : best .deny r s.entries with
      | none =>
        exfalso
        have htrue : decision s.entries r = true := by unfold decision; rw [hall, hkd]
        rw [htrue] at hdec; contradiction
      | some kd =>
        apply Or.inr
        have hle : ka ≤ kd := by
          have hdd2 : decision s.entries r = decide (kd < ka) := by unfold decision; rw [hall, hkd]
          rw [hdd2] at hdec
          have hnot : ¬ (kd < ka) := of_decide_eq_false hdec
          omega
        obtain ⟨e0, hmem0, hdepth0⟩ := denial_deny_achiever_aux2 r s.entries kd hkd
        have h0 := (filter_deny_mem2 e0 r s.entries).mp hmem0
        obtain ⟨hmem_e0, hMatch_e0, hEff_e0⟩ := h0
        refine ⟨e0, hmem_e0, hMatch_e0, hEff_e0, ?_⟩
        intro a hamem hMatch hEff
        have haf : a ∈ s.entries.filter (fun e => matchesB e r && e.effect == .allow) := by
          rw [filter_allow_mem2]; exact ⟨hamem, hMatch, hEff⟩
        have hEqA := best_eq_foldF .allow r s.entries
        have hle_a : depth a ≤ (((s.entries.filter (fun e => matchesB e r && e.effect == .allow)).foldl foldF none).getD 0) :=
          foldl_mem_le _ none a haf
        rw [← hEqA, hall] at hle_a
        simp at hle_a
        omega
  · have hstep : step s r = (.rejected, s) := by unfold step; rw [if_neg hc]
    have hfst : (step s r).1 = .rejected := by rw [hstep]
    rw [hfst] at hden; contradiction

end Acl
