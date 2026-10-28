import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def maxDenyDepth (l : List Entry) (r : Request) : Option Nat :=
  ((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth).foldl (fun acc d => match acc with | none => some d | some m => some (Nat.max m d)) none

def permittedB (l : List Entry) (r : Request) : Bool :=
  match maxDenyDepth l r with
  | none => l.any (fun e => matchesB e r && decide (e.effect = .allow))
  | some m => l.any (fun e => matchesB e r && decide (e.effect = .allow) && decide (m < depth e))

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := permittedB s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem foo_test_thm : True := trivial

theorem mem_contains_true_aux2 : True := trivial

theorem t_and (a b : Bool) (h : (a && b) = true) : a = true ∧ b = true :=
  Bool.and_eq_true_iff.mp h

theorem t_cont (s : State) (r : Request) (h1 : s.users.contains r.user = true) : r.user ∈ s.users := by
  have hh := List.contains_eq_mem (a := r.user) (as := s.users)
  rw [h1] at hh
  exact of_decide_eq_true (Eq.symm hh)

theorem t_ne (n : Nat) (h2 : (n != 0) = true) : n ≠ 0 := by
  intro heq
  rw [heq] at h2
  simp at h2

theorem guard_true_valid2 (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = true) : ValidQuery s r := by
  have hh := t_and _ _ h
  constructor
  · exact t_cont s r hh.1
  · exact t_ne _ hh.2

theorem matchesB_true_iff_dd (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  rw [Bool.and_eq_true_iff]
  constructor
  · intro ⟨h1, h2⟩
    rw [Bool.or_eq_true_iff] at h1
    constructor
    · rcases h1 with h1 | h1
      · left; exact (beq_iff_eq.mp h1)
      · right; exact (beq_iff_eq.mp h1)
    · exact (List.isPrefixOf_iff_prefix.mp h2)
  · intro ⟨h1, h2⟩
    constructor
    · rw [Bool.or_eq_true_iff]
      rcases h1 with h1 | h1
      · left; exact (beq_iff_eq.mpr h1)
      · right; exact (beq_iff_eq.mpr h1)
    · exact (List.isPrefixOf_iff_prefix.mpr h2)

theorem allowPred_true_iff_dd (e : Entry) (r : Request) : ((matchesB e r && decide (e.effect = .allow)) = true) ↔ (Matches e r ∧ e.effect = .allow) := by
  rw [Bool.and_eq_true_iff, matchesB_true_iff_dd, decide_eq_true_eq]

theorem allowPred2_true_hasAllow_dd (e : Entry) (r : Request) (m : Nat) : ((matchesB e r && decide (e.effect = .allow) && decide (m < depth e)) = true) → (Matches e r ∧ e.effect = .allow) := by
  intro h
  rw [Bool.and_eq_true_iff] at h
  obtain ⟨h12, _⟩ := h
  rw [Bool.and_eq_true_iff] at h12
  obtain ⟨hm, hd⟩ := h12
  exact ⟨(matchesB_true_iff_dd e r).mp hm, (decide_eq_true_eq.mp hd)⟩

theorem permittedB_true_hasAllow_dd (l : List Entry) (r : Request) : permittedB l r = true → HasAllow l r := by
  cases hm : maxDenyDepth l r with
  | none =>
    have hsimp : permittedB l r = l.any (fun e => matchesB e r && decide (e.effect = .allow)) := by
      unfold permittedB; simp [hm]
    intro h
    rw [hsimp, List.any_eq_true] at h
    obtain ⟨e, hmem, hpred⟩ := h
    rw [allowPred_true_iff_dd] at hpred
    exact ⟨e, hmem, hpred.1, hpred.2⟩
  | some m =>
    have hsimp : permittedB l r = l.any (fun e => matchesB e r && decide (e.effect = .allow) && decide (m < depth e)) := by
      unfold permittedB; simp [hm]
    intro h
    rw [hsimp, List.any_eq_true] at h
    obtain ⟨e, hmem, hpred⟩ := h
    have hh := allowPred2_true_hasAllow_dd e r m hpred
    exact ⟨e, hmem, hh.1, hh.2⟩

theorem foldMax_some_le_aux : ∀ (xs : List Nat) (acc : Option Nat) (m : Nat), acc = some m → ∃ m', (xs.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) acc = some m') ∧ m ≤ m' := by
  intro xs
  induction xs with
  | nil =>
    intro acc m h
    rw [List.foldl_nil]
    exact ⟨m, h, Nat.le_refl _⟩
  | cons y ys ih =>
    intro acc m h
    simp only [List.foldl_cons]
    cases hacc : acc with
    | none =>
      rw [h] at hacc
      simp at hacc
    | some mm =>
      rw [h] at hacc
      simp at hacc
      subst hacc
      have h2 : (match (some m : Option Nat) with | none => some y | some mm => some (Nat.max mm y)) = some (Nat.max m y) := rfl
      -- apply ih
      have hh := ih (some (Nat.max m y)) (Nat.max m y) rfl
      obtain ⟨m', hm', hle⟩ := hh
      exact ⟨m', hm', Nat.le_trans (Nat.le_max_left m y) hle⟩

theorem testInd (xs : List Nat) (acc : Option Nat) : True := by
  induction xs generalizing acc with
  | nil => trivial
  | cons a b c => trivial

theorem testInd2 (xs : List Nat) (y : Nat) (hy : y ∈ xs) (acc : Option Nat) : True := by
  induction xs generalizing acc with
  | nil => trivial
  | cons hd tl ih =>
    have htest : hd = hd := rfl
    trivial

theorem probe_contains (a : Nat) (as : List Nat) : decide (a ∈ as) = as.contains a := by
  exact List.contains_eq_mem (a := a) (as := as)

theorem valid_guard_proof (s : State) (r : Request) (h : ValidQuery s r) : (s.users.contains r.user && r.user != 0) = true := by
  have hdec : decide (r.user ∈ s.users) = true := decide_eq_true h.1
  have hh := probe_contains r.user s.users
  rw [hdec] at hh
  have hcc : s.users.contains r.user = true := hh.symm
  have hnz : (r.user != 0) = true := by simp [h.2]
  rw [hcc, hnz, Bool.and_self]

theorem probe_any_true (l : List Entry) (p : Entry → Bool) (e : Entry) (hm : e ∈ l) (hp : p e = true) : l.any p = true := by
  rw [List.any_eq_true]
  exact ⟨e, hm, hp⟩

theorem gj_denyPred_iff (e : Entry) (r : Request) : ((matchesB e r && decide (e.effect = .deny)) = true) ↔ (Matches e r ∧ e.effect = .deny) := by
  rw [Bool.and_eq_true_iff, matchesB_true_iff_dd, decide_eq_true_eq]
#check @List.mem_filter
#check @List.mem_map

theorem gj_fold_some_never_none2 (xs : List Nat) (acc : Option Nat) (m : Nat) (hacc : acc = some m) : ∃ m', xs.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) acc = some m' := by
  induction xs generalizing m acc with
  | nil => simp [List.foldl_nil, hacc]
  | cons y ys ih =>
    simp only [List.foldl_cons]
    cases hacc2 : acc with
    | none => rw [hacc] at hacc2; simp at hacc2
    | some mm =>
      rw [hacc] at hacc2; simp at hacc2; subst hacc2
      exact ih (acc := (some (Nat.max m y))) (m := Nat.max m y) rfl

theorem gj_inj_probe (a b : Nat) (h : (some a : Option Nat) = some b) : a = b := by
  simpa using h

theorem gj_contra_probe (acc : Option Nat) (m0 : Nat) (hacc : acc = none) (hm0 : acc = some m0) : False := by
  rw [hacc] at hm0; cases hm0

theorem gj_maxFold_le7 : ∀ (xs : List Nat) (acc : Option Nat) (mfin : Nat),
  (xs.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) acc = some mfin) →
  ((∀ m0, acc = some m0 → m0 ≤ mfin) ∧ ∀ z ∈ xs, z ≤ mfin) := by
  intro xs
  induction xs with
  | nil =>
    intro acc mfin h
    simp [List.foldl_nil] at h
    constructor
    · intro m0 hm0; rw [hm0] at h; simp at h; rw [h]; exact Nat.le_refl _
    · intro z hz; simp at hz
  | cons hd tl ih =>
    intro acc mfin h
    simp only [List.foldl_cons] at h
    cases acc with
    | none =>
      simp at h
      have hIH := ih (some hd) mfin h
      obtain ⟨hle_acc, hle_mem⟩ := hIH
      constructor
      · intro m0 hm0; cases hm0
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hmem
        · exact hle_acc _ rfl
        · exact hle_mem _ hmem
    | some cur =>
      simp at h
      have hIH := ih (some (Nat.max cur hd)) mfin h
      obtain ⟨hle_acc, hle_mem⟩ := hIH
      have hmax_le : Nat.max cur hd ≤ mfin := hle_acc _ rfl
      have hd_le : hd ≤ mfin := Nat.le_trans (Nat.le_max_right cur hd) hmax_le
      have hcur_le : cur ≤ mfin := Nat.le_trans (Nat.le_max_left cur hd) hmax_le
      constructor
      · intro m1 hm1
        have heq : cur = m1 := gj_inj_probe cur m1 hm1
        rw [← heq]; exact hcur_le
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hmem
        · exact hd_le
        · exact hle_mem _ hmem

theorem oi_mem_aux3 : ∀ (xs : List Nat) (acc : Option Nat) (mfin : Nat),
  (xs.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) acc = some mfin) →
  ((acc = none → mfin ∈ xs) ∧ ∀ cur, acc = some cur → mfin = cur ∨ mfin ∈ xs) := by
  intro xs
  induction xs with
  | nil =>
    intro acc mfin h
    simp [List.foldl_nil] at h
    constructor
    · intro hnone
      rw [hnone] at h
      simp at h
    · intro cur hcur
      rw [hcur] at h
      simp at h
      rw [h]
      exact Or.inl rfl
  | cons hd tl ih =>
    intro acc mfin h
    simp only [List.foldl_cons] at h
    cases hacc : acc with
    | none =>
      have h2 : List.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) (some hd) tl = some mfin := by simpa [hacc] using h
      have hIH := ih (some hd) mfin h2
      obtain ⟨_, hmem⟩ := hIH
      constructor
      · intro _
        simp only [List.mem_cons]
        have hc := hmem hd rfl
        rcases hc with rfl | hmem2
        · exact Or.inl rfl
        · exact Or.inr hmem2
      · intro cur hcur
        cases hcur
    | some cur =>
      have h2 : List.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) (some (Nat.max cur hd)) tl = some mfin := by simpa [hacc] using h
      have hIH := ih (some (Nat.max cur hd)) mfin h2
      obtain ⟨_, hmem⟩ := hIH
      constructor
      · intro hnone
        cases hnone
      · intro cur2 hcur2
        have hsome : (some cur : Option Nat) = some cur2 := hacc ▸ hcur2
        have heq : cur = cur2 := Option.some_inj.mp hsome
        subst heq
        have hc := hmem (Nat.max cur hd) rfl
        simp only [List.mem_cons]
        rcases hc with heq2 | hmem2
        · have hle3 := Nat.le_total cur hd
          rcases hle3 with hle3 | hle3
          · have hmax : Nat.max cur hd = hd := Nat.max_eq_right hle3
            rw [heq2, hmax]
            exact Or.inr (Or.inl rfl)
          · have hmax : Nat.max cur hd = cur := Nat.max_eq_left hle3
            rw [heq2, hmax]
            exact Or.inl rfl
        · exact Or.inr (Or.inr hmem2)

theorem de_probe1 (s : State) (r : Request) (h : (step s r).1 = .denied) :
    (s.users.contains r.user && r.user != 0) = true := by
  unfold step at h
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · exact hc
  · rw [if_neg hc] at h
    simp at h

theorem de_probe2 (s : State) (r : Request) (h : (step s r).1 = .denied) :
    permittedB s.entries r = false := by
  unfold step at h
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · rw [if_pos hc] at h
    simp only at h
    cases hg : permittedB s.entries r
    · rfl
    · simp [hg] at h
  · rw [if_neg hc] at h
    simp at h

theorem de_tmp : True := trivial

theorem de_anyFalse_mem3 (l : List Entry) (p : Entry → Bool) (h : l.any p = false) (e : Entry) (hm : e ∈ l) : p e = false := by
  induction l with
  | nil => simp at hm
  | cons hd tl ih =>
    have hcons : (p hd || List.any tl p) = false := by simpa using h
    have hboth := Bool.or_eq_false_iff.mp hcons
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hmem
    · exact hboth.1
    · exact ih hboth.2 hmem

theorem de_allowFalse_of_anyFalse3 (l : List Entry) (r : Request)
    (h : l.any (fun e => matchesB e r && decide (e.effect = .allow)) = false) :
    ¬ HasAllow l r := by
  intro ⟨a, hmem, hM, heff⟩
  have hpred : (matchesB a r && decide (a.effect = .allow)) = true := by
    rw [Bool.and_eq_true_iff, matchesB_true_iff_dd, decide_eq_true_eq]
    exact ⟨hM, heff⟩
  have hf := de_anyFalse_mem3 l _ h a hmem
  rw [hpred] at hf
  cases hf

theorem de_memDeny_of_memMap3 (l : List Entry) (r : Request) (z : Nat)
    (hz : z ∈ ((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth)) :
    ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧ depth d = z := by
  obtain ⟨e, hmemF, rfl⟩ := List.mem_map.mp hz
  rw [List.mem_filter] at hmemF
  obtain ⟨hmem, hpred⟩ := hmemF
  have hpp := (gj_denyPred_iff e r).mp hpred
  exact ⟨e, hmem, hpp.1, hpp.2, rfl⟩

theorem de_maxMem3 (l : List Entry) (r : Request) (m : Nat)
    (hm : maxDenyDepth l r = some m) :
    m ∈ ((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) := by
  unfold maxDenyDepth at hm
  have hgen := oi_mem_aux3
    (((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth))
    (none : Option Nat) m hm
  exact (hgen.1 rfl)

theorem de_none_any3 (l : List Entry) (r : Request) (hm : maxDenyDepth l r = none) :
    permittedB l r = l.any (fun e => matchesB e r && decide (e.effect = .allow)) := by
  unfold permittedB
  simp [hm]

theorem de_some_any3 (l : List Entry) (r : Request) (m : Nat) (hm : maxDenyDepth l r = some m) :
    permittedB l r = l.any (fun e => matchesB e r && decide (e.effect = .allow) && decide (m < depth e)) := by
  unfold permittedB
  simp [hm]

theorem de_bound_of_anyFalse4 (l : List Entry) (r : Request) (m : Nat)
    (h : l.any (fun e => matchesB e r && decide (e.effect = .allow) && decide (m < depth e)) = false) :
    ∀ a ∈ l, Matches a r → a.effect = .allow → depth a ≤ m := by
  intro a hmem hM heff
  have h1 : matchesB a r = true := (matchesB_true_iff_dd a r).mpr hM
  have h2 : decide (a.effect = .allow) = true := decide_eq_true heff
  have hab : (matchesB a r && decide (a.effect = .allow)) = true := by
    rw [Bool.and_eq_true_iff]; exact ⟨h1, h2⟩
  have hf := de_anyFalse_mem3 l _ h a hmem
  have hdec : decide (m < depth a) = false := by
    rw [hab] at hf
    simpa using hf
  have hnot : ¬ (m < depth a) := of_decide_eq_false hdec
  omega

theorem do_beta_test (hd : Nat) (tl : List Nat) :
    List.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) (none : Option Nat) (hd :: tl) =
    List.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) (some hd) tl := by
  simp only [List.foldl_cons]

theorem do_mem_mapped (l : List Entry) (r : Request) (d : Entry) (hmem : d ∈ l) (hM : Matches d r) (heff : d.effect = .deny) :
    depth d ∈ ((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) := by
  apply List.mem_map.mpr
  refine ⟨d, ?_, rfl⟩
  rw [List.mem_filter]
  constructor
  · exact hmem
  · exact (gj_denyPred_iff d r).mpr ⟨hM, heff⟩

theorem do_fold_none_cons (hd : Nat) (tl : List Nat) (m' : Nat)
    (h : List.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) (some hd) tl = some m') :
    List.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) (none : Option Nat) (hd :: tl) = some m' := by
  have h2 := do_beta_test hd tl
  rw [h2]
  exact h

theorem do_max_some_of_mem (xs : List Nat) (z : Nat) (hz : z ∈ xs) :
    ∃ m', List.foldl (fun acc d => match acc with | none => some d | some mm => some (Nat.max mm d)) (none : Option Nat) xs = some m' := by
  cases xs with
  | nil => simp at hz
  | cons hd tl =>
    have hex := gj_fold_some_never_none2 tl (some hd) hd rfl
    obtain ⟨m', hm'⟩ := hex
    exact ⟨m', do_fold_none_cons hd tl m' hm'⟩

theorem do_step_granted_perm2 (s : State) (r : Request) (h : (step s r).1 = .granted) : permittedB s.entries r = true := by
  unfold step at h
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · rw [if_pos hc] at h
    simp only at h
    cases hg : permittedB s.entries r
    · simp [hg] at h
    · rfl
  · rw [if_neg hc] at h
    simp at h

theorem do_any_false_of_all_false2 (l : List Entry) (p : Entry → Bool) (h : ∀ e ∈ l, p e = false) : l.any p = false := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.any_cons]
    rw [h hd List.mem_cons_self]
    rw [ih (fun e hm => h e (List.mem_cons_of_mem hd hm))]
    rfl

theorem do_mapped_le2 (l : List Entry) (r : Request) (m : Nat) (hm : maxDenyDepth l r = some m) (z : Nat)
    (hz : z ∈ ((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth)) : z ≤ m := by
  unfold maxDenyDepth at hm
  have hgen := gj_maxFold_le7 (((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth)) (none : Option Nat) m hm
  exact hgen.2 z hz

theorem do_tmp_false (e : Entry) (r : Request) (hMr : ¬ Matches e r) : matchesB e r = false := by
  have hne : matchesB e r ≠ true := fun ht => hMr ((matchesB_true_iff_dd e r).mp ht)
  exact eq_false_of_ne_true hne

theorem do_tmp_dec (m n : Nat) (h : ¬ (m < n)) : decide (m < n) = false := by
  exact decide_eq_false h

theorem do_tmp_dec2 (e : Entry) (h : ¬ e.effect = .allow) : decide (e.effect = .allow) = false := by
  exact decide_eq_false h

theorem do_pred_false2 (l : List Entry) (r : Request) (m : Nat) (d : Entry) (hmemd : d ∈ l) (hMd : Matches d r) (heffd : d.effect = .deny)
    (hm : maxDenyDepth l r = some m) (hbound : ∀ a ∈ l, Matches a r → a.effect = .allow → depth a ≤ depth d) :
    ∀ e ∈ l, ((matchesB e r && decide (e.effect = .allow) && decide (m < depth e)) = false) := by
  intro e hmem
  by_cases hMr : Matches e r
  · by_cases hEr : e.effect = .allow
    · have hle : depth e ≤ depth d := hbound e hmem hMr hEr
      have hzd_le : depth d ≤ m := do_mapped_le2 l r m hm (depth d) (do_mem_mapped l r d hmemd hMd heffd)
      have hle2 : depth e ≤ m := Nat.le_trans hle hzd_le
      have hnot : ¬ (m < depth e) := Nat.not_lt_of_ge hle2
      have hdec : decide (m < depth e) = false := do_tmp_dec m (depth e) hnot
      simp [hdec]
    · have h2 : decide (e.effect = .allow) = false := do_tmp_dec2 e hEr
      have h1 : matchesB e r = true := (matchesB_true_iff_dd e r).mpr hMr
      simp [h1, h2]
  · have h1 : matchesB e r = false := do_tmp_false e r hMr
    simp [h1]

theorem oi_perm_mem_probe (l l' : List Entry) (h : l.Perm l') (e : Entry) : e ∈ l ↔ e ∈ l' := by
  exact h.mem_iff
#check @List.Perm.mem_iff

theorem oi_Permitted_perm_aux (l l' : List Entry) (r : Request) (hperm : l.Perm l') : Permitted l r → Permitted l' r := by
  intro ⟨a, hmem, hM, hE, hB⟩
  refine ⟨a, hperm.mem_iff.mp hmem, hM, hE, ?_⟩
  intro d hmemD hMD hED
  exact hB d (hperm.mem_iff.mpr hmemD) hMD hED

theorem oi_Permitted_perm_iff (l l' : List Entry) (r : Request) (hperm : l.Perm l') : Permitted l r ↔ Permitted l' r := by
  constructor
  · exact oi_Permitted_perm_aux l l' r hperm
  · exact oi_Permitted_perm_aux l' l r hperm.symm

theorem oi_permittedB_of_Permitted (l : List Entry) (r : Request) (hP : Permitted l r) : permittedB l r = true := by
  obtain ⟨a, hmemA, hMa, hEa, hBound⟩ := hP
  have hpredA : (matchesB a r && decide (a.effect = .allow)) = true := by
    rw [allowPred_true_iff_dd]
    exact ⟨hMa, hEa⟩
  cases hm : maxDenyDepth l r with
  | none =>
    have heq := de_none_any3 l r hm
    rw [heq]
    exact probe_any_true l _ a hmemA hpredA
  | some m =>
    have hmem_map : m ∈ ((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) :=
      de_maxMem3 l r m hm
    obtain ⟨d, hmemD, hMd, hEd, hdepth⟩ := de_memDeny_of_memMap3 l r m hmem_map
    have hlt : m < depth a := by
      rw [← hdepth]
      exact hBound d hmemD hMd hEd
    have hdec : decide (m < depth a) = true := decide_eq_true hlt
    have hpredA2 : ((matchesB a r && decide (a.effect = .allow) && decide (m < depth a)) = true) := by
      rw [Bool.and_eq_true_iff]
      exact ⟨hpredA, hdec⟩
    have heq := de_some_any3 l r m hm
    rw [heq]
    exact probe_any_true l _ a hmemA hpredA2

theorem oi_Permitted_of_permittedB (l : List Entry) (r : Request) (hperm : permittedB l r = true) : Permitted l r := by
  cases hm : maxDenyDepth l r with
  | none =>
    have heq := de_none_any3 l r hm
    rw [heq] at hperm
    obtain ⟨a, hmemA, hpredA⟩ := List.any_eq_true.mp hperm
    have ⟨hMA, hEA⟩ := (allowPred_true_iff_dd a r).mp hpredA
    refine ⟨a, hmemA, hMA, hEA, ?_⟩
    intro d hmemD hMD hED
    have hzin : depth d ∈ ((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) :=
      do_mem_mapped l r d hmemD hMD hED
    obtain ⟨m', hm'⟩ := do_max_some_of_mem (((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth)) (depth d) hzin
    have hm2 : maxDenyDepth l r = some m' := by unfold maxDenyDepth; exact hm'
    rw [hm] at hm2
    cases hm2
  | some m =>
    have heq := de_some_any3 l r m hm
    rw [heq] at hperm
    obtain ⟨a, hmemA, hpredA⟩ := List.any_eq_true.mp hperm
    have h12 : ((matchesB a r && decide (a.effect = .allow)) = true) ∧ (decide (m < depth a) = true) :=
      Bool.and_eq_true_iff.mp hpredA
    have ⟨hMA, hEA⟩ := (allowPred_true_iff_dd a r).mp h12.1
    have hlt : m < depth a := of_decide_eq_true h12.2
    refine ⟨a, hmemA, hMA, hEA, ?_⟩
    intro d hmemD hMD hED
    have hzin : depth d ∈ ((l.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) :=
      do_mem_mapped l r d hmemD hMD hED
    have hle : depth d ≤ m := do_mapped_le2 l r m hm (depth d) hzin
    omega

theorem oi_permittedB_true_iff (l : List Entry) (r : Request) : permittedB l r = true ↔ Permitted l r := by
  constructor
  · exact oi_Permitted_of_permittedB l r
  · exact oi_permittedB_of_Permitted l r

theorem oi_permittedB_perm_congr2 (l l' : List Entry) (r : Request) (hperm : l.Perm l') : permittedB l r = permittedB l' r := by
  have hiff1 := oi_permittedB_true_iff l r
  have hiff2 := oi_permittedB_true_iff l' r
  have hPiff := oi_Permitted_perm_iff l l' r hperm
  cases hb1 : permittedB l r <;> cases hb2 : permittedB l' r
  · rfl
  · have hP' : Permitted l' r := hiff2.mp hb2
    have hP : Permitted l r := hPiff.mpr hP'
    have hb1' := (hiff1.mpr hP)
    rw [hb1'] at hb1
    cases hb1
  · have hP : Permitted l r := hiff1.mp hb1
    have hP' : Permitted l r := hP
    have hP2 : Permitted l' r := hPiff.mp hP'
    have hb2' := (hiff2.mpr hP2)
    rw [hb2'] at hb2
    cases hb2
  · rfl

theorem req_valid_answered     : ValidAnswered step := by
  intro s r hV
  have hc : (s.users.contains r.user && r.user != 0) = true := valid_guard_proof s r hV
  unfold step
  rw [if_pos hc]
  simp only
  cases hg : permittedB s.entries r <;> simp

theorem req_invalid_noop       : InvalidNoop step := by
  intro s r hN
  unfold step
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · exfalso; exact hN (guard_true_valid2 s r hc)
  · rw [if_neg hc]

theorem req_effects : Effects step := by
  intro s r hne
  unfold step at hne ⊢
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · rw [if_pos hc] at hne ⊢
    cases hg : permittedB s.entries r <;> simp_all
  · rw [if_neg hc] at hne
    exact False.elim (hne rfl)

theorem req_default_deny : DefaultDeny step := by
  intro s r hNo hEq
  have hPerm : permittedB s.entries r = true := by
    unfold step at hEq
    by_cases hc : (s.users.contains r.user && r.user != 0) = true
    · rw [if_pos hc] at hEq
      simp only at hEq
      split at hEq
      · next h => exact h
      · next h => simp at hEq
    · rw [if_neg hc] at hEq
      simp at hEq
  exact hNo (permittedB_true_hasAllow_dd s.entries r hPerm)

theorem req_deny_overrides : DenyOverrides step := by
  intro s r hO hG
  obtain ⟨d, hmemd, hMd, heffd, hbound⟩ := hO
  have hzin : depth d ∈ ((s.entries.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) :=
    do_mem_mapped s.entries r d hmemd hMd heffd
  obtain ⟨m, hm⟩ := do_max_some_of_mem (((s.entries.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth)) (depth d) hzin
  have hm2 : maxDenyDepth s.entries r = some m := by unfold maxDenyDepth; exact hm
  have hperm_false : permittedB s.entries r = false := by
    have heq := de_some_any3 s.entries r m hm2
    rw [heq]
    exact do_any_false_of_all_false2 _ _ (do_pred_false2 s.entries r m d hmemd hMd heffd hm2 hbound)
  have hperm_true := do_step_granted_perm2 s r hG
  rw [hperm_false] at hperm_true
  cases hperm_true

theorem req_specific_allow     : SpecificAllow step := by
  intro s r hV hP
  obtain ⟨a, hmemA, hMa, hEa, hBound⟩ := hP
  have hguard : (s.users.contains r.user && r.user != 0) = true := valid_guard_proof s r hV
  have hperm : permittedB s.entries r = true := by
    have hpredA : (matchesB a r && decide (a.effect = .allow)) = true := by
      rw [allowPred_true_iff_dd]
      exact ⟨hMa, hEa⟩
    cases hm : maxDenyDepth s.entries r with
    | none =>
      have heq := de_none_any3 s.entries r hm
      rw [heq]
      exact probe_any_true s.entries _ a hmemA hpredA
    | some m =>
      have hmem_map : m ∈ ((s.entries.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) :=
        de_maxMem3 s.entries r m hm
      obtain ⟨d, hmemD, hMd, hEd, hdepth⟩ := de_memDeny_of_memMap3 s.entries r m hmem_map
      have hlt : m < depth a := by
        rw [← hdepth]
        exact hBound d hmemD hMd hEd
      have hdec : decide (m < depth a) = true := decide_eq_true hlt
      have hpredA2 : ((matchesB a r && decide (a.effect = .allow) && decide (m < depth a)) = true) := by
        rw [Bool.and_eq_true_iff]
        exact ⟨hpredA, hdec⟩
      have heq := de_some_any3 s.entries r m hm
      rw [heq]
      exact probe_any_true s.entries _ a hmemA hpredA2
  unfold step
  rw [if_pos hguard]
  simp only
  rw [hperm]
  rfl

theorem req_grant_justified    : GrantJustified step := by
  intro s r hG
  have hperm : permittedB s.entries r = true := do_step_granted_perm2 s r hG
  cases hm : maxDenyDepth s.entries r with
  | none =>
    have heq := de_none_any3 s.entries r hm
    rw [heq] at hperm
    obtain ⟨a, hmemA, hpredA⟩ := List.any_eq_true.mp hperm
    have ⟨hMA, hEA⟩ := (allowPred_true_iff_dd a r).mp hpredA
    refine ⟨a, hmemA, hMA, hEA, ?_⟩
    intro d hmemD hMD hED
    have hzin : depth d ∈ ((s.entries.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) :=
      do_mem_mapped s.entries r d hmemD hMD hED
    obtain ⟨m', hm'⟩ := do_max_some_of_mem (((s.entries.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth)) (depth d) hzin
    have hm2 : maxDenyDepth s.entries r = some m' := by unfold maxDenyDepth; exact hm'
    rw [hm] at hm2
    cases hm2
  | some m =>
    have heq := de_some_any3 s.entries r m hm
    rw [heq] at hperm
    obtain ⟨a, hmemA, hpredA⟩ := List.any_eq_true.mp hperm
    have h12 : ((matchesB a r && decide (a.effect = .allow)) = true) ∧ (decide (m < depth a) = true) :=
      Bool.and_eq_true_iff.mp hpredA
    have ⟨hMA, hEA⟩ := (allowPred_true_iff_dd a r).mp h12.1
    have hlt : m < depth a := of_decide_eq_true h12.2
    refine ⟨a, hmemA, hMA, hEA, ?_⟩
    intro d hmemD hMD hED
    have hzin : depth d ∈ ((s.entries.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) :=
      do_mem_mapped s.entries r d hmemD hMD hED
    have hle : depth d ≤ m := do_mapped_le2 s.entries r m hm (depth d) hzin
    omega

theorem req_order_independent  : OrderIndependent step := by
  intro s r l hperm
  unfold step
  have hguard : (({ s with entries := l } : State).users.contains r.user && r.user != 0) = (s.users.contains r.user && r.user != 0) := by
    simp
  rw [hguard]
  by_cases hc : (s.users.contains r.user && r.user != 0) = true
  · rw [if_pos hc, if_pos hc]
    have hpb : permittedB l r = permittedB s.entries r := oi_permittedB_perm_congr2 l s.entries r hperm
    simp only
    rw [hpb]
  · rw [if_neg hc, if_neg hc]

theorem req_denial_explained   : DenialExplained step := by
  intro s r hDen
  have hperm : permittedB s.entries r = false := de_probe2 s r hDen
  cases hm : maxDenyDepth s.entries r with
  | none =>
    have heq := de_none_any3 s.entries r hm
    rw [heq] at hperm
    exact Or.inl (de_allowFalse_of_anyFalse3 s.entries r hperm)
  | some m =>
    have hdepth_mem : m ∈ ((s.entries.filter (fun e => matchesB e r && decide (e.effect = .deny))).map depth) :=
      de_maxMem3 s.entries r m hm
    obtain ⟨d, hmem, hM, heff, hdepth⟩ := de_memDeny_of_memMap3 s.entries r m hdepth_mem
    have heq := de_some_any3 s.entries r m hm
    rw [heq] at hperm
    have hbound := de_bound_of_anyFalse4 s.entries r m hperm
    have hbound2 : ∀ a ∈ s.entries, Matches a r → a.effect = .allow → depth a ≤ depth d := by
      intro a ha hMa hEa
      rw [hdepth]
      exact hbound a ha hMa hEa
    exact Or.inr ⟨d, hmem, hM, heff, hbound2⟩

end Acl
