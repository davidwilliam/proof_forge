import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def maxDepth (es : List Entry) : Nat :=
  es.foldl (fun acc e => Nat.max acc e.path.length) 0

def decision (l : List Entry) (r : Request) : Bool :=
  let ms := l.filter (matchesB · r)
  let allows := ms.filter (fun e => e.effect == .allow)
  let denies := ms.filter (fun e => e.effect == .deny)
  !allows.isEmpty && (denies.isEmpty || decide (maxDepth denies < maxDepth allows))

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

theorem req_effects_aux2 (s : State) (r : Request) (hc : r.user ∈ s.users ∧ r.user ≠ 0) (hg : decision s.entries r = true) :
    (step s r).2.users = s.users ∧ (step s r).2.entries = s.entries ∧ (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩] := by
  simp [step, hc, hg]

theorem req_effects_aux3 (s : State) (r : Request) (hc : r.user ∈ s.users ∧ r.user ≠ 0) (hg : decision s.entries r = false) :
    (step s r).2.users = s.users ∧ (step s r).2.entries = s.entries ∧ (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩] := by
  simp [step, hc, hg]

theorem foo_test3 : True := trivial

def myTestFoo : Nat := 42

theorem myLemTest : True := trivial

theorem helpSubj (a b : Nat) : ((a == 0 || a == b) = true) ↔ (a = 0 ∨ a = b) := by simp

theorem helpIsPrefNil (ys : List Nat) : List.isPrefixOf ([] : List Nat) ys = true := by simp

theorem helpBeqNat (a b : Nat) : ((a == b) = true) ↔ (a = b) := by simp

theorem probe_isPref : ∀ (xs ys : List Nat), xs.isPrefixOf ys = true ↔ xs <+: ys := by
  intro xs ys
  simp [List.isPrefixOf_iff_prefix]

theorem matchesB_iff3 (e : Entry) (r : Request) : matchesB e r = true ↔ Matches e r := by
  unfold matchesB Matches
  rw [Bool.and_eq_true, Bool.or_eq_true]
  rw [probe_isPref]
  constructor
  · rintro ⟨hsub, hpref⟩
    refine ⟨?_, hpref⟩
    cases hsub with
    | inl h => exact Or.inl ((helpBeqNat _ _).mp h)
    | inr h => exact Or.inr ((helpBeqNat _ _).mp h)
  · rintro ⟨hsub, hpref⟩
    refine ⟨?_, hpref⟩
    cases hsub with
    | inl h => exact Or.inl ((helpBeqNat _ _).mpr h)
    | inr h => exact Or.inr ((helpBeqNat _ _).mpr h)

theorem probe_lemmas : True := by
  trivial
#check List.filter
#check List.contains
#check decide
#check List.isEmpty

theorem probeB (e : Effect) : (e == .allow) = true ↔ e = .allow := by
  cases e <;> simp

theorem probeB2 (e : Effect) : (e == .deny) = true ↔ e = .deny := by
  cases e <;> simp
#check List.mem_filter
#check List.mem_append

theorem gj_probe_step2 (s : State) (r : Request) : (step s r).1 = if (s.users.contains r.user && r.user != 0) then (if decision s.entries r then .granted else .denied) else .rejected := by
  unfold step
  split
  · simp [*]
  · simp [*]

theorem gj_probe_lemmas_list : True := by
  trivial
#check maxDepth
#check decision
#check matchesB
#check Matches
#check depth
#check HasAllow
#check Permitted
#check Overridden

theorem gj_learn2 (s : State) (r : Request) (h : (step s r).1 = .granted) : decision s.entries r = true := by
  unfold step at h
  simp only at h
  split at h
  next hc =>
    split at h
    next hd => exact hd
    next hd => contradiction
  next hc => contradiction

theorem tmp_perm_api : True := trivial

theorem explore_env : True := by
  trace_state
  trivial

theorem mem_filter_matchesB (l : List Entry) (r : Request) (e : Entry) :
    e ∈ l.filter (matchesB · r) ↔ e ∈ l ∧ Matches e r := by
  simp only [List.mem_filter]
  constructor
  · rintro ⟨hmem, hmatch⟩
    exact ⟨hmem, (matchesB_iff3 e r).mp hmatch⟩
  · rintro ⟨hmem, hmatch⟩
    exact ⟨hmem, (matchesB_iff3 e r).mpr hmatch⟩

theorem maxDepth_fold_ge (es : List Entry) (acc : Nat) : acc ≤ es.foldl (fun acc e => Nat.max acc e.path.length) acc := by
  induction es generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h1 : acc ≤ Nat.max acc hd.path.length := Nat.le_max_left acc _
    have h2 := ih (Nat.max acc hd.path.length)
    exact Nat.le_trans h1 h2

theorem maxDepth_zero_ge (es : List Entry) : 0 ≤ maxDepth es := by
  unfold maxDepth
  exact Nat.zero_le _

theorem aux_contains_true3 (xs : List Nat) (x : Nat) (h : x ∈ xs) : xs.contains x = true := by
  rw [List.contains_eq_mem]
  simp [h]

theorem aux_bne_true3 (x : Nat) (h : x ≠ 0) : (x != 0) = true := by
  simp [bne_iff_ne, h]

theorem aux_cond_true3 (s : State) (r : Request) (h : ValidQuery s r) : (s.users.contains r.user && r.user != 0) = true := by
  unfold ValidQuery at h
  obtain ⟨hmem, hne⟩ := h
  have hc : s.users.contains r.user = true := aux_contains_true3 _ _ hmem
  have hn : (r.user != 0) = true := aux_bne_true3 _ hne
  rw [hc, hn]
  rfl

theorem req_valid_answered_probe : ValidAnswered step := by
  intro s r h
  have hc : (s.users.contains r.user && r.user != 0) = true := aux_cond_true3 s r h
  have hstep : (step s r).1 = (if decision s.entries r then .granted else .denied) := by
    have h2 := gj_probe_step2 s r
    rw [hc] at h2
    simpa using h2
  rw [hstep]
  cases hd : decision s.entries r <;> decide

theorem tmp_a1 (xs : List Nat) (x : Nat) : xs.contains x = true ↔ x ∈ xs := by
  rw [List.contains_eq_mem]
  simp

theorem tmp_a2 : True := trivial

theorem aux_mem_of_contains_trueX (xs : List Nat) (x : Nat) (h : xs.contains x = true) : x ∈ xs := by
  exact (tmp_a1 xs x).mp h

theorem aux_ne_of_bne_trueX (x : Nat) (h : (x != 0) = true) : x ≠ 0 := by
  exact (bne_iff_ne.mp h)





theorem plan0_step_rejected_of_cond_false (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = false) : step s r = (.rejected, s) := by
  unfold step
  rw [h]
  simp




theorem plan0_cond_true_imp_valid (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = true) : ValidQuery s r := by
  unfold ValidQuery
  have h2 : s.users.contains r.user = true ∧ (r.user != 0) = true := (Bool.and_eq_true_iff.mp h)
  obtain ⟨hc, hn⟩ := h2
  exact ⟨aux_mem_of_contains_trueX _ _ hc, aux_ne_of_bne_trueX _ hn⟩

theorem plan0_test_proof (s : State) (r : Request)
    (h : ¬ ValidQuery s r) : (s.users.contains r.user && r.user != 0) = false := by
  cases hc : (s.users.contains r.user && r.user != 0) with
  | true => exact absurd (plan0_cond_true_imp_valid s r hc) h | false => rfl

theorem plan0_cond_false_of_not_valid (s : State) (r : Request)
    (h : ¬ ValidQuery s r) : (s.users.contains r.user && r.user != 0) = false := by
  cases hc : (s.users.contains r.user && r.user != 0) with
  | true => exact absurd (plan0_cond_true_imp_valid s r hc) h
  | false => rfl

theorem plan0_step_rejected_of_cond_false_aux : True := trivial
#check step

theorem diag3 (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = false) : step s r = (.rejected, s) := by
  unfold step
  rw [h]
  simp

theorem plan0_step_rejected_of_cond_false2 (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = false) : step s r = (.rejected, s) := by
  unfold step
  rw [h]
  simp

theorem plan0_step_rejected_of_not_valid (s : State) (r : Request)
    (h : ¬ ValidQuery s r) : step s r = (.rejected, s) := by
  have hc : (s.users.contains r.user && r.user != 0) = false :=
    plan0_cond_false_of_not_valid s r h
  exact diag3 s r hc

theorem req_invalid_noop_proof : InvalidNoop step := by
  intro s r h
  exact plan0_step_rejected_of_not_valid s r h

theorem tmp_effects_valid (s : State) (r : Request) (hNe : (step s r).1 ≠ .rejected) : ValidQuery s r := by
  cases Decidable.em (ValidQuery s r) with
  | inl h => exact h
  | inr h =>
    have hEq := plan0_step_rejected_of_not_valid s r h
    have h1 : (step s r).1 = .rejected := by rw [hEq]
    exact False.elim (hNe h1)

theorem dd_probe_dec (l : List Entry) (r : Request) :
  decision l r = (!((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty && (((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty || decide (maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) < maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)))) ) := by
  unfold decision
  rfl

theorem dd_and_true (a b : Bool) (h : (a && b) = true) : a = true ∧ b = true := Bool.and_eq_true_iff.mp h
#check Bool.and_eq_true_iff
#check Bool.not_eq_true

theorem dd_isEmpty_false_of_not_true (b : Bool) (h : (!b) = true) : b = false := by
  cases b with
  | true => simp at h
  | false => rfl

theorem dd_nonempty_of_isEmpty_false2 (xs : List Entry) (h : xs.isEmpty = false) : ∃ x, x ∈ xs := by
  cases xs with
  | nil => simp [List.isEmpty] at h
  | cons hd tl => exact ⟨hd, by simp⟩

theorem dd_mem_allow_of_decTrue2 (l : List Entry) (r : Request) (h : decision l r = true) :
    ∃ a, a ∈ l ∧ Matches a r ∧ a.effect = .allow := by
  have hdec := dd_probe_dec l r
  rw [hdec] at h
  have hpair := dd_and_true _ _ h
  obtain ⟨h1, _h2⟩ := hpair
  have hNe : ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false :=
    dd_isEmpty_false_of_not_true _ h1
  obtain ⟨a, haMem⟩ := dd_nonempty_of_isEmpty_false2 _ hNe
  have hmem := haMem
  rw [List.mem_filter] at hmem
  obtain ⟨hmMs, heffB⟩ := hmem
  have hMs := (mem_filter_matchesB l r a).mp hmMs
  obtain ⟨hinL, hmatch⟩ := hMs
  have heff : a.effect = .allow := (probeB _).mp heffB
  exact ⟨a, hinL, hmatch, heff⟩

theorem do_test_induct (es : List Entry) : True := by
  induction es with
  | nil => trivial
  | cons hd tl ih => trivial

theorem do_debug1 (es : List Entry) (acc : Nat) (e : Entry) (hm : e ∈ es) : True := by
  induction es generalizing acc with
  | nil => trivial
  | cons hd tl ih =>
    have hfoo : hd = hd := rfl
    trivial

theorem do_mem_le_aux4 (es : List Entry) (acc : Nat) (x0 : Entry) (hm : x0 ∈ es) :
    x0.path.length ≤ es.foldl (fun a x => Nat.max a x.path.length) acc := by
  induction es generalizing acc with
  | nil => simp at hm
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    simp at hm
    cases hm with
    | inl heq =>
      rw [heq]
      have h1 : hd.path.length ≤ Nat.max acc hd.path.length := Nat.le_max_right acc _
      have h2 := maxDepth_fold_ge tl (Nat.max acc hd.path.length)
      exact Nat.le_trans h1 h2
    | inr hmem =>
      exact ih (Nat.max acc hd.path.length) hmem

theorem do_bounded_aux4 (es : List Entry) (acc N : Nat) (hacc : acc ≤ N)
    (hh : ∀ x0 ∈ es, x0.path.length ≤ N) :
    es.foldl (fun a x => Nat.max a x.path.length) acc ≤ N := by
  induction es generalizing acc with
  | nil => simpa
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hhd : hd.path.length ≤ N := hh hd (by simp)
    have hacc2 : Nat.max acc hd.path.length ≤ N := Nat.max_le.mpr ⟨hacc, hhd⟩
    have htl : ∀ x0 ∈ tl, x0.path.length ≤ N := fun x0 hm => hh x0 (List.mem_cons_of_mem hd hm)
    exact ih _ hacc2 htl

theorem do_bounded4 (es : List Entry) (N : Nat) (hh : ∀ x0 ∈ es, x0.path.length ≤ N) :
    maxDepth es ≤ N := by
  unfold maxDepth
  exact do_bounded_aux4 es 0 N (Nat.zero_le N) hh

theorem do_mem_le4 (es : List Entry) (x0 : Entry) (hm : x0 ∈ es) :
    x0.path.length ≤ maxDepth es := by
  unfold maxDepth
  exact do_mem_le_aux4 es 0 x0 hm

theorem do_mem_allows_iff (l : List Entry) (r : Request) (x0 : Entry) :
    x0 ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow) ↔
    x0 ∈ l ∧ Matches x0 r ∧ x0.effect = .allow := by
  constructor
  · intro hm
    rw [List.mem_filter] at hm
    obtain ⟨hmMs, heff⟩ := hm
    have hMs := (mem_filter_matchesB l r x0).mp hmMs
    obtain ⟨hinL, hmatch⟩ := hMs
    exact ⟨hinL, hmatch, (probeB _).mp heff⟩
  · rintro ⟨hinL, hmatch, heff⟩
    rw [List.mem_filter]
    constructor
    · exact (mem_filter_matchesB l r x0).mpr ⟨hinL, hmatch⟩
    · have : (x0.effect == .allow) = true := by rw [heff]; simp
      exact this

theorem do_mem_denies_iff (l : List Entry) (r : Request) (x0 : Entry) :
    x0 ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .deny) ↔
    x0 ∈ l ∧ Matches x0 r ∧ x0.effect = .deny := by
  constructor
  · intro hm
    rw [List.mem_filter] at hm
    obtain ⟨hmMs, heff⟩ := hm
    have hMs := (mem_filter_matchesB l r x0).mp hmMs
    obtain ⟨hinL, hmatch⟩ := hMs
    exact ⟨hinL, hmatch, (probeB2 _).mp heff⟩
  · rintro ⟨hinL, hmatch, heff⟩
    rw [List.mem_filter]
    constructor
    · exact (mem_filter_matchesB l r x0).mpr ⟨hinL, hmatch⟩
    · have : (x0.effect == .deny) = true := by rw [heff]; simp
      exact this





theorem plan1_allow_depth_le_of_overridden (l : List Entry) (r : Request) (h : Overridden l r) (a : Entry) (ha : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) : depth a ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by
  obtain ⟨d, hdmem, hdmatch, hdeff, hbound⟩ := h
  have haInfo := (do_mem_allows_iff l r a).mp ha
  obtain ⟨haL, haMatch, haEff⟩ := haInfo
  have hle : depth a ≤ depth d := hbound a haL haMatch haEff
  have hdIn : d ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .deny) :=
    (do_mem_denies_iff l r d).mpr ⟨hdmem, hdmatch, hdeff⟩
  have hle2 : depth d ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by
    have h := do_mem_le4 _ d hdIn
    unfold depth at *
    exact h
  unfold depth at hle ⊢
  exact Nat.le_trans hle hle2








theorem plan1_denies_test_tmp (l : List Entry) (r : Request) (h : Overridden l r) : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = false := by
  obtain ⟨d, hdmem, hdmatch, hdeff, _⟩ := h
  have hmem : d ∈ ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) :=
    (do_mem_denies_iff l r d).mpr ⟨hdmem, hdmatch, hdeff⟩
  cases hl : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) with
  | nil => simp [hl] at hmem
  | cons hd tl => simp

theorem plan1_denies_not_empty_of_overridden (l : List Entry) (r : Request) (h : Overridden l r) : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = false := by
  obtain ⟨d, hdmem, hdmatch, hdeff, _⟩ := h
  have hmem : d ∈ ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) :=
    (do_mem_denies_iff l r d).mpr ⟨hdmem, hdmatch, hdeff⟩
  cases hl : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) with
  | nil => simp [hl] at hmem
  | cons hd tl => simp

theorem plan1_decision_true_lt_of_denies_not_empty (l : List Entry) (r : Request) (hdec : decision l r = true) (hne : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = false) : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) < maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) := by
  unfold decision at hdec
  simp only at hdec
  have hpair := (Bool.and_eq_true_iff.mp hdec)
  obtain ⟨_, h2⟩ := hpair
  have hor := (Bool.or_eq_true_iff.mp h2)
  cases hor with
  | inl hEmpty =>
    rw [hne] at hEmpty
    contradiction
  | inr hDec =>
    exact (decide_eq_true_iff.mp hDec)

theorem testPlan1 (l : List Entry) (r : Request) (h : Overridden l r) (a : Entry) (ha : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) : depth a ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by
  obtain ⟨d, hdmem, hdmatch, hdeff, hbound⟩ := h
  have haInfo := (do_mem_allows_iff l r a).mp ha
  obtain ⟨haL, haMatch, haEff⟩ := haInfo
  have hle : depth a ≤ depth d := hbound a haL haMatch haEff
  have hdIn : d ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .deny) :=
    (do_mem_denies_iff l r d).mpr ⟨hdmem, hdmatch, hdeff⟩
  have hle2 : depth d ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by
    have h := do_mem_le4 _ d hdIn
    unfold depth at *
    exact h
  unfold depth at hle ⊢
  exact Nat.le_trans hle hle2

theorem plan1_maxDepth_aux_unique123 (l : List Entry) (r : Request) (h : Overridden l r) : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by
  apply do_bounded4 _ _ _
  intro x0 hx
  have hle := plan1_allow_depth_le_of_overridden l r h x0 hx
  unfold depth at hle
  exact hle

theorem plan1_maxDepth_allows_le_of_overridden (l : List Entry) (r : Request) (h : Overridden l r) : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by
  apply do_bounded4 _ _ _
  intro x0 hx
  have hle := plan1_allow_depth_le_of_overridden l r h x0 hx
  unfold depth at hle
  exact hle

theorem plan1_decision_not_true_of_overridden (l : List Entry) (r : Request) (h : Overridden l r) : decision l r ≠ true := by
  intro hdec
  have hne : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = false :=
    plan1_denies_not_empty_of_overridden l r h
  have hlt : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) < maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) :=
    plan1_decision_true_lt_of_denies_not_empty l r hdec hne
  have hle : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) :=
    plan1_maxDepth_allows_le_of_overridden l r h
  omega

theorem plan1_step_not_granted_of_overridden (s : State) (r : Request) (h : Overridden s.entries r) : (step s r).1 ≠ .granted := by
  intro hGrant
  have hdec : decision s.entries r = true := gj_learn2 s r hGrant
  exact plan1_decision_not_true_of_overridden s.entries r h hdec

theorem sa_allows_nonempty {l : List Entry} {r : Request} {a : Entry}
  (h : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) :
  (((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false) := by
  cases hL : ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) with
  | nil => simp [hL] at h
  | cons hd tl => simp

theorem sa_allow_mem {l : List Entry} {r : Request} {a : Entry}
  (haL : a ∈ l) (haM : Matches a r) (haE : a.effect = .allow) :
  a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow) :=
  (do_mem_allows_iff l r a).mpr ⟨haL, haM, haE⟩

theorem sa_maxAllows_ge {l : List Entry} {r : Request} {a : Entry}
  (haL : a ∈ l) (haM : Matches a r) (haE : a.effect = .allow) :
  depth a ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) := by
  have hmem : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow) :=
    sa_allow_mem haL haM haE
  have h := do_mem_le4 _ a hmem
  unfold depth at *
  exact h

theorem sa_strict_aux (es : List Entry) (acc N : Nat) (hacc : acc < N)
    (hh : ∀ x0 ∈ es, x0.path.length < N) :
    es.foldl (fun a x => Nat.max a x.path.length) acc < N := by
  induction es generalizing acc with
  | nil => simpa
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hhd : hd.path.length < N := hh hd (by simp)
    have hacc2 : Nat.max acc hd.path.length < N := Nat.max_lt.mpr ⟨hacc, hhd⟩
    have htl : ∀ x0 ∈ tl, x0.path.length < N := fun x0 hm => hh x0 (List.mem_cons_of_mem hd hm)
    exact ih _ hacc2 htl

theorem sa_denies_max_lt (l : List Entry) (r : Request) (a : Entry)
    (hNpos : 0 < depth a)
    (hbound : ∀ d ∈ l, Matches d r → d.effect = .deny → depth d < depth a) :
    maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) < depth a := by
  have hNpos2 : 0 < a.path.length := hNpos
  have hbound2 : ∀ x0 ∈ ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)), x0.path.length < a.path.length := by
    intro x0 hx
    have hinfo := (do_mem_denies_iff l r x0).mp hx
    obtain ⟨hinL, hmatch, heff⟩ := hinfo
    have h := hbound x0 hinL hmatch heff
    have h2 : x0.path.length < a.path.length := h
    exact h2
  unfold maxDepth
  have hlt := sa_strict_aux ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) 0 (a.path.length) hNpos2 hbound2
  have h2 : depth a = a.path.length := rfl
  omega

theorem sa_denies_empty_of_zero2 (l : List Entry) (r : Request) (a : Entry)
    (_haL : a ∈ l) (_haM : Matches a r) (_haE : a.effect = .allow)
    (hzero : depth a = 0)
    (hbound : ∀ d ∈ l, Matches d r → d.effect = .deny → depth d < depth a) :
    ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = true := by
  cases hE : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) with
  | cons hd tl =>
    have hmem : hd ∈ ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by rw [hE]; simp
    have hinfo := (do_mem_denies_iff l r hd).mp hmem
    obtain ⟨hinL, hmatch, heff⟩ := hinfo
    have h := hbound hd hinL hmatch heff
    omega
  | nil => simp [List.isEmpty]

theorem sa_step_granted_of_decTrue (s : State) (r : Request)
    (hv : ValidQuery s r) (hd : decision s.entries r = true) :
    (step s r).1 = .granted := by
  have hc : (s.users.contains r.user && r.user != 0) = true := aux_cond_true3 s r hv
  have h2 := gj_probe_step2 s r
  rw [hc, hd] at h2
  simpa using h2





theorem plan2_decision_true_of_permitted (l : List Entry) (r : Request)
    (h : Permitted l r) : decision l r = true := by
  obtain ⟨a, haL, haM, haE, hbound⟩ := h
  have hmemAllow : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow) :=
    sa_allow_mem haL haM haE
  have hAllow : (((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty) = false :=
    sa_allows_nonempty hmemAllow
  have hAllowGe : depth a ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) :=
    sa_maxAllows_ge haL haM haE
  have hDen : (((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = true) ∨
      (maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) <
        maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow))) := by
    cases hzero : depth a with
    | zero =>
      exact Or.inl (sa_denies_empty_of_zero2 l r a haL haM haE hzero hbound)
    | succ n =>
      have hpos : 0 < depth a := by omega
      have hlt : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) < depth a :=
        sa_denies_max_lt l r a hpos hbound
      exact Or.inr (Nat.lt_of_lt_of_le hlt hAllowGe)
  unfold decision
  simp only
  rw [hAllow]
  simp only [Bool.not_false, Bool.true_and]
  rcases hDen with he | hlt
  · rw [he]
    simp
  · have hd : decide (maxDepth (((l.filter (matchesB · r)).filter (fun e => e.effect == .deny))) < maxDepth (((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)))) = true :=
      decide_eq_true hlt
    rw [hd]
    cases (((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty) <;> simp


theorem plan2_step_granted_of_permitted (s : State) (r : Request)
    (hv : ValidQuery s r) (h : Permitted s.entries r) :
    (step s r).1 = .granted := by
  have hdec : decision s.entries r = true := plan2_decision_true_of_permitted s.entries r h
  exact sa_step_granted_of_decTrue s r hv hdec


theorem plan2_allows_not_empty_of_permitted (l : List Entry) (r : Request)
    (h : Permitted l r) :
    ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false := by
  obtain ⟨a, haL, haM, haE, _hbound⟩ := h
  have hmem : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow) :=
    sa_allow_mem haL haM haE
  exact sa_allows_nonempty hmem

theorem plan2_denies_empty_or_lt_of_permitted (l : List Entry) (r : Request)
    (h : Permitted l r) :
    ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = true ∨
      maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) <
        maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) := by
  obtain ⟨a, haL, haM, haE, hbound⟩ := h
  have hAllowGe : depth a ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) :=
    sa_maxAllows_ge haL haM haE
  cases hzero : depth a with
  | zero =>
    left
    exact sa_denies_empty_of_zero2 l r a haL haM haE hzero hbound
  | succ n =>
    right
    have hpos : 0 < depth a := by omega
    have hlt : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) < depth a :=
      sa_denies_max_lt l r a hpos hbound
    exact Nat.lt_of_lt_of_le hlt hAllowGe

theorem plan2_decision_true_of_permitted_proof3 (l : List Entry) (r : Request)
    (h : Permitted l r) : decision l r = true := by
  have hAllow : (((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty) = false :=
    plan2_allows_not_empty_of_permitted l r h
  have hDen := plan2_denies_empty_or_lt_of_permitted l r h
  unfold decision
  simp only
  rw [hAllow]
  simp only [Bool.not_false, Bool.true_and]
  rcases hDen with he | hlt
  · rw [he]
    simp
  · have hd : decide (maxDepth (((l.filter (matchesB · r)).filter (fun e => e.effect == .deny))) < maxDepth (((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)))) = true :=
      decide_eq_true hlt
    rw [hd]
    cases (((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty) <;> simp

theorem plan2_decision_true_of_permitted_aux_tmp : decision [⟨.allow, 0, []⟩] ⟨0, []⟩ = decision [⟨.allow, 0, []⟩] ⟨0, []⟩ := rfl

theorem plan2_self_contained_tmp2 : True := trivial

theorem plan2_step_granted_of_permitted2 (s : State) (r : Request)
    (hv : ValidQuery s r) (h : Permitted s.entries r) :
    (step s r).1 = .granted := by
  have hdec : decision s.entries r = true := plan2_decision_true_of_permitted s.entries r h
  exact sa_step_granted_of_decTrue s r hv hdec

theorem gj_maxDepth_mono2 (hd : Entry) (tl : List Entry) : maxDepth tl ≤ maxDepth (hd :: tl) := by
  apply do_bounded4 _ _ _
  intro x0 hx
  exact do_mem_le4 _ x0 (List.mem_cons_of_mem hd hx)

theorem gj_maxDepth_cons2 (hd : Entry) (tl : List Entry) : maxDepth (hd :: tl) = Nat.max hd.path.length (maxDepth tl) := by
  apply Nat.le_antisymm
  · apply do_bounded4 _ _ _
    intro x0 hx
    simp at hx
    cases hx with
    | inl heq => rw [heq]; exact Nat.le_max_left _ _
    | inr hmem =>
      have h1 : x0.path.length ≤ maxDepth tl := do_mem_le4 tl x0 hmem
      exact Nat.le_trans h1 (Nat.le_max_right _ _)
  · exact Nat.max_le.mpr ⟨do_mem_le4 _ hd (by simp), gj_maxDepth_mono2 hd tl⟩

theorem gj_maxDepth_cons_eq_right3 (hd : Entry) (tl : List Entry) (h : hd.path.length ≤ maxDepth tl) : maxDepth (hd :: tl) = maxDepth tl := by
  apply Nat.le_antisymm
  · apply do_bounded4 _ _ _
    intro x0 hx
    simp at hx
    cases hx with
    | inl heq => rw [heq]; exact h
    | inr hmem => exact do_mem_le4 tl x0 hmem
  · exact gj_maxDepth_mono2 hd tl

theorem gj_maxDepth_cons_eq_left3 (hd : Entry) (tl : List Entry) (h : maxDepth tl ≤ hd.path.length) : maxDepth (hd :: tl) = hd.path.length := by
  apply Nat.le_antisymm
  · apply do_bounded4 _ _ _
    intro x0 hx
    simp at hx
    cases hx with
    | inl heq => rw [heq]; exact Nat.le_refl _
    | inr hmem => exact Nat.le_trans (do_mem_le4 tl x0 hmem) h
  · exact do_mem_le4 _ hd (by simp)

theorem gj_exists_max_mem7 : ∀ (es : List Entry), es ≠ [] → ∃ x ∈ es, x.path.length = maxDepth es := by
  intro es
  induction es with
  | nil => intro h; contradiction
  | cons hd tl ih =>
    intro hne
    by_cases htl : tl = []
    · subst htl
      exact ⟨hd, by simp, by rw [gj_maxDepth_cons2 hd []]; unfold maxDepth; simp⟩
    · have hne_tl : tl ≠ [] := htl
      obtain ⟨w, hwmem, hweq⟩ := ih hne_tl
      by_cases hle : hd.path.length ≤ maxDepth tl
      · refine ⟨w, List.mem_cons_of_mem hd hwmem, ?_⟩
        rw [gj_maxDepth_cons_eq_right3 hd tl hle]
        exact hweq
      · have hle2 : maxDepth tl ≤ hd.path.length := by omega
        refine ⟨hd, by simp, ?_⟩
        rw [gj_maxDepth_cons_eq_left3 hd tl hle2]









theorem plan3_permitted_of_granted (s : State) (r : Request)
    (h : (step s r).1 = .granted) : Permitted s.entries r := by
  have hdec : decision s.entries r = true := gj_learn2 s r h
  have hAllowNe : (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false) := by
    have hdec2 := dd_probe_dec s.entries r
    rw [hdec2] at hdec
    have hpair := (Bool.and_eq_true_iff.mp hdec)
    obtain ⟨h1, h2⟩ := hpair
    exact dd_isEmpty_false_of_not_true _ h1
  have hDen : ((((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = true) ∨
      maxDepth (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny))) <
        maxDepth (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .allow)))) := by
    have hdec2 := dd_probe_dec s.entries r
    rw [hdec2] at hdec
    have hpair := (Bool.and_eq_true_iff.mp hdec)
    obtain ⟨h1, h2⟩ := hpair
    have hor := (Bool.or_eq_true_iff.mp h2)
    cases hor with
    | inl hEmpty => exact Or.inl hEmpty
    | inr hDec => exact Or.inr ((decide_eq_true_iff.mp hDec))
  have hne : (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .allow))) ≠ [] := by
    intro heq
    rw [heq] at hAllowNe
    simp [List.isEmpty] at hAllowNe
  obtain ⟨w, hwmem, hweq⟩ := gj_exists_max_mem7 _ hne
  have hinfo := (do_mem_allows_iff s.entries r w).mp hwmem
  obtain ⟨hinL, hmatch, heff⟩ := hinfo
  refine ⟨w, hinL, hmatch, heff, ?_⟩
  intro d hdL hdM hdE
  have hdMem : d ∈ ((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny)) :=
    (do_mem_denies_iff s.entries r d).mpr ⟨hdL, hdM, hdE⟩
  have hleDen : d.path.length ≤ maxDepth (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny))) :=
    do_mem_le4 _ d hdMem
  rcases hDen with hEmpty | hLt
  · exfalso
    cases hL : ((((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny)))) with
    | nil => simp [hL] at hdMem
    | cons hd tl =>
      have hF : ((hd :: tl).isEmpty) = false := by simp [List.isEmpty]
      rw [← hL] at hF
      rw [hEmpty] at hF
      contradiction
  · unfold depth
    omega


theorem plan3_parts_check2 (l : List Entry) (r : Request) (h : decision l r = true) :
    ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false ∧
    (((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = true ∨
      maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) <
        maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow))) := by
  have hdec := dd_probe_dec l r
  rw [hdec] at h
  have hpair := (Bool.and_eq_true_iff.mp h)
  obtain ⟨h1, h2⟩ := hpair
  have hAllow : (((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false) :=
    dd_isEmpty_false_of_not_true _ h1
  refine ⟨hAllow, ?_⟩
  have hor := (Bool.or_eq_true_iff.mp h2)
  cases hor with
  | inl hEmpty => exact Or.inl hEmpty
  | inr hDec =>
    have hlt : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) < maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) :=
      (decide_eq_true_iff.mp hDec)
    exact Or.inr hlt

theorem plan3_decision_true_parts_proof : True := trivial

theorem plan3_decision_true_parts (l : List Entry) (r : Request) (h : decision l r = true) :
    ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false ∧
    (((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = true ∨
      maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) <
        maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow))) :=
  plan3_parts_check2 l r h

theorem plan3_exists_max_allow_aux_test (l : List Entry) (r : Request) (h : decision l r = true) :
    ∃ a, a ∈ l ∧ Matches a r ∧ a.effect = .allow ∧
      a.path.length = maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) := by
  have hparts := plan3_parts_check2 l r h
  obtain ⟨hAllowNe, _⟩ := hparts
  have hne : ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) ≠ [] := by
    intro heq
    rw [heq] at hAllowNe
    simp [List.isEmpty] at hAllowNe
  obtain ⟨w, hwmem, hweq⟩ := gj_exists_max_mem7 _ hne
  have hinfo := (do_mem_allows_iff l r w).mp hwmem
  obtain ⟨hinL, hmatch, heff⟩ := hinfo
  exact ⟨w, hinL, hmatch, heff, hweq⟩

theorem plan3_exists_max_allow (l : List Entry) (r : Request) (h : decision l r = true) :
    ∃ a, a ∈ l ∧ Matches a r ∧ a.effect = .allow ∧
      a.path.length = maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) := by
  have hparts := plan3_parts_check2 l r h
  obtain ⟨hAllowNe, _⟩ := hparts
  have hne : ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) ≠ [] := by
    intro heq
    rw [heq] at hAllowNe
    simp [List.isEmpty] at hAllowNe
  obtain ⟨w, hwmem, hweq⟩ := gj_exists_max_mem7 _ hne
  have hinfo := (do_mem_allows_iff l r w).mp hwmem
  obtain ⟨hinL, hmatch, heff⟩ := hinfo
  exact ⟨w, hinL, hmatch, heff, hweq⟩

theorem plan3_deny_depth_lt_max_allow (l : List Entry) (r : Request) (h : decision l r = true)
    (a : Entry)
    (haMax : a.path.length = maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)))
    (d : Entry) (hdL : d ∈ l) (hdM : Matches d r) (hdE : d.effect = .deny) :
    depth d < depth a := by
  have hparts := plan3_parts_check2 l r h
  obtain ⟨hAllowNe, hDen⟩ := hparts
  have hdMem : d ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .deny) :=
    (do_mem_denies_iff l r d).mpr ⟨hdL, hdM, hdE⟩
  have hleDen : d.path.length ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) :=
    do_mem_le4 _ d hdMem
  rcases hDen with hEmpty | hLt
  · exfalso
    cases hL : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) with
    | nil => simp [hL] at hdMem
    | cons hd tl =>
      have hF : (((hd :: tl)).isEmpty) = false := by simp [List.isEmpty]
      rw [← hL] at hF
      rw [hEmpty] at hF
      contradiction
  · unfold depth
    omega

theorem plan3_permitted_of_decision_true (l : List Entry) (r : Request)
    (h : decision l r = true) : Permitted l r := by
  obtain ⟨a, haL, haM, haE, haMax⟩ := plan3_exists_max_allow l r h
  exact ⟨a, haL, haM, haE, fun d hdL hdM hdE => plan3_deny_depth_lt_max_allow l r h a haMax d hdL hdM hdE⟩

theorem plan3_permitted_of_granted_aux_tmp (s : State) (r : Request)
    (h : (step s r).1 = .granted) : Permitted s.entries r :=
  plan3_permitted_of_decision_true s.entries r (gj_learn2 s r h)

theorem plan3_fix2 (s : State) (r : Request)
    (h : (step s r).1 = .granted) : Permitted s.entries r := by
  have hdec : decision s.entries r = true := gj_learn2 s r h
  have hAllowNe : (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false) := by
    have hdec2 := dd_probe_dec s.entries r
    rw [hdec2] at hdec
    have hpair := (Bool.and_eq_true_iff.mp hdec)
    obtain ⟨h1, h2⟩ := hpair
    exact dd_isEmpty_false_of_not_true _ h1
  have hDen : ((((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = true) ∨
      maxDepth (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny))) <
        maxDepth (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .allow)))) := by
    have hdec2 := dd_probe_dec s.entries r
    rw [hdec2] at hdec
    have hpair := (Bool.and_eq_true_iff.mp hdec)
    obtain ⟨h1, h2⟩ := hpair
    have hor := (Bool.or_eq_true_iff.mp h2)
    cases hor with
    | inl hEmpty => exact Or.inl hEmpty
    | inr hDec => exact Or.inr ((decide_eq_true_iff.mp hDec))
  have hne : (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .allow))) ≠ [] := by
    intro heq
    rw [heq] at hAllowNe
    simp [List.isEmpty] at hAllowNe
  obtain ⟨w, hwmem, hweq⟩ := gj_exists_max_mem7 _ hne
  have hinfo := (do_mem_allows_iff s.entries r w).mp hwmem
  obtain ⟨hinL, hmatch, heff⟩ := hinfo
  refine ⟨w, hinL, hmatch, heff, ?_⟩
  intro d hdL hdM hdE
  have hdMem : d ∈ ((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny)) :=
    (do_mem_denies_iff s.entries r d).mpr ⟨hdL, hdM, hdE⟩
  have hleDen : d.path.length ≤ maxDepth (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny))) :=
    do_mem_le4 _ d hdMem
  rcases hDen with hEmpty | hLt
  · exfalso
    cases hL : ((((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .deny)))) with
    | nil => simp [hL] at hdMem
    | cons hd tl =>
      have hF : ((hd :: tl).isEmpty) = false := by simp [List.isEmpty]
      rw [← hL] at hF
      rw [hEmpty] at hF
      contradiction
  · unfold depth
    omega

theorem show_sig : True := trivial
#check @List.Perm.mem_iff

theorem perm_mem_iff_test3 {α : Type} {l1 l2 : List α} (h : l1.Perm l2) (a : α) : a ∈ l1 ↔ a ∈ l2 := by
  induction h with
  | nil => simp
  | cons x t ih =>
    simp only [List.mem_cons]
    rw [ih]
  | swap x y l =>
    simp only [List.mem_cons]
    constructor
    · intro hh
      rcases hh with rfl | rfl | hm
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hm)
    · intro hh
      rcases hh with rfl | rfl | hm
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hm)
  | trans h1 h2 ih1 ih2 =>
    exact Iff.trans (ih1) (ih2)











theorem plan4_mem_iff_of_perm {l l' : List Entry} (h : l.Perm l') (x : Entry) :
    x ∈ l ↔ x ∈ l' := perm_mem_iff_test3 h x

theorem plan4_maxDepth_eq_of_mem_iff {es1 es2 : List Entry}
    (h : ∀ x, x ∈ es1 ↔ x ∈ es2) : maxDepth es1 = maxDepth es2 := by
  apply Nat.le_antisymm
  · apply do_bounded4 _ _ _
    intro x0 hx
    have hx2 : x0 ∈ es2 := (h x0).mp hx
    exact do_mem_le4 es2 x0 hx2
  · apply do_bounded4 _ _ _
    intro x0 hx
    have hx1 : x0 ∈ es1 := (h x0).mpr hx
    exact do_mem_le4 es1 x0 hx1

theorem plan4_isEmpty_eq_of_mem_iff2 {es1 es2 : List Entry}
    (h : ∀ x, x ∈ es1 ↔ x ∈ es2) : es1.isEmpty = es2.isEmpty := by
  cases es1 with
  | nil =>
    cases es2 with
    | nil => rfl
    | cons hd tl =>
      exfalso
      have hmem : hd ∈ (hd :: tl) := by simp
      have hmem2 : hd ∈ ([] : List Entry) := (h hd).mpr hmem
      simp at hmem2
  | cons hd tl =>
    cases es2 with
    | nil =>
      exfalso
      have hmem : hd ∈ (hd :: tl) := by simp
      have hmem2 : hd ∈ ([] : List Entry) := (h hd).mp hmem
      simp at hmem2
    | cons hd2 tl2 => rfl

theorem plan4_isEmpty_eq_of_mem_iff {es1 es2 : List Entry}
    (h : ∀ x, x ∈ es1 ↔ x ∈ es2) : es1.isEmpty = es2.isEmpty := by
  cases es1 with
  | nil =>
    cases es2 with
    | nil => rfl
    | cons hd tl =>
      exfalso
      have hmem : hd ∈ (hd :: tl) := by simp
      have hmem2 : hd ∈ ([] : List Entry) := (h hd).mpr hmem
      simp at hmem2
  | cons hd tl =>
    cases es2 with
    | nil =>
      exfalso
      have hmem : hd ∈ (hd :: tl) := by simp
      have hmem2 : hd ∈ ([] : List Entry) := (h hd).mp hmem
      simp at hmem2
    | cons hd2 tl2 => rfl

theorem plan4_decision_eq_of_mem_iff {l1 l2 : List Entry} (r : Request)
    (h : ∀ x, x ∈ l1 ↔ x ∈ l2) : decision l1 r = decision l2 r := by
  have hAllow : ∀ x, x ∈ (l1.filter (matchesB · r)).filter (fun e => e.effect == .allow) ↔
      x ∈ (l2.filter (matchesB · r)).filter (fun e => e.effect == .allow) := by
    intro x
    rw [do_mem_allows_iff, do_mem_allows_iff]
    constructor
    · rintro ⟨hm1, hmM, hmE⟩
      exact ⟨(h x).mp hm1, hmM, hmE⟩
    · rintro ⟨hm2, hmM, hmE⟩
      exact ⟨(h x).mpr hm2, hmM, hmE⟩
  have hDeny : ∀ x, x ∈ (l1.filter (matchesB · r)).filter (fun e => e.effect == .deny) ↔
      x ∈ (l2.filter (matchesB · r)).filter (fun e => e.effect == .deny) := by
    intro x
    rw [do_mem_denies_iff, do_mem_denies_iff]
    constructor
    · rintro ⟨hm1, hmM, hmE⟩
      exact ⟨(h x).mp hm1, hmM, hmE⟩
    · rintro ⟨hm2, hmM, hmE⟩
      exact ⟨(h x).mpr hm2, hmM, hmE⟩
  have hAllowEmpty : (((l1.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty) =
      (((l2.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty) :=
    plan4_isEmpty_eq_of_mem_iff hAllow
  have hDenyEmpty : (((l1.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty) =
      (((l2.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty) :=
    plan4_isEmpty_eq_of_mem_iff hDeny
  have hAllowMax : maxDepth ((l1.filter (matchesB · r)).filter (fun e => e.effect == .allow)) =
      maxDepth ((l2.filter (matchesB · r)).filter (fun e => e.effect == .allow)) :=
    plan4_maxDepth_eq_of_mem_iff hAllow
  have hDenyMax : maxDepth ((l1.filter (matchesB · r)).filter (fun e => e.effect == .deny)) =
      maxDepth ((l2.filter (matchesB · r)).filter (fun e => e.effect == .deny)) :=
    plan4_maxDepth_eq_of_mem_iff hDeny
  unfold decision
  simp only
  rw [hAllowEmpty, hDenyEmpty, hAllowMax, hDenyMax]

theorem plan4_step_fst_eq_of_perm_test2 (s : State) (r : Request) (l : List Entry)
    (h : l.Perm s.entries) :
    (step { s with entries := l } r).1 = (step s r).1 := by
  have hmem : ∀ x, x ∈ l ↔ x ∈ s.entries := fun x => plan4_mem_iff_of_perm h x
  have hdec : decision l r = decision s.entries r :=
    plan4_decision_eq_of_mem_iff r hmem
  have e1 := gj_probe_step2 { s with entries := l } r
  have e2 := gj_probe_step2 s r
  simp only at e1
  rw [hdec] at e1
  exact e1.trans e2.symm

theorem plan4_step_fst_eq_of_perm (s : State) (r : Request) (l : List Entry)
    (h : l.Perm s.entries) :
    (step { s with entries := l } r).1 = (step s r).1 := by
  have hmem : ∀ x, x ∈ l ↔ x ∈ s.entries := fun x => plan4_mem_iff_of_perm h x
  have hdec : decision l r = decision s.entries r :=
    plan4_decision_eq_of_mem_iff r hmem
  have e1 := gj_probe_step2 { s with entries := l } r
  have e2 := gj_probe_step2 s r
  simp only at e1
  rw [hdec] at e1
  exact e1.trans e2.symm

theorem req_order_independent_aux_wrap : OrderIndependent step := fun s r l h => plan4_step_fst_eq_of_perm s r l h

theorem de_step_denied_decFalse (s : State) (r : Request)
    (h : (step s r).1 = .denied) : decision s.entries r = false := by
  have hc : (s.users.contains r.user && r.user != 0) = true := by
    have hNe : (step s r).1 ≠ .rejected := by rw [h]; decide
    have hV := tmp_effects_valid s r hNe
    exact aux_cond_true3 s r hV
  have h2 := gj_probe_step2 s r
  rw [hc] at h2
  rw [h] at h2
  by_cases hd : decision s.entries r = true
  · rw [hd] at h2
    simp at h2
  · exact Bool.eq_false_iff.mpr (fun heq => hd heq)

theorem de_hasAllow_of_memAllow (l : List Entry) (r : Request)
    (a : Entry) (hm : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) :
    HasAllow l r := by
  have hinfo := (do_mem_allows_iff l r a).mp hm
  obtain ⟨hinL, hmatch, heff⟩ := hinfo
  exact ⟨a, hinL, hmatch, heff⟩

theorem de_allows_empty_imp_noAllow (l : List Entry) (r : Request)
    (hE : ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = true) :
    ¬ HasAllow l r := by
  intro hA
  obtain ⟨a, haL, haM, haE⟩ := hA
  have hmem : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow) :=
    (do_mem_allows_iff l r a).mpr ⟨haL, haM, haE⟩
  cases hL : ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) with
  | nil => simp [hL] at hmem
  | cons hd tl =>
    have hF : (hd :: tl).isEmpty = false := by simp [List.isEmpty]
    rw [← hL] at hF
    rw [hE] at hF
    contradiction

theorem de_decFalse_parts (l : List Entry) (r : Request)
    (h : decision l r = false)
    (hAne : ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false) :
    ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = false ∧
    maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) ≤
      maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by
  have hdec := dd_probe_dec l r
  rw [hdec] at h
  rw [hAne] at h
  simp only [Bool.not_false, Bool.true_and] at h
  have hpair := Bool.or_eq_false_iff.mp h
  obtain ⟨h1, h2⟩ := hpair
  refine ⟨h1, ?_⟩
  have hlt := decide_eq_false_iff_not.mp h2
  omega

theorem de_overridden_of_decFalse_nonempty (l : List Entry) (r : Request)
    (h : decision l r = false)
    (hAne : ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty = false) :
    Overridden l r := by
  obtain ⟨hDne, hle⟩ := de_decFalse_parts l r h hAne
  have hneD : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) ≠ [] := by
    intro heq
    rw [heq] at hDne
    simp [List.isEmpty] at hDne
  obtain ⟨w, hwmem, hweq⟩ := gj_exists_max_mem7 _ hneD
  have hinfo := (do_mem_denies_iff l r w).mp hwmem
  obtain ⟨hinL, hmatch, heff⟩ := hinfo
  refine ⟨w, hinL, hmatch, heff, ?_⟩
  intro a haL haM haE
  have hamem : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow) :=
    (do_mem_allows_iff l r a).mpr ⟨haL, haM, haE⟩
  have hleA : a.path.length ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) :=
    do_mem_le4 _ a hamem
  unfold depth
  omega

theorem req_valid_answered     : ValidAnswered step := by
  intro s r h
  have hc : (s.users.contains r.user && r.user != 0) = true := aux_cond_true3 s r h
  have hstep : (step s r).1 = (if decision s.entries r then .granted else .denied) := by
    have h2 := gj_probe_step2 s r
    rw [hc] at h2
    simpa using h2
  rw [hstep]
  cases hd : decision s.entries r <;> decide

theorem req_invalid_noop       : InvalidNoop step := by
  intro s r h
  exact plan0_step_rejected_of_not_valid s r h

theorem req_effects : Effects step := by
  intro s r hNe
  have hValid : ValidQuery s r := tmp_effects_valid s r hNe
  obtain ⟨hmem, hne⟩ := hValid
  cases hd : decision s.entries r with
  | false => exact req_effects_aux3 s r ⟨hmem, hne⟩ hd
  | true => exact req_effects_aux2 s r ⟨hmem, hne⟩ hd

theorem req_default_deny     : DefaultDeny step := by
  intro s r hNoAllow hGrant
  have hdec : decision s.entries r = true := gj_learn2 s r hGrant
  obtain ⟨a, hinL, hmatch, heff⟩ := dd_mem_allow_of_decTrue2 s.entries r hdec
  exact hNoAllow ⟨a, hinL, hmatch, heff⟩

theorem req_deny_overrides : DenyOverrides step := by
  intro s r h
  exact plan1_step_not_granted_of_overridden s r h

theorem req_specific_allow     : SpecificAllow step := by
  intro s r hv h
  exact plan2_step_granted_of_permitted2 s r hv h

theorem req_grant_justified : GrantJustified step := by
  intro s r h
  exact plan3_permitted_of_granted s r h

theorem req_order_independent : OrderIndependent step := fun s r l h => plan4_step_fst_eq_of_perm s r l h

theorem req_denial_explained : DenialExplained step := by
  intro s r hDen
  have hdec : decision s.entries r = false := de_step_denied_decFalse s r hDen
  cases hA : (((s.entries.filter (matchesB · r)).filter (fun e => e.effect == .allow)).isEmpty) with
  | true =>
    exact Or.inl (de_allows_empty_imp_noAllow s.entries r hA)
  | false =>
    exact Or.inr (de_overridden_of_decFalse_nonempty s.entries r hdec hA)

end Acl
