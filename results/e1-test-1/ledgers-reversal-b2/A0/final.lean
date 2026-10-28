import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | none => (.rejected, s)
    | some e => if i ∈ s.reversed then (.rejected, s) else (.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a })

theorem step_post_eq (s : State) (e : Entry) :
  step s (.post e) =
    (if ValidPost s e then
      (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a })
    else (.rejected, s)) := rfl

theorem step_rev_none (s : State) (i : EntryId) (h : findEntry s.journal i = none) :
  step s (.reverse i) = (.rejected, s) := by
  unfold step
  simp [h]

theorem step_rev_rej (s : State) (i : EntryId) (e : Entry)
  (hfind : findEntry s.journal i = some e) (hm : i ∈ s.reversed) :
  step s (.reverse i) = (.rejected, s) := by
  unfold step
  simp [hfind, hm]

theorem step_rev_ok (s : State) (i : EntryId) (e : Entry)
  (hfind : findEntry s.journal i = some e) (hm : i ∉ s.reversed) :
  step s (.reverse i)
    = (.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a }) := by
  unfold step
  simp [hfind, hm]

theorem sum_zero_list {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver_cons] at ih ⊢; omega

theorem sum_net_eq_lineSum (accs : List Nat) (ls : List Line)
  (hnodup : accs.Nodup) (hsub : ∀ l ∈ ls, l.1 ∈ accs) :
  sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have h0 : (fun a : Nat => netOf ([] : List Line) a) = (fun _ => (0 : Int)) := by
      funext a; rfl
    rw [h0]
    exact sum_zero_list accs
  | cons hd tl ih =>
    have hmem : hd.1 ∈ accs := hsub hd (by simp)
    have hsubt : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hsub l (List.mem_cons_of_mem hd hl)
    have ihtm := ih hsubt
    have h1 : (fun a : Nat => netOf (hd :: tl) a)
      = (fun a => (if hd.1 = a then hd.2 else (0 : Int)) + netOf tl a) := by
      funext a; rfl
    rw [h1, sumOver_add]
    have h2 : sumOver accs (fun a => if hd.1 = a then hd.2 else (0 : Int)) = hd.2 := by
      have heq : (fun a : Nat => (if hd.1 = a then hd.2 else (0 : Int)))
        = (fun a => if a = hd.1 then hd.2 else (0 : Int)) := by
        funext a
        by_cases h : a = hd.1
        · subst h; rfl
        · have h' : ¬ (hd.1 = a) := fun he => h he.symm
          simp [h, h']
      rw [heq, sumOver_ite_eq hnodup, if_pos hmem]
    rw [h2, ihtm]
    rfl

theorem nodup_append_single {l : List Nat} {x : Nat}
  (hl : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hhd : hd ∉ tl := by
      have htmp := List.nodup_cons.mp hl
      exact htmp.1
    have htl : tl.Nodup := by
      have htmp := List.nodup_cons.mp hl
      exact htmp.2
    have hx_tl : x ∉ tl := fun hm => hx (List.mem_cons_of_mem hd hm)
    have hx_hd : hd ≠ x := by
      intro heq
      apply hx
      rw [heq]
      simp
    have ih' := ih htl hx_tl
    have heq : ((hd :: tl) ++ [x]) = hd :: (tl ++ [x]) := rfl
    rw [heq]
    rw [List.nodup_cons]
    constructor
    · intro h
      rw [List.mem_append] at h
      cases h with
      | inl hmem => exact hhd hmem
      | inr hmem2 =>
        simp only [List.mem_singleton] at hmem2
        exact hx_hd hmem2
    · exact ih'

theorem ids_append_single (j : List Entry) (e : Entry) :
  ids (j ++ [e]) = ids j ++ [e.id] := by
  unfold ids
  simp only [List.map_append, List.map_cons, List.map_nil]

theorem find_none_of_not_mem (j : List Entry) (i : EntryId)
  (h : i ∉ ids j) : findEntry j i = none := by
  induction j with
  | nil => rfl
  | cons hd tl ih =>
    have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hids, List.mem_cons, not_or] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : ¬ (hd.id = i) := fun heq => h1 heq.symm
    simp [findEntry, h1', ih h2]

theorem find_some_of_mem (j : List Entry) (i : EntryId)
  (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil =>
    have hids : ids ([] : List Entry) = [] := rfl
    rw [hids] at h
    simp at h
  | cons hd tl ih =>
    by_cases heq : hd.id = i
    · exact ⟨hd, by simp [findEntry, heq]⟩
    · have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [hids, List.mem_cons] at h
      have hmem : i ∈ ids tl := by
        cases h with
        | inl heq2 => exact absurd heq2.symm heq
        | inr hm => exact hm
      obtain ⟨e, he⟩ := ih hmem
      exact ⟨e, by simp [findEntry, heq, he]⟩

theorem find_mem {j : List Entry} {i : EntryId} {e : Entry}
  (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    by_cases heq : hd.id = i
    · simp [findEntry, heq] at h
      subst h
      simp
    · simp [findEntry, heq] at h
      exact List.mem_cons_of_mem hd (ih h)

theorem find_id {j : List Entry} {i : EntryId} {e : Entry}
  (h : findEntry j i = some e) : e.id = i := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    by_cases heq : hd.id = i
    · simp [findEntry, heq] at h
      subst h
      exact heq
    · simp [findEntry, heq] at h
      exact ih h

theorem mem_ids_of_mem (tl : List Entry) (e' : Entry)
  (h : e' ∈ tl) : e'.id ∈ ids tl := by
  induction tl with
  | nil => simp at h
  | cons hd t ih =>
    have hids : ids (hd :: t) = hd.id :: ids t := rfl
    rw [hids]
    simp only [List.mem_cons]
    simp only [List.mem_cons] at h
    cases h with
    | inl heq => rw [heq]; exact Or.inl rfl
    | inr hmem => exact Or.inr (ih hmem)

theorem find_mem_ids {j : List Entry} {i : EntryId} {e : Entry}
  (h : findEntry j i = some e) : i ∈ ids j := by
  have hid := find_id h
  have hm := find_mem h
  rw [← hid]
  exact mem_ids_of_mem j e hm

theorem find_append (j1 j2 : List Entry) (i : EntryId) :
  findEntry (j1 ++ j2) i =
    match findEntry j1 i with
    | some e => some e
    | none => findEntry j2 i := by
  induction j1 with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have happ : ((hd :: tl) ++ j2) = hd :: (tl ++ j2) := rfl
    rw [happ]
    by_cases heq : hd.id = i
    · simp [findEntry, heq]
    · simp [findEntry, heq, ih]

theorem find_singleton (e : Entry) : findEntry [e] e.id = some e := by
  simp [findEntry]

theorem find_append_single (j : List Entry) (e : Entry)
  (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  have hnone : findEntry j e.id = none := find_none_of_not_mem j e.id h
  rw [find_append, hnone, find_singleton]

theorem sum_zero_of_not_mem (tl : List Entry) (i : EntryId) (a : AccountId)
  (h : i ∉ ids tl) :
  sumOver tl (fun e' => if e'.id = i then netOf e'.lines a else (0 : Int)) = 0 := by
  induction tl with
  | nil => rfl
  | cons hd t ih =>
    have hids : ids (hd :: t) = hd.id :: ids t := rfl
    rw [hids, List.mem_cons, not_or] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : ¬ (hd.id = i) := fun heq => h1 heq.symm
    show ((if hd.id = i then netOf hd.lines a else 0) + sumOver t _ ) = 0
    simp [h1', ih h2]

theorem sum_pick_id (j : List Entry) (i : EntryId) (e : Entry) (a : AccountId)
  (hnodup : (ids j).Nodup) (hfind : findEntry j i = some e) :
  sumOver j (fun e' => if e'.id = i then netOf e'.lines a else (0 : Int)) = netOf e.lines a := by
  induction j with
  | nil => simp [findEntry] at hfind
  | cons hd tl ih =>
    have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hids] at hnodup
    have hnodup_tl : (ids tl).Nodup := (List.nodup_cons.mp hnodup).2
    have hnotmem : hd.id ∉ ids tl := (List.nodup_cons.mp hnodup).1
    show ((if hd.id = i then netOf hd.lines a else 0) + sumOver tl _) = _
    by_cases heq : hd.id = i
    · simp [findEntry, heq] at hfind
      subst hfind
      simp [heq]
      have hi : i ∉ ids tl := by rw [← heq]; exact hnotmem
      have hzero := sum_zero_of_not_mem tl i a hi
      simp [hzero]
    · simp [findEntry, heq] at hfind
      simp [heq, ih hnodup_tl hfind]

theorem activeNet_rev_eq (j : List Entry) (r : List EntryId) (i : EntryId) (e : Entry) (a : AccountId)
  (hnodup : (ids j).Nodup) (hfind : findEntry j i = some e) (hnot : i ∉ r) :
  sumOver j (fun e' => if e'.id ∈ i :: r then (0 : Int) else netOf e'.lines a)
  = sumOver j (fun e' => if e'.id ∈ r then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  have hpoint : ∀ e' ∈ j,
    (if e'.id ∈ i :: r then (0 : Int) else netOf e'.lines a)
    = ((if e'.id ∈ r then (0 : Int) else netOf e'.lines a) - (if e'.id = i then netOf e'.lines a else 0)) := by
    intro e' _
    by_cases heq : e'.id = i
    · subst heq
      simp [hnot]
    · by_cases hmem : e'.id ∈ r
      · have hT2 : e'.id ∈ i :: r := List.mem_cons_of_mem i hmem
        simp [hT2, hmem, heq]
      · have hF2 : e'.id ∉ i :: r := by simp [heq, hmem]
        simp [hF2, hmem, heq]
  have hcongr := sumOver_congr j _ _ hpoint
  rw [hcongr, sumOver_sub, sum_pick_id j i e a hnodup hfind]

theorem opt_exists (o : Option Entry) (h : o ≠ none) : ∃ e, o = some e := by
  cases o with
  | none => contradiction
  | some e => exact ⟨e, rfl⟩

theorem post_success_valid (s : State) (e : Entry)
  (h : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases hc : ValidPost s e
  · exact hc
  · exfalso
    have hstep : step s (.post e) = (Outcome.rejected, s) := by
      rw [step_post_eq, if_neg hc]
    rw [hstep] at h
    simp at h

theorem rev_success_exists (s : State) (i : EntryId)
  (h : (step s (.reverse i)).1 = .ok) :
  ∃ e, findEntry s.journal i = some e ∧ i ∉ s.reversed := by
  by_cases hnone : findEntry s.journal i = none
  · exfalso
    have hstep := step_rev_none s i hnone
    rw [hstep] at h
    simp at h
  · obtain ⟨e, he⟩ := opt_exists _ hnone
    by_cases hm : i ∈ s.reversed
    · exfalso
      have hstep := step_rev_rej s i e he hm
      rw [hstep] at h
      simp at h
    · exact ⟨e, he, hm⟩

theorem req_post_succeeds    : PostSucceeds step := by
  intro s e h
  rw [step_post_eq, if_pos h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  obtain ⟨hmem, hnot⟩ := h
  obtain ⟨e, he⟩ := find_some_of_mem s.journal i hmem
  have hstep := step_rev_ok s i e he hnot
  rw [hstep]

theorem req_invalid_noop     : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    have hV : ¬ Valid s (.post e) := h
    have hVn : ¬ ValidPost s e := hV
    rw [step_post_eq, if_neg hVn]
  | reverse i =>
    have hV : ¬ Valid s (.reverse i) := h
    have hVn : ¬ ValidReverse s i := hV
    by_cases hnone : findEntry s.journal i = none
    · exact step_rev_none s i hnone
    · obtain ⟨e, he⟩ := opt_exists _ hnone
      have hmem' : i ∈ ids s.journal := find_mem_ids he
      have hrev : i ∈ s.reversed := by
        by_cases hm2 : i ∈ s.reversed
        · exact hm2
        · exfalso
          exact hVn ⟨hmem', hm2⟩
      exact step_rev_rej s i e he hrev

theorem req_post_effects     : PostEffects step := by
  intro s e h_ok
  have hv := post_success_valid s e h_ok
  have hstep : step s (.post e)
    = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
    rw [step_post_eq, if_pos hv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep]
  · rw [hstep]
  · rw [hstep]
  · rw [hstep]
  · intro a
    rw [hstep]

theorem req_reverse_effects  : ReverseEffects step := by
  intro s i e h_ok h_find
  obtain ⟨e0, _, he0_not⟩ := rev_success_exists s i h_ok
  have hstep := step_rev_ok s i e h_find he0_not
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep]
  · rw [hstep]
  · rw [hstep]
  · intro x
    rw [hstep]
    exact List.mem_cons
  · intro a
    rw [hstep]

theorem req_reverse_once     : ReverseOnce step := by
  intro s i h_ok
  obtain ⟨e, he_find, he_not⟩ := rev_success_exists s i h_ok
  have hstep := step_rev_ok s i e he_find he_not
  have hj : (step s (.reverse i)).2.journal = s.journal := by rw [hstep]
  have hr : (step s (.reverse i)).2.reversed = i :: s.reversed := by rw [hstep]
  have hfind' : findEntry (step s (.reverse i)).2.journal i = some e := by rw [hj, he_find]
  have hmem' : i ∈ (step s (.reverse i)).2.reversed := by rw [hr]; simp only [List.mem_cons, true_or]
  exact step_rev_rej _ _ _ hfind' hmem'

theorem req_roundtrip        : RoundTrip step := by
  intro s e h_ok
  have hv := post_success_valid s e h_ok
  have hstep_post : step s (.post e)
    = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
    rw [step_post_eq, if_pos hv]
  have hnid : e.id ∉ ids s.journal := hv.2.2.2.2.1
  have hnrev : e.id ∉ s.reversed := hv.2.2.2.2.2
  have hfind : findEntry (s.journal ++ [e]) e.id = some e :=
    find_append_single s.journal e hnid
  have hs1j : (step s (.post e)).2.journal = s.journal ++ [e] := by rw [hstep_post]
  have hs1r : (step s (.post e)).2.reversed = s.reversed := by rw [hstep_post]
  have hfind' : findEntry (step s (.post e)).2.journal e.id = some e := by rw [hs1j]; exact hfind
  have hnot' : e.id ∉ (step s (.post e)).2.reversed := by rw [hs1r]; exact hnrev
  have hstep_rev := step_rev_ok (step s (.post e)).2 e.id e hfind' hnot'
  refine ⟨by rw [hstep_rev], ?_⟩
  have hbal_pt : ∀ a, (step (step s (.post e)).2 (.reverse e.id)).2.balance a
      = (step s (.post e)).2.balance a - netOf e.lines a := fun a => by rw [hstep_rev]
  have hs1b_pt : ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := fun a => by rw [hstep_post]
  funext a
  rw [hbal_pt a, hs1b_pt a]
  omega

theorem req_trial_balance    : TrialBalance step := by
  intro s c hwf h_ok
  cases c with
  | post e =>
    have hv := post_success_valid s e h_ok
    have heff := req_post_effects s e h_ok
    obtain ⟨hacc, _, _, _, hbal⟩ := heff
    have hn : s.accounts.Nodup := hwf.1
    have hsub : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hv.2.1
    have hsum0 : lineSum e.lines = 0 := hv.2.2.2.1
    have hnet : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
      rw [sum_net_eq_lineSum s.accounts e.lines hn hsub, hsum0]
    unfold total
    rw [hacc]
    have hcongr : ∀ a ∈ s.accounts,
      (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := fun a _ => hbal a
    rw [sumOver_congr s.accounts _ _ hcongr, sumOver_add, hnet, Int.add_zero]
  | reverse i =>
    obtain ⟨e, he_find, _⟩ := rev_success_exists s i h_ok
    have heff := req_reverse_effects s i e h_ok he_find
    obtain ⟨hacc, _, _, _, hbal⟩ := heff
    have hn : s.accounts.Nodup := hwf.1
    have hmem : e ∈ s.journal := find_mem he_find
    have hbalW := hwf.2.2.2 e hmem
    have hsub : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hbalW.1
    have hsum0 : lineSum e.lines = 0 := hbalW.2
    have hnet : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
      rw [sum_net_eq_lineSum s.accounts e.lines hn hsub, hsum0]
    unfold total
    rw [hacc]
    have hcongr : ∀ a ∈ s.accounts,
      (step s (.reverse i)).2.balance a = s.balance a - netOf e.lines a := fun a _ => hbal a
    rw [sumOver_congr s.accounts _ _ hcongr, sumOver_sub, hnet, Int.sub_zero]

theorem req_well_formed      : StaysWellFormed step := by
  intro s c hwf
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hstep : step s (.post e)
          = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
          rw [step_post_eq, if_pos hv]
      have h2 : (step s (.post e)).2
          = { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } := by rw [hstep]
      rw [h2]
      obtain ⟨hnAcc, hnIds, hsubR, hbalJ⟩ := hwf
      have hnid : e.id ∉ ids s.journal := hv.2.2.2.2.1
      have hsubE : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hv.2.1
      have hsumE : lineSum e.lines = 0 := hv.2.2.2.1
      have hidsEq : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := ids_append_single s.journal e
      show WellFormed _
      unfold WellFormed
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hnAcc
      · show (ids (s.journal ++ [e])).Nodup
        rw [hidsEq]
        exact nodup_append_single hnIds hnid
      · intro i hi
        have hiJ := hsubR i hi
        show i ∈ ids (s.journal ++ [e])
        rw [hidsEq, List.mem_append]
        exact Or.inl hiJ
      · intro e' he'
        have he'' : e' ∈ s.journal ++ [e] := he'
        rw [List.mem_append] at he''
        cases he'' with
        | inl hmem => exact hbalJ e' hmem
        | inr hmem2 =>
          have heq : e' = e := by simpa using hmem2
          subst heq
          exact ⟨hsubE, hsumE⟩
    · have hstep : step s (.post e) = (Outcome.rejected, s) := by
        rw [step_post_eq, if_neg hv]
      have h2 : (step s (.post e)).2 = s := by rw [hstep]
      rw [h2]
      exact hwf
  | reverse i =>
    by_cases hnone : findEntry s.journal i = none
    · have hstep := step_rev_none s i hnone
      have h2 : (step s (.reverse i)).2 = s := by rw [hstep]
      rw [h2]
      exact hwf
    · obtain ⟨e, he⟩ := opt_exists _ hnone
      by_cases hm : i ∈ s.reversed
      · have hstep := step_rev_rej s i e he hm
        have h2 : (step s (.reverse i)).2 = s := by rw [hstep]
        rw [h2]
        exact hwf
      · have hstep := step_rev_ok s i e he hm
        have h2 : (step s (.reverse i)).2
            = { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } := by rw [hstep]
        rw [h2]
        obtain ⟨hnAcc, hnIds, hsubR, hbalJ⟩ := hwf
        have hmem : i ∈ ids s.journal := find_mem_ids he
        show WellFormed _
        unfold WellFormed
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact hnAcc
        · exact hnIds
        · intro x hx
          have hx' : (x = i ∨ x ∈ s.reversed) := List.mem_cons.mp hx
          cases hx' with
          | inl heq => rw [heq]; exact hmem
          | inr hmem2 => exact hsubR x hmem2
        · intro e' he'
          exact hbalJ e' he'

theorem req_consistent       : StaysConsistent step := by
  intro s c hwf hcons
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hstep : step s (.post e)
          = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
          rw [step_post_eq, if_pos hv]
      have h2 : (step s (.post e)).2
          = { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } := by rw [hstep]
      rw [h2]
      intro a
      have hcons_a := hcons a
      have hnrev : e.id ∉ s.reversed := hv.2.2.2.2.2
      have hact : activeNet ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) a
          = activeNet s a + netOf e.lines a := by
          unfold activeNet
          show sumOver (s.journal ++ [e]) (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a) = _ + _
          rw [sumOver_append]
          have hsing : sumOver [e] (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a) = netOf e.lines a := by
            simp [if_neg hnrev]
          rw [hsing]
      show ((s.balance a + netOf e.lines a)) = (s.opening a) + activeNet ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) a
      rw [hact, hcons_a]
      omega
    · have hstep : step s (.post e) = (Outcome.rejected, s) := by
        rw [step_post_eq, if_neg hv]
      have h2 : (step s (.post e)).2 = s := by rw [hstep]
      rw [h2]
      exact hcons
  | reverse i =>
    by_cases hnone : findEntry s.journal i = none
    · have hstep := step_rev_none s i hnone
      have h2 : (step s (.reverse i)).2 = s := by rw [hstep]
      rw [h2]
      exact hcons
    · obtain ⟨e, he⟩ := opt_exists _ hnone
      by_cases hm : i ∈ s.reversed
      · have hstep := step_rev_rej s i e he hm
        have h2 : (step s (.reverse i)).2 = s := by rw [hstep]
        rw [h2]
        exact hcons
      · have hstep := step_rev_ok s i e he hm
        have h2 : (step s (.reverse i)).2
            = { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } := by rw [hstep]
        rw [h2]
        intro a
        have hcons_a := hcons a
        have hnIds : (ids s.journal).Nodup := hwf.2.1
        have hact : activeNet ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) a
            = activeNet s a - netOf e.lines a := by
            unfold activeNet
            show sumOver s.journal (fun e' => if e'.id ∈ i :: s.reversed then (0 : Int) else netOf e'.lines a) = _ - _
            exact activeNet_rev_eq s.journal s.reversed i e a hnIds he hm
        show ((s.balance a - netOf e.lines a)) = (s.opening a) + activeNet ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) a
        rw [hact, hcons_a]
        omega

end Reversal
