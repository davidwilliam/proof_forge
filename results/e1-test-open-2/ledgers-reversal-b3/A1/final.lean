import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

def checkValidPost (s : State) (e : Entry) : Bool :=
  decide (e.lines ≠ []) &&
  decide (∀ l ∈ e.lines, l.1 ∈ s.accounts) &&
  decide (∀ l ∈ e.lines, l.2 ≠ 0) &&
  decide (lineSum e.lines = 0) &&
  decide (e.id ∉ ids s.journal) &&
  decide (e.id ∉ s.reversed)

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if checkValidPost s e then
      (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | none => (.rejected, s)
    | some e =>
      if i ∈ s.reversed then (.rejected, s)
      else (.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a })

theorem find_mem_aux (l : List Entry) (i : EntryId) (hm : i ∈ ids l) : ∃ e, findEntry l i = some e := by
  match l with
  | [] => simp [ids] at hm
  | hd :: tl =>
    unfold findEntry
    by_cases he : hd.id = i
    · simp [he]
    · simp [he]
      have hmem2 : i ∈ ids tl := by
        have : ids (hd :: tl) = hd.id :: ids tl := rfl
        rw [this] at hm
        simp at hm
        rcases hm with h1 | h2
        · exact absurd h1.symm he
        · exact h2
      exact find_mem_aux tl i hmem2

theorem findEntry_some_eq9 {l : List Entry} {i e} (h : findEntry l i = some e) : e.id = i := by
  induction l with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; rw [← h]; exact heq
    · simp [heq] at h; exact ih h

theorem findEntry_some_mem9 {l : List Entry} {i e} (h : findEntry l i = some e) : e ∈ l := by
  induction l with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; rw [h]; simp
    · simp [heq] at h; exact List.Mem.tail _ (ih h)

theorem findEntry_some_ids9 {l : List Entry} {i e} (h : findEntry l i = some e) : i ∈ ids l := by
  have hm := findEntry_some_mem9 h
  have heq := findEntry_some_eq9 h
  unfold ids
  rw [List.mem_map]
  exact ⟨e, hm, by omega⟩

theorem nodup_append_singleton_aux4 {α} (l : List α) (a : α) (hl : l.Nodup) (ha : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have h1 : hd ∉ tl := by
      have := hl
      rw [List.nodup_cons] at this
      exact this.1
    have h2 : tl.Nodup := by
      have := hl
      rw [List.nodup_cons] at this
      exact this.2
    have ha' : a ∉ tl := fun hm => ha (List.mem_cons.mpr (Or.inr hm))
    have h3 : a ≠ hd := fun heq => ha (by rw [heq]; exact List.mem_cons.mpr (Or.inl rfl))
    have ih' := ih h2 ha'
    have goal : (hd :: (tl ++ [a])).Nodup := by
      rw [List.nodup_cons]
      refine ⟨?_, ih'⟩
      intro hmem
      rw [List.mem_append] at hmem
      rcases hmem with hm | hm
      · exact h1 hm
      · simp at hm
        exact h3 hm.symm
    have heq : (hd :: tl ++ [a]) = (hd :: (tl ++ [a])) := by simp
    rw [heq]
    exact goal

theorem checkValidPost_imp_validX (s : State) (e : Entry) (h : checkValidPost s e = true) : ValidPost s e := by
  unfold checkValidPost at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem findEntry_none_of_not_memX (l : List Entry) (i : EntryId) (h : i ∉ ids l) : findEntry l i = none := by
  cases hfind : findEntry l i with
  | none => rfl
  | some e =>
    have hmem := findEntry_some_ids9 hfind
    exact absurd hmem h

theorem findEntry_append_hit_ok (l : List Entry) (e : Entry) (hnotin : e.id ∉ ids l) :
  findEntry (l ++ [e]) e.id = some e := by
  induction l with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have ht : e.id ∉ ids tl := by
      intro hmem
      apply hnotin
      exact List.mem_cons.mpr (Or.inr hmem)
    have hhd : hd.id ≠ e.id := by
      intro heq
      apply hnotin
      simp [ids, heq]
    simp [findEntry, hhd, ih ht]

theorem sumOver_zero2 (accs : List AccountId) : sumOver accs (fun _ => (0 : Int)) = 0 := by
  induction accs with
  | nil => rfl
  | cons hd tl ih => simp [sumOver_cons, ih]

theorem sum_netOf_eq_lineSum2 (accs : List AccountId) (hNodup : accs.Nodup) (ls : List Line) (hall : ∀ l ∈ ls, l.1 ∈ accs) :
  sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have hcongr : sumOver accs (fun a => netOf [] a) = sumOver accs (fun _ => (0 : Int)) := by
      apply sumOver_congr; intro a _; simp [netOf]
    rw [hcongr, sumOver_zero2]; rfl
  | cons hd tl ih =>
    have hall_tl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hall l (List.mem_cons.mpr (Or.inr hl))
    have hmem : hd.1 ∈ accs := hall hd (by simp)
    have h1 : ∀ a, netOf (hd :: tl) a = (if a = hd.1 then hd.2 else 0) + netOf tl a := by
      intro a; simp [netOf, sumOver_cons]
      by_cases h : hd.1 = a
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    have h2 : sumOver accs (fun a => netOf (hd :: tl) a) = sumOver accs (fun a => (if a = hd.1 then hd.2 else 0) + netOf tl a) := by
      apply sumOver_congr; intro a _; rw [h1]
    rw [h2, sumOver_add]
    have h3' : sumOver accs (fun a => if a = hd.1 then hd.2 else (0 : Int)) = hd.2 := by
      rw [sumOver_ite_eq hNodup hd.1 hd.2, if_pos hmem]
    rw [h3', ih hall_tl]
    simp [lineSum, sumOver_cons]

theorem activeNet_append_singleton7 (journal : List Entry) (reversed : List EntryId) (e : Entry) (he_notin_rev : e.id ∉ reversed) (a : AccountId) :
  sumOver (journal ++ [e]) (fun e' => if e'.id ∈ reversed then (0 : Int) else netOf e'.lines a) = sumOver journal (fun e' => if e'.id ∈ reversed then (0 : Int) else netOf e'.lines a) + netOf e.lines a := by
  rw [sumOver_append]
  simp [if_neg he_notin_rev]

theorem activeNet_reverse_aux7 (journal : List Entry) (reversed : List EntryId) (i : EntryId) (e : Entry) (hfind : findEntry journal i = some e) (hnodup : (ids journal).Nodup) (hnotmem : i ∉ reversed) (a : AccountId) :
  sumOver journal (fun e' => if e'.id ∈ (i :: reversed) then (0 : Int) else netOf e'.lines a) = sumOver journal (fun e' => if e'.id ∈ reversed then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  induction journal with
  | nil => simp [findEntry] at hfind
  | cons hd tl ih =>
    simp only [sumOver_cons]
    have hNodupCons : hd.id ∉ ids tl ∧ (ids tl).Nodup := by
      have h : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [h] at hnodup
      exact ⟨(List.nodup_cons.mp hnodup).1, (List.nodup_cons.mp hnodup).2⟩
    simp only [findEntry] at hfind
    by_cases heq_hd : hd.id = i
    · simp [heq_hd] at hfind
      have heq : hd = e := by rw [← hfind]
      have h_hd_new : (if hd.id ∈ (i :: reversed) then (0 : Int) else netOf hd.lines a) = 0 := by simp [heq_hd]
      have h_hd_old : (if hd.id ∈ reversed then (0 : Int) else netOf hd.lines a) = netOf hd.lines a := by simp [hnotmem, heq_hd]
      have h_tl_congr : ∀ x ∈ tl, (if x.id ∈ (i :: reversed) then (0 : Int) else netOf x.lines a) = (if x.id ∈ reversed then (0 : Int) else netOf x.lines a) := by
        intro x hx
        have h_ne : x.id ≠ i := by
          intro heq2
          apply hNodupCons.1
          unfold ids; rw [List.mem_map]; exact ⟨x, hx, by rw [heq2, heq_hd]⟩
        simp [h_ne]
      have h_sum_eq := sumOver_congr tl _ _ h_tl_congr
      rw [heq] at h_hd_new h_hd_old ⊢
      rw [h_hd_new, h_hd_old, h_sum_eq]
      omega
    · simp [heq_hd] at hfind
      have ih' := ih hfind hNodupCons.2
      have h_hd_eq : (if hd.id ∈ (i :: reversed) then (0 : Int) else netOf hd.lines a) = (if hd.id ∈ reversed then (0 : Int) else netOf hd.lines a) := by simp [heq_hd]
      rw [h_hd_eq, ih']
      omega

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  unfold step checkValidPost
  have h1 : e.lines ≠ [] := h.1
  have h2 : ∀ l ∈ e.lines, l.1 ∈ s.accounts := h.2.1
  have h3 : ∀ l ∈ e.lines, l.2 ≠ 0 := h.2.2.1
  have h4 : lineSum e.lines = 0 := h.2.2.2.1
  have h5 : e.id ∉ ids s.journal := h.2.2.2.2.1
  have h6 : e.id ∉ s.reversed := h.2.2.2.2.2
  simp [decide_eq_true h1, decide_eq_true h2, decide_eq_true h3, decide_eq_true h4, decide_eq_true h5, decide_eq_true h6]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  have hmem : i ∈ ids s.journal := h.1
  have hnot : i ∉ s.reversed := h.2
  have hfind : ∃ e, findEntry s.journal i = some e := find_mem_aux s.journal i hmem
  obtain ⟨e, he⟩ := hfind
  unfold step
  simp only [he, hnot, decide_false, ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c hInvalid
  cases c with
  | post e =>
    have hNotValidPost : ¬ ValidPost s e := fun hv => hInvalid hv
    by_cases hc : checkValidPost s e = true
    · have hv := checkValidPost_imp_validX s e hc
      exact absurd hv hNotValidPost
    · simp at hc
      have hstep : step s (Command.post e) = (Outcome.rejected, s) := by
        unfold step; simp [hc]
      exact hstep
  | reverse i =>
    have hNotValidRev : ¬ ValidReverse s i := fun hv => hInvalid hv
    have hOr : i ∉ ids s.journal ∨ i ∈ s.reversed := by
      by_cases h1 : i ∈ ids s.journal
      · by_cases h2 : i ∈ s.reversed
        · exact Or.inr h2
        · exfalso; exact hNotValidRev ⟨h1, h2⟩
      · exact Or.inl h1
    rcases hOr with hNotIn | hInRev
    · have hfindNone : findEntry s.journal i = none := findEntry_none_of_not_memX s.journal i hNotIn
      have hstep : step s (Command.reverse i) = (Outcome.rejected, s) := by
        unfold step; simp [hfindNone]
      exact hstep
    · cases hfind : findEntry s.journal i with
      | none =>
        have hstep : step s (Command.reverse i) = (Outcome.rejected, s) := by
          unfold step; simp [hfind]
        exact hstep
      | some e =>
        have hstep : step s (Command.reverse i) = (Outcome.rejected, s) := by
          unfold step; simp [hfind, hInRev]
        exact hstep

theorem req_post_effects : PostEffects step := by
  intro s e hok
  unfold step at hok ⊢
  cases hc : checkValidPost s e
  · simp [hc] at hok
  · simp [hc]

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hfind
  unfold step
  simp only [hfind]
  have h1 : (if i ∈ s.reversed then (Outcome.rejected, s) else (Outcome.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a })).1 = Outcome.ok := by
    unfold step at hok
    simp only [hfind] at hok
    exact hok
  have hni : i ∉ s.reversed := by
    unfold step at hok
    simp only [hfind] at hok
    by_cases hc : i ∈ s.reversed
    · simp [hc] at hok
    · exact hc
  simp [hni]

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  cases he : findEntry s.journal i with
  | none =>
    unfold step at hok; simp [he] at hok
  | some e =>
    by_cases hr : i ∈ s.reversed
    · unfold step at hok; simp [he, hr] at hok
    · have hstep_eq : step s (.reverse i) = (.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a }) := by
        unfold step; simp [he, hr]
      have hgoal : step ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) (.reverse i) = (.rejected, ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State)) := by
        unfold step; simp [he]
      rw [hstep_eq]
      exact hgoal

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hposts := req_post_effects s e hok
  have hcheck : checkValidPost s e = true := by
    unfold step at hok
    by_cases hc : checkValidPost s e = true
    · exact hc
    · simp [hc] at hok
  have hvalid : ValidPost s e := checkValidPost_imp_validX s e hcheck
  have hnotin_ids : e.id ∉ ids s.journal := hvalid.2.2.2.2.1
  have hnotin_rev : e.id ∉ s.reversed := hvalid.2.2.2.2.2
  have h_journal : (step s (.post e)).2.journal = s.journal ++ [e] := hposts.2.2.1
  have h_rev : (step s (.post e)).2.reversed = s.reversed := hposts.2.2.2.1
  have h_bal : ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := hposts.2.2.2.2
  let s1 := (step s (.post e)).2
  have s1_journal : s1.journal = s.journal ++ [e] := h_journal
  have s1_reversed : s1.reversed = s.reversed := h_rev
  have hfind : findEntry s1.journal e.id = some e := by
    rw [s1_journal]; exact findEntry_append_hit_ok s.journal e hnotin_ids
  have h_rev_succeeds : (step s1 (.reverse e.id)).1 = .ok := by
    unfold step; simp [hfind, s1_reversed, hnotin_rev]
  constructor
  · exact h_rev_succeeds
  · have hrev_effects : ∀ a, (step s1 (.reverse e.id)).2.balance a = s1.balance a - netOf e.lines a := by
      have hge := req_reverse_effects s1 e.id e h_rev_succeeds hfind
      exact hge.2.2.2.2
    funext a
    have h1 := h_bal a
    have h2 := hrev_effects a
    change (step s1 (.reverse e.id)).2.balance a = s.balance a
    rw [h2, h1]; omega

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBalanced⟩ := hwf
  cases c with
  | post e =>
    unfold step at hok ⊢
    cases hc : checkValidPost s e with
    | false => simp [hc] at hok
    | true =>
      simp only [hc, ↓reduceIte] at hok ⊢
      unfold total
      have hvalid := checkValidPost_imp_validX s e hc
      have hall : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hvalid.2.1
      have hzero : lineSum e.lines = 0 := hvalid.2.2.2.1
      have h1 : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := sumOver_add s.accounts s.balance (fun a => netOf e.lines a)
      rw [h1, sum_netOf_eq_lineSum2 s.accounts hNodupAcc e.lines hall, hzero, Int.add_zero]
  | reverse i =>
    unfold step at hok ⊢
    cases hfind : findEntry s.journal i with
    | none => simp [hfind] at hok
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · simp [hfind, hmem] at hok
      · simp only [hfind, hmem, ↓reduceIte] at hok ⊢
        unfold total
        have hmemEntry : e ∈ s.journal := findEntry_some_mem9 hfind
        have hprop := hBalanced e hmemEntry
        have hall : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hprop.1
        have hzero : lineSum e.lines = 0 := hprop.2
        have h1 : sumOver s.accounts (fun a => s.balance a - netOf e.lines a) = sumOver s.accounts s.balance - sumOver s.accounts (fun a => netOf e.lines a) := sumOver_sub s.accounts s.balance (fun a => netOf e.lines a)
        rw [h1, sum_netOf_eq_lineSum2 s.accounts hNodupAcc e.lines hall, hzero, Int.sub_zero]

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBalanced⟩ := hwf
  cases c with
  | post e =>
    show WellFormed (step s (Command.post e)).2
    unfold step
    simp only
    by_cases hvalid : checkValidPost s e = true
    · simp [hvalid]
      refine ⟨hNodupAcc, ?_, ?_, ?_⟩
      · show (ids (s.journal ++ [e])).Nodup
        rw [show ids (s.journal ++ [e]) = ids s.journal ++ [e.id] from by simp [ids]]
        have h_notin : e.id ∉ ids s.journal := by
          unfold checkValidPost at hvalid
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
          obtain ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩ := hvalid
          exact h5
        exact nodup_append_singleton_aux4 (ids s.journal) e.id hNodupIds h_notin
      · intro j hj
        show j ∈ ids (s.journal ++ [e])
        have hmem_old := hRevSub j hj
        rw [show ids (s.journal ++ [e]) = ids s.journal ++ [e.id] from by simp [ids]]
        exact List.mem_append.mpr (Or.inl hmem_old)
      · intro e2 he2
        have hmem : e2 ∈ s.journal ∨ e2 = e := by
          have : e2 ∈ s.journal ++ [e] := he2
          rw [List.mem_append] at this
          rcases this with h | h
          · left; exact h
          · right; simp at h; exact h
        rcases hmem with hm | heq
        · exact hBalanced e2 hm
        · rw [heq]
          have h1 : ∀ (ln : Line), ln ∈ e.lines → ln.1 ∈ s.accounts := by
            unfold checkValidPost at hvalid
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
            obtain ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩ := hvalid
            exact h2
          have h2 : lineSum e.lines = 0 := by
            unfold checkValidPost at hvalid
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
            obtain ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩ := hvalid
            exact h4
          exact ⟨h1, h2⟩
    · simp [hvalid]
      exact ⟨hNodupAcc, hNodupIds, hRevSub, hBalanced⟩
  | reverse i =>
    show WellFormed (step s (Command.reverse i)).2
    unfold step
    simp only
    cases hfind : findEntry s.journal i with
    | none =>
      simp [hfind]
      exact ⟨hNodupAcc, hNodupIds, hRevSub, hBalanced⟩
    | some entry =>
      by_cases hmem : i ∈ s.reversed
      · simp [hfind, hmem]
        exact ⟨hNodupAcc, hNodupIds, hRevSub, hBalanced⟩
      · simp [hfind, hmem]
        have hids_mem : i ∈ ids s.journal := findEntry_some_ids9 hfind
        refine ⟨hNodupAcc, hNodupIds, ?_, hBalanced⟩
        intro j hj
        simp at hj
        rcases hj with rfl | hj2
        · exact hids_mem
        · exact hRevSub j hj2

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBalanced⟩ := hwf
  cases c with
  | post e =>
    show Consistent (step s (Command.post e)).2
    unfold step
    by_cases hvalid : checkValidPost s e = true
    · simp only [hvalid, ↓reduceIte]
      intro a
      have h_bal_s : s.balance a = s.opening a + activeNet s a := hcons a
      have hvalidP := checkValidPost_imp_validX s e hvalid
      have he_notin_rev : e.id ∉ s.reversed := hvalidP.2.2.2.2.2
      have h_eq : sumOver (s.journal ++ [e]) (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a) = sumOver s.journal (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a) + netOf e.lines a := activeNet_append_singleton7 s.journal s.reversed e he_notin_rev a
      have : activeNet ({ s with journal := s.journal ++ [e] } : State) a = sumOver (s.journal ++ [e]) (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a) := rfl
      have h_eq2 : activeNet ({ s with journal := s.journal ++ [e], reversed := s.reversed } : State) a = activeNet s a + netOf e.lines a := by
        unfold activeNet; simp only; exact h_eq
      have h_irrel : activeNet ({ s with journal := s.journal ++ [e], reversed := s.reversed, balance := fun a => s.balance a + netOf e.lines a, accounts := s.accounts, opening := s.opening } : State) a = activeNet ({ s with journal := s.journal ++ [e], reversed := s.reversed } : State) a := rfl
      show s.balance a + netOf e.lines a = s.opening a + activeNet ({ s with journal := s.journal ++ [e], reversed := s.reversed, balance := fun a => s.balance a + netOf e.lines a, accounts := s.accounts, opening := s.opening } : State) a
      rw [h_irrel, h_eq2]
      omega
    · simp [hvalid]
      exact hcons
  | reverse i =>
    show Consistent (step s (Command.reverse i)).2
    unfold step
    cases hfind : findEntry s.journal i with
    | none =>
      simp [hfind]
      exact hcons
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · simp [hfind, hmem]
        exact hcons
      · simp only [hfind, hmem, ↓reduceIte]
        intro a
        have h_bal_s : s.balance a = s.opening a + activeNet s a := hcons a
        have h_sub : activeNet ({ s with reversed := i :: s.reversed } : State) a = activeNet s a - netOf e.lines a := by
          unfold activeNet; simp only
          exact activeNet_reverse_aux7 s.journal s.reversed i e hfind hNodupIds hmem a
        have h_irrel : activeNet ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal } : State) a = activeNet ({ s with reversed := i :: s.reversed } : State) a := rfl
        show s.balance a - netOf e.lines a = s.opening a + activeNet ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal } : State) a
        rw [h_irrel, h_sub]
        omega

end Reversal
