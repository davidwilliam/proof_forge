import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance
instance instDecidableValidReverse (s : State) (i : EntryId) : Decidable (ValidReverse s i) := by
  unfold ValidReverse; infer_instance
/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b
/-- Post every line, first to last. -/
def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)
def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    if ValidReverse s i then
      match findEntry s.journal i with
      | some e =>
        (.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                       reversed := i :: s.reversed })
      | none => (.rejected, s)
    else (.rejected, s)

theorem findEntry_some_of_mem : ∀ (js : List Entry) (i : EntryId), i ∈ ids js → ∃ e, findEntry js i = some e := by
  intro js i h
  induction js with
  | nil => simp [ids] at h
  | cons e es ih =>
    simp only [ids, List.map_cons, List.mem_cons] at h
    simp only [findEntry]
    by_cases he : e.id = i
    · simp [he]
    · simp [he]
      rcases h with h | h
      · exact absurd h (Ne.symm he)
      · exact ih h

theorem netOf_cons (l : Line) (ls : List Line) (a : AccountId) :
    netOf (l :: ls) a = (if l.1 = a then l.2 else 0) + netOf ls a := by
  simp [netOf]

theorem postLines_apply_aux (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    postLines ls bal a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil => simp [postLines, netOf]
  | cons l ls ih =>
    simp only [postLines, netOf_cons]
    have ih' := ih (adjust bal l.1 l.2)
    rw [ih']
    unfold adjust
    by_cases h : a = l.1
    · simp only [h, ite_true]; omega
    · have h2 : l.1 ≠ a := fun h2 => h h2.symm
      simp only [h, h2, ite_false]; omega

theorem sumOver_zero_aux {α : Type} (l : List α) : sumOver l (fun _ => (0:Int)) = 0 := by
  induction l with
  | nil => simp [sumOver]
  | cons a t ih => simp [sumOver_cons, ih]

theorem sum_netOf_eq_lineSum_aux (ls : List Line) (acs : List AccountId) (hsub : ∀ l ∈ ls, l.1 ∈ acs) (hNodup : acs.Nodup) :
    sumOver acs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have h1 : sumOver acs (fun a => netOf [] a) = 0 := by
      have hc : ∀ a ∈ acs, netOf ([] : List Line) a = (0:Int) := by intro a _; rfl
      have := sumOver_congr acs (fun a => netOf [] a) (fun _ => (0:Int)) hc
      rw [this, sumOver_zero_aux]
    simp [lineSum, sumOver] at *
    -- lineSum [] =0, and sum =0
    rw [h1]
  | cons l ls ih =>
    have hsub_tail : ∀ x, x ∈ ls → x.1 ∈ acs := fun x hx => hsub x (by simp [hx])
    have hsub_head : l.1 ∈ acs := hsub l (by simp)
    have h_expand : ∀ a, netOf (l :: ls) a = (if l.1 = a then l.2 else 0) + netOf ls a := fun a => netOf_cons l ls a
    have h_congr_sum : sumOver acs (fun a => netOf (l :: ls) a) = sumOver acs (fun a => (if l.1 = a then l.2 else 0) + netOf ls a) := by
      apply sumOver_congr; intro a _; exact h_expand a
    rw [h_congr_sum, sumOver_add]
    have h1 : sumOver acs (fun a => if l.1 = a then l.2 else 0) = l.2 := by
      have h_eq : sumOver acs (fun a => if l.1 = a then l.2 else 0) = sumOver acs (fun a => if a = l.1 then l.2 else 0) := by
        apply sumOver_congr; intro a _; simp [eq_comm]
      rw [h_eq]
      have := sumOver_ite_eq hNodup l.1 l.2
      simp [hsub_head] at this
      exact this
    rw [h1, ih hsub_tail]
    simp [lineSum]

theorem postLines_total_aux (ls : List Line) (bal : AccountId → Int) (acs : List AccountId) (hsub : ∀ l ∈ ls, l.1 ∈ acs) (hNodup : acs.Nodup) (hbal : lineSum ls = 0) :
    sumOver acs (postLines ls bal) = sumOver acs bal := by
  have hadd : ∀ a, postLines ls bal a = bal a + netOf ls a := fun a => postLines_apply_aux ls bal a
  have hcongr : sumOver acs (postLines ls bal) = sumOver acs (fun a => bal a + netOf ls a) := by
    apply sumOver_congr; intro a _; exact hadd a
  rw [hcongr, sumOver_add, sum_netOf_eq_lineSum_aux ls acs hsub hNodup, hbal]
  omega

theorem neg_lineSum_aux (ls : List Line) : lineSum (ls.map (fun l => (l.1, -l.2))) = - lineSum ls := by
  simp only [lineSum]
  induction ls with
  | nil => simp
  | cons a ls ih => simp [ih]; omega

theorem postLines_neg_total_aux (ls : List Line) (bal : AccountId → Int) (acs : List AccountId) (hsub : ∀ l ∈ ls, l.1 ∈ acs) (hNodup : acs.Nodup) (hbal : lineSum ls = 0) :
    sumOver acs (postLines (ls.map (fun l => (l.1, -l.2))) bal) = sumOver acs bal := by
  have hsub' : ∀ l ∈ ls.map (fun l => (l.1, -l.2)), l.1 ∈ acs := by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨l0, hl0_mem, rfl⟩ := hl
    exact hsub l0 hl0_mem
  have hsum' : lineSum (ls.map (fun l => (l.1, -l.2))) = 0 := by
    rw [neg_lineSum_aux, hbal]; simp
  exact postLines_total_aux _ bal acs hsub' hNodup hsum'

theorem findEntry_mem_aux (js : List Entry) (i : EntryId) (e : Entry) (he : findEntry js i = some e) : e ∈ js := by
  induction js with
  | nil => simp [findEntry] at he
  | cons hd tl ih =>
    simp [findEntry] at he
    by_cases hh : hd.id = i
    · simp [hh] at he; rw [← he]; simp
    · simp [hh] at he
      have := ih he
      simp [this]

theorem nodup_append_singleton_final {α : Type} [DecidableEq α] (l : List α) (x : α) (hN : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hN_cons := List.nodup_cons.mp hN
    have hN1 : a ∉ t := hN_cons.1
    have hN2 : t.Nodup := hN_cons.2
    have hx1 : x ≠ a := by
      intro heq
      subst heq
      exact hx (List.mem_cons.mpr (Or.inl rfl))
    have hx2 : x ∉ t := by
      intro hm
      exact hx (List.mem_cons.mpr (Or.inr hm))
    have ih' : (t ++ [x]).Nodup := ih hN2 hx2
    have heq : (a :: t) ++ [x] = a :: (t ++ [x]) := rfl
    rw [heq]
    rw [List.nodup_cons]
    constructor
    · intro hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact hN1 hm
      · simp at hm
        exact hx1 hm.symm
    · exact ih'

theorem ids_append_aux_final (js : List Entry) (e : Entry) : ids (js ++ [e]) = ids js ++ [e.id] := by
  simp [ids]

theorem wellFormed_post_valid_final (s : State) (e : Entry) (hW : WellFormed s) (hv : ValidPost s e) :
    WellFormed { s with journal := s.journal ++ [e], balance := postLines e.lines s.balance } := by
  have hW1 := hW.1
  have hW2 := hW.2.1
  have hW3 := hW.2.2.1
  have hW4 := hW.2.2.2
  have hV2 : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hv.2.1
  have hV4 : lineSum e.lines = 0 := hv.2.2.2.1
  have hV5 : e.id ∉ ids s.journal := hv.2.2.2.2.1
  unfold WellFormed
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hW1
  · rw [ids_append_aux_final]
    exact nodup_append_singleton_final (ids s.journal) e.id hW2 hV5
  · intro i hi
    rw [ids_append_aux_final]
    apply List.mem_append.mpr
    left
    exact hW3 i hi
  · intro e' he'
    rw [List.mem_append] at he'
    rcases he' with he' | he'
    · exact hW4 e' he'
    · simp at he'
      subst he'
      exact ⟨hV2, hV4⟩

theorem wellFormed_reverse_valid_final (s : State) (i : EntryId) (e : Entry) (hW : WellFormed s) (hv : ValidReverse s i) (he : findEntry s.journal i = some e) :
    WellFormed { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed } := by
  unfold WellFormed
  refine ⟨hW.1, hW.2.1, ?_, hW.2.2.2⟩
  intro j hj
  simp at hj
  rcases hj with rfl | hj
  · exact hv.1
  · exact hW.2.2.1 j hj

theorem dummy_lemma : 1+1 = (2:Nat) := by rfl

theorem activeNet_post_eq2 (s : State) (e : Entry) (hv : ValidPost s e) (a : AccountId) :
    activeNet { s with journal := s.journal ++ [e] } a = activeNet s a + netOf e.lines a := by
  unfold activeNet
  rw [sumOver_append]
  have h : e.id ∉ s.reversed := hv.2.2.2.2.2
  simp [h]

theorem neg_netOf2 (ls : List Line) (a : AccountId) :
    netOf (ls.map (fun l => (l.1, -l.2))) a = - netOf ls a := by
  induction ls with
  | nil => simp [netOf]
  | cons hd tl ih =>
    simp [netOf_cons, ih]
    by_cases h : hd.1 = a <;> simp [h] <;> omega

theorem postLines_neg_apply2 (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    postLines (ls.map (fun l => (l.1, -l.2))) bal a = bal a - netOf ls a := by
  have h1 := postLines_apply_aux (ls.map (fun l => (l.1, -l.2))) bal a
  rw [neg_netOf2 ls a] at h1
  omega

theorem sumOver_congr_active_reverse2 (tl : List Entry) (rs : List EntryId) (i : EntryId) (a : AccountId) (hNodup : (ids tl).Nodup) (hNotIn : i ∉ ids tl) :
    sumOver tl (fun e => if e.id ∈ i :: rs then (0:Int) else netOf e.lines a) = sumOver tl (fun e => if e.id ∈ rs then (0:Int) else netOf e.lines a) := by
  apply sumOver_congr
  intro e he
  have hid : e.id ∈ ids tl := by simp [ids]; exact ⟨e, he, rfl⟩
  have hne : e.id ≠ i := by intro heq; rw [heq] at hid; exact hNotIn hid
  simp [hne]

theorem activeNet_reverse_lemma4b : ∀ (js : List Entry) (rs : List EntryId) (i : EntryId) (e : Entry),
    (ids js).Nodup → i ∈ ids js → i ∉ rs → findEntry js i = some e → ∀ a, sumOver js (fun e' => if e'.id ∈ i :: rs then (0:Int) else netOf e'.lines a) = sumOver js (fun e' => if e'.id ∈ rs then (0:Int) else netOf e'.lines a) - netOf e.lines a := by
  intro js
  induction js with
  | nil =>
    intro rs i e hNodup hmem hNot hFind
    simp [ids] at hmem
  | cons hd tl ih =>
    intro rs i e hNodup hmem hNot hFind a
    have hNodup_tl : (ids tl).Nodup := by
      have h : (hd.id :: ids tl).Nodup := by simpa [ids] using hNodup
      exact (List.nodup_cons.mp h).2
    have hNotIn_cons : hd.id ∉ ids tl := by
      have h : (hd.id :: ids tl).Nodup := by simpa [ids] using hNodup
      exact (List.nodup_cons.mp h).1
    simp only [sumOver_cons]
    by_cases hhd : hd.id = i
    · have hFindHd : findEntry (hd :: tl) i = some hd := by simp [findEntry, hhd]
      have heq : e = hd := by
        have h1 : findEntry (hd :: tl) i = some e := hFind
        rw [hFindHd] at h1
        exact (Option.some_inj.mp h1).symm
      rw [heq]
      have hNotInIds : i ∉ ids tl := by rw [← hhd]; exact hNotIn_cons
      have hcongr := sumOver_congr_active_reverse2 tl rs i a hNodup_tl hNotInIds
      have h1 : (if hd.id ∈ i :: rs then (0:Int) else netOf hd.lines a) = 0 := by simp [hhd]
      have h2 : (if hd.id ∈ rs then (0:Int) else netOf hd.lines a) = netOf hd.lines a := by
        have : hd.id ∉ rs := by rw [hhd]; exact hNot
        simp [this]
      rw [h1, h2, hcongr]
      omega
    · have hH : findEntry tl i = some e := by
        have : findEntry (hd :: tl) i = findEntry tl i := by simp [findEntry, hhd]
        rw [this] at hFind; exact hFind
      have hhd_eq : (if hd.id ∈ i :: rs then (0:Int) else netOf hd.lines a) = (if hd.id ∈ rs then (0:Int) else netOf hd.lines a) := by
        have : hd.id ≠ i := hhd
        simp [this]
      rw [hhd_eq]
      have hmem_tl : i ∈ ids tl := by
        have hids : ids (hd :: tl) = hd.id :: ids tl := by simp [ids]
        rw [hids] at hmem
        simp at hmem
        rcases hmem with h | h
        · exact absurd h.symm hhd
        · exact h
      have ih' := ih rs i e hNodup_tl hmem_tl hNot hH a
      omega

theorem findEntry_append_hit3b {js : List Entry} {e : Entry} (hNotIn : e.id ∉ ids js) : findEntry (js ++ [e]) e.id = some e := by
  induction js with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    simp [findEntry]
    have hhd : hd.id ≠ e.id := by
      intro hc
      have : e.id ∈ ids (hd :: tl) := by simp [ids, hc]
      exact hNotIn this
    simp [hhd]
    exact ih (fun hm => hNotIn (List.mem_cons.mpr (Or.inr hm)))

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  simp only [step]
  have hv : ValidReverse s i := h
  simp [hv]
  have hmem : i ∈ ids s.journal := h.1
  obtain ⟨e, he⟩ := findEntry_some_of_mem s.journal i hmem
  simp [he]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    simp only [Valid] at h
    simp only [step, h, ite_false]
  | reverse i =>
    simp only [Valid] at h
    simp only [step, h, ite_false]

theorem req_post_effects : PostEffects step := by
  intro s e hOk
  by_cases hv : ValidPost s e
  · simp [step, hv, postLines_apply_aux]
  · have hStep : step s (.post e) = (.rejected, s) := by simp [step, hv]
    have h1 : (step s (.post e)).1 = .rejected := by rw [hStep]
    rw [h1] at hOk
    simp at hOk

theorem req_reverse_effects  : ReverseEffects step := by
  intro s i e hOk hFind
  by_cases hVR : ValidReverse s i
  · have hStepEq : step s (.reverse i) = (.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed }) := by
      simp [step, hVR, hFind]
    have hBalEq : (step s (.reverse i)).2.balance = postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance := by
      rw [hStepEq]
    have hRevEq : (step s (.reverse i)).2.reversed = i :: s.reversed := by
      rw [hStepEq]
    have hAccEq : (step s (.reverse i)).2.accounts = s.accounts := by rw [hStepEq]
    have hOpEq : (step s (.reverse i)).2.opening = s.opening := by rw [hStepEq]
    have hJEq : (step s (.reverse i)).2.journal = s.journal := by rw [hStepEq]
    refine ⟨hAccEq, hOpEq, hJEq, ?_, ?_⟩
    · intro x
      rw [hRevEq]
      simp
    · intro a
      rw [hBalEq]
      rw [postLines_neg_apply2 e.lines s.balance a]
  · have hRej : (step s (.reverse i)).1 = .rejected := by simp [step, hVR]
    rw [hRej] at hOk
    cases hOk

theorem req_reverse_once : ReverseOnce step := by
  intro s i h
  by_cases hVR : ValidReverse s i
  · have hmem : i ∈ ids s.journal := hVR.1
    obtain ⟨e, he⟩ := findEntry_some_of_mem s.journal i hmem
    have hstep_eq : step s (.reverse i) = (.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed }) := by
      simp [step, hVR, he]
    have hstate_eq : (step s (.reverse i)).2 = { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed } := by
      rw [hstep_eq]
    rw [hstate_eq]
    have hNotValid : ¬ ValidReverse { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed } i := by
      simp only [ValidReverse]
      simp
    simp [step, hNotValid]
  · have h1 : step s (.reverse i) = (.rejected, s) := by simp [step, hVR]
    have h2 : (step s (.reverse i)).1 = .rejected := by simp [h1]
    rw [h2] at h
    cases h

theorem req_roundtrip : RoundTrip step := by
  intro s e hOk
  have hv : ValidPost s e := by
    by_cases h : ValidPost s e
    · exact h
    · have : (step s (.post e)).1 = .rejected := by simp [step, h]
      rw [this] at hOk
      cases hOk
  have hStepPost : step s (.post e) = (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by simp [step, hv]
  have hIdsApp : e.id ∈ ids (s.journal ++ [e]) := by simp [ids_append_aux_final]
  have hRevValid : ValidReverse { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } e.id :=
    ⟨hIdsApp, hv.2.2.2.2.2⟩
  have hFind : findEntry (s.journal ++ [e]) e.id = some e := findEntry_append_hit3b hv.2.2.2.2.1
  have hPost2Eq : (step s (.post e)).2 = { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } := by simp [hStepPost]
  constructor
  · rw [hPost2Eq]
    simp [step, hRevValid, hFind]
  · rw [hPost2Eq]
    have hBal : (step { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } (.reverse e.id)).2.balance = postLines (e.lines.map (fun l => (l.1, -l.2))) (postLines e.lines s.balance) := by
      have hs : step { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } (.reverse e.id) = (.ok, { s with journal := s.journal ++ [e], reversed := e.id :: s.reversed, balance := postLines (e.lines.map (fun l => (l.1, -l.2))) (postLines e.lines s.balance) }) := by
        simp [step, hRevValid, hFind]
      simp [hs]
    rw [hBal]
    funext a
    rw [postLines_neg_apply2 e.lines (postLines e.lines s.balance) a]
    rw [postLines_apply_aux e.lines s.balance a]
    omega

theorem req_trial_balance : TrialBalance step := by
  intro s c hW hOk
  cases c with
  | post e =>
    simp only [step] at hOk ⊢
    by_cases hv : ValidPost s e
    · simp [hv] at hOk ⊢
      -- hOk is now irrelevant, we have hv
      unfold total
      -- Need to show sumOver s.accounts (postLines e.lines s.balance) = sumOver s.accounts s.balance
      have hNodup : s.accounts.Nodup := hW.1
      have hsub : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hv.2.1
      have hbal : lineSum e.lines = 0 := hv.2.2.2.1
      exact postLines_total_aux e.lines s.balance s.accounts hsub hNodup hbal
    · simp [hv] at hOk
  | reverse i =>
    simp only [step] at hOk ⊢
    by_cases hv : ValidReverse s i
    · simp [hv] at hOk ⊢
      obtain ⟨e, he⟩ := findEntry_some_of_mem s.journal i hv.1
      simp [he] at hOk ⊢
      unfold total
      have hNodup : s.accounts.Nodup := hW.1
      have heMem : e ∈ s.journal := findEntry_mem_aux s.journal i e he
      have hEntryWF := hW.2.2.2 e heMem
      have hsub : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hEntryWF.1
      have hbal : lineSum e.lines = 0 := hEntryWF.2
      exact postLines_neg_total_aux e.lines s.balance s.accounts hsub hNodup hbal
    · simp [hv] at hOk

theorem req_well_formed : StaysWellFormed step := by
  intro s c hW
  cases c with
  | post e =>
    simp only [step]
    by_cases hv : ValidPost s e
    · simp [hv]
      exact wellFormed_post_valid_final s e hW hv
    · simp [hv]
      exact hW
  | reverse i =>
    simp only [step]
    by_cases hv : ValidReverse s i
    · simp [hv]
      have hmem : i ∈ ids s.journal := hv.1
      obtain ⟨e, he⟩ := findEntry_some_of_mem s.journal i hmem
      simp [he]
      exact wellFormed_reverse_valid_final s i e hW hv he
    · simp [hv]
      exact hW

theorem req_consistent : StaysConsistent step := by
  intro s c hW hC
  cases c with
  | post e =>
    simp only [step] at *
    by_cases hv : ValidPost s e
    · simp only [hv, ite_true]
      unfold Consistent at *
      intro a
      show (postLines e.lines s.balance) a = s.opening a + activeNet { s with journal := s.journal ++ [e] } a
      rw [postLines_apply_aux, activeNet_post_eq2 s e hv a, hC a]
      omega
    · simp [hv]
      exact hC
  | reverse i =>
    simp only [step] at *
    by_cases hv : ValidReverse s i
    · simp only [hv, ite_true]
      obtain ⟨e, he⟩ := findEntry_some_of_mem s.journal i hv.1
      simp only [he]
      unfold Consistent at *
      intro a
      show (postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance) a = s.opening a + activeNet { s with reversed := i :: s.reversed } a
      rw [postLines_neg_apply2 e.lines s.balance a, hC a]
      have hAct : activeNet { s with reversed := i :: s.reversed } a = activeNet s a - netOf e.lines a := by
        have hNodup : (ids s.journal).Nodup := hW.2.1
        have hLemma := activeNet_reverse_lemma4b s.journal s.reversed i e hNodup hv.1 hv.2 he a
        unfold activeNet at hLemma ⊢
        exact hLemma
      rw [hAct]
      omega
    · simp [hv]
      exact hC

end Reversal
