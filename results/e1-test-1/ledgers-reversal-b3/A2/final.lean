import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance
def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | some e =>
      if i ∈ s.reversed then (.rejected, s)
      else (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed })
    | none => (.rejected, s)

theorem findEntry_of_mem_ids_aux (j : List Entry) (i : EntryId) (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons e es ih =>
    by_cases he : e.id = i
    · exact ⟨e, by simp [findEntry, he]⟩
    · have hne : i ≠ e.id := fun contra => he contra.symm
      have h2 : i ∈ ids es := by
        have hmem : i ∈ e.id :: ids es := by have := h; rwa [ids, List.map_cons] at h
        simp [hne] at hmem
        exact hmem
      obtain ⟨e', he'⟩ := ih h2
      exact ⟨e', by simp [findEntry, he, he']⟩

theorem findEntry_none_of_not_mem' (j : List Entry) (i : EntryId) (h : i ∉ ids j) : findEntry j i = none := by
  induction j with
  | nil => simp [findEntry]
  | cons e es ih =>
    have hne : e.id ≠ i := by
      intro heq
      apply h
      have : e.id ∈ ids (e :: es) := by simp [ids]
      rwa [heq] at this
    have htail : i ∉ ids es := by
      intro hmem
      apply h
      simp only [ids, List.map_cons, List.mem_cons]
      exact Or.inr hmem
    simp [findEntry, hne, ih htail]

theorem req_post_effects_aux : PostEffects step := by
  intro s e hok
  by_cases h : ValidPost s e
  · simp [step, h]
  · simp [step, h] at hok

theorem findEntry_append_notmem_aux (j1 : List Entry) (j2 : List Entry) (i : EntryId) (h : i ∉ ids j1) : findEntry (j1 ++ j2) i = findEntry j2 i := by
  induction j1 with
  | nil => simp
  | cons e es ih =>
    have hne : ¬ (e.id = i) := by
      intro heq
      apply h
      simp only [ids, List.map_cons, List.mem_cons]
      exact Or.inl heq.symm
    have htail : i ∉ ids es := by
      intro hmem
      apply h
      simp only [ids, List.map_cons, List.mem_cons]
      exact Or.inr hmem
    simp only [List.cons_append]
    simp only [findEntry, hne, ↓reduceIte, ih htail]

theorem roundtrip_debug_aux (s : State) (e : Entry) (hvalid : ValidPost s e) :
    findEntry (s.journal ++ [e]) e.id = some e := by
  have h1 : findEntry (s.journal ++ [e]) e.id = findEntry [e] e.id :=
    findEntry_append_notmem_aux s.journal [e] e.id hvalid.2.2.2.2.1
  rw [h1]
  unfold findEntry
  simp

theorem sumOver_zero_list_aux (l : List AccountId) : sumOver l (fun _ : AccountId => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [sumOver_cons, ih, Int.add_zero]

theorem indicator_swap_aux (accs : List AccountId) (x : AccountId) (c : Int) :
    sumOver accs (fun a => if x = a then c else (0 : Int)) = sumOver accs (fun a => if a = x then c else (0 : Int)) := by
  apply sumOver_congr
  intro a _
  by_cases h1 : x = a
  · subst h1; rfl
  · have h2 : ¬ (a = x) := fun h => h1 h.symm
    rw [if_neg h1, if_neg h2]

theorem indicator_eval_aux (accs : List AccountId) (hnd : accs.Nodup) (x : AccountId) (c : Int) :
    sumOver accs (fun a => if x = a then c else (0 : Int)) = if x ∈ accs then c else 0 := by
  rw [indicator_swap_aux accs x c]
  exact sumOver_ite_eq hnd x c

theorem netSum_aux2 (accs : List AccountId) (hnd : accs.Nodup) (ls : List Line) (hmem : ∀ l ∈ ls, l.1 ∈ accs) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  unfold netOf lineSum
  induction ls with
  | nil =>
    have : (fun a : AccountId => sumOver ([] : List Line) (fun l : Line => if l.1 = a then l.2 else (0 : Int))) = (fun _ : AccountId => (0 : Int)) := by rfl
    rw [this]
    exact sumOver_zero_list_aux accs
  | cons hd tl ih =>
    have hhead : hd.1 ∈ accs := hmem hd (by simp)
    have htail : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hmem l (by simp [hl])
    have hexpand : ∀ a : AccountId, (sumOver (hd :: tl) (fun l : Line => if l.1 = a then l.2 else (0 : Int))) = (if hd.1 = a then hd.2 else (0 : Int)) + sumOver tl (fun l : Line => if l.1 = a then l.2 else (0 : Int)) := by intro a; rfl
    have hLHS : sumOver accs (fun a => sumOver (hd :: tl) (fun l : Line => if l.1 = a then l.2 else (0 : Int))) = sumOver accs (fun a => (if hd.1 = a then hd.2 else (0 : Int))) + sumOver accs (fun a => sumOver tl (fun l : Line => if l.1 = a then l.2 else (0 : Int))) := by
      have hsa := sumOver_add accs (fun a => (if hd.1 = a then hd.2 else (0 : Int))) (fun a => sumOver tl (fun l : Line => if l.1 = a then l.2 else (0 : Int)))
      rw [← hsa]
      apply sumOver_congr
      intro a _
      exact hexpand a
    rw [hLHS, ih htail, indicator_eval_aux accs hnd hd.1 hd.2, if_pos hhead]
    simp only [sumOver_cons]

theorem findEntry_mem_aux3 (j : List Entry) (i : EntryId) (e : Entry) (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    split at h
    · next heq =>
      cases h
      simp
    · next hne =>
      exact List.mem_cons_of_mem hd (ih h)

theorem total_add_net_aux (s : State) (ls : List Line) : total { s with balance := fun a => s.balance a + netOf ls a } = total s + sumOver s.accounts (fun a => netOf ls a) := by
  unfold total
  simp only [sumOver_add]

theorem total_sub_net_aux (s : State) (ls : List Line) : total { s with balance := fun a => s.balance a - netOf ls a } = total s - sumOver s.accounts (fun a => netOf ls a) := by
  unfold total
  simp only [sumOver_sub]

theorem netSum_zero_aux_helper (accs : List AccountId) (hnd : accs.Nodup) (ls : List Line) (hmem : ∀ l ∈ ls, l.1 ∈ accs) (hzero : lineSum ls = 0) : sumOver accs (fun a => netOf ls a) = 0 := by
  rw [netSum_aux2 accs hnd ls hmem, hzero]

theorem nodup_append_singleton_aux (l : List Nat) (a : Nat) (h1 : l.Nodup) (h2 : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    rw [List.nodup_cons] at h1
    have h2' : a ∉ tl := fun h => h2 (List.mem_cons_of_mem hd h)
    have hne : hd ≠ a := fun heq => h2 (heq ▸ List.mem_cons_self)
    rw [List.cons_append]
    rw [List.nodup_cons]
    constructor
    · intro hmem
      rw [List.mem_append] at hmem
      cases hmem with
      | inl h => exact h1.1 h
      | inr h =>
        simp at h
        exact hne h
    · exact ih h1.2 h2'

theorem findEntry_some_mem_ids_aux2 (j : List Entry) (i : EntryId) (e : Entry) (h : findEntry j i = some e) : i ∈ ids j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    split at h
    · next heq => cases h; subst heq; simp [ids]
    · next hne =>
      have := ih h
      simp only [ids, List.map_cons, List.mem_cons]
      exact Or.inr this

theorem ids_append_single_aux (j : List Entry) (e : Entry) : ids (j ++ [e]) = ids j ++ [e.id] := by
  simp [ids]

theorem findEntry_id_eq_aux (j : List Entry) (i : EntryId) (e : Entry) (h : findEntry j i = some e) : e.id = i := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    split at h
    · next heq => cases h; exact heq
    · next hne => exact ih h

theorem activeNet_post_aux (s : State) (e : Entry) (a : AccountId) (hnotrev : e.id ∉ s.reversed) :
    activeNet { s with journal := s.journal ++ [e] } a = activeNet s a + netOf e.lines a := by
  unfold activeNet
  simp only [sumOver_append]
  have h : (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a) e = netOf e.lines a := by
    simp [hnotrev]
  simp [h]

theorem activeNet_tail_eq_aux (tl : List Entry) (rev : List EntryId) (i : EntryId) (a : AccountId)
    (h : ∀ e' ∈ tl, e'.id ≠ i) :
    sumOver tl (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a)
    = sumOver tl (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) := by
  apply sumOver_congr
  intro e' he'
  have hne : e'.id ≠ i := h e' he'
  have heq : (e'.id ∈ i :: rev) = (e'.id ∈ rev) := by
    simp [hne]
  simp [heq]

theorem tail_ids_ne_aux2 (hd : Entry) (tl : List Entry) (i : EntryId)
    (hnd : (ids (hd :: tl)).Nodup) (hhd : hd.id = i) (e' : Entry) (hmem : e' ∈ tl) : e'.id ≠ i := by
  simp only [ids, List.map_cons, List.nodup_cons] at hnd
  intro hcon
  apply hnd.1
  have hmaps : e'.id ∈ List.map (fun x => x.id) tl := List.mem_map_of_mem hmem
  have heq : e'.id = hd.id := Eq.trans hcon hhd.symm
  rw [heq] at hmaps
  exact hmaps

theorem activeNet_reverse_aux4 (j : List Entry) (rev : List EntryId) (i : EntryId) (a : AccountId) (e : Entry)
    (hfind : findEntry j i = some e) (hnd : (ids j).Nodup) (hnotrev : i ∉ rev) :
    sumOver j (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a)
    = sumOver j (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  induction j generalizing rev with
  | nil => simp [findEntry] at hfind
  | cons hd tl ih =>
    by_cases heq : hd.id = i
    · have hfe : findEntry (hd :: tl) i = some hd := by simp [findEntry, heq]
      rw [hfe] at hfind
      have hde : hd = e := by cases hfind; rfl
      simp only [sumOver_cons]
      have hmem_tail : ∀ e' ∈ tl, e'.id ≠ i :=
        fun e' hmem => tail_ids_ne_aux2 hd tl i hnd heq e' hmem
      have hhd_new : (if hd.id ∈ i :: rev then (0 : Int) else netOf hd.lines a) = 0 := by
        simp [heq]
      have hhd_old : (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) = netOf hd.lines a := by
        have hnr : hd.id ∉ rev := by rw [heq]; exact hnotrev
        simp [hnr]
      have hen : netOf e.lines a = netOf hd.lines a := by rw [hde]
      rw [hhd_new, hhd_old, hen]
      have htail := activeNet_tail_eq_aux tl rev i a hmem_tail
      omega
    · have hfind_tl : findEntry tl i = some e := by simp [findEntry, heq] at hfind; exact hfind
      simp only [sumOver_cons]
      have hhd_eq : (if hd.id ∈ (i :: rev) then (0 : Int) else netOf hd.lines a)
        = (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) := by
        by_cases hh : hd.id ∈ rev
        · simp [hh]
        · simp [hh, heq]
      rw [hhd_eq]
      have hnd_tl : (ids tl).Nodup := by
        have h2 : (ids (hd :: tl)).Nodup := hnd
        simp only [ids, List.map_cons, List.nodup_cons] at h2
        simp only [ids]
        exact h2.2
      have hih := ih (rev := rev) hfind_tl hnd_tl hnotrev
      omega

theorem plan0_valid_of_post_ok (s : State) (e : Entry) (h : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases hv : ValidPost s e
  · exact hv
  · simp [step, hv] at h










theorem plan0_balance_after_reverse_post (s : State) (e : Entry) (hv : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).2.balance = s.balance := by
  have hfresh : e.id ∉ ids s.journal := hv.2.2.2.2.1
  have hnotrev : e.id ∉ s.reversed := hv.2.2.2.2.2
  have hEq : step s (.post e) = (.ok, ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State)) := by simp [step, hv]
  have hS' : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by rw [hEq]
  have hfind0 : findEntry (s.journal ++ [e]) e.id = some e := by
    have h1 : findEntry (s.journal ++ [e]) e.id = findEntry [e] e.id :=
      findEntry_append_notmem_aux s.journal [e] e.id hfresh
    rw [h1]
    simp [findEntry]
  have hRevT : step ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) (.reverse e.id) = (.ok, ({ s with balance := fun a => (s.balance a + netOf e.lines a) - netOf e.lines a, journal := s.journal ++ [e], reversed := e.id :: s.reversed } : State)) := by
    simp [step, hfind0, hnotrev]
  rw [hS', hRevT]
  funext a
  simp


theorem plan0_valid_of_post_ok_test (s : State) (e : Entry) (h : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases hv : ValidPost s e
  · exact hv
  · simp [step, hv] at h

theorem plan0_step_post_eq (s : State) (e : Entry) (hv : ValidPost s e) : step s (.post e) = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by
  simp [step, hv]

theorem plan0_findEntry_append_notMem (j1 j2 : List Entry) (i : EntryId) (h : i ∉ ids j1) : findEntry (j1 ++ j2) i = findEntry j2 i :=
  findEntry_append_notmem_aux j1 j2 i h

theorem plan0_findEntry_append_singleton (j : List Entry) (e : Entry) (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  have h1 : findEntry (j ++ [e]) e.id = findEntry [e] e.id :=
    findEntry_append_notmem_aux j [e] e.id h
  rw [h1]
  simp [findEntry]

theorem plan0_probeB (s : State) (e : Entry) (hv : ValidPost s e) : True := by
  have hpair := plan0_step_post_eq s e hv
  have hsJ : ((step s (.post e)).2).journal = s.journal ++ [e] := by rw [hpair]
  have hR : ((step s (.post e)).2).reversed = s.reversed := by rw [hpair]
  have hfresh : e.id ∉ ids s.journal := hv.2.2.2.2.1
  have hnotrev : e.id ∉ s.reversed := hv.2.2.2.2.2
  have hfind0 : findEntry (s.journal ++ [e]) e.id = some e :=
    plan0_findEntry_append_singleton s.journal e hfresh
  have hfind : findEntry ((step s (.post e)).2).journal e.id = some e := by rw [hsJ]; exact hfind0
  have hrev : e.id ∉ ((step s (.post e)).2).reversed := by rw [hR]; exact hnotrev
  let s' := (step s (Command.post e)).2
  have heq : step s' (Command.reverse e.id) =
    (match findEntry s'.journal e.id with
     | some e2 => if e.id ∈ s'.reversed then ((.rejected : Outcome), s') else ((.ok : Outcome), { s' with balance := fun a => s'.balance a - netOf e2.lines a, reversed := e.id :: s'.reversed })
     | none => ((.rejected : Outcome), s')) := rfl
  trivial



theorem plan1_findEntry_append_singleton (j : List Entry) (e : Entry)
    (h : e.id ∉ ids j) :
    findEntry (j ++ [e]) e.id = some e := by
  have h1 : findEntry (j ++ [e]) e.id = findEntry [e] e.id :=
    findEntry_append_notmem_aux j [e] e.id h
  rw [h1]
  simp [findEntry]






theorem plan1_post_eq (s : State) (e : Entry) (hv : ValidPost s e) :
    step s (.post e) =
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a,
                     journal := s.journal ++ [e] }) := by
  simp [step, hv]

theorem plan1_findEntry_append_singleton_proof (j : List Entry) (e : Entry)
    (h : e.id ∉ ids j) :
    findEntry (j ++ [e]) e.id = some e := by
  have h1 : findEntry (j ++ [e]) e.id = findEntry [e] e.id :=
    findEntry_append_notmem_aux j [e] e.id h
  rw [h1]
  simp [findEntry]

theorem plan1_post_state_finds_and_fresh (s : State) (e : Entry)
    (hv : ValidPost s e) :
    findEntry ((step s (.post e)).2.journal) e.id = some e ∧
      e.id ∉ (step s (.post e)).2.reversed := by
  have hEq := plan1_post_eq s e hv
  have hJ : ((step s (.post e)).2).journal = s.journal ++ [e] := by rw [hEq]
  have hR : ((step s (.post e)).2).reversed = s.reversed := by rw [hEq]
  have hfresh : e.id ∉ ids s.journal := hv.2.2.2.2.1
  have hnotrev : e.id ∉ s.reversed := hv.2.2.2.2.2
  constructor
  · rw [hJ]
    exact plan1_findEntry_append_singleton s.journal e hfresh
  · rw [hR]; exact hnotrev

theorem plan1_reverse_ok_of_find (t : State) (i : EntryId) (e : Entry)
    (hf : findEntry t.journal i = some e) (hr : i ∉ t.reversed) :
    (step t (.reverse i)).1 = .ok := by
  simp [step, hf, hr]

theorem plan0_reverse_after_post_ok_test2 (s : State) (e : Entry) (hv : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by
  obtain ⟨hf, hr⟩ := plan1_post_state_finds_and_fresh s e hv
  exact plan1_reverse_ok_of_find _ _ _ hf hr

theorem plan0_reverse_after_post_ok (s : State) (e : Entry) (hv : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by
  obtain ⟨hf, hr⟩ := plan1_post_state_finds_and_fresh s e hv
  exact plan1_reverse_ok_of_find _ _ _ hf hr

theorem plan0_balance_explicit3 (s : State) (e : Entry) (hv : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).2.balance = s.balance := by
  have hfresh : e.id ∉ ids s.journal := hv.2.2.2.2.1
  have hnotrev : e.id ∉ s.reversed := hv.2.2.2.2.2
  have hEq : step s (.post e) = (.ok, ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State)) := by simp [step, hv]
  have hS' : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by rw [hEq]
  have hfind0 : findEntry (s.journal ++ [e]) e.id = some e := by
    have h1 : findEntry (s.journal ++ [e]) e.id = findEntry [e] e.id :=
      findEntry_append_notmem_aux s.journal [e] e.id hfresh
    rw [h1]
    simp [findEntry]
  have hRevT : step ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) (.reverse e.id) = (.ok, ({ s with balance := fun a => (s.balance a + netOf e.lines a) - netOf e.lines a, journal := s.journal ++ [e], reversed := e.id :: s.reversed } : State)) := by
    simp [step, hfind0, hnotrev]
  rw [hS', hRevT]
  funext a
  simp

theorem req_post_succeeds    : PostSucceeds step := by
  intro s e h
  simp only [step, h]
  rfl

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  have hmem : i ∈ ids s.journal := h.1
  have hnotrev : i ∉ s.reversed := h.2
  obtain ⟨e, he⟩ := findEntry_of_mem_ids_aux s.journal i hmem
  show (step s (Command.reverse i)).1 = .ok
  simp only [step, he]
  simp [hnotrev]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    simp only [Valid] at h
    simp [step, h]
  | reverse i =>
    simp only [Valid, ValidReverse] at h
    have hdisj : i ∉ ids s.journal ∨ i ∈ s.reversed := by
      by_cases hm : i ∈ ids s.journal
      · by_cases hr : i ∈ s.reversed
        · exact Or.inr hr
        · exact absurd ⟨hm, hr⟩ h
      · exact Or.inl hm
    cases hdisj with
    | inl hnotin =>
      have hnone := findEntry_none_of_not_mem' s.journal i hnotin
      simp [step, hnone]
    | inr hin =>
      cases heq : findEntry s.journal i with
      | none =>
        simp [step, heq]
      | some e =>
        simp [step, heq, hin]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  by_cases h : ValidPost s e
  · simp [step, h]
  · simp [step, h] at hok

theorem req_reverse_effects  : ReverseEffects step := by
  intro s i e hok hfind
  simp only [step, hfind] at hok ⊢
  by_cases hr : i ∈ s.reversed
  · simp [hr] at hok
  · simp [hr]

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  cases hfind : findEntry s.journal i with
  | none =>
    simp only [step, hfind] at hok
    exact absurd hok (by decide)
  | some e =>
    by_cases hr : i ∈ s.reversed
    · simp only [step, hfind, hr, ↓reduceIte] at hok
      exact absurd hok (by decide)
    · have hs2 : (step s (Command.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by
        simp [step, hfind, hr]
      have h_eq : step (step s (Command.reverse i)).2 (Command.reverse i) = (.rejected, (step s (Command.reverse i)).2) := by
        rw [hs2]
        simp [step, hfind]
      exact h_eq

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hv : ValidPost s e := plan0_valid_of_post_ok s e hok
  exact ⟨plan0_reverse_after_post_ok s e hv, plan0_balance_explicit3 s e hv⟩

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hstep : step s (.post e) = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by
        simp [step, hv]
      have hbal : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by rw [hstep]
      have hmem : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hv.2.1
      have hzero : lineSum e.lines = 0 := hv.2.2.2.1
      have hsum : sumOver s.accounts (fun a => netOf e.lines a) = 0 :=
        netSum_zero_aux_helper s.accounts hwf.1 e.lines hmem hzero
      have htot : total (step s (.post e)).2 = total s + sumOver s.accounts (fun a => netOf e.lines a) := by
        rw [hbal]
        exact total_add_net_aux s e.lines
      rw [htot, hsum, Int.add_zero]
    · have hrej : (step s (.post e)).1 = .rejected := by simp [step, hv]
      rw [hrej] at hok
      simp at hok
  | reverse i =>
    cases heq : findEntry s.journal i with
    | none =>
      have hrej : (step s (.reverse i)).1 = .rejected := by simp [step, heq]
      rw [hrej] at hok
      simp at hok
    | some e =>
      by_cases hr : i ∈ s.reversed
      · have hrej : (step s (.reverse i)).1 = .rejected := by simp [step, heq, hr]
        rw [hrej] at hok
        simp at hok
      · have hstep : step s (.reverse i) = (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
          simp [step, heq, hr]
        have hbal : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by rw [hstep]
        have hmemJ : e ∈ s.journal := findEntry_mem_aux3 s.journal i e heq
        obtain ⟨hmemA, hzero⟩ := hwf.2.2.2 e hmemJ
        have hsum : sumOver s.accounts (fun a => netOf e.lines a) = 0 :=
          netSum_zero_aux_helper s.accounts hwf.1 e.lines hmemA hzero
        have htot : total (step s (.reverse i)).2 = total s - sumOver s.accounts (fun a => netOf e.lines a) := by
          rw [hbal]
          exact total_sub_net_aux s e.lines
        rw [htot, hsum, Int.sub_zero]

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  obtain ⟨hndAcc, hndIds, hrevSub, hbal⟩ := hwf
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hstep2 : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by
        simp [step, hv]
      rw [hstep2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using hndAcc
      · have hnotin : e.id ∉ ids s.journal := hv.2.2.2.2.1
        have : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := ids_append_single_aux s.journal e
        rw [this]
        exact nodup_append_singleton_aux _ _ hndIds hnotin
      · intro i hi
        have hi' : i ∈ s.reversed := hi
        have hmem := hrevSub i hi'
        rw [ids_append_single_aux]
        simp [hmem]
      · intro e' he'
        have hJ : e' ∈ s.journal ++ [e] := he'
        rw [List.mem_append] at hJ
        cases hJ with
        | inl hmem =>
          have hb := hbal e' hmem
          refine ⟨?_, ?_⟩
          · intro l hl
            exact hb.1 l hl
          · exact hb.2
        | inr hmem =>
          simp at hmem
          subst hmem
          exact ⟨hv.2.1, hv.2.2.2.1⟩
    · have hstep2 : (step s (.post e)).2 = s := by simp [step, hv]
      rw [hstep2]
      exact ⟨hndAcc, hndIds, hrevSub, hbal⟩
  | reverse i =>
    cases heq : findEntry s.journal i with
    | none =>
      have hstep2 : (step s (.reverse i)).2 = s := by simp [step, heq]
      rw [hstep2]
      exact ⟨hndAcc, hndIds, hrevSub, hbal⟩
    | some e =>
      by_cases hr : i ∈ s.reversed
      · have hstep2 : (step s (.reverse i)).2 = s := by simp [step, heq, hr]
        rw [hstep2]
        exact ⟨hndAcc, hndIds, hrevSub, hbal⟩
      · have hstep2 : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by
          simp [step, heq, hr]
        rw [hstep2]
        have hmemIds : i ∈ ids s.journal := findEntry_some_mem_ids_aux2 s.journal i e heq
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa using hndAcc
        · simpa using hndIds
        · intro x hx
          simp at hx
          cases hx with
          | inl hxi => rw [hxi]; exact hmemIds
          | inr hxr => exact hrevSub x hxr
        · intro e' he'
          exact hbal e' he'

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hstep2 : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by
        simp [step, hv]
      rw [hstep2]
      intro a
      have hold : s.balance a = s.opening a + activeNet s a := hcons a
      have hnewBal : ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State).balance a
          = s.balance a + netOf e.lines a := rfl
      have hnewOp : ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State).opening = s.opening := rfl
      rw [hnewBal, hnewOp]
      have hnotrev : e.id ∉ s.reversed := hv.2.2.2.2.2
      have hact : activeNet ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) a
          = activeNet s a + netOf e.lines a := by
        have h := activeNet_post_aux s e a hnotrev
        -- unfold to see equality up to record updates
        have heq : activeNet ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) a
            = activeNet ({ s with journal := s.journal ++ [e] } : State) a := rfl
        rw [heq]
        have heq2 : activeNet ({ s with journal := s.journal ++ [e] } : State) a
            = activeNet ({ s with journal := s.journal ++ [e] } ) a := rfl
        exact h
      rw [hact, hold]
      omega
    · have hstep2 : (step s (.post e)).2 = s := by simp [step, hv]
      rw [hstep2]
      exact hcons
  | reverse i =>
    cases heq : findEntry s.journal i with
    | none =>
      have hstep2 : (step s (.reverse i)).2 = s := by simp [step, heq]
      rw [hstep2]
      exact hcons
    | some e =>
      by_cases hr : i ∈ s.reversed
      · have hstep2 : (step s (.reverse i)).2 = s := by simp [step, heq, hr]
        rw [hstep2]
        exact hcons
      · have hstep2 : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by
          simp [step, heq, hr]
        rw [hstep2]
        intro a
        have hold : s.balance a = s.opening a + activeNet s a := hcons a
        have hnewBal : ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State).balance a
            = s.balance a - netOf e.lines a := rfl
        have hnewOp : ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State).opening = s.opening := rfl
        rw [hnewBal, hnewOp]
        obtain ⟨hndAcc, hndIds, hrevSub, hbal⟩ := hwf
        have hact : activeNet ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) a
            = activeNet s a - netOf e.lines a := by
          have h := activeNet_reverse_aux4 s.journal s.reversed i a e heq hndIds hr
          unfold activeNet at h ⊢
          simpa using h
        rw [hact, hold]
        omega

end Reversal
