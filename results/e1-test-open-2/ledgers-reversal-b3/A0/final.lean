import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance decValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

theorem ids_append_single (l : List Entry) (e : Entry) : ids (l ++ [e]) = ids l ++ [e.id] := by
  unfold ids; simp

theorem findEntry_mem (l : List Entry) (i : EntryId) (e : Entry) (h : findEntry l i = some e) :
    e ∈ l ∧ e.id = i := by
  induction l with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; cases h; exact ⟨List.mem_cons.mpr (Or.inl rfl), heq⟩
    · simp [heq] at h; have t := ih h; exact ⟨List.mem_cons.mpr (Or.inr t.1), t.2⟩

theorem findEntry_ids (l : List Entry) (i : EntryId) (e : Entry) (h : findEntry l i = some e) :
    i ∈ ids l := by
  have t := findEntry_mem l i e h
  have : e.id ∈ ids l := by unfold ids; exact List.mem_map.mpr ⟨e, t.1, rfl⟩
  rwa [t.2] at this

theorem findEntry_of_mem_ids (l : List Entry) (i : EntryId) (hm : i ∈ ids l) :
    ∃ e, findEntry l i = some e := by
  induction l with
  | nil => simp [ids] at hm
  | cons hd tl ih =>
    simp only [findEntry]
    by_cases heq : hd.id = i
    · exact ⟨hd, by simp [heq]⟩
    · simp [heq]; unfold ids at hm; simp [heq] at hm; exact ih hm

theorem findEntry_append_new (l : List Entry) (e : Entry) (h : e.id ∉ ids l) :
    findEntry (l ++ [e]) e.id = some e := by
  induction l with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    simp only [findEntry]
    by_cases heq : hd.id = e.id
    · exfalso; apply h; unfold ids; simp [heq]
    · simp [heq]; exact ih (fun hmem => h (by unfold ids; simp [List.mem_cons.mpr (Or.inr hmem)]))

theorem nodup_append_singleton {α : Type} {l : List α} {x : α} (hl : l.Nodup) (hx : x ∉ l) :
    (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hl2 : tl.Nodup := (List.nodup_cons.mp hl).2
    have hhd : hd ∉ tl := (List.nodup_cons.mp hl).1
    have hx2 : x ∉ tl := fun h => hx (List.mem_cons.mpr (Or.inr h))
    have ih2 := ih hl2 hx2
    have hhd2 : hd ∉ tl ++ [x] := by
      intro hmem
      rcases List.mem_append.mp hmem with h1 | h1
      · exact hhd h1
      · simp at h1; subst h1; exact hx (List.mem_cons.mpr (Or.inl rfl))
    exact List.nodup_cons.mpr ⟨hhd2, ih2⟩

theorem sumOver_zero {α} (l : List α) : sumOver l (fun _ => (0:Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [sumOver_cons, ih]

theorem sum_netOf_eq_lineSum_of_accounts (accs : List AccountId) (ls : List Line)
    (hall : ∀ l ∈ ls, l.1 ∈ accs) (hNodup : accs.Nodup) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    unfold netOf lineSum
    simp only [sumOver_nil]
    exact sumOver_zero accs
  | cons hd tl ih =>
    have hall_tl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hall l (List.mem_cons.mpr (Or.inr hl))
    have ih' := ih hall_tl
    have hfun : (fun a => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else (0:Int)) + netOf tl a) := by
      funext a; rfl
    rw [hfun]
    have hadd := sumOver_add accs (fun a => if hd.1 = a then (hd.2:Int) else 0) (fun a => netOf tl a)
    rw [hadd, ih']
    have hsingle : sumOver accs (fun a => if hd.1 = a then (hd.2:Int) else 0) = hd.2 := by
      have hmem : hd.1 ∈ accs := hall hd (by simp)
      have hconv : (fun a => if hd.1 = a then (hd.2:Int) else 0) = (fun a => if a = hd.1 then hd.2 else 0) := by
        funext a; by_cases h : a = hd.1 <;> simp [h, eq_comm]
      rw [hconv]
      have h2 := sumOver_ite_eq hNodup hd.1 hd.2
      simp [hmem] at h2; exact h2
    rw [hsingle]
    unfold lineSum
    simp [sumOver_cons]

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | some e => if i ∈ s.reversed then (.rejected, s) else (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed })
    | none => (.rejected, s)

theorem req_post_succeeds : PostSucceeds step := by
  intro s e hV; simp [step, hV]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i hV; obtain ⟨e,he⟩:=findEntry_of_mem_ids s.journal i hV.1; simp [step, he, hV.2]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c hInv
  cases c with
  | post e =>
    have h : ¬ValidPost s e := by simpa [Valid] using hInv
    simp [step, h]
  | reverse i =>
    cases hf : findEntry s.journal i with
    | none => simp [step, hf]
    | some e =>
      simp only [step, hf]
      by_cases hr : i ∈ s.reversed
      · simp [hr]
      · exfalso; exact hInv ⟨findEntry_ids s.journal i e hf, hr⟩

theorem req_post_effects : PostEffects step := by
  intro s e hOk
  have hV : ValidPost s e := by
    by_cases hv : ValidPost s e
    · exact hv
    · have heq : (step s (.post e)).1 = .rejected := by simp [step, hv]
      rw [heq] at hOk; cases hOk
  have hSnd : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by simp [step, hV]
  rw [hSnd]; exact ⟨rfl,rfl,rfl,rfl, fun _=>rfl⟩

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hOk hFind
  have hr : i ∉ s.reversed := by
    intro hm; have heq : (step s (.reverse i)).1 = .rejected := by simp [step, hFind, hm]
    rw [heq] at hOk; cases hOk
  have hSnd : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed } := by simp [step, hFind, hr]
  rw [hSnd]; refine ⟨rfl,rfl,rfl,?_, fun _=>rfl⟩
  intro x; simp only [List.mem_cons]
  constructor
  · intro h; rcases h with rfl|h; left; rfl; right; exact h
  · intro h; rcases h with rfl|h; left; rfl; right; exact h

theorem req_reverse_once : ReverseOnce step := by
  intro s i hOk
  cases hf : findEntry s.journal i with
  | none =>
    have heq : step s (.reverse i) = (.rejected, s) := by simp [step, hf]
    rw [heq] at hOk; simp at hOk
  | some e =>
    by_cases hr : i ∈ s.reversed
    · have heq : step s (.reverse i) = (.rejected, s) := by simp [step, hf, hr]
      rw [heq] at hOk; simp at hOk
    · have heq : step s (.reverse i) = (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed }) := by simp [step, hf, hr]
      have h2 : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed } := by rw [heq]
      rw [h2]; simp [step, hf]

theorem req_roundtrip : RoundTrip step := by
  intro s e hOk
  have hV : ValidPost s e := by
    by_cases hv : ValidPost s e
    · exact hv
    · have heq : (step s (.post e)).1 = .rejected := by simp [step, hv]
      rw [heq] at hOk; cases hOk
  have hPost2 : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by simp [step, hV]
  have hfind : findEntry (s.journal ++ [e]) e.id = some e := findEntry_append_new s.journal e hV.2.2.2.2.1
  constructor
  · rw [hPost2]; simp [step, hfind, hV.2.2.2.2.2]
  · rw [hPost2]; simp [step, hfind, hV.2.2.2.2.2]

theorem req_trial_balance : TrialBalance step := by
  intro s c hWF hOk
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hSnd : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by simp [step, hV]
      rw [hSnd]; show total _ = total s; unfold total
      have hSum : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := sumOver_add _ _ _
      have hNetZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by rw [sum_netOf_eq_lineSum_of_accounts s.accounts e.lines hV.2.1 hWF.1, hV.2.2.2.1]
      rw [hSum, hNetZero]; simp
    · have heq : step s (.post e) = (.rejected, s) := by simp [step, hV]
      have : (step s (.post e)).1 = .ok := hOk; rw [heq] at this; simp at this
  | reverse i =>
    cases hf : findEntry s.journal i with
    | none => have heq : step s (.reverse i) = (.rejected, s) := by simp [step, hf]; have : (step s (.reverse i)).1 = .ok := hOk; rw [heq] at this; simp at this
    | some e =>
      by_cases hr : i ∈ s.reversed
      · have heq : step s (.reverse i) = (.rejected, s) := by simp [step, hf, hr]; have : (step s (.reverse i)).1 = .ok := hOk; rw [heq] at this; simp at this
      · have hSnd : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed } := by simp [step, hf, hr]
        rw [hSnd]; show total _ = total s; unfold total
        have hSum : sumOver s.accounts (fun a => s.balance a - netOf e.lines a) = sumOver s.accounts s.balance - sumOver s.accounts (fun a => netOf e.lines a) := sumOver_sub _ _ _
        have hmem : e ∈ s.journal := (findEntry_mem s.journal i e hf).1
        have hNetZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by rw [sum_netOf_eq_lineSum_of_accounts s.accounts e.lines (hWF.2.2.2 e hmem).1 hWF.1, (hWF.2.2.2 e hmem).2]
        rw [hSum, hNetZero]; simp

theorem req_well_formed : StaysWellFormed step := by
  intro s c hWF
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hSnd : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by simp [step, hV]
      rw [hSnd]
      have hNodupIds2 : (ids (s.journal ++ [e])).Nodup := by rw [ids_append_single]; exact nodup_append_singleton hWF.2.1 hV.2.2.2.2.1
      refine ⟨hWF.1, hNodupIds2, ?_, ?_⟩
      · intro j hj; show j ∈ ids (s.journal ++ [e]); rw [ids_append_single]; exact List.mem_append.mpr (Or.inl (hWF.2.2.1 j hj))
      · intro e' he'; rcases List.mem_append.mp he' with h|h
        · exact hWF.2.2.2 e' h
        · simp at h; subst h; exact ⟨hV.2.1, hV.2.2.2.1⟩
    · have hSnd : (step s (.post e)).2 = s := by simp [step, hV]; rw [hSnd]; exact hWF
  | reverse i =>
    by_cases hf_none : findEntry s.journal i = none
    · have hSnd : (step s (.reverse i)).2 = s := by simp [step, hf_none]; rw [hSnd]; exact hWF
    · have hf_some : ∃ e, findEntry s.journal i = some e := by
        cases h : findEntry s.journal i with
        | none => exact absurd h hf_none
        | some e => exact ⟨e, rfl⟩
      obtain ⟨e, he⟩ := hf_some
      by_cases hr : i ∈ s.reversed
      · have hSnd : (step s (.reverse i)).2 = s := by simp [step, he, hr]; rw [hSnd]; exact hWF
      · have hSnd : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed } := by simp [step, he, hr]
        rw [hSnd]; refine ⟨hWF.1, hWF.2.1, ?_, hWF.2.2.2⟩
        intro j hj
        have hj' : j = i ∨ j ∈ s.reversed := by
          simpa [List.mem_cons] using hj
        rcases hj' with rfl | hj'
        · exact findEntry_ids s.journal i e he
        · exact hWF.2.2.1 j hj'

theorem aux_sumEq (journal : List Entry) (rev : List EntryId) (target : EntryId)
    (targetEntry : Entry) (a : AccountId) (hNodup : (ids journal).Nodup)
    (hf : findEntry journal target = some targetEntry) (hr : target ∉ rev) :
    sumOver journal (fun e' => if e'.id ∈ target :: rev then (0:Int) else netOf e'.lines a) =
      sumOver journal (fun e' => if e'.id ∈ rev then (0:Int) else netOf e'.lines a) - netOf targetEntry.lines a := by
  induction journal with
  | nil => simp at hf
  | cons hd tl ih =>
    simp only [findEntry] at hf; by_cases heq : hd.id = target
    · simp only [heq, ite_true] at hf
      have hEq : hd = targetEntry := Option.some_inj.mp hf
      subst hEq
      have hNodupIds : target ∉ ids tl := by
        have h2 : ids (hd :: tl) = hd.id :: ids tl := by unfold ids; simp
        have : hd.id ∉ ids tl := (List.nodup_cons.mp (h2 ▸ hNodup)).1
        simpa [heq] using this
      have hTlEq : sumOver tl (fun e' => if e'.id ∈ target :: rev then (0:Int) else netOf e'.lines a) =
          sumOver tl (fun e' => if e'.id ∈ rev then (0:Int) else netOf e'.lines a) := by
        apply sumOver_congr; intro e' he'
        have ne : e'.id ≠ target := by intro heq2; exact hNodupIds (by unfold ids; rw [← heq2]; exact List.mem_map.mpr ⟨e', he', rfl⟩)
        simp [ne]
      have h1 : (if hd.id ∈ target :: rev then (0:Int) else netOf hd.lines a) = 0 := by simp [heq]
      have h2 : (if hd.id ∈ rev then (0:Int) else netOf hd.lines a) = netOf hd.lines a := by simp [heq, hr]
      simp only [sumOver_cons, h1, h2, hTlEq]; omega
    · simp only [heq, ite_false] at hf
      have hNodupTl : (ids tl).Nodup := by
        have h2 : ids (hd :: tl) = hd.id :: ids tl := by unfold ids; simp
        exact (List.nodup_cons.mp (h2 ▸ hNodup)).2
      have ih2 := ih hNodupTl hf; simp only [sumOver_cons]
      have h1 : (if hd.id ∈ target :: rev then (0:Int) else netOf hd.lines a) = (if hd.id ∈ rev then (0:Int) else netOf hd.lines a) := by simp [heq]
      rw [h1, ih2]; omega

theorem req_consistent : StaysConsistent step := by
  intro s c hWF hCons
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hSnd : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by simp [step, hV]
      rw [hSnd]; intro a; have hConsA := hCons a; show s.balance a + netOf e.lines a = s.opening a + activeNet _ a; unfold activeNet; simp only
      have hAppend : sumOver (s.journal ++ [e]) (fun e' => if e'.id ∈ s.reversed then (0:Int) else netOf e'.lines a) =
          sumOver s.journal (fun e' => if e'.id ∈ s.reversed then (0:Int) else netOf e'.lines a) + netOf e.lines a := by
        have h1 := sumOver_append s.journal [e] (fun e' => if e'.id ∈ s.reversed then (0:Int) else netOf e'.lines a); simp at h1; have : e.id ∉ s.reversed := hV.2.2.2.2.2; simp [this] at h1; exact h1
      have hActive : activeNet s a = sumOver s.journal (fun e' => if e'.id ∈ s.reversed then (0:Int) else netOf e'.lines a) := rfl; omega
    · have hSnd : (step s (.post e)).2 = s := by simp [step, hV]; rw [hSnd]; exact hCons
  | reverse i =>
    by_cases hf_none : findEntry s.journal i = none
    · have hSnd : (step s (.reverse i)).2 = s := by simp [step, hf_none]; rw [hSnd]; exact hCons
    · have hf_some : ∃ e, findEntry s.journal i = some e := by
        cases h : findEntry s.journal i with
        | none => exact absurd h hf_none
        | some e => exact ⟨e, rfl⟩
      obtain ⟨e, he⟩ := hf_some
      by_cases hr : i ∈ s.reversed
      · have hSnd : (step s (.reverse i)).2 = s := by simp [step, he, hr]; rw [hSnd]; exact hCons
      · have hSnd : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed } := by simp [step, he, hr]
        rw [hSnd]; intro a; have hConsA := hCons a; show s.balance a - netOf e.lines a = s.opening a + activeNet _ a; unfold activeNet; simp only
        have hSumEq := aux_sumEq s.journal s.reversed i e a hWF.2.1 he hr
        have hActive : activeNet s a = sumOver s.journal (fun e' => if e'.id ∈ s.reversed then (0:Int) else netOf e'.lines a) := rfl; omega

end Reversal
