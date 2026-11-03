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

theorem findEntry_of_mem_ids3 {j : List Entry} {i : EntryId} (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil =>
    have : ids ([] : List Entry) = [] := rfl
    simp [this] at h
  | cons e es ih =>
    have hcons : ids (e :: es) = e.id :: ids es := rfl
    have hmem : i ∈ e.id :: ids es := hcons ▸ h
    rw [List.mem_cons] at hmem
    simp only [findEntry]
    by_cases heq : e.id = i
    · simp [heq]
    · simp [heq]
      apply ih
      exact hmem.resolve_left (fun hc => heq hc.symm)

theorem dummy : True := by trivial

theorem ids_cons_mem (x : Entry) (xs : List Entry) (i : EntryId) : i ∈ ids (x :: xs) ↔ i = x.id ∨ i ∈ ids xs := by
  simp [ids]

theorem findEntry_append_of_notMem (j : List Entry) (e : Entry) (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons x xs ih =>
    simp only [List.cons_append, findEntry]
    have hx : x.id ≠ e.id := by
      intro heq
      apply h
      rw [ids_cons_mem]
      exact Or.inl heq.symm
    simp [hx]
    have h' : e.id ∉ ids xs := by
      intro hm
      apply h
      rw [ids_cons_mem]
      exact Or.inr hm
    exact ih h'

theorem ids_append2 (l₁ l₂ : List Entry) : ids (l₁ ++ l₂) = ids l₁ ++ ids l₂ := by
  unfold ids; rw [List.map_append]

theorem findEntry_mem_ids2 {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : i ∈ ids j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons x xs ih =>
    simp only [findEntry] at h
    split at h
    · next heq =>
      simp [ids]
      exact Or.inl heq.symm
    · next _ =>
      exact List.Mem.tail _ (ih h)

theorem nodup_append_singleton2 {l : List EntryId} {x : EntryId} (hl : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | cons a t ih =>
    have h1 : a ∉ t := (List.nodup_cons.mp hl).1
    have h2 : t.Nodup := (List.nodup_cons.mp hl).2
    have hx2 : x ∉ t := fun hm => hx (List.Mem.tail a hm)
    have hxa : x ≠ a := fun heq => hx (heq ▸ List.Mem.head t)
    have ih2 := ih h2 hx2
    show (a :: (t ++ [x])).Nodup
    rw [List.nodup_cons]
    exact ⟨fun hmem => by
      rw [List.mem_append] at hmem
      cases hmem with
      | inl h => exact h1 h
      | inr h => simp at h; exact hxa h.symm
    , ih2⟩

theorem sum_reversed_diff {j : List Entry} {rev : List EntryId} {i : EntryId} {e : Entry} {a : AccountId}
  (hNodup : (ids j).Nodup) (hFind : findEntry j i = some e) (hNotMem : i ∉ rev) :
  sumOver j (fun ee => if ee.id ∈ i :: rev then (0 : Int) else netOf ee.lines a) =
  sumOver j (fun ee => if ee.id ∈ rev then (0 : Int) else netOf ee.lines a) - netOf e.lines a := by
  induction j with
  | nil => simp [findEntry] at hFind
  | cons x xs ih =>
    simp only [findEntry] at hFind
    by_cases hx : x.id = i
    · simp [hx] at hFind
      subst hFind
      simp only [sumOver_cons]
      have hHead1 : (if x.id ∈ i :: rev then (0 : Int) else netOf x.lines a) = 0 := by
        have : x.id ∈ i :: rev := by simp [hx]
        simp [this]
      have hHead2 : (if x.id ∈ rev then (0 : Int) else netOf x.lines a) = netOf x.lines a := by
        have : x.id ∉ rev := by rw [hx]; exact hNotMem
        simp [this]
      rw [hHead1, hHead2]
      have hNotInIds : i ∉ ids xs := by
        have hEq : ids (x :: xs) = x.id :: ids xs := rfl
        rw [hEq] at hNodup
        rw [List.nodup_cons] at hNodup
        have hxNot : x.id ∉ ids xs := hNodup.1
        rw [hx] at hxNot
        exact hxNot
      have hEqXs : sumOver xs (fun ee => if ee.id ∈ i :: rev then (0 : Int) else netOf ee.lines a) = sumOver xs (fun ee => if ee.id ∈ rev then (0 : Int) else netOf ee.lines a) := by
        apply sumOver_congr
        intro ee hMemXs
        have hEeIdNe : ee.id ≠ i := by
          intro heq
          apply hNotInIds
          unfold ids
          rw [List.mem_map]
          exact ⟨ee, hMemXs, heq⟩
        by_cases hInRev : ee.id ∈ rev
        · simp [hInRev]
        · simp [hInRev, hEeIdNe]
      rw [hEqXs]
      omega
    · simp [hx] at hFind
      simp only [sumOver_cons]
      have hEqHead : (if x.id ∈ i :: rev then (0 : Int) else netOf x.lines a) = (if x.id ∈ rev then (0 : Int) else netOf x.lines a) := by
        by_cases hInRev : x.id ∈ rev
        · simp [hInRev]
        · have hxNe : x.id ≠ i := hx
          simp [hInRev, hxNe]
      rw [hEqHead]
      have hNodupTail : (ids xs).Nodup := by
        have hEq : ids (x :: xs) = x.id :: ids xs := rfl
        rw [hEq] at hNodup
        exact (List.nodup_cons.mp hNodup).2
      have hIH := ih hNodupTail hFind
      omega

theorem sumOver_const_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [sumOver_cons, ih]

theorem sum_netOf_eq_lineSum (ls : List Line) (accs : List AccountId) (hNodup : accs.Nodup) (hMem : ∀ l ∈ ls, l.1 ∈ accs) :
  sumOver accs (fun a => netOf ls a) = lineSum ls := by
  unfold netOf lineSum
  induction ls with
  | nil =>
    simp only [sumOver_nil]
    exact sumOver_const_zero accs
  | cons hd tl ih =>
    have hhd : hd.1 ∈ accs := hMem hd (by simp)
    have htl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hMem l (by simp [hl])
    have ih' := ih htl
    simp only [sumOver_cons]
    calc sumOver accs (fun a => (if hd.1 = a then hd.2 else 0) + sumOver tl (fun l => if l.1 = a then l.2 else 0))
        = sumOver accs (fun a => (if a = hd.1 then hd.2 else 0) + sumOver tl (fun l => if l.1 = a then l.2 else 0)) := by
          apply sumOver_congr
          intro a _
          by_cases heq : hd.1 = a
          · subst heq; simp
          · have h2 : ¬ a = hd.1 := fun h => heq (Eq.symm h)
            simp [heq, h2]
      _ = sumOver accs (fun a => if a = hd.1 then hd.2 else 0) + sumOver accs (fun a => sumOver tl (fun l => if l.1 = a then l.2 else 0)) := by
          rw [← sumOver_add]
      _ = hd.2 + sumOver tl (fun x => x.2) := by
          rw [sumOver_ite_eq hNodup hd.1 hd.2, if_pos hhd, ih']

theorem mem_of_findEntry {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons x xs ih =>
    simp only [findEntry] at h
    by_cases heq : x.id = i
    · simp [heq] at h; subst h; simp
    · simp [heq] at h; exact List.Mem.tail x (ih h)

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  have hnotin : i ∉ s.reversed := h.2
  have ⟨e, he⟩ := findEntry_of_mem_ids3 h.1
  simp [step, he, hnotin]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    simp [Valid] at h
    simp [step, h]
  | reverse i =>
    have h1 : ¬ Valid s (Command.reverse i) := h
    simp [Valid, ValidReverse] at h1
    -- h1 : i ∈ ids s.journal → i ∈ s.reversed
    cases hFE : findEntry s.journal i with
    | none =>
      simp [step, hFE]
    | some e =>
      have hMemIds : i ∈ ids s.journal := findEntry_mem_ids2 hFE
      have hRev : i ∈ s.reversed := h1 hMemIds
      simp [step, hFE, hRev]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  by_cases hV : ValidPost s e
  · simp [step, hV] at hok ⊢
  · have : (step s (.post e)).1 = .rejected := by simp [step, hV]
    rw [this] at hok
    simp at hok

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hOk hFind
  have hNotMem : i ∉ s.reversed := by
    intro hMem
    have hEq : step s (.reverse i) = (Outcome.rejected, s) := by
      simp [step, hFind, hMem]
    have hFst : (step s (.reverse i)).1 = Outcome.rejected := by rw [hEq]
    rw [hFst] at hOk
    cases hOk
  have hStepEq : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
    simp [step, hFind, hNotMem]
  have h1 : (step s (.reverse i)).2.accounts = s.accounts := by rw [hStepEq]
  have h2 : (step s (.reverse i)).2.opening = s.opening := by rw [hStepEq]
  have h3 : (step s (.reverse i)).2.journal = s.journal := by rw [hStepEq]
  have h4 : (∀ x, x ∈ (step s (.reverse i)).2.reversed ↔ x = i ∨ x ∈ s.reversed) := by
    rw [hStepEq]
    intro x
    simp
  have h5 : ∀ a, (step s (.reverse i)).2.balance a = s.balance a - netOf e.lines a := by
    intro a
    rw [hStepEq]
  exact ⟨h1, h2, h3, h4, h5⟩

theorem req_reverse_once : ReverseOnce step := by
  intro s i hOk
  cases hFE : findEntry s.journal i with
  | none =>
    simp [step, hFE] at hOk
  | some e =>
    by_cases hMem : i ∈ s.reversed
    · simp [step, hFE, hMem] at hOk
    · have hStepEq : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
        simp [step, hFE, hMem]
      let t : State := { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }
      have ht : (step s (.reverse i)).2 = t := by rw [hStepEq]
      have hFind_t : findEntry t.journal i = some e := by simp [t, hFE]
      have hMem_t : i ∈ t.reversed := by simp [t]
      have hStep2_t : step t (.reverse i) = (Outcome.rejected, t) := by
        simp [step, hFind_t, hMem_t]
      have hGoal : step (step s (.reverse i)).2 (.reverse i) = (Outcome.rejected, (step s (.reverse i)).2) := by
        rw [ht, hStep2_t]
      exact hGoal

theorem req_roundtrip : RoundTrip step := by
  intro s e hOk
  have hV : ValidPost s e := by
    by_cases hv : ValidPost s e
    · exact hv
    · have hRej : (step s (.post e)).1 = .rejected := by simp [step, hv]
      rw [hRej] at hOk
      simp at hOk
  have hStepPost : step s (.post e) = (Outcome.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by
    simp [step, hV]
  have hFindAux : findEntry (s.journal ++ [e]) e.id = some e :=
    findEntry_append_of_notMem s.journal e hV.2.2.2.2.1
  have hNotRevAux : e.id ∉ s.reversed := hV.2.2.2.2.2
  constructor
  · rw [hStepPost]
    simp [step, hFindAux, hNotRevAux]
  · rw [hStepPost]
    simp only [step, hFindAux, hNotRevAux, ↓reduceIte]
    funext a
    simp

theorem req_trial_balance : TrialBalance step := by
  intro s c hWf hOk
  cases c with
  | post e =>
    have hV : ValidPost s e := by
      by_cases hv : ValidPost s e
      · exact hv
      · have : (step s (.post e)).1 = .rejected := by simp [step, hv]
        rw [this] at hOk; simp at hOk
    have hStep : step s (.post e) = (Outcome.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by
      simp [step, hV]
    have hTotal : total (step s (.post e)).2 = total s := by
      rw [hStep]
      unfold total
      have h_eq : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := by rw [← sumOver_add]
      rw [h_eq]
      have h_zero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
        rw [sum_netOf_eq_lineSum e.lines s.accounts hWf.1 hV.2.1, hV.2.2.2.1]
      omega
    exact hTotal
  | reverse i =>
    cases hFE : findEntry s.journal i with
    | none => simp [step, hFE] at hOk
    | some e =>
      by_cases hMem : i ∈ s.reversed
      · simp [step, hFE, hMem] at hOk
      · have hStep : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by simp [step, hFE, hMem]
        have hTotal : total (step s (.reverse i)).2 = total s := by
          rw [hStep]
          unfold total
          have h_eq : sumOver s.accounts (fun a => s.balance a - netOf e.lines a) = sumOver s.accounts s.balance - sumOver s.accounts (fun a => netOf e.lines a) := by rw [← sumOver_sub]
          rw [h_eq]
          have h_bal : lineSum e.lines = 0 := (hWf.2.2.2 e (mem_of_findEntry hFE)).2
          have h_mem_acc : ∀ l ∈ e.lines, l.1 ∈ s.accounts := (hWf.2.2.2 e (mem_of_findEntry hFE)).1
          have h_zero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
            rw [sum_netOf_eq_lineSum e.lines s.accounts hWf.1 h_mem_acc, h_bal]
          omega
        exact hTotal

theorem req_well_formed      : StaysWellFormed step := by
  intro s c hWf
  cases c with
  | post e =>
    unfold step
    by_cases hV : ValidPost s e
    · simp [hV]
      obtain ⟨hAccNodup, hIdsNodup, hRevSub, hBalanced⟩ := hWf
      refine ⟨hAccNodup, ?_, ?_, ?_⟩
      · have hIdsEq : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := ids_append2 s.journal [e]
        rw [hIdsEq]
        exact nodup_append_singleton2 hIdsNodup hV.2.2.2.2.1
      · intro i hi
        have hi' : i ∈ ids s.journal := hRevSub i hi
        rw [ids_append2]
        exact List.mem_append.mpr (Or.inl hi')
      · intro e' he'
        rw [List.mem_append] at he'
        cases he' with
        | inl hOld => exact hBalanced e' hOld
        | inr hNew => simp at hNew; subst hNew; exact ⟨hV.2.1, hV.2.2.2.1⟩
    · simp [hV]
      exact hWf
  | reverse i =>
    unfold step
    cases hFind : findEntry s.journal i with
    | none => simp [hFind]; exact hWf
    | some e =>
      by_cases hMem : i ∈ s.reversed
      · simp [hFind, hMem]; exact hWf
      · simp [hFind, hMem]
        obtain ⟨hAccNodup, hIdsNodup, hRevSub, hBalanced⟩ := hWf
        refine ⟨hAccNodup, hIdsNodup, ?_, hBalanced⟩
        intro x hx
        simp at hx
        cases hx with
        | inl heq => subst heq; exact findEntry_mem_ids2 hFind
        | inr hOld => exact hRevSub x hOld

theorem req_consistent : StaysConsistent step := by
  intro s c hWf hCons
  cases c with
  | post e =>
    unfold step
    by_cases hV : ValidPost s e
    · simp only [hV, ↓reduceIte]
      intro a
      show s.balance a + netOf e.lines a = s.opening a + activeNet ⟨s.accounts, s.opening, fun a => s.balance a + netOf e.lines a, s.journal ++ [e], s.reversed⟩ a
      have hNotMemRev : e.id ∉ s.reversed := hV.2.2.2.2.2
      have hActivePost : activeNet ⟨s.accounts, s.opening, fun a => s.balance a + netOf e.lines a, s.journal ++ [e], s.reversed⟩ a = activeNet s a + netOf e.lines a := by
        unfold activeNet
        rw [sumOver_append]
        have hEq : (if e.id ∈ s.reversed then (0 : Int) else netOf e.lines a) = netOf e.lines a := by simp [hNotMemRev]
        simp [hEq]
      rw [hActivePost]
      have hConsA := hCons a
      omega
    · simp [hV]
      exact hCons
  | reverse i =>
    cases hFind : findEntry s.journal i with
    | none =>
      have hStep : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, hFind]
      simp [hStep]
      exact hCons
    | some e =>
      by_cases hMem : i ∈ s.reversed
      · have hStep : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, hFind, hMem]
        simp [hStep]
        exact hCons
      · have hStep : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
          simp [step, hFind, hMem]
        have hStep2Eq : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by
          rw [hStep]
        rw [hStep2Eq]
        intro a
        show s.balance a - netOf e.lines a = s.opening a + activeNet ⟨s.accounts, s.opening, fun a => s.balance a - netOf e.lines a, s.journal, i :: s.reversed⟩ a
        have hActiveRev : activeNet ⟨s.accounts, s.opening, fun a => s.balance a - netOf e.lines a, s.journal, i :: s.reversed⟩ a = activeNet s a - netOf e.lines a := by
          unfold activeNet
          exact sum_reversed_diff hWf.2.1 hFind hMem
        rw [hActiveRev]
        have hConsA := hCons a
        omega

end Reversal
