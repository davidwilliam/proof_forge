import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
noncomputable instance instDecPost (s : State) (e : Entry) : Decidable (ValidPost s e) := Classical.propDecidable _
noncomputable instance instDecRev (s : State) (i : EntryId) : Decidable (ValidReverse s i) := Classical.propDecidable _
noncomputable instance instDecValid (s : State) (c : Command) : Decidable (Valid s c) := Classical.propDecidable _
noncomputable def step : Impl := fun s c =>
  match c with
  | .post e => if ValidPost s e then (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) else (.rejected, s)
  | .reverse i => if ValidReverse s i then match findEntry s.journal i with | some e => (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) | none => (.rejected, s) else (.rejected, s)

theorem findEntry_prop {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e ∈ j ∧ e.id = i := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih => simp only [findEntry] at h; split at h; next heq => injection h with h2; subst h2; exact ⟨List.mem_cons.mpr (Or.inl rfl), heq⟩; next _ => have r := ih h; exact ⟨List.mem_cons.mpr (Or.inr r.1), r.2⟩

theorem mem_ids_findEntry_isSome {j : List Entry} {i : EntryId} (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons hd tl ih =>
    simp only [findEntry]; by_cases heq : hd.id = i; simp [heq]
    · simp only [heq, ite_false]; have htl : i ∈ ids tl := by have h1 : i ∈ hd.id :: ids tl := by simpa [ids] using h; rcases List.mem_cons.mp h1 with hEq | hMem; exact absurd hEq.symm heq; exact hMem; exact ih htl

theorem ids_append_single (j : List Entry) (e : Entry) : ids (j ++ [e]) = ids j ++ [e.id] := by simp [ids]
theorem nodup_append_single {α : Type} [DecidableEq α] {l : List α} {x : α} (hl : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by rw [List.nodup_append]; refine ⟨hl, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩; intro a ha1 ha2; simp at ha2; subst ha2; exact hx ha1
theorem sumOver_zero_list {α : Type} (l : List α) : sumOver l (fun _ : α => (0:Int)) = 0 := by induction l with | nil => rfl | cons _ tl ih => simp only [sumOver_cons, ih, add_zero]
theorem sum_single'_general {xs : List AccountId} {k : AccountId} {v : Int} (hn : xs.Nodup) : sumOver xs (fun a => if k = a then v else 0) = if k ∈ xs then v else 0 := by have h : (fun a => if k = a then v else (0:Int)) = (fun a => if a = k then v else 0) := by funext a; by_cases h1 : k = a <;> by_cases h2 : a = k <;> simp_all; rw [h]; exact sumOver_ite_eq hn k v
theorem netOf_total_aux (accounts : List AccountId) (hn : accounts.Nodup) (ls : List Line) : sumOver accounts (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ accounts then l.2 else 0) := by induction ls with | nil => simp only [netOf, sumOver_zero_list] | cons hd tl ih => have h1 : ∀ a, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else (0:Int)) + netOf tl a := by intro a; simp [netOf]; have h2 : sumOver accounts (fun a => netOf (hd :: tl) a) = sumOver accounts (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by apply sumOver_congr; intro a _; exact h1 a; rw [h2, sumOver_add, sum_single'_general hn, ih]; rfl
theorem lineSum_eq_netTotal {accounts : List AccountId} (hn : accounts.Nodup) {ls : List Line} (h : ∀ l ∈ ls, l.1 ∈ accounts) : sumOver accounts (fun a => netOf ls a) = lineSum ls := by rw [netOf_total_aux accounts hn ls]; apply sumOver_congr; intro l hl; simp [h l hl]
theorem activeNet_post_not_reversed (s : State) (e : Entry) (a : AccountId) (he_not_rev : e.id ∉ s.reversed) : activeNet { s with journal := s.journal ++ [e] } a = activeNet s a + netOf e.lines a := by have h1 : activeNet { s with journal := s.journal ++ [e] } a = sumOver (s.journal ++ [e]) (fun e_1 => if e_1.id ∈ s.reversed then (0:Int) else netOf e_1.lines a) := rfl; rw [h1, sumOver_append]; simp only [sumOver_cons, sumOver_nil, add_zero]; have h2 : (if e.id ∈ s.reversed then (0:Int) else netOf e.lines a) = netOf e.lines a := by simp [he_not_rev]; rw [h2]
theorem activeNet_reverse_nodup (s : State) (i : EntryId) (e : Entry) (a : AccountId) (hfind : findEntry s.journal i = some e) (hnodup : (ids s.journal).Nodup) : activeNet { s with reversed := i :: s.reversed } a = activeNet s a - netOf e.lines a := by induction s.journal with | nil => simp [findEntry] at hfind | cons hd tl ih => simp only [findEntry] at hfind; by_cases heq : hd.id = i; simp [heq] at hfind; subst hfind; have hnotin : i ∉ ids tl := by have h1 : (ids (hd :: tl)).Nodup := hnodup; simp [ids] at h1; exact h1.1; have hrest_eq : sumOver tl (fun e_1 => if e_1.id ∈ i :: s.reversed then (0:Int) else netOf e_1.lines a) = sumOver tl (fun e_1 => if e_1.id ∈ s.reversed then 0 else netOf e_1.lines a) := by apply sumOver_congr; intro e_1 he_1; have he_id_ne : e_1.id ≠ i := by intro hc; have : e_1.id ∈ ids tl := by simp [ids, List.mem_map.mpr ⟨e_1, he_1, rfl⟩]; rw [← hc] at hnotin; exact hnotin this; simp [he_id_ne]; simp only [activeNet, sumOver_cons] at *; omega; simp only [heq, ite_false] at hfind; have hnodup_tl : (ids tl).Nodup := by simp [ids] at hnodup; exact hnodup.2; have ih' := ih hfind hnodup_tl; have hhead : (if hd.id ∈ i :: s.reversed then (0:Int) else netOf hd.lines a) = (if hd.id ∈ s.reversed then 0 else netOf hd.lines a) := by simp [heq]; simp only [activeNet, sumOver_cons, hhead] at ih' ⊢; omega
theorem findEntry_append_notMem {j : List Entry} {e : Entry} (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by induction j with | nil => simp [findEntry] | cons hd tl ih => have hhd : hd.id ≠ e.id := by intro heq; apply h; simp [ids, heq]; have htl : e.id ∉ ids tl := by intro hm; apply h; simp [ids, hm]; have : (hd :: tl) ++ [e] = hd :: (tl ++ [e]) := by simp; rw [this]; simp [findEntry, hhd, ih htl]
theorem post_ok_imp_valid {s : State} {e : Entry} (hOk : (step s (.post e)).1 = .ok) : ValidPost s e := by unfold step at hOk; by_cases hv : ValidPost s e; exact hv; simp [hv] at hOk
theorem rev_ok_imp_valid {s : State} {i : EntryId} (hOk : (step s (.reverse i)).1 = .ok) : ValidReverse s i := by unfold step at hOk; by_cases hv : ValidReverse s i; exact hv; simp [hv] at hOk

theorem req_post_succeeds : PostSucceeds step := by intro s e h; unfold step; simp [h]
theorem req_reverse_succeeds : ReverseSucceeds step := by intro s i h; unfold step; simp only [h, ↓reduceIte]; obtain ⟨e, he⟩ := mem_ids_findEntry_isSome h.1; simp [he]
theorem req_invalid_noop : InvalidNoop step := by intro s c h; cases c with | post e => unfold Valid at h; simp [step, h] | reverse i => unfold Valid at h; unfold step; have hn : ¬ValidReverse s i := h; simp [hn]
theorem req_post_effects : PostEffects step := by
  intro s e hOk
  have hV : ValidPost s e := post_ok_imp_valid hOk
  have hEq : step s (.post e) = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by unfold step; simp [hV]
  have h2 : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by rw [hEq]
  refine ⟨by rw [h2], by rw [h2], by rw [h2], by rw [h2], ?_⟩
  intro a; rw [h2]
theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hOk hFind
  have hV : ValidReverse s i := rev_ok_imp_valid hOk
  have hEq : step s (.reverse i) = (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by unfold step; simp [hV, hFind]
  have h2 : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by rw [hEq]
  refine ⟨by rw [h2], by rw [h2], by rw [h2], ?_, ?_⟩
  · intro x; rw [h2]; simp
  · intro a; rw [h2]
theorem req_reverse_once : ReverseOnce step := by
  intro s i hOk
  have hV : ValidReverse s i := rev_ok_imp_valid hOk
  obtain ⟨e, he⟩ := mem_ids_findEntry_isSome hV.1
  have hEq : step s (.reverse i) = (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by unfold step; simp [hV, he]
  have hSt : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by rw [hEq]
  rw [hSt]
  have hNot : ¬ ValidReverse { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } i := by simp [ValidReverse]
  show step { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } (.reverse i) = _
  unfold step; simp [hNot]
theorem req_roundtrip : RoundTrip step := by
  intro s e hOk
  have hV : ValidPost s e := post_ok_imp_valid hOk
  have hEqPost : step s (.post e) = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by unfold step; simp [hV]
  have hSt : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by rw [hEqPost]
  have hFind : findEntry (s.journal ++ [e]) e.id = some e := findEntry_append_notMem hV.2.2.2.2.1
  have hValidRev : ValidReverse { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } e.id := by constructor; rw [ids_append_single]; simp; simp; exact hV.2.2.2.2.2
  have hEqRev : step { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } (.reverse e.id) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a - netOf e.lines a, journal := s.journal ++ [e], reversed := e.id :: s.reversed }) := by unfold step; simp [hValidRev, hFind]
  constructor
  · have : (step (step s (.post e)).2 (.reverse e.id)).1 = (step { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } (.reverse e.id)).1 := by rw [hSt]
    rw [this, hEqRev]
  · have : (step (step s (.post e)).2 (.reverse e.id)).2.balance = (step { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } (.reverse e.id)).2.balance := by rw [hSt]
    rw [this, hEqRev]; funext a; simp only; omega
theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hOk; cases c with
  | post e =>
    have hV : ValidPost s e := post_ok_imp_valid hOk
    have hEq : step s (.post e) = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by unfold step; simp [hV]
    have h1 : total (step s (.post e)).2 = total { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed } := by rw [hEq]
    have h1' : total { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed } = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := rfl
    have h2 : (sumOver s.accounts fun a => s.balance a + netOf e.lines a) = total s + sumOver s.accounts (fun a => netOf e.lines a) := by unfold total; rw [sumOver_add]
    have h3 : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := lineSum_eq_netTotal hwf.1 hV.2.1
    rw [h1, h1', h2, h3, hV.2.2.2.1]; omega
  | reverse i =>
    have hV : ValidReverse s i := rev_ok_imp_valid hOk
    obtain ⟨e, he⟩ := mem_ids_findEntry_isSome hV.1
    have hEq : step s (.reverse i) = (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by unfold step; simp [hV, he]
    have h1 : total (step s (.reverse i)).2 = total { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by rw [hEq]
    have h1' : total { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } = sumOver s.accounts (fun a => s.balance a - netOf e.lines a) := rfl
    have h2 : (sumOver s.accounts fun a => s.balance a - netOf e.lines a) = total s - sumOver s.accounts (fun a => netOf e.lines a) := by unfold total; rw [sumOver_sub]
    have he_in : e ∈ s.journal := (findEntry_prop he).1
    have hBal := hwf.2.2.2 e he_in
    have h3 : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := lineSum_eq_netTotal hwf.1 hBal.1
    rw [h1, h1', h2, h3]; omega
theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf; cases c with
  | post e =>
    unfold step; by_cases hV : ValidPost s e
    · simp only [hV, ite_true]; obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩ := hwf
      refine ⟨hNodupAcc, ?_, ?_, ?_⟩
      · rw [ids_append_single]; exact nodup_append_single hNodupIds hV.2.2.2.2.1
      · intro j hj; have : j ∈ ids s.journal := hRevSub j hj; rw [ids_append_single]; exact List.mem_append.mpr (Or.inl this)
      · intro e' he'; have hmem : e' ∈ s.journal ∨ e' = e := by rcases List.mem_append.mp he' with h | h; exact Or.inl h; have : e' ∈ [e] := h; rw [List.mem_singleton.mp this]; exact Or.inr rfl; rcases hmem with h | rfl; exact hBal e' h; exact ⟨hV.2.1, hV.2.2.2.1⟩
    · simp only [hV, ite_false]; exact hwf
  | reverse i =>
    unfold step; by_cases hV : ValidReverse s i
    · simp only [hV, ite_true]; have hEx : ∃ e, findEntry s.journal i = some e := mem_ids_findEntry_isSome hV.1; obtain ⟨e, he⟩ := hEx; simp only [he]
      obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩ := hwf; exact ⟨hNodupAcc, hNodupIds, by intro j hj; rcases List.mem_cons.mp hj with rfl | hmem; exact hV.1; exact hRevSub j hmem, hBal⟩
    · simp only [hV, ite_false]; exact hwf
theorem req_consistent : StaysConsistent step := by
  intro s c hwf hCons; cases c with
  | post e =>
    unfold step; by_cases hV : ValidPost s e
    · simp only [hV, ite_true]; intro a; show s.balance a + netOf e.lines a = s.opening a + activeNet { s with journal := s.journal ++ [e] } a
      have hActive := activeNet_post_not_reversed s e a hV.2.2.2.2.2; rw [hActive, hCons a]; omega
    · simp only [hV, ite_false]; exact hCons
  | reverse i =>
    unfold step; by_cases hV : ValidReverse s i
    · simp only [hV, ite_true]; have hEx : ∃ e, findEntry s.journal i = some e := mem_ids_findEntry_isSome hV.1; obtain ⟨e, he⟩ := hEx; simp only [he]; intro a
      have hActive := activeNet_reverse_nodup s i e a he hwf.2.1
      show s.balance a - netOf e.lines a = s.opening a + activeNet { s with reversed := i :: s.reversed } a; rw [hActive, hCons a]; omega
    · simp only [hV, ite_false]; exact hCons
end Reversal
