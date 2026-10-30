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
    | some e =>
      if i ∈ s.reversed then (.rejected, s)
      else (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed })

theorem findEntry_mem_ids_aux2 {j : List Entry} {i : EntryId} (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons hd tl ih =>
    unfold findEntry
    by_cases he : hd.id = i
    · exact ⟨hd, by simp [he]⟩
    · simp only [he, ite_false]
      apply ih
      have h2 : i ∈ ids tl := by
        have h' : i ∈ hd.id :: ids tl := by
          have : ids (hd :: tl) = hd.id :: ids tl := rfl
          rw [← this]
          exact h
        simp at h'
        rcases h' with h1 | h2
        · exact absurd h1.symm he
        · exact h2
      exact h2

theorem findEntry_some_mem_ids7 {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : i ∈ ids j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    unfold findEntry at h
    split at h
    next heq =>
      have : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [this]
      simp [heq]
    next heq =>
      have ih2 := ih h
      have : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [this]
      exact List.Mem.tail _ ih2

theorem sumOver_zeroList {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem sumOver_swap2 {α β : Type} (l1 : List α) (l2 : List β) (f : β → α → Int) :
    sumOver l1 (fun a => sumOver l2 (fun b => f b a)) = sumOver l2 (fun b => sumOver l1 (fun a => f b a)) := by
  induction l2 with
  | nil => simp only [sumOver_nil, sumOver_zeroList]
  | cons b bs ih =>
    simp only [sumOver_cons]
    have h1 : sumOver l1 (fun a => f b a + sumOver bs (fun b2 => f b2 a)) = sumOver l1 (fun a => f b a) + sumOver l1 (fun a => sumOver bs (fun b2 => f b2 a)) := by
      rw [← sumOver_add]
    calc sumOver l1 (fun a => f b a + sumOver bs (fun b2 => f b2 a)) = sumOver l1 (fun a => f b a) + sumOver l1 (fun a => sumOver bs (fun b2 => f b2 a)) := h1
      _ = sumOver l1 (fun a => f b a) + sumOver bs (fun b2 => sumOver l1 (fun a => f b2 a)) := by rw [ih]
      _ = sumOver (b :: bs) (fun b => sumOver l1 (fun a => f b a)) := by simp

theorem sumNetAux2 (ls : List Line) (accs : List AccountId) (hl : accs.Nodup) :
    sumOver accs (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ accs then l.2 else 0) := by
  unfold netOf
  have hswap := sumOver_swap2 accs ls (fun l a => if l.1 = a then l.2 else 0)
  rw [hswap]
  apply sumOver_congr
  intro l _
  have h : sumOver accs (fun a => if l.1 = a then l.2 else (0 : Int)) = if l.1 ∈ accs then l.2 else 0 := by
    have hsym : ∀ a, (if l.1 = a then l.2 else (0 : Int)) = (if a = l.1 then l.2 else 0) := by
      intro a; by_cases heq : l.1 = a
      · subst heq; simp
      · have : a ≠ l.1 := fun h => heq h.symm
        simp [heq, this]
    have heq2 : sumOver accs (fun a => if l.1 = a then l.2 else (0 : Int)) = sumOver accs (fun a => if a = l.1 then l.2 else 0) := by
      apply sumOver_congr; intro a ha; exact hsym a
    rw [heq2]
    exact sumOver_ite_eq hl l.1 l.2
  exact h

theorem sumNet_eq_lineSum_aux2 (ls : List Line) (accs : List AccountId) (hNodup : accs.Nodup) (hMem : ∀ l ∈ ls, l.1 ∈ accs) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  rw [sumNetAux2 ls accs hNodup]
  unfold lineSum
  apply sumOver_congr
  intro l hl
  have hm := hMem l hl
  simp [hm]

theorem findEntry_mem3 {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e ∈ j ∧ e.id = i := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    unfold findEntry at h
    by_cases heq : hd.id = i
    · simp [heq] at h
      simp [← h, heq]
    · simp [heq] at h
      have ih2 := ih h
      exact ⟨List.Mem.tail _ ih2.1, ih2.2⟩

theorem reverse_activeNet_aux2 (a : AccountId) (l : List Entry) (rev : List EntryId) (i : EntryId) (e : Entry) (hFind : findEntry l i = some e) (hNodup : (ids l).Nodup) (hNotRev : i ∉ rev) :
    sumOver l (fun e2 => if e2.id ∈ (i :: rev) then (0 : Int) else netOf e2.lines a) =
    sumOver l (fun e2 => if e2.id ∈ rev then (0 : Int) else netOf e2.lines a) - netOf e.lines a := by
  induction l with
  | nil => simp [findEntry] at hFind
  | cons hd tl ih =>
    have hIdsEq : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hIdsEq] at hNodup
    have hHdNotIn : hd.id ∉ ids tl := (List.nodup_cons.mp hNodup).1
    have hNodupTl : (ids tl).Nodup := (List.nodup_cons.mp hNodup).2
    unfold findEntry at hFind
    by_cases heq : hd.id = i
    · simp [heq] at hFind
      have hHdEq : hd = e := by simp [← hFind]
      subst hHdEq
      have hHdNotRev : hd.id ∉ rev := by rw [heq]; exact hNotRev
      simp only [sumOver_cons]
      have h1 : (if hd.id ∈ (i :: rev) then (0 : Int) else netOf hd.lines a) = 0 := by simp [heq]
      have h2 : (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) = netOf hd.lines a := by simp [hHdNotRev]
      rw [h1, h2]
      have hTlEq : sumOver tl (fun e2 => if e2.id ∈ (i :: rev) then (0 : Int) else netOf e2.lines a) = sumOver tl (fun e2 => if e2.id ∈ rev then (0 : Int) else netOf e2.lines a) := by
        apply sumOver_congr
        intro e2 hMem2
        have hIdNe : e2.id ≠ i := by
          intro hEq2
          have hIn : e2.id ∈ ids tl := by simp [ids]; exact ⟨e2, hMem2, rfl⟩
          rw [hEq2] at hIn
          have hContra : hd.id ∈ ids tl := by rw [heq]; exact hIn
          exact hHdNotIn hContra
        have hNotIn1 : (e2.id ∈ (i :: rev)) = (e2.id ∈ rev) := by simp [hIdNe]
        simp [hNotIn1]
      rw [hTlEq]
      omega
    · simp [heq] at hFind
      have ih' := ih hFind hNodupTl
      simp only [sumOver_cons]
      have hCase : (if hd.id ∈ (i :: rev) then (0 : Int) else netOf hd.lines a) = (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) := by
        by_cases hHdRev : hd.id ∈ rev
        · have hHdIn' : hd.id ∈ (i :: rev) := by simp [hHdRev]
          simp [hHdIn', hHdRev]
        · have hHdNotIn' : hd.id ∉ (i :: rev) := by simp [hHdRev, heq]
          simp [hHdRev, hHdNotIn']
      rw [hCase, ih']
      omega

theorem findEntry_append_of_not_mem (j : List Entry) (e : Entry) (hNot : e.id ∉ ids j) :
    findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have hHdNe : hd.id ≠ e.id := by
      intro heq
      apply hNot
      have : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [this]
      simp [heq]
    have hNotTail : e.id ∉ ids tl := by
      intro hmem
      apply hNot
      have : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [this]
      exact List.Mem.tail _ hmem
    simp [findEntry, hHdNe, ih hNotTail]

theorem req_post_succeeds    : PostSucceeds step := by
  intro s e h
  simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i ⟨hIds, hNotRev⟩
  have hex := findEntry_mem_ids_aux2 hIds
  rcases hex with ⟨e, he⟩
  simp [step, he, hNotRev]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c hNot
  cases c with
  | post e =>
    simp [Valid] at hNot
    simp [step, hNot]
  | reverse i =>
    simp [Valid, ValidReverse] at hNot
    cases hFind : findEntry s.journal i with
    | none =>
      simp [step, hFind]
    | some e =>
      by_cases hMem : i ∈ s.reversed
      · simp [step, hFind, hMem]
      · exfalso
        have hIds : i ∈ ids s.journal := findEntry_some_mem_ids7 hFind
        have hRev : i ∈ s.reversed := hNot hIds
        exact hMem hRev

theorem req_post_effects : PostEffects step := by
  intro s e hok
  by_cases hV : ValidPost s e
  · have hs : step s (.post e) = (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by simp [step, hV]
    rw [hs]
    exact ⟨rfl, rfl, rfl, rfl, fun a => rfl⟩
  · have hs : step s (.post e) = (.rejected, s) := by simp [step, hV]
    rw [hs] at hok
    cases hok

theorem req_reverse_effects  : ReverseEffects step := by
  intro s i e hOk hFind
  have hUnfold : step s (Command.reverse i) =
    match findEntry s.journal i with
    | none => (Outcome.rejected, s)
    | some e' => if i ∈ s.reversed then (Outcome.rejected, s) else (Outcome.ok, { s with balance := fun a => s.balance a - netOf e'.lines a, reversed := i :: s.reversed }) := rfl
  rw [hFind] at hUnfold
  by_cases hMem : i ∈ s.reversed
  · have : (step s (Command.reverse i)).1 = Outcome.rejected := by rw [hUnfold]; simp [hMem]
    rw [this] at hOk
    contradiction
  · have hEq : step s (Command.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
      rw [hUnfold]; simp [hMem]
    rw [hEq]
    exact ⟨rfl, rfl, rfl, by simp, fun a => rfl⟩

theorem req_reverse_once : ReverseOnce step := by
  intro s i hOk
  cases hFind : findEntry s.journal i with
  | none =>
    have : (step s (Command.reverse i)).1 = Outcome.rejected := by simp [step, hFind]
    rw [this] at hOk
    contradiction
  | some e =>
    by_cases hMem : i ∈ s.reversed
    · have : (step s (Command.reverse i)).1 = Outcome.rejected := by simp [step, hFind, hMem]
      rw [this] at hOk
      contradiction
    · have hEq1 : step s (Command.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
        simp [step, hFind, hMem]
      have hFE2 : findEntry (step s (Command.reverse i)).2.journal i = some e := by
        have hJ : (step s (Command.reverse i)).2.journal = s.journal := by rw [hEq1]
        rw [hJ, hFind]
      have hMem2 : i ∈ (step s (Command.reverse i)).2.reversed := by
        have hR : (step s (Command.reverse i)).2.reversed = i :: s.reversed := by rw [hEq1]
        rw [hR]; simp
      show step (step s (Command.reverse i)).2 (Command.reverse i) = (Outcome.rejected, (step s (Command.reverse i)).2)
      have hStep2 : step (step s (Command.reverse i)).2 (Command.reverse i) =
        match findEntry (step s (Command.reverse i)).2.journal i with
        | none => (Outcome.rejected, (step s (Command.reverse i)).2)
        | some e' => if i ∈ (step s (Command.reverse i)).2.reversed then (Outcome.rejected, (step s (Command.reverse i)).2) else (Outcome.ok, { (step s (Command.reverse i)).2 with balance := fun a => (step s (Command.reverse i)).2.balance a - netOf e'.lines a, reversed := i :: (step s (Command.reverse i)).2.reversed }) := rfl
      rw [hStep2, hFE2]
      simp [hMem2]

theorem req_roundtrip : RoundTrip step := by
  intro s e hOk
  have hV : ValidPost s e := by
    by_cases h : ValidPost s e
    · exact h
    · have hs : (step s (Command.post e)).1 = Outcome.rejected := by simp [step, h]
      rw [hs] at hOk
      cases hOk
  have hPost : step s (.post e) = (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by simp [step, hV]
  have hNotInIds : e.id ∉ ids s.journal := hV.2.2.2.2.1
  have hNotRev : e.id ∉ s.reversed := hV.2.2.2.2.2
  have hFind : findEntry (s.journal ++ [e]) e.id = some e :=
    findEntry_append_of_not_mem s.journal e hNotInIds
  have hFind2 : findEntry ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State).journal e.id = some e := hFind
  have hRev2 : e.id ∉ ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State).reversed := hNotRev
  have hStep2 : step { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } (.reverse e.id) =
    (Outcome.ok, { ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) with balance := fun a => (({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State).balance a - netOf e.lines a), reversed := e.id :: ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State).reversed }) := by
    simp [step, hFind2, hRev2]
  have hS1eq : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by rw [hPost]
  constructor
  · rw [hS1eq, hStep2]
  · rw [hS1eq, hStep2]
    funext a
    simp

theorem req_trial_balance    : TrialBalance step := by
  intro s c hWF hOk
  cases c with
  | post e =>
    have hV : ValidPost s e := by
      by_cases h : ValidPost s e
      · exact h
      · have hs : (step s (Command.post e)).1 = Outcome.rejected := by simp [step, h]
        rw [hs] at hOk
        cases hOk
    have hAcc : (step s (Command.post e)).2.accounts = s.accounts := by simp [step, hV]
    have hBal : (step s (Command.post e)).2.balance = fun a => s.balance a + netOf e.lines a := by
      ext a; simp [step, hV]
    unfold total
    rw [hAcc, hBal]
    have hsum : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := by
      rw [← sumOver_add]
    rw [hsum]
    have hNetZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
      have hNetEq := sumNet_eq_lineSum_aux2 e.lines s.accounts hWF.1 hV.2.1
      have hLineZero : lineSum e.lines = 0 := hV.2.2.2.1
      rw [hNetEq, hLineZero]
    rw [hNetZero]
    simp
  | reverse i =>
    cases hFind : findEntry s.journal i with
    | none =>
      have hs : (step s (Command.reverse i)).1 = Outcome.rejected := by simp [step, hFind]
      rw [hs] at hOk
      cases hOk
    | some e =>
      by_cases hMem : i ∈ s.reversed
      · have hs : (step s (Command.reverse i)).1 = Outcome.rejected := by simp [step, hFind, hMem]
        rw [hs] at hOk
        cases hOk
      · have hAcc : (step s (Command.reverse i)).2.accounts = s.accounts := by simp [step, hFind, hMem]
        have hBal : (step s (Command.reverse i)).2.balance = fun a => s.balance a - netOf e.lines a := by
          ext a; simp [step, hFind, hMem]
        unfold total
        rw [hAcc, hBal]
        have hsum : sumOver s.accounts (fun a => s.balance a - netOf e.lines a) = sumOver s.accounts s.balance - sumOver s.accounts (fun a => netOf e.lines a) := by
          rw [← sumOver_sub]
        rw [hsum]
        have hNetZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
          have hE_mem := findEntry_mem3 hFind
          have hE_prop := hWF.2.2.2 e hE_mem.1
          have hLineZero : lineSum e.lines = 0 := hE_prop.2
          have hMemAcc : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hE_prop.1
          have hNetEq := sumNet_eq_lineSum_aux2 e.lines s.accounts hWF.1 hMemAcc
          rw [hNetEq, hLineZero]
        rw [hNetZero]
        simp

theorem req_well_formed      : StaysWellFormed step := by
  intro s c hWF
  have hNodupAppend : ∀ (l : List EntryId) (x : EntryId), l.Nodup → x ∉ l → (l ++ [x]).Nodup := by
    intro l x hN hNot
    induction l with
    | nil => simp
    | cons hd tl ih =>
      have hTlNodup : tl.Nodup := (List.nodup_cons.mp hN).2
      have hHdNotTl : hd ∉ tl := (List.nodup_cons.mp hN).1
      have hNotTl : x ∉ tl := fun h => hNot (List.mem_cons_of_mem _ h)
      have ih' := ih hTlNodup hNotTl
      have hHdNot : hd ∉ tl ++ [x] := by
        intro hmem
        have hmem' := List.mem_append.mp hmem
        rcases hmem' with ht | hx
        · exact hHdNotTl ht
        · simp at hx
          have : x ∈ hd :: tl := by rw [← hx]; exact List.Mem.head _
          exact hNot this
      have hEq : hd :: tl ++ [x] = hd :: (tl ++ [x]) := rfl
      rw [hEq]
      exact List.nodup_cons.mpr ⟨hHdNot, ih'⟩
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hStep : (step s (Command.post e)).2 = { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } := by
        simp [step, hV]
      rw [hStep]
      have hAcc : s.accounts.Nodup := hWF.1
      have hIds : (ids s.journal).Nodup := hWF.2.1
      have hRev : ∀ i ∈ s.reversed, i ∈ ids s.journal := hWF.2.2.1
      refine ⟨by simp; exact hAcc, ?_, ?_, ?_⟩
      · have hIdsEq : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := by simp [ids]
        rw [hIdsEq]
        exact hNodupAppend _ _ hIds hV.2.2.2.2.1
      · intro i hi
        have : i ∈ ids s.journal := hRev i hi
        show i ∈ ids (s.journal ++ [e])
        simp [ids] at this ⊢
        simp [this]
      · intro e2 he2
        simp at he2
        rcases he2 with heMem | rfl
        · have h := hWF.2.2.2 e2 heMem
          exact h
        · exact ⟨hV.2.1, hV.2.2.2.1⟩
    · have hStep : (step s (Command.post e)).2 = s := by simp [step, hV]
      rw [hStep]; exact hWF
  | reverse i =>
    by_cases hFE : findEntry s.journal i = none
    · have hStep : (step s (Command.reverse i)).2 = s := by simp [step, hFE]
      rw [hStep]; exact hWF
    · have hExists : ∃ e, findEntry s.journal i = some e := by
        cases h : findEntry s.journal i with
        | none => simp [h] at hFE
        | some e => exact ⟨e, rfl⟩
      rcases hExists with ⟨e, hFE2⟩
      by_cases hMem : i ∈ s.reversed
      · have hStep : (step s (Command.reverse i)).2 = s := by simp [step, hFE2, hMem]
        rw [hStep]; exact hWF
      · have hStep : (step s (Command.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by
          simp [step, hFE2, hMem]
        rw [hStep]
        refine ⟨by simp; exact hWF.1, by simp; exact hWF.2.1, ?_, ?_⟩
        · intro j hj
          simp at hj
          rcases hj with rfl | hjMem
          · exact findEntry_some_mem_ids7 hFE2
          · exact hWF.2.2.1 j hjMem
        · intro e2 he2
          have h := hWF.2.2.2 e2 he2
          exact h

theorem req_consistent : StaysConsistent step := by
  intro s c hWF hCons
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hStep : (step s (Command.post e)).2 = { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } := by simp [step, hV]
      rw [hStep]
      intro a
      simp only
      have hBal : s.balance a = s.opening a + activeNet s a := hCons a
      have hNotRev : e.id ∉ s.reversed := hV.2.2.2.2.2
      have hActive : activeNet ({ s with journal := s.journal ++ [e] } : State) a = activeNet s a + netOf e.lines a := by
        unfold activeNet
        rw [sumOver_append]
        simp only [sumOver_cons, sumOver_nil]
        have hIf : (if e.id ∈ s.reversed then (0 : Int) else netOf e.lines a) = netOf e.lines a := by simp [hNotRev]
        rw [hIf]
        omega
      have hActive2 : activeNet ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) a = activeNet ({ s with journal := s.journal ++ [e] } : State) a := rfl
      rw [hActive2, hActive]
      omega
    · have hStep : (step s (Command.post e)).2 = s := by simp [step, hV]
      rw [hStep]; exact hCons
  | reverse i =>
    by_cases hFindNone : findEntry s.journal i = none
    · have hStep : (step s (Command.reverse i)).2 = s := by simp [step, hFindNone]
      rw [hStep]; exact hCons
    · have hExists : ∃ e, findEntry s.journal i = some e := by
        cases h : findEntry s.journal i with
        | none => simp [h] at hFindNone
        | some e => exact ⟨e, rfl⟩
      rcases hExists with ⟨e, hFind⟩
      by_cases hMem : i ∈ s.reversed
      · have hStep : (step s (Command.reverse i)).2 = s := by simp [step, hFind, hMem]
        rw [hStep]; exact hCons
      · have hStep : (step s (Command.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by simp [step, hFind, hMem]
        rw [hStep]
        intro a
        simp only
        have hBal : s.balance a = s.opening a + activeNet s a := hCons a
        have hActiveEq : activeNet ({ s with reversed := i :: s.reversed } : State) a = activeNet s a - netOf e.lines a := by
          unfold activeNet
          exact reverse_activeNet_aux2 a s.journal s.reversed i e hFind hWF.2.1 hMem
        have hActiveEq2 : activeNet ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) a = activeNet ({ s with reversed := i :: s.reversed } : State) a := rfl
        rw [hActiveEq2, hActiveEq]
        omega

end Reversal
