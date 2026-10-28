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

def myTestDef : Nat := 1

theorem myTestThm : 1 = 1 := rfl

theorem auxFindMem (j : List Entry) (i : EntryId) (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons e es ih =>
    simp only [ids, List.map_cons, List.mem_cons] at h
    by_cases he : e.id = i
    · exact ⟨e, by simp [findEntry, he]⟩
    · have hmem : i ∈ ids es := by
        cases h with
        | inl h_eq => exact absurd h_eq.symm he
        | inr h_mem => exact h_mem
      obtain ⟨e', he'⟩ := ih hmem
      exact ⟨e', by simp [findEntry, he, he']⟩

theorem findMem_of_some (j : List Entry) (i : EntryId) (e : Entry)
    (h : findEntry j i = some e) : i ∈ ids j := by
  unfold ids
  induction j with
  | nil => simp [findEntry] at h
  | cons e' es ih =>
    simp only [findEntry] at h
    by_cases he : e'.id = i
    · simp [he]
    · simp only [he, ↓reduceIte] at h
      have ihm := ih h
      simp [ihm]

theorem req_reverse_once_proof : True := trivial

theorem findEntry_of_not_mem_append2 (j : List Entry) (e : Entry) (h : e.id ∉ ids j) :
    findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have hne : hd.id ≠ e.id := by
      intro hEq
      apply h
      have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [hids]
      simp [hEq]
    have hmem : e.id ∉ ids tl := by
      intro hIn
      apply h
      have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [hids]
      simp [hIn]
    have hih := ih hmem
    have hcons : (hd :: tl) ++ [e] = hd :: (tl ++ [e]) := rfl
    rw [hcons]
    simp only [findEntry, hne, ↓reduceIte]
    exact hih

theorem req_roundtrip_aux_test : True := trivial

theorem trial_test : 1 = 1 := rfl

theorem trial_sumNet_aux2 (accs : List AccountId) (x : AccountId) (c : Int) (hmem : x ∈ accs) (hnd : accs.Nodup) :
    sumOver accs (fun a => if x = a then c else 0) = c := by
  have h1 : (fun a : AccountId => if x = a then c else (0:Int)) = (fun a => if a = x then c else 0) := by
    funext a
    simp [eq_comm]
  rw [h1, sumOver_ite_eq hnd x c]
  simp [hmem]

theorem trial_zero (accs : List AccountId) : sumOver accs (fun _ : AccountId => (0:Int)) = 0 := by
  induction accs with
  | nil => simp
  | cons a l ih => simp [ih]

theorem trial_sumNet3 (ls : List Line) (accs : List AccountId)
    (hmem : ∀ l ∈ ls, l.1 ∈ accs) (hnd : accs.Nodup) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have hfun : (fun a : AccountId => netOf ([] : List Line) a) = (fun _ => (0:Int)) := by
      funext a; simp [netOf]
    rw [hfun]
    have hz : lineSum ([] : List Line) = 0 := by simp [lineSum]
    rw [hz]
    exact trial_zero accs
  | cons hd tl ih =>
    have hhd : hd.1 ∈ accs := hmem hd (by simp)
    have htl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hmem l (by simp [hl])
    have ih_eq := ih htl
    have hcongr : sumOver accs (fun a => netOf (hd :: tl) a)
        = sumOver accs (fun a => ((if hd.1 = a then hd.2 else 0) + netOf tl a)) := by
      apply sumOver_congr
      intro a _
      simp [netOf]
    rw [hcongr, sumOver_add accs _ _, trial_sumNet_aux2 accs hd.1 hd.2 hhd hnd, ih_eq]
    simp [lineSum]

theorem trial_find_mem4 (j : List Entry) (i : EntryId) (e : Entry)
    (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases he : hd.id = i
    · simp only [he, ↓reduceIte] at h
      have heq : hd = e := Option.some_inj.mp h
      rw [← heq]; simp
    · simp only [he, ↓reduceIte] at h
      have ihm := ih h
      simp [ihm]

theorem nodup_append_singleton_aux2 (l : List Nat) (x : Nat) (hN : l.Nodup) (hNi : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hN1 : hd ∉ tl := (List.nodup_cons.mp hN).1
    have hN2 : tl.Nodup := (List.nodup_cons.mp hN).2
    have hNi2 : x ∉ tl := fun h => hNi (List.mem_cons_of_mem hd h)
    have hne : hd ≠ x := fun hEq => hNi (by simp [hEq])
    have ihR := ih hN2 hNi2
    simp only [List.cons_append]
    rw [List.nodup_cons]
    refine ⟨?_, ihR⟩
    intro hMem
    rw [List.mem_append] at hMem
    cases hMem with
    | inl h1 => exact hN1 h1
    | inr h2 => simp at h2; exact hne h2

theorem activeNet_post_eq (j : List Entry) (e : Entry) (r : List EntryId) (a : AccountId)
    (h : e.id ∉ r) :
    sumOver (j ++ [e]) (fun x => if x.id ∈ r then (0:Int) else netOf x.lines a)
      = sumOver j (fun x => if x.id ∈ r then (0:Int) else netOf x.lines a) + netOf e.lines a := by
  rw [sumOver_append]
  simp [h]

theorem activeNet_reverse_eq_aux2 (j : List Entry) (r : List EntryId) (i : EntryId) (e : Entry) (a : AccountId)
    (hFind : findEntry j i = some e) (hNot : i ∉ r) (hNodup : (ids j).Nodup) :
    sumOver j (fun x => if x.id ∈ (i :: r) then (0:Int) else netOf x.lines a)
      = sumOver j (fun x => if x.id ∈ r then (0:Int) else netOf x.lines a) - netOf e.lines a := by
  induction j generalizing e with
  | nil => simp [findEntry] at hFind
  | cons hd tl ih =>
    have hCons : ids (hd :: tl) = hd.id :: ids tl := rfl
    have hNodupCons : (hd.id :: ids tl).Nodup := hCons ▸ hNodup
    rw [List.nodup_cons] at hNodupCons
    obtain ⟨hHdNot, hTlNodup⟩ := hNodupCons
    have hTlNodup2 : (ids tl).Nodup := hTlNodup
    simp only [sumOver_cons]
    by_cases heq : hd.id = i
    · have hFind2 : (some hd : Option Entry) = some e := by simpa [findEntry, heq] using hFind
      have he : hd = e := Option.some_inj.mp hFind2
      have hHdIn : hd.id ∈ (i :: r) := List.mem_cons.mpr (Or.inl heq)
      have hHdNotR : hd.id ∉ r := by intro hC; apply hNot; exact heq ▸ hC
      have hif1 : (if hd.id ∈ (i :: r) then (0:Int) else netOf hd.lines a) = 0 := if_pos hHdIn
      have hif2 : (if hd.id ∈ r then (0:Int) else netOf hd.lines a) = netOf hd.lines a := if_neg hHdNotR
      have hE : netOf e.lines a = netOf hd.lines a := by rw [← he]
      rw [hif1, hif2, hE]
      have htail_congr : sumOver tl (fun x => if x.id ∈ (i :: r) then (0:Int) else netOf x.lines a)
          = sumOver tl (fun x => if x.id ∈ r then (0:Int) else netOf x.lines a) := by
        apply sumOver_congr
        intro x hx
        have hxids : x.id ∈ ids tl := List.mem_map.mpr ⟨x, hx, rfl⟩
        have hne : x.id ≠ i := by
          intro hEq
          apply hHdNot
          exact heq ▸ hEq ▸ hxids
        have hmem1 : (x.id ∈ (i :: r)) = (x.id ∈ r) := by simp [List.mem_cons, hne]
        simp only [hmem1]
      rw [htail_congr]
      omega
    · have hFindTl : findEntry tl i = some e := by simpa [findEntry, heq] using hFind
      have ihR := ih e hFindTl hTlNodup2
      have hhead : (if hd.id ∈ (i :: r) then (0:Int) else netOf hd.lines a)
          = (if hd.id ∈ r then (0:Int) else netOf hd.lines a) := by
        by_cases hHr : hd.id ∈ r
        · have hHi : hd.id ∈ (i :: r) := List.mem_cons.mpr (Or.inr hHr)
          simp [hHi, hHr]
        · have hHi : hd.id ∉ (i :: r) := by simp [List.mem_cons, heq, hHr]
          simp [hHi, hHr]
      rw [hhead, ihR]
      omega

theorem myHelperUnique123 : 1 = 1 := rfl

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  unfold step
  simp [h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  obtain ⟨hmem, hnot⟩ := h
  obtain ⟨e, he⟩ := auxFindMem s.journal i hmem
  unfold step
  simp [he, hnot]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c hInv
  cases c with
  | post e =>
    have hNP : ¬ ValidPost s e := hInv
    unfold step
    simp [hNP]
  | reverse i =>
    have hNR : ¬ ValidReverse s i := hInv
    unfold ValidReverse at hNR
    cases hEq : findEntry s.journal i with
    | none =>
      unfold step
      simp [hEq]
    | some e =>
      have hmem : i ∈ ids s.journal := findMem_of_some s.journal i e hEq
      have hIn : i ∈ s.reversed := Decidable.byContradiction (fun hN => hNR ⟨hmem, hN⟩)
      unfold step
      simp [hEq, hIn]

theorem req_post_effects : PostEffects step := by
  intro s e hOk
  by_cases hV : ValidPost s e
  · have hEq : step s (.post e) = (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
      simp [step, hV]
    rw [hEq]
    exact ⟨rfl, rfl, rfl, rfl, fun a => rfl⟩
  · have hRej : (step s (.post e)).1 = .rejected := by
      simp [step, hV]
    rw [hRej] at hOk
    contradiction

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hOk hFind
  have hNot : i ∉ s.reversed := by
    intro hIn
    have hStep : step s (.reverse i) = (.rejected, s) := by
      simp [step, hFind, hIn]
    have hEq : (step s (.reverse i)).1 = .rejected := by rw [hStep]
    rw [hEq] at hOk
    contradiction
  have hStep : step s (.reverse i) =
    (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
    simp [step, hFind, hNot]
  have h2 : (step s (.reverse i)).2 =
    ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
    rw [hStep]
  rw [h2]
  exact ⟨rfl, rfl, rfl, (fun x => by simp), fun a => rfl⟩

theorem req_reverse_once : ReverseOnce step := by
  intro s i hOk
  cases hEq : findEntry s.journal i with
  | none =>
    have hRej : (step s (.reverse i)).1 = .rejected := by simp [step, hEq]
    rw [hRej] at hOk
    contradiction
  | some e =>
    by_cases hIn : i ∈ s.reversed
    · have hRej : (step s (.reverse i)).1 = .rejected := by simp [step, hEq, hIn]
      rw [hRej] at hOk
      contradiction
    · have hStep : step s (.reverse i) =
        (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
        simp [step, hEq, hIn]
      have hR : (step s (.reverse i)).2.reversed = i :: s.reversed := by rw [hStep]
      have hMem : i ∈ (step s (.reverse i)).2.reversed := by rw [hR]; exact List.mem_cons_self
      have hNotValid : ¬ Valid (step s (.reverse i)).2 (.reverse i) := by
        intro hV
        have hVR : ValidReverse (step s (.reverse i)).2 i := hV
        exact hVR.2 hMem
      exact req_invalid_noop _ _ hNotValid

theorem req_roundtrip : RoundTrip step := by
  intro s e hOk
  by_cases hV : ValidPost s e
  · have hEff := req_post_effects s e hOk
    obtain ⟨hAcc, hOpen, hJ, hR, hB⟩ := hEff
    have hValidRev : ValidReverse (step s (.post e)).2 e.id := by
      constructor
      · rw [hJ]
        simp [ids]
      · rw [hR]
        exact hV.2.2.2.2.2
    have hOkRev : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok :=
      req_reverse_succeeds _ _ hValidRev
    refine ⟨hOkRev, ?_⟩
    have hFind : findEntry (step s (.post e)).2.journal e.id = some e := by
      rw [hJ]
      exact findEntry_of_not_mem_append2 s.journal e hV.2.2.2.2.1
    have hRevEff := req_reverse_effects (step s (.post e)).2 e.id e hOkRev hFind
    obtain ⟨_, _, _, _, hbalEq⟩ := hRevEff
    funext a
    have h1 := hbalEq a
    have h2 := hB a
    omega
  · have hRej : (step s (.post e)).1 = .rejected := by simp [step, hV]
    rw [hRej] at hOk
    contradiction

theorem req_trial_balance : TrialBalance step := by
  intro s c hWF hOk
  obtain ⟨hAccN, hIdsN, hRevSub, hEntWF⟩ := hWF
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hStep1 : (step s (.post e)).1 = .ok := by simp [step, hV]
      have hStep2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        simp [step, hV]
      have hAccEq : (step s (.post e)).2.accounts = s.accounts := by rw [hStep2]
      have hBal : ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by
        intro a; rw [hStep2]
      have hSum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
        trial_sumNet3 e.lines s.accounts hV.2.1 hAccN
      have hZero : lineSum e.lines = 0 := hV.2.2.2.1
      unfold total
      rw [hAccEq]
      have hcongr : sumOver s.accounts (step s (.post e)).2.balance = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
        apply sumOver_congr
        intro a _
        exact hBal a
      rw [hcongr, sumOver_add, hSum, hZero, Int.add_zero]
    · have hRej : (step s (.post e)).1 = .rejected := by simp [step, hV]
      rw [hRej] at hOk
      contradiction
  | reverse i =>
    cases hEq : findEntry s.journal i with
    | none =>
      have hRej : (step s (.reverse i)).1 = .rejected := by simp [step, hEq]
      rw [hRej] at hOk
      contradiction
    | some e =>
      by_cases hIn : i ∈ s.reversed
      · have hRej : (step s (.reverse i)).1 = .rejected := by simp [step, hEq, hIn]
        rw [hRej] at hOk
        contradiction
      · have hStep2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
          simp [step, hEq, hIn]
        have hAccEq : (step s (.reverse i)).2.accounts = s.accounts := by rw [hStep2]
        have hBal : ∀ a, (step s (.reverse i)).2.balance a = s.balance a - netOf e.lines a := by
          intro a; rw [hStep2]
        have hMem : e ∈ s.journal := trial_find_mem4 s.journal i e hEq
        have hEWF := hEntWF e hMem
        obtain ⟨hMemAcc, hBalZero⟩ := hEWF
        have hSum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
          trial_sumNet3 e.lines s.accounts hMemAcc hAccN
        unfold total
        rw [hAccEq]
        have hcongr : sumOver s.accounts (step s (.reverse i)).2.balance = sumOver s.accounts (fun a => s.balance a - netOf e.lines a) := by
          apply sumOver_congr
          intro a _
          exact hBal a
        rw [hcongr, sumOver_sub, hSum, hBalZero, Int.sub_zero]

theorem req_well_formed : StaysWellFormed step := by
  intro s c hWF
  obtain ⟨hAccN, hIdsN, hRevSub, hEntWF⟩ := hWF
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hStep2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        simp [step, hV]
      rw [hStep2]
      show WellFormed _
      unfold WellFormed
      simp only
      refine ⟨hAccN, ?_, ?_, ?_⟩
      · have hidseq : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := by simp [ids]
        rw [hidseq]
        exact nodup_append_singleton_aux2 (ids s.journal) e.id hIdsN hV.2.2.2.2.1
      · intro i hi
        have hOld := hRevSub i hi
        simp only [ids, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
        exact Or.inl hOld
      · intro e' he'
        rw [List.mem_append] at he'
        cases he' with
        | inl hMem =>
          exact hEntWF e' hMem
        | inr hSing =>
          simp at hSing
          subst hSing
          exact ⟨hV.2.1, hV.2.2.2.1⟩
    · have hStep2 : (step s (.post e)).2 = s := by simp [step, hV]
      rw [hStep2]
      exact ⟨hAccN, hIdsN, hRevSub, hEntWF⟩
  | reverse i =>
    cases hEq : findEntry s.journal i with
    | none =>
      have hStep2 : (step s (.reverse i)).2 = s := by simp [step, hEq]
      rw [hStep2]
      exact ⟨hAccN, hIdsN, hRevSub, hEntWF⟩
    | some e =>
      by_cases hIn : i ∈ s.reversed
      · have hStep2 : (step s (.reverse i)).2 = s := by simp [step, hEq, hIn]
        rw [hStep2]
        exact ⟨hAccN, hIdsN, hRevSub, hEntWF⟩
      · have hStep2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
          simp [step, hEq, hIn]
        rw [hStep2]
        show WellFormed _
        unfold WellFormed
        simp only
        have hmem : i ∈ ids s.journal := findMem_of_some s.journal i e hEq
        refine ⟨hAccN, hIdsN, ?_, hEntWF⟩
        intro x hx
        simp at hx
        cases hx with
        | inl hEqx =>
          rw [hEqx]; exact hmem
        | inr hMem =>
          exact hRevSub x hMem

theorem req_consistent : StaysConsistent step := by
  intro s c hWF hCons
  obtain ⟨hAccN, hIdsN, hRevSub, hEntWF⟩ := hWF
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hStep2 : (step s (.post e)).2
          = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        simp [step, hV]
      have hNotR : e.id ∉ s.reversed := hV.2.2.2.2.2
      intro a
      show (step s (.post e)).2.balance a = (step s (.post e)).2.opening a + activeNet (step s (.post e)).2 a
      rw [hStep2]
      simp only
      have hOld : s.balance a = s.opening a + activeNet s a := hCons a
      unfold activeNet at hOld ⊢
      simp only at hOld ⊢
      have hPost : sumOver (s.journal ++ [e]) (fun x => if x.id ∈ s.reversed then (0:Int) else netOf x.lines a)
          = sumOver s.journal (fun x => if x.id ∈ s.reversed then (0:Int) else netOf x.lines a) + netOf e.lines a :=
        activeNet_post_eq s.journal e s.reversed a hNotR
      omega
    · have hStep2 : (step s (.post e)).2 = s := by simp [step, hV]
      rw [hStep2]
      exact hCons
  | reverse i =>
    cases hEq : findEntry s.journal i with
    | none =>
      have hStep2 : (step s (.reverse i)).2 = s := by simp [step, hEq]
      rw [hStep2]
      exact hCons
    | some e =>
      by_cases hIn : i ∈ s.reversed
      · have hStep2 : (step s (.reverse i)).2 = s := by simp [step, hEq, hIn]
        rw [hStep2]
        exact hCons
      · have hStep2 : (step s (.reverse i)).2
            = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
          simp [step, hEq, hIn]
        intro a
        show (step s (.reverse i)).2.balance a = (step s (.reverse i)).2.opening a + activeNet (step s (.reverse i)).2 a
        rw [hStep2]
        simp only
        have hOld : s.balance a = s.opening a + activeNet s a := hCons a
        unfold activeNet at hOld ⊢
        simp only at hOld ⊢
        have hRev : sumOver s.journal (fun x => if x.id ∈ (i :: s.reversed) then (0:Int) else netOf x.lines a)
            = sumOver s.journal (fun x => if x.id ∈ s.reversed then (0:Int) else netOf x.lines a) - netOf e.lines a :=
          activeNet_reverse_eq_aux2 s.journal s.reversed i e a hEq hIn hIdsN
        omega

end Reversal
