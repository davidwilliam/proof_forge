import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance
instance instDecidableValidReverse (s : State) (i : EntryId) : Decidable (ValidReverse s i) := by
  unfold ValidReverse; infer_instance
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b
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

private theorem findEntry_some_of_ids_mem2 : ∀ (j : List Entry) (i : EntryId), i ∈ ids j → ∃ e, findEntry j i = some e
  | [], _, h => by simp [ids] at h
  | e :: es, i, h => by
    have h' : i = e.id ∨ i ∈ ids es := by simpa [ids] using h
    by_cases he : e.id = i
    · exact ⟨e, by simp [findEntry, he]⟩
    · have hmem : i ∈ ids es := by
        rcases h' with rfl | hh
        · exact absurd rfl (fun h => he h.symm)
        · exact hh
      have hf : findEntry (e :: es) i = findEntry es i := by simp [findEntry, he]
      rw [hf]
      exact findEntry_some_of_ids_mem2 es i hmem

theorem postLines_correct_aux2 : ∀ (ls : List Line) (bal : AccountId → Int) (a : AccountId),
    postLines ls bal a = bal a + netOf ls a := by
  intro ls
  induction ls with
  | nil => intro bal a; simp [postLines, netOf, sumOver]
  | cons hd ls ih =>
    intro bal a
    simp only [postLines]
    have ih2 := ih (adjust bal hd.1 hd.2) a
    rw [ih2]
    have h1 : netOf (hd :: ls) a = (if hd.1 = a then hd.2 else 0) + netOf ls a := by simp [netOf]
    rw [h1]
    unfold adjust
    by_cases ha : a = hd.1
    · rw [if_pos ha]
      have ha2 : hd.1 = a := ha.symm
      rw [if_pos ha2]
      omega
    · rw [if_neg ha]
      have ha2 : ¬ hd.1 = a := fun h => ha h.symm
      rw [if_neg ha2]
      omega

theorem netOf_map_neg2 : ∀ (ls : List Line) (a : AccountId), netOf (ls.map (fun l => (l.1, -l.2))) a = - netOf ls a := by
  intro ls a
  unfold netOf
  induction ls with
  | nil => simp
  | cons hd tl ih =>
    simp [ih]
    by_cases h : hd.1 = a <;> simp [h] <;> omega

theorem findEntry_append_notmem_aux (j : List Entry) (e : Entry) (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have hhd : hd.id ≠ e.id := by intro heq; apply h; simp [ids, heq]
    simp [findEntry, hhd]
    apply ih
    intro hm
    apply h
    have : e.id ∈ hd.id :: ids tl := List.Mem.tail _ hm
    simpa [ids] using this

theorem sumOver_zero (accs : List AccountId) : sumOver accs (fun _ => (0 : Int)) = 0 := by
  induction accs with
  | nil => rfl
  | cons hd tl ih => simp only [sumOver_cons, ih, Int.add_zero]

theorem sum_netOf_eq_lineSum_of_mem2 (accs : List AccountId) (hNodup : accs.Nodup) (ls : List Line) (hMem : ∀ l ∈ ls, l.1 ∈ accs) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  unfold netOf lineSum
  induction ls with
  | nil => exact sumOver_zero accs
  | cons hd tl ih =>
    have hHdMem : hd.1 ∈ accs := hMem hd (by simp)
    have hTlMem : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hMem l (List.mem_cons_of_mem _ hl)
    have h1b : ∀ a, sumOver (hd :: tl) (fun l => if l.1 = a then l.2 else 0) = (if hd.1 = a then hd.2 else 0) + sumOver tl (fun l => if l.1 = a then l.2 else 0) := by intro a; rfl
    have hLHS : sumOver accs (fun a => (if hd.1 = a then hd.2 else 0) + sumOver tl (fun l => if l.1 = a then l.2 else 0)) =
        sumOver accs (fun a => if hd.1 = a then hd.2 else 0) + sumOver accs (fun a => sumOver tl (fun l => if l.1 = a then l.2 else 0)) := by
      have h1 : (fun a : AccountId => (if hd.1 = a then hd.2 else 0) + sumOver tl (fun l => if l.1 = a then l.2 else 0)) = (fun a => (fun a => if hd.1 = a then hd.2 else 0) a + (fun a => sumOver tl (fun l => if l.1 = a then l.2 else 0)) a) := rfl
      rw [h1, ← sumOver_add]
    have hFlip : sumOver accs (fun a => if hd.1 = a then hd.2 else 0) = hd.2 := by
      have hEq : sumOver accs (fun a => if hd.1 = a then hd.2 else 0) = sumOver accs (fun a => if a = hd.1 then hd.2 else 0) := by
        apply sumOver_congr
        intro a _
        by_cases ha : a = hd.1
        · have hb : hd.1 = a := ha.symm
          rw [if_pos hb, if_pos ha]
        · have hb : ¬ hd.1 = a := fun h => ha h.symm
          rw [if_neg hb, if_neg ha]
      rw [hEq, sumOver_ite_eq hNodup hd.1 hd.2, if_pos hHdMem]
    calc sumOver accs (fun a => sumOver (hd :: tl) (fun l => if l.1 = a then l.2 else 0))
        = sumOver accs (fun a => (if hd.1 = a then hd.2 else 0) + sumOver tl (fun l => if l.1 = a then l.2 else 0)) := by
            apply sumOver_congr; intro a _; exact h1b a
      _ = sumOver accs (fun a => if hd.1 = a then hd.2 else 0) + sumOver accs (fun a => sumOver tl (fun l => if l.1 = a then l.2 else 0)) := hLHS
      _ = sumOver accs (fun a => if hd.1 = a then hd.2 else 0) + sumOver tl (fun x => x.2) := by rw [ih hTlMem]
      _ = hd.2 + sumOver tl (fun x => x.2) := by rw [hFlip]
      _ = sumOver (hd :: tl) (fun x => x.2) := rfl

private theorem findEntry_mem {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp [findEntry] at h
    by_cases he : hd.id = i
    · simp [he] at h
      subst h
      simp
    · simp [he] at h
      exact List.Mem.tail _ (ih h)

private theorem activeNet_post_eq (j : List Entry) (rev : List EntryId) (e : Entry) (a : AccountId) (hrev : e.id ∉ rev) :
    sumOver (j ++ [e]) (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) =
    sumOver j (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) + netOf e.lines a := by
  rw [sumOver_append]
  simp [hrev]

private theorem activeNet_reverse_aux : ∀ (j : List Entry) (rev : List EntryId) (i : EntryId) (e : Entry) (a : AccountId),
    (ids j).Nodup → i ∉ rev → findEntry j i = some e →
    sumOver j (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a) =
    sumOver j (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  intro j
  induction j with
  | nil => intro rev i e a _ _ h; simp [findEntry] at h
  | cons hd tl ih =>
    intro rev i e a hNodup hNotRev hFind
    have hNodupTail : (ids tl).Nodup := by
      have h : ids (hd :: tl) = hd.id :: ids tl := by simp [ids]
      rw [h] at hNodup
      exact (List.nodup_cons.mp hNodup).2
    have hNotInTail_hd : ¬hd.id ∈ ids tl := by
      have h : ids (hd :: tl) = hd.id :: ids tl := by simp [ids]
      rw [h] at hNodup
      exact (List.nodup_cons.mp hNodup).1
    simp [findEntry] at hFind
    by_cases heq : hd.id = i
    · simp [heq] at hFind
      subst hFind
      have hTailEq : sumOver tl (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a) =
          sumOver tl (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) := by
        apply sumOver_congr
        intro x hx
        have hxid : x.id ≠ i := by
          intro hEq
          have h1 : x.id ∈ ids tl := by
            -- x ∈ tl implies x.id ∈ map id
            have : x.id ∈ tl.map (fun e => e.id) := List.mem_map.mpr ⟨x, hx, rfl⟩
            simpa [ids] using this
          have h2 : i ∈ ids tl := hEq ▸ h1
          have h3 : hd.id ∈ ids tl := heq ▸ h2
          exact hNotInTail_hd h3
        simp [hxid]
      have hHeadOld : (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) = netOf hd.lines a := by simp [hNotRev, heq]
      have hHeadNew : (if hd.id ∈ i :: rev then (0 : Int) else netOf hd.lines a) = (0 : Int) := by simp [heq]
      simp only [sumOver_cons]
      rw [hHeadNew, hHeadOld, hTailEq]
      omega
    · simp [heq] at hFind
      have hHeadEq : (if hd.id ∈ i :: rev then (0 : Int) else netOf hd.lines a) = (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) := by
        simp [heq]
      simp only [sumOver_cons]
      rw [hHeadEq]
      have hIH := ih rev i e a hNodupTail hNotRev hFind
      omega

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  unfold step
  simp [h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  unfold step
  have hVR : ValidReverse s i := h
  simp only [hVR]
  obtain ⟨e, he⟩ := findEntry_some_of_ids_mem2 s.journal i h.1
  simp [he]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    have hVP : ¬ ValidPost s e := by
      intro hvp
      apply h
      exact hvp
    unfold step
    simp [hVP]
  | reverse i =>
    have hVR : ¬ ValidReverse s i := by
      intro hvr
      apply h
      exact hvr
    unfold step
    simp [hVR]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  have hVP : ValidPost s e := by
    by_cases h : ValidPost s e
    · exact h
    · have hs : (step s (Command.post e)).1 = Outcome.rejected := by unfold step; simp [h]
      rw [hs] at hok; contradiction
  have hStepEq : step s (Command.post e) = (Outcome.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by unfold step; simp [hVP]
  have h2eq : (step s (Command.post e)).2 = { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } := by rw [hStepEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h2eq]
  · rw [h2eq]
  · rw [h2eq]
  · rw [h2eq]
  · intro a; rw [h2eq]; simp; exact postLines_correct_aux2 e.lines s.balance a

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hFind
  have hVR : ValidReverse s i := by
    by_cases h : ValidReverse s i
    · exact h
    · have hs : (step s (Command.reverse i)).1 = .rejected := by unfold step; simp [h]
      rw [hs] at hok; contradiction
  have hStepEq : step s (Command.reverse i) = (Outcome.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed }) := by
    unfold step; simp [hVR, hFind]
  have h2eq : (step s (Command.reverse i)).2 = { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed } := by rw [hStepEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h2eq]
  · rw [h2eq]
  · rw [h2eq]
  · intro x; rw [h2eq]; simp
  · intro a; rw [h2eq]; simp
    have hcorr := postLines_correct_aux2 (e.lines.map (fun l => (l.1, -l.2))) s.balance a
    rw [hcorr, netOf_map_neg2]; omega

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  have hVR : ValidReverse s i := by
    by_cases h : ValidReverse s i
    · exact h
    · have hs : (step s (Command.reverse i)).1 = .rejected := by unfold step; simp [h]
      rw [hs] at hok; contradiction
  obtain ⟨e, he⟩ := findEntry_some_of_ids_mem2 s.journal i hVR.1
  have hStepEq : step s (Command.reverse i) = (Outcome.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed }) := by
    unfold step; simp [hVR, he]
  have h2eq : (step s (Command.reverse i)).2 = { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed } := by rw [hStepEq]
  let s1 : State := { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed }
  have hs1eq : (step s (Command.reverse i)).2 = s1 := h2eq
  have hNotValid_s1 : ¬ ValidReverse s1 i := by
    unfold ValidReverse; simp [s1]
  have hStep_s1 : step s1 (Command.reverse i) = (.rejected, s1) := by
    unfold step; simp [hNotValid_s1]
  rw [hs1eq]
  exact hStep_s1

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hVP : ValidPost s e := by
    by_cases h : ValidPost s e
    · exact h
    · have hs : (step s (Command.post e)).1 = Outcome.rejected := by unfold step; simp [h]
      rw [hs] at hok; contradiction
  have h_not_ids : e.id ∉ ids s.journal := hVP.2.2.2.2.1
  have hStepEq : step s (Command.post e) = (Outcome.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by unfold step; simp [hVP]
  have h2eq : (step s (Command.post e)).2 = { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } := by rw [hStepEq]
  let s1 : State := { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }
  have hs1eq : (step s (Command.post e)).2 = s1 := h2eq
  have h_not_rev : e.id ∉ s1.reversed := by simp [s1, hVP.2.2.2.2.2]
  have h_ids_mem : e.id ∈ ids s1.journal := by simp [s1, ids]
  have hVR_s1 : ValidReverse s1 e.id := ⟨h_ids_mem, h_not_rev⟩
  have hFind : findEntry s1.journal e.id = some e := by
    show findEntry (s.journal ++ [e]) e.id = some e
    exact findEntry_append_notmem_aux s.journal e h_not_ids
  have hStepRev : step s1 (Command.reverse e.id) = (Outcome.ok, { s1 with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s1.balance, reversed := e.id :: s1.reversed }) := by
    unfold step; simp [hVR_s1, hFind]
  constructor
  · calc (step (step s (Command.post e)).2 (Command.reverse e.id)).1
        = (step s1 (Command.reverse e.id)).1 := by rw [hs1eq]
      _ = Outcome.ok := by rw [hStepRev]
  · have hBal_s1 : ∀ a, s1.balance a = s.balance a + netOf e.lines a := by
      intro a; simp [s1]; exact postLines_correct_aux2 e.lines s.balance a
    have hcorr : ∀ a, postLines (e.lines.map (fun l => (l.1, -l.2))) s1.balance a = s1.balance a - netOf e.lines a := by
      intro a
      have h1 := postLines_correct_aux2 (e.lines.map (fun l => (l.1, -l.2))) s1.balance a
      rw [h1, netOf_map_neg2]
      omega
    have hFinal : (step s1 (Command.reverse e.id)).2.balance = s.balance := by
      funext a
      have h2 : (step s1 (Command.reverse e.id)).2.balance a = s1.balance a - netOf e.lines a := by
        have : (step s1 (Command.reverse e.id)).2 = { s1 with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s1.balance, reversed := e.id :: s1.reversed } := by rw [hStepRev]
        simp [this, hcorr]
      rw [h2, hBal_s1]
      omega
    calc (step (step s (Command.post e)).2 (Command.reverse e.id)).2.balance
        = (step s1 (Command.reverse e.id)).2.balance := by rw [hs1eq]
      _ = s.balance := hFinal

theorem req_trial_balance    : TrialBalance step := by
  intro s c hWF hOk
  obtain ⟨hAcNodup, _hIdsNodup, _hRevSub, hBalanced⟩ := hWF
  cases c with
  | post e =>
    unfold step at hOk
    by_cases hVP : ValidPost s e
    · simp [hVP] at hOk
      have hStepEq : step s (Command.post e) = (Outcome.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by unfold step; simp [hVP]
      have h2eq : (step s (Command.post e)).2 = { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } := by rw [hStepEq]
      rw [h2eq]
      unfold total
      have hBalEq : ∀ a, (postLines e.lines s.balance) a = s.balance a + netOf e.lines a := fun a => postLines_correct_aux2 e.lines s.balance a
      have hSumEq : sumOver s.accounts (postLines e.lines s.balance) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := by
        have hcongr : sumOver s.accounts (postLines e.lines s.balance) = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) :=
          sumOver_congr s.accounts _ _ (fun a _ => hBalEq a)
        rw [hcongr, sumOver_add]
      rw [hSumEq]
      have hMem : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hVP.2.1
      have hSumZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
        rw [sum_netOf_eq_lineSum_of_mem2 s.accounts hAcNodup e.lines hMem]
        exact hVP.2.2.2.1
      omega
    · simp [hVP] at hOk
  | reverse i =>
    unfold step at hOk
    by_cases hVR : ValidReverse s i
    · obtain ⟨e, he⟩ := findEntry_some_of_ids_mem2 s.journal i hVR.1
      have hStepEq : step s (Command.reverse i) = (Outcome.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed }) := by unfold step; simp [hVR, he]
      have h2eq : (step s (Command.reverse i)).2 = { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed } := by rw [hStepEq]
      have heMem : e ∈ s.journal := findEntry_mem he
      have hBalE := hBalanced e heMem
      have hLineZero : lineSum e.lines = 0 := hBalE.2
      have hMemE : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hBalE.1
      rw [h2eq]
      unfold total
      have hBalEq : ∀ a, postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance a = s.balance a - netOf e.lines a := by
        intro a
        have h1 := postLines_correct_aux2 (e.lines.map (fun l => (l.1, -l.2))) s.balance a
        rw [h1, netOf_map_neg2]; omega
      have hSumEq : sumOver s.accounts (postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance) =
          sumOver s.accounts s.balance - sumOver s.accounts (fun a => netOf e.lines a) := by
        have hcongr : sumOver s.accounts (postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance) =
            sumOver s.accounts (fun a => s.balance a - netOf e.lines a) :=
          sumOver_congr s.accounts _ _ (fun a _ => hBalEq a)
        rw [hcongr, sumOver_sub]
      rw [hSumEq]
      have hSumZero : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
        rw [sum_netOf_eq_lineSum_of_mem2 s.accounts hAcNodup e.lines hMemE, hLineZero]
      omega
    · simp [hVR] at hOk

theorem req_well_formed : StaysWellFormed step := by
  intro s c hWF
  obtain ⟨hAcNodup, hIdsNodup, hRevSub, hBalanced⟩ := hWF
  cases c with
  | post e =>
    unfold step
    by_cases hVP : ValidPost s e
    · simp only [hVP, ↓reduceIte]
      refine ⟨hAcNodup, ?_, ?_, ?_⟩
      · show (ids (s.journal ++ [e])).Nodup
        have h : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := by simp [ids]
        rw [h]
        rw [List.nodup_append]
        refine ⟨hIdsNodup, by simp, ?_⟩
        simp
        intro a ha heq
        rw [heq] at ha
        exact hVP.2.2.2.2.1 ha
      · intro i hi
        have hm : i ∈ ids s.journal := hRevSub i hi
        show i ∈ ids (s.journal ++ [e])
        simp [ids]
        simp [ids] at hm
        simp [hm]
      · intro e' he'
        rw [List.mem_append] at he'
        rcases he' with hmem | hmem
        · exact hBalanced e' hmem
        · simp at hmem
          subst hmem
          exact ⟨hVP.2.1, hVP.2.2.2.1⟩
    · simp only [hVP, ↓reduceIte]
      exact ⟨hAcNodup, hIdsNodup, hRevSub, hBalanced⟩
  | reverse i =>
    unfold step
    by_cases hVR : ValidReverse s i
    · obtain ⟨e, he⟩ := findEntry_some_of_ids_mem2 s.journal i hVR.1
      simp only [hVR, he, ↓reduceIte]
      refine ⟨hAcNodup, hIdsNodup, ?_, hBalanced⟩
      intro j hj
      simp at hj
      rcases hj with rfl | hmem
      · exact hVR.1
      · exact hRevSub j hmem
    · simp only [hVR, ↓reduceIte]
      exact ⟨hAcNodup, hIdsNodup, hRevSub, hBalanced⟩

theorem req_consistent       : StaysConsistent step := by
  intro s c hWF hCons
  cases c with
  | post e =>
    unfold step
    by_cases hVP : ValidPost s e
    · simp only [hVP, ↓reduceIte]
      intro a
      have hBal : (postLines e.lines s.balance) a = s.balance a + netOf e.lines a := postLines_correct_aux2 e.lines s.balance a
      have hConsA := hCons a
      simp only [hBal]
      rw [hConsA]
      have hActive : activeNet { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } a =
          activeNet s a + netOf e.lines a := by
        unfold activeNet
        have h1 : (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a) = (fun e' : Entry => if e'.id ∈ ({ s with journal := s.journal ++ [e] } : State).reversed then 0 else netOf e'.lines a) := rfl
        rw [← h1]
        exact activeNet_post_eq s.journal s.reversed e a hVP.2.2.2.2.2
      omega
    · simp only [hVP, ↓reduceIte]
      exact hCons
  | reverse i =>
    unfold step
    by_cases hVR : ValidReverse s i
    · obtain ⟨e, he⟩ := findEntry_some_of_ids_mem2 s.journal i hVR.1
      simp only [hVR, he, ↓reduceIte]
      intro a
      have hBal : postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance a = s.balance a - netOf e.lines a := by
        have h1 := postLines_correct_aux2 (e.lines.map (fun l => (l.1, -l.2))) s.balance a
        rw [h1, netOf_map_neg2]; omega
      have hConsA := hCons a
      simp only [hBal]
      rw [hConsA]
      have hActiveRev : activeNet { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := i :: s.reversed } a =
          activeNet s a - netOf e.lines a := by
        change sumOver s.journal (fun e' => if e'.id ∈ i :: s.reversed then (0 : Int) else netOf e'.lines a) =
          sumOver s.journal (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a) - netOf e.lines a
        exact activeNet_reverse_aux s.journal s.reversed i e a hWF.2.1 hVR.2 he
      omega
    · simp only [hVR, ↓reduceIte]
      exact hCons

end Reversal
