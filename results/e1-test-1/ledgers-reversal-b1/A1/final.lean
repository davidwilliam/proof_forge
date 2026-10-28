import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance
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
    match findEntry s.journal i with
    | some e =>
      if i ∈ s.reversed then (.rejected, s)
      else (.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                          reversed := i :: s.reversed })
    | none => (.rejected, s)

theorem findEntry_some_of_mem_ids_aux : ∀ (j : List Entry) (i : EntryId), i ∈ ids j → ∃ e, findEntry j i = some e := by
  intro j
  induction j with
  | nil => intro i h; simp [ids] at h
  | cons e es ih =>
    intro i h
    have h2 : i = e.id ∨ i ∈ ids es := by simpa [ids] using h
    unfold findEntry
    by_cases he : e.id = i
    · simp [he]
    · have hne : ¬ (i = e.id) := fun hh => he hh.symm
      simp [he, hne] at h2 ⊢
      exact ih i h2

theorem ids_cons_test (hd : Entry) (tl : List Entry) : ids (hd :: tl) = hd.id :: ids tl := rfl

theorem ids_mem_cons_test (hd : Entry) (tl : List Entry) (i : EntryId) : (i ∈ ids (hd :: tl)) = (i = hd.id ∨ i ∈ ids tl) := by simp [ids]

theorem findEntry_none_of_not_mem_aux (j : List Entry) (i : EntryId) (h : i ∉ ids j) : findEntry j i = none := by
  induction j with
  | nil => rfl
  | cons hd tl ih =>
    have hcons : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hcons] at h
    simp at h
    obtain ⟨hne1, hnetl⟩ := h
    have hne : ¬ (hd.id = i) := fun heq => hne1 heq.symm
    show (if hd.id = i then (some hd : Option Entry) else findEntry tl i) = none
    rw [if_neg hne]
    exact ih hnetl

theorem adjust_eq_test4 (bal : AccountId → Int) (x a : AccountId) (amt : Int) :
    adjust bal x amt a = bal a + (if x = a then amt else 0) := by
  unfold adjust
  by_cases h1 : a = x
  · subst h1
    rw [if_pos rfl, if_pos rfl]
  · have h2 : ¬ (x = a) := fun h => h1 h.symm
    rw [if_neg h1, if_neg h2]
    omega

theorem postLines_bal (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    postLines ls bal a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil =>
    have hn : netOf ([] : List Line) a = 0 := rfl
    have hp : postLines ([] : List Line) bal = bal := rfl
    rw [hp, hn]
    omega
  | cons l ls ih =>
    have h1 : postLines (l :: ls) bal a = postLines ls (adjust bal l.1 l.2) a := rfl
    rw [h1, ih]
    have hnet : netOf (l :: ls) a = (if l.1 = a then l.2 else 0) + netOf ls a := rfl
    have hadj : adjust bal l.1 l.2 a = bal a + (if l.1 = a then l.2 else 0) := adjust_eq_test4 bal l.1 a l.2
    rw [hadj, hnet]
    omega

theorem sumOver_map_aux2 {α β : Type} (ls : List α) (f : α → β) (g : β → Int) :
    sumOver (ls.map f) g = sumOver ls (fun x => g (f x)) := by
  induction ls with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem netOf_map_neg_aux4 (ls : List Line) (a : AccountId) :
    netOf (ls.map (fun l => (l.1, -l.2))) a = - netOf ls a := by
  rw [netOf, netOf, sumOver_map_aux2]
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [sumOver_cons] at ih ⊢
    by_cases h : l.1 = a
    · simp [h]; omega
    · simp [h, ih]

theorem postLines_neg_aux5 (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    postLines (ls.map (fun l => (l.1, -l.2))) bal a = bal a - netOf ls a := by
  rw [postLines_bal, netOf_map_neg_aux4]
  omega

theorem helper_rev_once_test1 (s : State) (i : EntryId) (e : Entry)
    (hfe : findEntry s.journal i = some e) (hrev : i ∉ s.reversed) :
    (step s (.reverse i)).2.journal = s.journal := by
  have hs : step s (.reverse i) =
      (.ok, ({ s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                      reversed := i :: s.reversed } : State)) := by simp [step, hfe, hrev]
  have hS : (step s (.reverse i)).2 =
      (({ s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                      reversed := i :: s.reversed } : State)) := congrArg Prod.snd hs
  rw [hS]

theorem helper_reject_test2 (s' : State) (i : EntryId) (e : Entry)
    (hf : findEntry s'.journal i = some e) (hm : i ∈ s'.reversed) :
    step s' (.reverse i) = (.rejected, s') := by
  simp [step, hf, hm]

theorem helper_rev_once_test3 (s : State) (i : EntryId) (e : Entry)
    (hfe : findEntry s.journal i = some e) (hrev : i ∉ s.reversed) :
    i ∈ (step s (.reverse i)).2.reversed := by
  have hs : step s (.reverse i) =
      (.ok, ({ s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                      reversed := i :: s.reversed } : State)) := by simp [step, hfe, hrev]
  have hS : (step s (.reverse i)).2 =
      ((({ s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                      reversed := i :: s.reversed } : State))) := congrArg Prod.snd hs
  rw [hS]
  exact List.mem_cons.mpr (Or.inl rfl)

theorem helper_rev_once_test4 (s : State) (i : EntryId) (e : Entry)
    (hfe : findEntry s.journal i = some e) (hrev : i ∉ s.reversed) :
    findEntry (step s (.reverse i)).2.journal i = some e ∧ i ∈ (step s (.reverse i)).2.reversed := by
  have hS : (step s (.reverse i)).2 =
      ({ s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                      reversed := (i :: s.reversed) } : State) := by
    have hs : step s (.reverse i) =
        (.ok, ({ s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                        reversed := (i :: s.reversed) } : State)) := by simp [step, hfe, hrev]
    exact congrArg Prod.snd hs
  constructor
  · rw [hS]; exact hfe
  · rw [hS]; exact List.mem_cons.mpr (Or.inl rfl)

theorem helper_rev_once_test5 (s : State) (i : EntryId)
    (hok : (step s (.reverse i)).1 = .ok) :
    step (step s (.reverse i)).2 (.reverse i) = (.rejected, (step s (.reverse i)).2) := by
  cases hfe : findEntry s.journal i with
  | none =>
    have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe]
    rw [hs] at hok
    simp at hok
  | some e =>
    by_cases hrev : i ∈ s.reversed
    · have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe, hrev]
      rw [hs] at hok
      simp at hok
    · obtain ⟨hfind2, hmem2⟩ := helper_rev_once_test4 s i e hfe hrev
      exact helper_reject_test2 _ i e hfind2 hmem2

theorem req_reverse_once_proved_aux : ReverseOnce step :=
  fun s i hok => helper_rev_once_test5 s i hok

theorem rt_post_valid (s : State) (e : Entry)
    (hok : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases h : ValidPost s e
  · exact h
  · have hs : step s (.post e) = (.rejected, s) := by simp [step, h]
    rw [hs] at hok
    simp at hok

theorem rt_find_append (j : List Entry) (e : Entry)
    (hni : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil =>
    simp [findEntry]
  | cons hd tl ih =>
    have hcons : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hcons] at hni
    simp at hni
    obtain ⟨hne1, hnetl⟩ := hni
    have hne : ¬ (hd.id = e.id) := fun heq => hne1 heq.symm
    have happ : (hd :: tl) ++ [e] = hd :: (tl ++ [e]) := rfl
    rw [happ]
    show (if hd.id = e.id then (some hd : Option Entry) else findEntry (tl ++ [e]) e.id) = some e
    rw [if_neg hne]
    exact ih hnetl

theorem rt_ids_append (j : List Entry) (e : Entry) : ids (j ++ [e]) = ids j ++ [e.id] := by simp [ids]

theorem rt_mem_append (j : List Entry) (e : Entry) : e.id ∈ ids (j ++ [e]) := by
  rw [rt_ids_append]
  exact List.mem_append.mpr (Or.inr (by simp))

theorem findEntry_mem_tb3 (j : List Entry) (i : EntryId) (e : Entry)
    (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h
      rw [h]
      exact List.mem_cons.mpr (Or.inl rfl)
    · simp [heq] at h
      have hm := ih h
      exact List.mem_cons.mpr (Or.inr hm)

theorem sumOver_zero_tb3 (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [sumOver_cons] at ih ⊢; omega

theorem sumNet_eq_lineSum_tb3 (acc : List AccountId) (ls : List Line)
    (hNodup : acc.Nodup) (hMem : ∀ l ∈ ls, l.1 ∈ acc) :
    sumOver acc (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have h0 : (fun a : AccountId => netOf ([] : List Line) a) = (fun _ => (0 : Int)) := by rfl
    rw [h0]
    exact sumOver_zero_tb3 acc
  | cons hd tl ih =>
    have hMemTl : ∀ l ∈ tl, l.1 ∈ acc := fun l hl => hMem l (List.mem_cons.mpr (Or.inr hl))
    have ih' := ih hMemTl
    have hHeadMem : hd.1 ∈ acc := hMem hd (by simp)
    have hNetCons : ∀ a : AccountId, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      intro a; rfl
    have hEq : (fun a : AccountId => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else (0:Int)) + netOf tl a) := by
      funext a; exact hNetCons a
    rw [hEq]
    rw [sumOver_add]
    have hIf : sumOver acc (fun a => (if hd.1 = a then hd.2 else (0:Int))) = hd.2 := by
      have hCong : sumOver acc (fun a => (if hd.1 = a then hd.2 else (0:Int))) =
          sumOver acc (fun a => (if a = hd.1 then hd.2 else (0:Int))) := by
        apply sumOver_congr
        intro a _ha
        by_cases h : a = hd.1
        · subst h; simp
        · have h2 : ¬ (hd.1 = a) := fun hh => h hh.symm
          simp [h, h2]
      rw [hCong, sumOver_ite_eq hNodup hd.1 hd.2]
      simp [hHeadMem]
    rw [hIf, ih']
    rfl

theorem findEntry_some_mem_ids_test3 (j : List Entry) (i : EntryId) (e : Entry)
    (h : findEntry j i = some e) : i ∈ ids j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    have hcons : ids (hd :: tl) = hd.id :: ids tl := rfl
    have hfe : (if hd.id = i then (some hd : Option Entry) else findEntry tl i) = some e := h
    by_cases heq : hd.id = i
    · rw [hcons, heq]
      exact List.mem_cons.mpr (Or.inl rfl)
    · rw [if_neg heq] at hfe
      have hm := ih hfe
      rw [hcons]
      exact List.mem_cons.mpr (Or.inr hm)

theorem nodup_append_singleton_aux2 (l : List Nat) (x : Nat)
    (hN : l.Nodup) (hni : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.nodup_cons] at hN
    obtain ⟨hhd, htl⟩ := hN
    simp at hni
    obtain ⟨hne1, hni2⟩ := hni
    have hne1' : hd ≠ x := fun heq => hne1 heq.symm
    have ih' := ih htl hni2
    have hmem : hd ∉ tl ++ [x] := by
      rw [List.mem_append]
      simp [hhd, hne1']
    have hcons : (hd :: tl) ++ [x] = hd :: (tl ++ [x]) := rfl
    rw [hcons]
    rw [List.nodup_cons]
    exact ⟨hmem, ih'⟩

theorem nodup_ids_append_aux2 (j : List Entry) (e : Entry)
    (hN : (ids j).Nodup) (hni : e.id ∉ ids j) : (ids (j ++ [e])).Nodup := by
  rw [rt_ids_append]
  exact nodup_append_singleton_aux2 (ids j) e.id hN hni

theorem mem_ids_append_mono_aux3 (j : List Entry) (e : Entry) (x : EntryId)
    (h : x ∈ ids j) : x ∈ ids (j ++ [e]) := by
  rw [rt_ids_append]
  exact List.mem_append.mpr (Or.inl h)

theorem pos_ok_aux2 (s : State) (e : Entry) (hv : ValidPost s e) :
    (step s (.post e)).1 = .ok := by simp [step, hv]

theorem activePost_eq_auxSC2 (j : List Entry) (e : Entry) (r : List EntryId) (a : AccountId) :
    sumOver (j ++ [e]) (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a) =
    sumOver j (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a) +
    (if e.id ∈ r then (0:Int) else netOf e.lines a) := by
  have h := sumOver_append j [e] (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a)
  rw [h]
  simp

theorem pointwise_rev_auxSC3 (e' : Entry) (i : EntryId) (r : List EntryId) (a : AccountId)
    (hne : e'.id ≠ i) :
    (if e'.id ∈ (i :: r) then (0:Int) else netOf e'.lines a) =
    (if e'.id ∈ r then (0:Int) else netOf e'.lines a) := by
  by_cases hm : e'.id ∈ r
  · have hm2 : e'.id ∈ (i :: r) := List.mem_cons.mpr (Or.inr hm)
    simp [hm, hm2]
  · have hm2 : e'.id ∉ (i :: r) := by
      simp [hm, hne]
    simp [hm, hm2]

theorem mem_ids_of_mem_auxSC4 (tl : List Entry) (e' : Entry) (h : e' ∈ tl) : e'.id ∈ ids tl := by
  unfold ids
  exact List.mem_map.mpr ⟨e', h, rfl⟩

theorem ne_of_nodup_auxSC6 (tl : List Entry) (hd : Entry) (i : EntryId)
    (hhdni : hd.id ∉ ids tl) (heq : hd.id = i) (e' : Entry) (he' : e' ∈ tl) : e'.id ≠ i := by
  intro hcon
  apply hhdni
  have hmem : e'.id ∈ ids tl := mem_ids_of_mem_auxSC4 tl e' he'
  rw [hcon] at hmem
  rw [← heq] at hmem
  exact hmem

theorem tail_eq_of_ne_auxSC7 (tl : List Entry) (r : List EntryId) (i : EntryId) (a : AccountId)
    (h : ∀ e' ∈ tl, e'.id ≠ i) :
    sumOver tl (fun e' => if e'.id ∈ (i :: r) then (0:Int) else netOf e'.lines a) =
    sumOver tl (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a) := by
  apply sumOver_congr
  intro e' he'
  exact pointwise_rev_auxSC3 e' i r a (h e' he')

theorem activeReverse_eq_auxSC7 : ∀ (j : List Entry) (r : List EntryId) (i : EntryId) (e : Entry) (a : AccountId),
    (ids j).Nodup → findEntry j i = some e → i ∉ r →
    sumOver j (fun e' => if e'.id ∈ (i :: r) then (0:Int) else netOf e'.lines a) =
    sumOver j (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a) - netOf e.lines a := by
  intro j
  induction j with
  | nil =>
    intro r i e a _ hfind _
    simp [findEntry] at hfind
  | cons hd tl ih =>
    intro r i e a hNod hfind hnir
    have hcons : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hcons, List.nodup_cons] at hNod
    obtain ⟨hhdni, htlNod⟩ := hNod
    show sumOver (hd :: tl) (fun e' => if e'.id ∈ (i :: r) then (0:Int) else netOf e'.lines a) = _
    rw [sumOver_cons, sumOver_cons]
    simp only [findEntry] at hfind
    by_cases heq : hd.id = i
    · subst heq
      simp at hfind
      subst hfind
      have hhd_notin_r : hd.id ∉ r := hnir
      have hhd_in_cons : hd.id ∈ (hd.id :: r) := List.mem_cons.mpr (Or.inl rfl)
      rw [if_pos hhd_in_cons, if_neg hhd_notin_r]
      have hEqTl : sumOver tl (fun e' => if e'.id ∈ (hd.id :: r) then (0:Int) else netOf e'.lines a) =
          sumOver tl (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a) := by
        apply tail_eq_of_ne_auxSC7
        intro e' he'
        exact ne_of_nodup_auxSC6 tl hd hd.id hhdni rfl e' he'
      rw [hEqTl]
      omega
    · rw [if_neg heq] at hfind
      have ih' := ih r i e a htlNod hfind hnir
      have hpt : (if hd.id ∈ (i :: r) then (0:Int) else netOf hd.lines a) =
          (if hd.id ∈ r then (0:Int) else netOf hd.lines a) :=
        pointwise_rev_auxSC3 hd i r a heq
      rw [hpt, ih']
      omega

theorem diag1 (s : State) (e : Entry) (hv : ValidPost s e) :
    step s (.post e) = (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by
  simp [step, hv]

theorem req_roundtrip_dup : True := trivial

theorem req_well_formed_aux_test : StaysWellFormed step := by
  intro s c hwf
  obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩ := hwf
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hvc := hv
      obtain ⟨hne, hmemAcc, hneZero, hsum0, hnid, hnrev⟩ := hvc
      have hs : step s (.post e) = (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by simp [step, hv]
      have hS2 : (step s (.post e)).2 = ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State) := congrArg Prod.snd hs
      rw [hS2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hNodupAcc
      · have h1 : ids ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State).journal = ids (s.journal ++ [e]) := rfl
        rw [h1, rt_ids_append]
        exact nodup_append_singleton_aux2 (ids s.journal) e.id hNodupIds hnid
      · intro i hi
        have h2 : ids ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State).journal = ids (s.journal ++ [e]) := rfl
        rw [h2]
        exact mem_ids_append_mono_aux3 s.journal e i (hRevSub i hi)
      · intro e' he'
        have hejt : e' ∈ s.journal ++ [e] := he'
        rw [List.mem_append] at hejt
        simp only [List.mem_singleton] at hejt
        cases hejt with
        | inl hmem =>
          have hp := hBal e' hmem
          obtain ⟨haccOld, hsumOld⟩ := hp
          constructor
          · intro l hl
            exact haccOld l hl
          · exact hsumOld
        | inr heq =>
          subst heq
          constructor
          · intro l hl
            exact hmemAcc l hl
          · exact hsum0
    · have hs : step s (.post e) = (.rejected, s) := by simp [step, hv]
      have hS2 : (step s (.post e)).2 = s := by rw [hs]
      rw [hS2]
      exact ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩
  | reverse i =>
    cases hfe : findEntry s.journal i with
    | none =>
      have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe]
      have hS2 : (step s (.reverse i)).2 = s := by rw [hs]
      rw [hS2]
      exact ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩
    | some e =>
      by_cases hrev : i ∈ s.reversed
      · have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe, hrev]
        have hS2 : (step s (.reverse i)).2 = s := by rw [hs]
        rw [hS2]
        exact ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩
      · have hs : step s (.reverse i) =
            (.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                            reversed := i :: s.reversed }) := by simp [step, hfe, hrev]
        have hS2 : (step s (.reverse i)).2 =
            ({ s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                            reversed := i :: s.reversed } : State) := congrArg Prod.snd hs
        rw [hS2]
        have hmemIds : i ∈ ids s.journal := findEntry_some_mem_ids_test3 s.journal i e hfe
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact hNodupAcc
        · exact hNodupIds
        · intro x hx
          simp only [List.mem_cons] at hx
          cases hx with
          | inl heq => subst heq; exact hmemIds
          | inr hmem => exact hRevSub x hmem
        · intro e' he'
          exact hBal e' he'

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  obtain ⟨hmem, hnot⟩ := h
  obtain ⟨e, he⟩ := findEntry_some_of_mem_ids_aux s.journal i hmem
  simp only [step, he, hnot, ite_false]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    have hnp : ¬ ValidPost s e := fun hv => h hv
    simp [step, hnp]
  | reverse i =>
    have hnr : ¬ (i ∈ ids s.journal ∧ i ∉ s.reversed) := fun hv => h hv
    by_cases hmem : i ∈ ids s.journal
    · by_cases hrev : i ∈ s.reversed
      · obtain ⟨e, he⟩ := findEntry_some_of_mem_ids_aux s.journal i hmem
        simp [step, he, hrev]
      · exfalso; exact hnr ⟨hmem, hrev⟩
    · have hnone : findEntry s.journal i = none := findEntry_none_of_not_mem_aux s.journal i hmem
      simp [step, hnone]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  by_cases hv : ValidPost s e
  · have hs : step s (.post e) = (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by simp [step, hv]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have : (step s (.post e)).2.accounts = s.accounts := by rw [hs]
      exact this
    · have : (step s (.post e)).2.opening = s.opening := by rw [hs]
      exact this
    · have : (step s (.post e)).2.journal = s.journal ++ [e] := by rw [hs]
      exact this
    · have : (step s (.post e)).2.reversed = s.reversed := by rw [hs]
      exact this
    · intro a
      have : (step s (.post e)).2.balance a = postLines e.lines s.balance a := by rw [hs]
      rw [this, postLines_bal]
  · have hs : step s (.post e) = (.rejected, s) := by simp [step, hv]
    rw [hs] at hok
    simp at hok

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hfind
  by_cases hrev : i ∈ s.reversed
  · have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfind, hrev]
    rw [hs] at hok
    simp at hok
  · have hs : step s (.reverse i) =
        (.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                        reversed := i :: s.reversed }) := by simp [step, hfind, hrev]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h2 : (step s (.reverse i)).2.accounts = s.accounts := by rw [hs]
      exact h2
    · have h2 : (step s (.reverse i)).2.opening = s.opening := by rw [hs]
      exact h2
    · have h2 : (step s (.reverse i)).2.journal = s.journal := by rw [hs]
      exact h2
    · intro x
      have h2 : (step s (.reverse i)).2.reversed = i :: s.reversed := by rw [hs]
      rw [h2]
      simp
    · intro a
      have hb : (step s (.reverse i)).2.balance a =
          postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance a := by rw [hs]
      rw [hb, postLines_neg_aux5]

theorem req_reverse_once : ReverseOnce step := req_reverse_once_proved_aux

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hv0 : ValidPost s e := rt_post_valid s e hok
  have hDiag := diag1 s e hv0
  have hS2 : (step s (.post e)).2 = (({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State)) := congrArg Prod.snd hDiag
  have hmem2pre : e.id ∈ ids ((step s (.post e)).2).journal := by
    rw [hS2]
    exact rt_mem_append s.journal e
  have hnotrev2 : e.id ∉ ((step s (.post e)).2).reversed := by
    rw [hS2]
    exact hv0.2.2.2.2.2
  have hfind2 : findEntry ((step s (.post e)).2).journal e.id = some e := by
    rw [hS2]
    exact rt_find_append s.journal e hv0.2.2.2.2.1
  have hvalid2 : ValidReverse ((step s (.post e)).2) e.id := ⟨hmem2pre, hnotrev2⟩
  have hok2 : (step ((step s (.post e)).2) (.reverse e.id)).1 = .ok := req_reverse_succeeds _ _ hvalid2
  refine ⟨hok2, ?_⟩
  have heffPost := req_post_effects s e hok
  obtain ⟨haccP, hopenP, hjourP, hrevP, hbalP⟩ := heffPost
  have heffRev := req_reverse_effects ((step s (.post e)).2) e.id e hok2 hfind2
  obtain ⟨haccR, hopenR, hjourR, hrevR, hbalR⟩ := heffRev
  funext a
  rw [hbalR a, hbalP a]
  omega

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩ := hwf
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · obtain ⟨hne, hmemAcc, hneZero, hsum0, hnid, hnrev⟩ := hv
      have heff := req_post_effects s e hok
      obtain ⟨hacc, hopen, hjour, hrev, hbal⟩ := heff
      have hTotal2 : total ((step s (.post e)).2) = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
        unfold total
        rw [hacc]
        apply sumOver_congr
        intro a _ha
        rw [hbal a]
      rw [hTotal2]
      rw [sumOver_add]
      have hSumNet : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
        rw [sumNet_eq_lineSum_tb3 s.accounts e.lines hNodupAcc hmemAcc, hsum0]
      rw [hSumNet]
      simp [total]
    · have hs : step s (.post e) = (.rejected, s) := by simp [step, hv]
      rw [hs] at hok
      simp at hok
  | reverse i =>
    cases hfe : findEntry s.journal i with
    | none =>
      have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe]
      rw [hs] at hok
      simp at hok
    | some e =>
      by_cases hrev : i ∈ s.reversed
      · have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe, hrev]
        rw [hs] at hok
        simp at hok
      · have heMem : e ∈ s.journal := findEntry_mem_tb3 s.journal i e hfe
        have heProp := hBal e heMem
        obtain ⟨heAcc, heSum0⟩ := heProp
        have heff := req_reverse_effects s i e hok hfe
        obtain ⟨hacc, hopen, hjour, hrev, hbal⟩ := heff
        have hTotal2 : total ((step s (.reverse i)).2) = sumOver s.accounts (fun a => s.balance a - netOf e.lines a) := by
          unfold total
          rw [hacc]
          apply sumOver_congr
          intro a _ha
          rw [hbal a]
        rw [hTotal2]
        rw [sumOver_sub]
        have hSumNet : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
          rw [sumNet_eq_lineSum_tb3 s.accounts e.lines hNodupAcc heAcc, heSum0]
        rw [hSumNet]
        simp [total]

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩ := hwf
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hvc := hv
      obtain ⟨hne, hmemAcc, hneZero, hsum0, hnid, hnrev⟩ := hvc
      have hs : step s (.post e) = (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by simp [step, hv]
      have hS2 : (step s (.post e)).2 = ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State) := congrArg Prod.snd hs
      rw [hS2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hNodupAcc
      · have h1 : ids ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State).journal = ids (s.journal ++ [e]) := rfl
        rw [h1, rt_ids_append]
        exact nodup_append_singleton_aux2 (ids s.journal) e.id hNodupIds hnid
      · intro i hi
        have h2 : ids ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State).journal = ids (s.journal ++ [e]) := rfl
        rw [h2]
        exact mem_ids_append_mono_aux3 s.journal e i (hRevSub i hi)
      · intro e' he'
        have hejt : e' ∈ s.journal ++ [e] := he'
        rw [List.mem_append] at hejt
        simp only [List.mem_singleton] at hejt
        cases hejt with
        | inl hmem =>
          have hp := hBal e' hmem
          obtain ⟨haccOld, hsumOld⟩ := hp
          constructor
          · intro l hl
            exact haccOld l hl
          · exact hsumOld
        | inr heq =>
          subst heq
          constructor
          · intro l hl
            exact hmemAcc l hl
          · exact hsum0
    · have hs : step s (.post e) = (.rejected, s) := by simp [step, hv]
      have hS2 : (step s (.post e)).2 = s := by rw [hs]
      rw [hS2]
      exact ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩
  | reverse i =>
    cases hfe : findEntry s.journal i with
    | none =>
      have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe]
      have hS2 : (step s (.reverse i)).2 = s := by rw [hs]
      rw [hS2]
      exact ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩
    | some e =>
      by_cases hrev : i ∈ s.reversed
      · have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe, hrev]
        have hS2 : (step s (.reverse i)).2 = s := by rw [hs]
        rw [hS2]
        exact ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩
      · have hs : step s (.reverse i) =
            (.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                            reversed := i :: s.reversed }) := by simp [step, hfe, hrev]
        have hS2 : (step s (.reverse i)).2 =
            ({ s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                            reversed := i :: s.reversed } : State) := congrArg Prod.snd hs
        rw [hS2]
        have hmemIds : i ∈ ids s.journal := findEntry_some_mem_ids_test3 s.journal i e hfe
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact hNodupAcc
        · exact hNodupIds
        · intro x hx
          simp only [List.mem_cons] at hx
          cases hx with
          | inl heq => subst heq; exact hmemIds
          | inr hmem => exact hRevSub x hmem
        · intro e' he'
          exact hBal e' he'

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩ := hwf
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hvCopy := hv
      obtain ⟨hne, hmemAcc, hneZero, hsum0, hnid, hnrev⟩ := hvCopy
      have hs : step s (.post e) = (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by simp [step, hv]
      have hS2 : (step s (.post e)).2 = ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State) := congrArg Prod.snd hs
      intro a
      have hbal2 : (step s (.post e)).2.balance a = postLines e.lines s.balance a := by rw [hS2]
      have hopen2 : (step s (.post e)).2.opening a = s.opening a := by rw [hS2]
      have hjour2 : (step s (.post e)).2.journal = s.journal ++ [e] := by rw [hS2]
      have hrev2 : (step s (.post e)).2.reversed = s.reversed := by rw [hS2]
      rw [hbal2, hopen2]
      have hpost : postLines e.lines s.balance a = s.balance a + netOf e.lines a := postLines_bal e.lines s.balance a
      rw [hpost]
      have hconsa := hcons a
      rw [hconsa]
      have hAct : activeNet ((step s (.post e)).2) a = activeNet s a + netOf e.lines a := by
        unfold activeNet
        rw [hjour2, hrev2]
        have h := activePost_eq_auxSC2 s.journal e s.reversed a
        rw [h]
        have hIf : (if e.id ∈ s.reversed then (0:Int) else netOf e.lines a) = netOf e.lines a := by simp [hnrev]
        rw [hIf]
      rw [hAct]
      omega
    · have hs : step s (.post e) = (.rejected, s) := by simp [step, hv]
      have hS2 : (step s (.post e)).2 = s := by rw [hs]
      rw [hS2]
      exact hcons
  | reverse i =>
    cases hfe : findEntry s.journal i with
    | none =>
      have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe]
      have hS2 : (step s (.reverse i)).2 = s := by rw [hs]
      rw [hS2]
      exact hcons
    | some e =>
      by_cases hrev : i ∈ s.reversed
      · have hs : step s (.reverse i) = (.rejected, s) := by simp [step, hfe, hrev]
        have hS2 : (step s (.reverse i)).2 = s := by rw [hs]
        rw [hS2]
        exact hcons
      · have hs : step s (.reverse i) =
            (.ok, { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                            reversed := i :: s.reversed }) := by simp [step, hfe, hrev]
        have hS2 : (step s (.reverse i)).2 =
            ({ s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance,
                            reversed := i :: s.reversed } : State) := congrArg Prod.snd hs
        intro a
        have hbal2 : (step s (.reverse i)).2.balance a = postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance a := by rw [hS2]
        have hopen2 : (step s (.reverse i)).2.opening a = s.opening a := by rw [hS2]
        have hjour2 : (step s (.reverse i)).2.journal = s.journal := by rw [hS2]
        have hrev2 : (step s (.reverse i)).2.reversed = i :: s.reversed := by rw [hS2]
        rw [hbal2, hopen2]
        have hpost : postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance a = s.balance a - netOf e.lines a := postLines_neg_aux5 e.lines s.balance a
        rw [hpost]
        have hconsa := hcons a
        rw [hconsa]
        have hAct : activeNet ((step s (.reverse i)).2) a = activeNet s a - netOf e.lines a := by
          unfold activeNet
          rw [hjour2, hrev2]
          exact activeReverse_eq_auxSC7 s.journal s.reversed i e a hNodupIds hfe hrev
        rw [hAct]
        omega

end Reversal
