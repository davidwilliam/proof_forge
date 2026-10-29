import Reversal.Spec
import Reversal.Lemmas

namespace Reversal

def linesOkAcc : List AccountId → List Line → Bool
  | _, [] => true
  | accs, l :: ls => decide (l.1 ∈ accs) && linesOkAcc accs ls

def linesNonZero : List Line → Bool
  | [] => true
  | l :: ls => decide (l.2 ≠ 0) && linesNonZero ls

def postOk (s : State) (e : Entry) : Bool :=
  (!e.lines.isEmpty) && linesOkAcc s.accounts e.lines && linesNonZero e.lines && decide (lineSum e.lines = 0) && decide (e.id ∉ ids s.journal) && decide (e.id ∉ s.reversed)

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if postOk s e then
      (Outcome.ok,
        { accounts := s.accounts,
          opening := s.opening,
          balance := fun a => s.balance a + netOf e.lines a,
          journal := s.journal ++ [e],
          reversed := s.reversed })
    else (Outcome.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | none => (Outcome.rejected, s)
    | some e =>
      if i ∈ s.reversed then (Outcome.rejected, s)
      else
        (Outcome.ok,
          { accounts := s.accounts,
            opening := s.opening,
            balance := fun a => s.balance a - netOf e.lines a,
            journal := s.journal,
            reversed := i :: s.reversed })

theorem linesOkAcc_true_iff2 (accs : List AccountId) (ls : List Line) :
    linesOkAcc accs ls = true ↔ ∀ l ∈ ls, l.1 ∈ accs := by
  induction ls with
  | nil => simp [linesOkAcc]
  | cons h t ih =>
    simp only [linesOkAcc]
    constructor
    · intro htrue l hl
      simp only [Bool.and_eq_true] at htrue
      obtain ⟨hmem, hrest⟩ := htrue
      have hdec : decide (h.1 ∈ accs) = true := hmem
      have hrw := ih.mp hrest
      simp at hl
      rcases hl with rfl | hmem2
      · exact decide_eq_true_eq.mp hdec
      · exact hrw l hmem2
    · intro hall
      simp only [Bool.and_eq_true]
      constructor
      · exact decide_eq_true_eq.mpr (hall h (by simp))
      · exact ih.mpr (fun l hl => hall l (by simp [hl]))

theorem linesNonZero_true_iff2 (ls : List Line) :
    linesNonZero ls = true ↔ ∀ l ∈ ls, l.2 ≠ 0 := by
  induction ls with
  | nil => simp [linesNonZero]
  | cons h t ih =>
    simp only [linesNonZero, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hh, ht⟩ l hl
      simp at hl
      rcases hl with rfl | hm
      · exact hh
      · exact (ih.mp ht) l hm
    · intro hall
      exact ⟨hall h (by simp), ih.mpr (fun l hl => hall l (by simp [hl]))⟩

theorem notEmpty_iff3 (l : List Line) : ((!l.isEmpty) = true) ↔ l ≠ [] := by
  cases l with
  | nil => simp
  | cons h t => simp

theorem postOk_true_iff3 (s : State) (e : Entry) :
    postOk s e = true ↔ ValidPost s e := by
  unfold postOk ValidPost
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [notEmpty_iff3, linesOkAcc_true_iff2, linesNonZero_true_iff2]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩
    exact ⟨h1,h2,h3,h4,h5,h6⟩
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩
    exact ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩

theorem findEntry_mem_helper4 (j : List Entry) (i : EntryId) (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons e es ih =>
    simp only [findEntry]
    by_cases he : e.id = i
    · simp only [he, ↓reduceIte]
      exact ⟨e, rfl⟩
    · simp only [he, ↓reduceIte]
      apply ih
      unfold ids at h ⊢
      simp at h ⊢
      cases h with
      | inl hl => exact absurd hl.symm he
      | inr hr => exact hr

theorem findEntry_none_of_notMem5 (j : List Entry) (i : EntryId) (h : i ∉ ids j) : findEntry j i = none := by
  induction j with
  | nil => rfl
  | cons e es ih =>
    have hne : ¬ (e.id = i) := by
      intro heq
      apply h
      have hEq : ids (e :: es) = e.id :: ids es := rfl
      rw [hEq, heq]
      exact List.mem_cons_self
    simp only [findEntry, hne, ↓reduceIte]
    apply ih
    intro hmem
    apply h
    have hEq : ids (e :: es) = e.id :: ids es := rfl
    rw [hEq]
    exact List.mem_cons_of_mem e.id hmem

theorem findEntry_some_mem5 (j : List Entry) (i : EntryId) (e : Entry) (h : findEntry j i = some e) : i ∈ ids j := by
  induction j with
  | nil => cases h
  | cons hd tl ih =>
    have hEq : ids (hd :: tl) = hd.id :: ids tl := rfl
    by_cases heq : hd.id = i
    · rw [hEq, heq]
      exact List.mem_cons_self
    · have h2 : findEntry tl i = some e := by simp only [findEntry, heq, ↓reduceIte] at h; exact h
      have ihm := ih h2
      rw [hEq]
      exact List.mem_cons_of_mem hd.id ihm

theorem req_invalid_noop_test1 (s : State) (i : EntryId) (e : Entry)
    (hfind : findEntry s.journal i = some e) (hmem_rev : i ∈ s.reversed) :
    step s (Command.reverse i) = (Outcome.rejected, s) := by
  unfold step
  simp only [hfind, hmem_rev, ↓reduceIte]

theorem req_invalid_noop_aux99 : True := trivial

theorem req_invalid_noop_probe2 (s : State) (e : Entry) (hf : postOk s e = false) :
    step s (Command.post e) = (Outcome.rejected, s) := by
  unfold step
  simp [hf]

theorem revOnceHelperA (s : State) (i : EntryId) (e : Entry)
    (hfe : findEntry s.journal i = some e) (hmem : i ∉ s.reversed) :
    (step s (Command.reverse i)).2.journal = s.journal := by
  unfold step
  simp [hfe, hmem]

theorem revOnceHelperB (t : State) (i : EntryId) (e : Entry)
    (hf : findEntry t.journal i = some e) (hm : i ∈ t.reversed) :
    step t (Command.reverse i) = (Outcome.rejected, t) := by
  simp [step, hf, hm]

theorem revOnceHelperC (s : State) (i : EntryId) (e : Entry)
    (hfe : findEntry s.journal i = some e) (hmem : i ∉ s.reversed) :
    (step s (Command.reverse i)).2.reversed = i :: s.reversed := by
  unfold step
  simp [hfe, hmem]

theorem revOnceMain (s : State) (i : EntryId) (e : Entry)
    (hfe : findEntry s.journal i = some e) (hmem : i ∉ s.reversed) :
    step (step s (Command.reverse i)).2 (Command.reverse i) =
      (Outcome.rejected, (step s (Command.reverse i)).2) := by
  have hJ := revOnceHelperA s i e hfe hmem
  have hR := revOnceHelperC s i e hfe hmem
  have hfindT : findEntry (step s (Command.reverse i)).2.journal i = some e := by
    rw [hJ]
    exact hfe
  have hmemT : i ∈ (step s (Command.reverse i)).2.reversed := by
    rw [hR]
    exact List.mem_cons_self
  exact revOnceHelperB _ _ _ hfindT hmemT

theorem findEntry_self_aux (e : Entry) : findEntry [e] e.id = some e := by
  unfold findEntry
  simp

theorem findEntry_self_aux2 (e : Entry) : findEntry [e] e.id = some e := by
  simp only [findEntry]
  simp

theorem findEntry_append_singleton_aux3 (j : List Entry) (e : Entry) (h : e.id ∉ ids j) :
    findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil =>
    simp only [List.nil_append]
    exact findEntry_self_aux e
  | cons hd tl ih =>
    have h2 : e.id ∉ ids tl := by
      unfold ids at h ⊢
      simp at h ⊢
      exact h.2
    have hhd : ¬ (hd.id = e.id) := by
      unfold ids at h
      simp at h
      exact fun heq => h.1 heq.symm
    simp only [List.cons_append, findEntry, hhd, ↓reduceIte]
    exact ih h2

theorem req_roundtrip_check_tmp : True := trivial

theorem fooTrialTmp : True := trivial

theorem sumAccSingle (accs : List AccountId) (hNodup : accs.Nodup) (x : AccountId) (c : Int) :
    sumOver accs (fun a => if x = a then c else 0) = if x ∈ accs then c else 0 := by
  have hswap : (fun a => (if x = a then c else (0 : Int))) = (fun a => if a = x then c else 0) := by
    funext a
    by_cases h : x = a
    · subst h; simp
    · have h2 : ¬ (a = x) := fun he => h he.symm
      simp [h, h2]
  rw [hswap]
  exact sumOver_ite_eq hNodup x c

theorem sumOverZero (accs : List AccountId) : sumOver accs (fun _ => (0 : Int)) = 0 := by
  induction accs with
  | nil => simp
  | cons hd tl ih => simp [ih]

theorem sumNetEqLineSum3 (accs : List AccountId) (hNodup : accs.Nodup) (ls : List Line)
    (hmem : ∀ l ∈ ls, l.1 ∈ accs) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    simp only [lineSum, sumOver_nil]
    have h0 : (fun a => netOf ([] : List Line) a) = (fun _ => (0 : Int)) := by
      funext a
      simp [netOf]
    rw [h0]
    exact sumOverZero accs
  | cons hd tl ih =>
    have hNetCons : ∀ a : AccountId, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      intro a
      simp [netOf]
    have h1 : sumOver accs (fun a => netOf (hd :: tl) a)
        = sumOver accs (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      apply sumOver_congr
      intro a _
      exact hNetCons a
    rw [h1, sumOver_add]
    have hmemHd : hd.1 ∈ accs := hmem hd (by simp)
    have hSingle : sumOver accs (fun a => (if hd.1 = a then hd.2 else 0)) = hd.2 := by
      have h := sumAccSingle accs hNodup hd.1 hd.2
      rw [if_pos hmemHd] at h
      exact h
    rw [hSingle]
    have iht := ih (fun l hl => hmem l (by simp [hl]))
    have hls : lineSum (hd :: tl) = hd.2 + lineSum tl := by
      simp [lineSum]
    rw [hls, iht]

theorem findEntryMemOfSome {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h
      subst h
      exact List.mem_cons_self
    · simp [heq] at h
      exact List.mem_cons_of_mem hd (ih h)

theorem totalPostAux (s : State) (e : Entry) :
    (step s (Command.post e)).1 = Outcome.ok → postOk s e = true := by
  intro hOk
  by_cases h : postOk s e = true
  · exact h
  · have hF : postOk s e = false := Bool.eq_false_iff.mpr h
    have hst : step s (Command.post e) = (Outcome.rejected, s) := req_invalid_noop_probe2 s e hF
    have h1 : (step s (Command.post e)).1 = Outcome.rejected := by rw [hst]
    rw [h1] at hOk
    contradiction

theorem ids_append_singleton2 (j : List Entry) (e : Entry) : ids (j ++ [e]) = ids j ++ [e.id] := by simp [ids]

#check @List.nodup_append
#check @List.Nodup
#check List.nodup_cons

theorem activeNet_post_eq_aux (j : List Entry) (r : List EntryId) (e : Entry) (a : AccountId) (h : e.id ∉ r) :
    sumOver (j ++ [e]) (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a)
    = sumOver j (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a) + netOf e.lines a := by
  have h1 : sumOver (j ++ [e]) (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a)
    = sumOver j (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a) + sumOver [e] (fun e' => if e'.id ∈ r then (0:Int) else netOf e'.lines a) := sumOver_append j [e] _
  rw [h1]
  simp only [sumOver_cons, sumOver_nil] at h1 ⊢
  simp [h]

theorem mem_ids_of_mem2 (j : List Entry) (e' : Entry) (h : e' ∈ j) : e'.id ∈ ids j := by
  unfold ids
  apply List.mem_map_of_mem
  exact h

theorem ite_rev_congr_aux2 (tl : List Entry) (r : List EntryId) (i : EntryId) (a : AccountId) (hni : i ∉ ids tl) :
    sumOver tl (fun e' => (if e'.id ∈ i :: r then (0:Int) else netOf e'.lines a))
    = sumOver tl (fun e' => (if e'.id ∈ r then (0:Int) else netOf e'.lines a)) := by
  apply sumOver_congr
  intro e' he'
  have hid : e'.id ∈ ids tl := mem_ids_of_mem2 tl e' he'
  have hne : e'.id ≠ i := by
    intro heq
    apply hni
    rw [heq] at hid
    exact hid
  have hmem : (e'.id ∈ i :: r) ↔ (e'.id ∈ r) := by
    simp only [List.mem_cons]
    constructor
    · rintro (h | h)
      · exact absurd h hne
      · exact h
    · intro h
      exact Or.inr h
  by_cases hm : e'.id ∈ r
  · have hm2 : e'.id ∈ i :: r := hmem.mpr hm
    simp [hm, hm2]
  · have hm2 : e'.id ∉ i :: r := fun h => hm (hmem.mp h)
    simp [hm, hm2]

theorem headTermEq_aux (hdId i : EntryId) (r : List EntryId) (v : Int) (hne : hdId ≠ i) :
    (if hdId ∈ i :: r then (0:Int) else v) = (if hdId ∈ r then (0:Int) else v) := by
  have hmem : (hdId ∈ i :: r) ↔ (hdId ∈ r) := by
    simp only [List.mem_cons]
    constructor
    · rintro (h | h)
      · exact absurd h hne
      · exact h
    · intro h; exact Or.inr h
  by_cases hm : hdId ∈ r
  · have hm2 : hdId ∈ i :: r := hmem.mpr hm
    simp [hm, hm2]
  · have hm2 : hdId ∉ i :: r := fun h => hm (hmem.mp h)
    simp [hm, hm2]

theorem nIdsTail_of_nodup (hd : Entry) (tl : List Entry) (h : (ids (hd :: tl)).Nodup) : (ids tl).Nodup := by
  unfold ids at h ⊢
  simp at h ⊢
  exact h.2

theorem nIdNotMemTail (hd : Entry) (tl : List Entry) (h : (ids (hd :: tl)).Nodup) : hd.id ∉ ids tl := by
  unfold ids at h ⊢
  simp at h ⊢
  exact h.1

theorem reverseActiveSub_aux3 (j : List Entry) (r : List EntryId) (i : EntryId) (e : Entry) (a : AccountId)
    (hNodup : (ids j).Nodup) (hfind : findEntry j i = some e) (hnot : i ∉ r) :
    sumOver j (fun e' => (if e'.id ∈ i :: r then (0:Int) else netOf e'.lines a))
    = sumOver j (fun e' => (if e'.id ∈ r then (0:Int) else netOf e'.lines a)) - netOf e.lines a := by
  induction j with
  | nil =>
    simp only [findEntry] at hfind
    cases hfind
  | cons hd tl ih =>
    have hTailNodup : (ids tl).Nodup := nIdsTail_of_nodup hd tl hNodup
    have hHdNot : hd.id ∉ ids tl := nIdNotMemTail hd tl hNodup
    by_cases heq : hd.id = i
    · have hSimp : findEntry (hd :: tl) i = some hd := by simp [findEntry, heq]
      rw [hSimp] at hfind
      have hee : hd = e := Option.some_inj.mp hfind
      have hhdNotR : hd.id ∉ r := by rw [heq]; exact hnot
      have hiNotTail : i ∉ ids tl := by
        intro hm
        apply hHdNot
        have : hd.id ∈ ids tl := heq ▸ hm
        exact this
      have htailEq : sumOver tl (fun e' => (if e'.id ∈ i :: r then (0:Int) else netOf e'.lines a))
        = sumOver tl (fun e' => (if e'.id ∈ r then (0:Int) else netOf e'.lines a)) :=
        ite_rev_congr_aux2 tl r i a hiNotTail
      simp only [sumOver_cons]
      have hheadNew : (if hd.id ∈ i :: r then (0:Int) else netOf hd.lines a) = 0 := by simp [heq]
      have hheadOld : (if hd.id ∈ r then (0:Int) else netOf hd.lines a) = netOf hd.lines a := by simp [hhdNotR]
      rw [hheadNew, hheadOld, htailEq, hee]
      omega
    · have hfindTl : findEntry tl i = some e := by simp [findEntry, heq] at hfind; exact hfind
      have ih' := ih hTailNodup hfindTl
      simp only [sumOver_cons]
      have hheadEq : (if hd.id ∈ i :: r then (0:Int) else netOf hd.lines a) = (if hd.id ∈ r then (0:Int) else netOf hd.lines a) :=
        headTermEq_aux hd.id i r (netOf hd.lines a) heq
      rw [hheadEq, ih']
      omega

theorem postNotRev_of_ok (s : State) (e : Entry) (h : postOk s e = true) : e.id ∉ s.reversed := by
  have hV := (postOk_true_iff3 s e).mp h
  unfold ValidPost at hV
  obtain ⟨_, _, _, _, _, h6⟩ := hV
  exact h6

theorem stepPostSecondEq (s : State) (e : Entry) (h : postOk s e = true) :
    (step s (Command.post e)).2 =
      { accounts := s.accounts,
        opening := s.opening,
        balance := fun a => s.balance a + netOf e.lines a,
        journal := s.journal ++ [e],
        reversed := s.reversed } := by
  unfold step
  simp [h]

theorem stepPostRejSecond (s : State) (e : Entry) (h : postOk s e = false) :
    (step s (Command.post e)).2 = s := by
  unfold step
  simp [h]

theorem stepRevNoneSecond (s : State) (i : EntryId) (h : findEntry s.journal i = none) :
    (step s (Command.reverse i)).2 = s := by
  unfold step
  simp [h]

theorem stepRevMemSecond (s : State) (i : EntryId) (e : Entry) (hfind : findEntry s.journal i = some e) (hmem : i ∈ s.reversed) :
    (step s (Command.reverse i)).2 = s := by
  unfold step
  simp [hfind, hmem]

theorem stepRevOkSecond (s : State) (i : EntryId) (e : Entry) (hfind : findEntry s.journal i = some e) (hmem : i ∉ s.reversed) :
    (step s (Command.reverse i)).2 =
      { accounts := s.accounts,
        opening := s.opening,
        balance := fun a => s.balance a - netOf e.lines a,
        journal := s.journal,
        reversed := i :: s.reversed } := by
  unfold step
  simp [hfind, hmem]

theorem testReverseOnce : ReverseOnce step := by
  unfold ReverseOnce
  intro s i hOk
  match hfind : findEntry s.journal i with
  | none =>
    have hEq : (step s (Command.reverse i)).1 = Outcome.rejected := by
      unfold step; simp [hfind]
    rw [hEq] at hOk
    contradiction
  | some e =>
    by_cases hmem : i ∈ s.reversed
    · have hEq : (step s (Command.reverse i)).1 = Outcome.rejected := by
        unfold step; simp [hfind, hmem]
      rw [hEq] at hOk
      contradiction
    · exact revOnceMain s i e hfind hmem

theorem roundtripMidFindY (s : State) (e : Entry) (hT : postOk s e = true) :
    findEntry (step s (Command.post e)).2.journal e.id = some e := by
  have hV : ValidPost s e := (postOk_true_iff3 s e).mp hT
  obtain ⟨hNe, hAcc, hNz, hSum, hNotJ, hNotR⟩ := hV
  have hStepEq := stepPostSecondEq s e hT
  have hJ : (step s (Command.post e)).2.journal = s.journal ++ [e] := by rw [hStepEq]
  rw [hJ]
  exact findEntry_append_singleton_aux3 s.journal e hNotJ

theorem roundtripMidNotRevY (s : State) (e : Entry) (hT : postOk s e = true) :
    e.id ∉ (step s (Command.post e)).2.reversed := by
  have hV : ValidPost s e := (postOk_true_iff3 s e).mp hT
  obtain ⟨hNe, hAcc, hNz, hSum, hNotJ, hNotR⟩ := hV
  have hStepEq := stepPostSecondEq s e hT
  have hR : (step s (Command.post e)).2.reversed = s.reversed := by rw [hStepEq]
  rw [hR]
  exact hNotR

theorem roundtripMidBalY (s : State) (e : Entry) (hT : postOk s e = true) (a : AccountId) :
    (step s (Command.post e)).2.balance a = s.balance a + netOf e.lines a := by
  have hStepEq := stepPostSecondEq s e hT
  rw [hStepEq]

theorem roundtripRevPairY (t : State) (e0 : Entry) (hFind : findEntry t.journal e0.id = some e0) (hN : e0.id ∉ t.reversed) :
    step t (Command.reverse e0.id) =
      (Outcome.ok,
        { accounts := t.accounts,
          opening := t.opening,
          balance := fun a => t.balance a - netOf e0.lines a,
          journal := t.journal,
          reversed := e0.id :: t.reversed }) := by
  simp [step, hFind, hN]

theorem tmpCheckA : True := trivial
#check @List.nodup_append
#check List.Nodup

theorem nodupAppendSingleAux (l : List Nat) (x : Nat) (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil =>
    simp only [List.nil_append]
    rw [List.nodup_cons]
    exact ⟨by simp, List.nodup_nil⟩
  | cons hd tl ih =>
    rw [List.nodup_cons] at h1
    obtain ⟨hhd, htl⟩ := h1
    have hx_tl : x ∉ tl := by
      intro hm
      apply h2
      exact List.mem_cons_of_mem hd hm
    have hne : hd ≠ x := by
      intro heq
      apply h2
      rw [heq]
      exact List.mem_cons_self
    have ih' := ih htl hx_tl
    have heq : ((hd :: tl) ++ [x]) = hd :: (tl ++ [x]) := rfl
    rw [heq, List.nodup_cons]
    constructor
    · intro hm
      rw [List.mem_append] at hm
      cases hm with
      | inl h =>
        exact hhd h
      | inr h =>
        simp at h
        exact hne h
    · exact ih'

theorem wfIdsAppendW (j : List Entry) (e : Entry) (h1 : (ids j).Nodup) (h2 : e.id ∉ ids j) : (ids (j ++ [e])).Nodup := by
  rw [ids_append_singleton2]
  exact nodupAppendSingleAux (ids j) e.id h1 h2

theorem wfValidOfPostOk (s : State) (e : Entry) (h : postOk s e = true) : ValidPost s e :=
  (postOk_true_iff3 s e).mp h

theorem wfMemAppendLeftW (j : List Entry) (e : Entry) (x : EntryId) (h : x ∈ ids j) : x ∈ ids (j ++ [e]) := by
  rw [ids_append_singleton2, List.mem_append]
  exact Or.inl h

theorem wfBalAppendW (j : List Entry) (e : Entry) (s : State) (hJBal : ∀ e_1 ∈ j, (∀ l ∈ e_1.lines, l.1 ∈ s.accounts) ∧ lineSum e_1.lines = 0)
    (hV : ValidPost s e) (e' : Entry) (h : e' ∈ j ++ [e]) : (∀ l ∈ e'.lines, l.1 ∈ s.accounts) ∧ lineSum e'.lines = 0 := by
  rw [List.mem_append] at h
  cases h with
  | inl hm => exact hJBal e' hm
  | inr hm =>
    simp at hm
    subst hm
    obtain ⟨_, hAcc, _, hSum, _, _⟩ := hV
    exact ⟨hAcc, hSum⟩

theorem req_post_succeeds : PostSucceeds step := by
  intro s e hV
  have hT : postOk s e = true := (postOk_true_iff3 s e).mpr hV
  show (step s (Command.post e)).1 = _
  unfold step
  simp [hT]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  unfold ReverseSucceeds ValidReverse
  intro s i h
  obtain ⟨hmem, hnot⟩ := h
  obtain ⟨e, he⟩ := findEntry_mem_helper4 s.journal i hmem
  unfold step
  simp only [he]
  simp [hnot]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s c hInvalid
  cases c with
  | post e =>
    have hF : postOk s e = false := by
      by_cases h : postOk s e = true
      · have hV : ValidPost s e := (postOk_true_iff3 s e).mp h
        have hV2 : Valid s (Command.post e) := hV
        exact False.elim (hInvalid hV2)
      · exact Bool.eq_false_iff.mpr h
    exact req_invalid_noop_probe2 s e hF
  | reverse i =>
    have hcase : findEntry s.journal i = none ∨ ∃ e, findEntry s.journal i = some e := by
      cases h : findEntry s.journal i with
      | none => exact Or.inl rfl
      | some e => exact Or.inr ⟨e, rfl⟩
    cases hcase with
    | inl hnone =>
      have hfind : findEntry s.journal i = none := hnone
      show step s (Command.reverse i) = _
      unfold step
      simp [hfind]
    | inr hex =>
      obtain ⟨e, hfind⟩ := hex
      have hmem : i ∈ ids s.journal := findEntry_some_mem5 s.journal i e hfind
      have hmemRev : i ∈ s.reversed := by
        by_cases hN : i ∈ s.reversed
        · exact hN
        · have hV : Valid s (Command.reverse i) := ⟨hmem, hN⟩
          exact False.elim (hInvalid hV)
      show step s (Command.reverse i) = _
      unfold step
      simp [hfind, hmemRev]

theorem req_post_effects : PostEffects step := by
  intro s e hOk
  have hT : postOk s e = true := by
    by_cases h : postOk s e = true
    · exact h
    · have hF : postOk s e = false := Bool.eq_false_iff.mpr h
      have hst := req_invalid_noop_probe2 s e hF
      have h1 : (step s (Command.post e)).1 = Outcome.rejected := by rw [hst]
      rw [h1] at hOk
      contradiction
  have hStep : step s (Command.post e) =
      (Outcome.ok,
        { accounts := s.accounts,
          opening := s.opening,
          balance := fun a => s.balance a + netOf e.lines a,
          journal := s.journal ++ [e],
          reversed := s.reversed }) := by
    unfold step
    simp [hT]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (step s (Command.post e)).2.accounts = s.accounts := by rw [hStep]
    exact this
  · have : (step s (Command.post e)).2.opening = s.opening := by rw [hStep]
    exact this
  · have : (step s (Command.post e)).2.journal = s.journal ++ [e] := by rw [hStep]
    exact this
  · have : (step s (Command.post e)).2.reversed = s.reversed := by rw [hStep]
    exact this
  · intro a
    have : (step s (Command.post e)).2.balance a = s.balance a + netOf e.lines a := by rw [hStep]
    exact this

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hOk hfind
  by_cases hmem : i ∈ s.reversed
  · have hEq : step s (Command.reverse i) = (Outcome.rejected, s) := by
      unfold step
      simp only [hfind, hmem, ↓reduceIte]
    have h1 : (step s (Command.reverse i)).1 = Outcome.rejected := by rw [hEq]
    rw [h1] at hOk
    exact absurd hOk (by decide)
  · have hStep : step s (Command.reverse i) =
        (Outcome.ok,
          { accounts := s.accounts,
            opening := s.opening,
            balance := fun a => s.balance a - netOf e.lines a,
            journal := s.journal,
            reversed := i :: s.reversed }) := by
      unfold step
      simp only [hfind, hmem, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h2 : (step s (Command.reverse i)).2.accounts = s.accounts := by rw [hStep]
      exact h2
    · have h3 : (step s (Command.reverse i)).2.opening = s.opening := by rw [hStep]
      exact h3
    · have h4 : (step s (Command.reverse i)).2.journal = s.journal := by rw [hStep]
      exact h4
    · intro x
      have h5 : (step s (Command.reverse i)).2.reversed = i :: s.reversed := by rw [hStep]
      rw [h5]
      simp only [List.mem_cons]
    · intro a
      have h6 : (step s (Command.reverse i)).2.balance a = s.balance a - netOf e.lines a := by rw [hStep]
      exact h6

theorem req_reverse_once : ReverseOnce step := by
  unfold ReverseOnce
  intro s i hOk
  match hfind : findEntry s.journal i with
  | none =>
    have hEq : (step s (Command.reverse i)).1 = Outcome.rejected := by
      unfold step; simp [hfind]
    rw [hEq] at hOk
    contradiction
  | some e =>
    by_cases hmem : i ∈ s.reversed
    · have hEq : (step s (Command.reverse i)).1 = Outcome.rejected := by
        unfold step; simp [hfind, hmem]
      rw [hEq] at hOk
      contradiction
    · exact revOnceMain s i e hfind hmem

theorem req_roundtrip : RoundTrip step := by
  unfold RoundTrip
  intro s e hOk
  have hT : postOk s e = true := (totalPostAux s e) hOk
  have hFind : findEntry (step s (Command.post e)).2.journal e.id = some e :=
    roundtripMidFindY s e hT
  have hNotR : e.id ∉ (step s (Command.post e)).2.reversed :=
    roundtripMidNotRevY s e hT
  have hBal : ∀ a, (step s (Command.post e)).2.balance a = s.balance a + netOf e.lines a := fun a =>
    roundtripMidBalY s e hT a
  -- reversing succeeds
  have hRevOk : (step (step s (Command.post e)).2 (Command.reverse e.id)).1 = Outcome.ok := by
    have hPair := roundtripRevPairY (step s (Command.post e)).2 e hFind hNotR
    rw [hPair]
  refine ⟨hRevOk, ?_⟩
  have hPair := roundtripRevPairY (step s (Command.post e)).2 e hFind hNotR
  have hBal2 : ∀ a, (step (step s (Command.post e)).2 (Command.reverse e.id)).2.balance a = s.balance a := by
    intro a
    have hStepEq : (step (step s (Command.post e)).2 (Command.reverse e.id)).2.balance a
      = (step s (Command.post e)).2.balance a - netOf e.lines a := by
      rw [hPair]
    rw [hStepEq, hBal a]
    omega
  funext a
  exact hBal2 a

theorem req_trial_balance : TrialBalance step := by
  unfold TrialBalance
  intro s c hWF hOk
  obtain ⟨hAccNodup, hJidsNodup, hRevSub, hJBal⟩ := hWF
  cases c with
  | post e =>
    have hT : postOk s e = true := by
      by_cases h : postOk s e = true
      · exact h
      · have hF : postOk s e = false := Bool.eq_false_iff.mpr h
        have hst := req_invalid_noop_probe2 s e hF
        have h1 : (step s (Command.post e)).1 = Outcome.rejected := by rw [hst]
        rw [h1] at hOk
        contradiction
    have hStep2 := stepPostSecondEq s e hT
    have hV : ValidPost s e := (postOk_true_iff3 s e).mp hT
    obtain ⟨hNe, hAccMem, hNz, hSum0, hNotJ, hNotR⟩ := hV
    have hAccEq : (step s (Command.post e)).2.accounts = s.accounts := by rw [hStep2]
    have hBalEq : ∀ a, (step s (Command.post e)).2.balance a = s.balance a + netOf e.lines a := by
      intro a; rw [hStep2]
    have hTot : total (step s (Command.post e)).2 = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
      unfold total
      rw [hAccEq]
      apply sumOver_congr
      intro a _
      exact hBalEq a
    rw [hTot, sumOver_add]
    have hNetSum : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
      rw [sumNetEqLineSum3 s.accounts hAccNodup e.lines hAccMem, hSum0]
    rw [hNetSum]
    simp [total]
  | reverse i =>
    match hfind : findEntry s.journal i with
    | none =>
      have hEq : (step s (Command.reverse i)).1 = Outcome.rejected := by
        unfold step; simp [hfind]
      rw [hEq] at hOk
      contradiction
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · have hEq : (step s (Command.reverse i)).1 = Outcome.rejected := by
          unfold step; simp [hfind, hmem]
        rw [hEq] at hOk
        contradiction
      · have hStep2 := stepRevOkSecond s i e hfind hmem
        have hMemJ : e ∈ s.journal := findEntryMemOfSome hfind
        have hJB := hJBal e hMemJ
        obtain ⟨hMemAcc, hSum0⟩ := hJB
        have hAccEq : (step s (Command.reverse i)).2.accounts = s.accounts := by rw [hStep2]
        have hBalEq : ∀ a, (step s (Command.reverse i)).2.balance a = s.balance a - netOf e.lines a := by
          intro a; rw [hStep2]
        have hTot : total (step s (Command.reverse i)).2 = sumOver s.accounts (fun a => s.balance a - netOf e.lines a) := by
          unfold total
          rw [hAccEq]
          apply sumOver_congr
          intro a _
          exact hBalEq a
        rw [hTot, sumOver_sub]
        have hNetSum : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
          rw [sumNetEqLineSum3 s.accounts hAccNodup e.lines hMemAcc, hSum0]
        rw [hNetSum]
        simp [total]

theorem req_well_formed : StaysWellFormed step := by
  unfold StaysWellFormed WellFormed
  intro s c hWF
  obtain ⟨hAccNodup, hJidsNodup, hRevSub, hJBal⟩ := hWF
  cases c with
  | post e =>
    by_cases hOk : postOk s e = true
    · have h2 := stepPostSecondEq s e hOk
      have hVp : ValidPost s e := wfValidOfPostOk s e hOk
      obtain ⟨hNe, hAccMem, hNz, hSum0, hNotJ, hNotR⟩ := hVp
      have hAccEq : (step s (Command.post e)).2.accounts = s.accounts := by rw [h2]
      have hJEq : (step s (Command.post e)).2.journal = s.journal ++ [e] := by rw [h2]
      have hREq : (step s (Command.post e)).2.reversed = s.reversed := by rw [h2]
      have hVfull : ValidPost s e := ⟨hNe, hAccMem, hNz, hSum0, hNotJ, hNotR⟩
      refine ⟨by rw [hAccEq]; exact hAccNodup, by rw [hJEq]; exact wfIdsAppendW s.journal e hJidsNodup hNotJ, ?_, ?_⟩
      · intro i hi
        rw [hREq] at hi
        rw [hJEq]
        exact wfMemAppendLeftW s.journal e i (hRevSub i hi)
      · intro e' he'
        rw [hJEq] at he'
        rw [hAccEq]
        exact wfBalAppendW s.journal e s hJBal hVfull e' he'
    · have hF : postOk s e = false := Bool.eq_false_iff.mpr (fun h => hOk h)
      have h2 := stepPostRejSecond s e hF
      rw [h2]
      exact ⟨hAccNodup, hJidsNodup, hRevSub, hJBal⟩
  | reverse i =>
    match hfind : findEntry s.journal i with
    | none =>
      have h2 := stepRevNoneSecond s i hfind
      rw [h2]
      exact ⟨hAccNodup, hJidsNodup, hRevSub, hJBal⟩
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · have h2 := stepRevMemSecond s i e hfind hmem
        rw [h2]
        exact ⟨hAccNodup, hJidsNodup, hRevSub, hJBal⟩
      · have h2 := stepRevOkSecond s i e hfind hmem
        have hAccEq : (step s (Command.reverse i)).2.accounts = s.accounts := by rw [h2]
        have hJEq : (step s (Command.reverse i)).2.journal = s.journal := by rw [h2]
        have hREq : (step s (Command.reverse i)).2.reversed = i :: s.reversed := by rw [h2]
        have hiMem : i ∈ ids s.journal := findEntry_some_mem5 s.journal i e hfind
        refine ⟨by rw [hAccEq]; exact hAccNodup, by rw [hJEq]; exact hJidsNodup, ?_, ?_⟩
        · intro x hx
          rw [hREq] at hx
          rw [hJEq]
          simp only [List.mem_cons] at hx
          cases hx with
          | inl heq =>
            subst heq
            exact hiMem
          | inr hm => exact hRevSub x hm
        · intro e' he'
          rw [hJEq] at he'
          rw [hAccEq]
          exact hJBal e' he'

theorem req_consistent : StaysConsistent step := by
  unfold StaysConsistent Consistent WellFormed
  intro s c hWF hCons
  obtain ⟨hAccNodup, hJidsNodup, hRevSub, hJBal⟩ := hWF
  cases c with
  | post e =>
    by_cases hOk : postOk s e = true
    · have h2 := stepPostSecondEq s e hOk
      have hNotRev : e.id ∉ s.reversed := postNotRev_of_ok s e hOk
      intro a
      have hBalPre := hCons a
      have hShow2 : ((step s (Command.post e)).2.balance a)
          = s.balance a + netOf e.lines a := by rw [h2]
      have hOpen2 : ((step s (Command.post e)).2.opening a) = s.opening a := by rw [h2]
      have hAct2 : activeNet (step s (Command.post e)).2 a
          = activeNet s a + netOf e.lines a := by
        have hJ2 : (step s (Command.post e)).2.journal = s.journal ++ [e] := by rw [h2]
        have hR2 : (step s (Command.post e)).2.reversed = s.reversed := by rw [h2]
        unfold activeNet
        rw [hJ2, hR2]
        exact activeNet_post_eq_aux s.journal s.reversed e a hNotRev
      rw [hShow2, hOpen2, hAct2, hBalPre]
      omega
    · have hF : postOk s e = false := Bool.eq_false_iff.mpr (fun h => hOk h)
      have h2 := stepPostRejSecond s e hF
      intro a
      have hBalPre := hCons a
      have hShow2 : ((step s (Command.post e)).2.balance a) = s.balance a := by rw [h2]
      have hOpen2 : ((step s (Command.post e)).2.opening a) = s.opening a := by rw [h2]
      have hAct2 : activeNet (step s (Command.post e)).2 a = activeNet s a := by rw [h2]
      rw [hShow2, hOpen2, hAct2]
      exact hBalPre
  | reverse i =>
    match hfind : findEntry s.journal i with
    | none =>
      have h2 := stepRevNoneSecond s i hfind
      intro a
      have hBalPre := hCons a
      have hShow2 : ((step s (Command.reverse i)).2.balance a) = s.balance a := by rw [h2]
      have hOpen2 : ((step s (Command.reverse i)).2.opening a) = s.opening a := by rw [h2]
      have hAct2 : activeNet (step s (Command.reverse i)).2 a = activeNet s a := by rw [h2]
      rw [hShow2, hOpen2, hAct2]
      exact hBalPre
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · have h2 := stepRevMemSecond s i e hfind hmem
        intro a
        have hBalPre := hCons a
        have hShow2 : ((step s (Command.reverse i)).2.balance a) = s.balance a := by rw [h2]
        have hOpen2 : ((step s (Command.reverse i)).2.opening a) = s.opening a := by rw [h2]
        have hAct2 : activeNet (step s (Command.reverse i)).2 a = activeNet s a := by rw [h2]
        rw [hShow2, hOpen2, hAct2]
        exact hBalPre
      · have h2 := stepRevOkSecond s i e hfind hmem
        intro a
        have hBalPre := hCons a
        have hShow2 : ((step s (Command.reverse i)).2.balance a) = s.balance a - netOf e.lines a := by rw [h2]
        have hOpen2 : ((step s (Command.reverse i)).2.opening a) = s.opening a := by rw [h2]
        have hAct2 : activeNet (step s (Command.reverse i)).2 a
            = activeNet s a - netOf e.lines a := by
          have hJ2 : (step s (Command.reverse i)).2.journal = s.journal := by rw [h2]
          have hR2 : (step s (Command.reverse i)).2.reversed = i :: s.reversed := by rw [h2]
          unfold activeNet
          rw [hJ2, hR2]
          exact reverseActiveSub_aux3 s.journal s.reversed i e a hJidsNodup hfind hmem
        rw [hShow2, hOpen2, hAct2, hBalPre]
        omega

end Reversal
