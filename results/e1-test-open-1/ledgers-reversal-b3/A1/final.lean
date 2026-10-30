import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)

def isValidPost (s : State) (e : Entry) : Bool :=
  (!e.lines.isEmpty)
  && (e.lines.all fun l => s.accounts.contains l.1)
  && (e.lines.all fun l => decide (l.2 ≠ 0))
  && (decide (lineSum e.lines = 0))
  && (! (ids s.journal).contains e.id)
  && (! s.reversed.contains e.id)

def isValidReverse (s : State) (i : EntryId) : Bool :=
  ((ids s.journal).contains i) && (! s.reversed.contains i)

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if isValidPost s e then
      (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    if isValidReverse s i then
      match findEntry s.journal i with
      | some e =>
        (.ok, { s with balance := fun a => s.balance a - netOf e.lines a,
                         journal := s.journal,
                         reversed := i :: s.reversed })
      | none => (.rejected, s)
    else (.rejected, s)

theorem req_reverse_once_aux : True := trivial

theorem req_reverse_once_helper_aux : True := trivial

theorem sumOver_zero_aux2 (accs : List AccountId) : sumOver accs (fun _ : AccountId => (0:Int)) = 0 := by
  induction accs with
  | nil => rfl
  | cons _ _ ih => simp [sumOver_cons, ih]

theorem sumOver_netOf_eq_lineSum_aux2 (accs : List AccountId) (hNodup : accs.Nodup)
    (ls : List Line) (hMem : ∀ l ∈ ls, l.1 ∈ accs) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    simp only [netOf, lineSum]
    exact sumOver_zero_aux2 accs
  | cons hd tl ih =>
    have hMemHd : hd.1 ∈ accs := hMem hd (by simp)
    have hMemTl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hMem l (by simp [hl])
    have hNetCons : ∀ a, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      intro a; simp [netOf]
    have hEq1 : sumOver accs (fun a => netOf (hd :: tl) a) =
                sumOver accs (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      apply sumOver_congr; intro a _; exact hNetCons a
    rw [hEq1, sumOver_add]
    have hSym : (fun a => if hd.1 = a then (hd.2 : Int) else 0) = (fun a => if a = hd.1 then hd.2 else 0) := by
      funext a; by_cases ha : a = hd.1
      · simp [ha]
      · have hb : hd.1 ≠ a := fun h => ha h.symm
        simp [ha, hb]
    have hIte : sumOver accs (fun a => if hd.1 = a then hd.2 else 0) = hd.2 := by
      rw [hSym, sumOver_ite_eq hNodup hd.1 hd.2, if_pos hMemHd]
    rw [hIte, ih hMemTl]
    simp [lineSum]

theorem exists_findEntry_of_mem_ids2 {j : List Entry} {i : EntryId} (h : i ∈ ids j) :
    ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons hd tl ih =>
    simp only [findEntry]
    by_cases heq : hd.id = i
    · exact ⟨hd, by simp [heq]⟩
    · simp only [heq, ↓reduceIte]
      have hMemTl : i ∈ ids tl := by
        simp only [ids, List.map_cons, List.mem_cons] at h
        rcases h with rfl | hh
        · exact absurd rfl heq
        · simp [ids, hh]
      exact ih hMemTl

theorem mem_journal_of_findEntry2 {j : List Entry} {i : EntryId} {e : Entry}
    (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; subst h; simp
    · simp [heq] at h; exact List.mem_cons_of_mem hd (ih h)

theorem activeNet_reverse_lemma2 (j : List Entry) (rev : List EntryId) (i : EntryId) (e : Entry)
    (hNodup : (ids j).Nodup) (hFind : findEntry j i = some e) (hNotRev : i ∉ rev) (a : AccountId) :
    sumOver j (fun e' => if e'.id ∈ (i :: rev) then (0:Int) else netOf e'.lines a) =
    sumOver j (fun e' => if e'.id ∈ rev then (0:Int) else netOf e'.lines a) - netOf e.lines a := by
  induction j with
  | nil => simp [findEntry] at hFind
  | cons hd tl ih =>
    simp only [findEntry] at hFind
    by_cases heq : hd.id = i
    · simp only [heq, ↓reduceIte] at hFind
      have hEq : hd = e := by injection hFind
      subst hEq
      have hNodupIds : (ids (hd :: tl)).Nodup := hNodup
      have hNodupTail : (ids tl).Nodup := by
        have h1 : (ids (hd :: tl)) = hd.id :: ids tl := rfl
        rw [h1] at hNodupIds
        exact (List.nodup_cons.mp hNodupIds).2
      have hNotInTl : hd.id ∉ ids tl := (List.nodup_cons.mp (by rwa [show ids (hd :: tl) = hd.id :: ids tl from rfl] at hNodupIds)).1
      have hNotMemTl : ∀ x ∈ tl, x.id ≠ hd.id := by
        intro x hx hEq2
        have : hd.id ∈ ids tl := by simp [ids, List.mem_map]; exact ⟨x, hx, hEq2⟩
        exact hNotInTl this
      simp only [sumOver_cons]
      have h1 : (if hd.id ∈ (hd.id :: rev) then (0:Int) else netOf hd.lines a) = 0 := by simp
      have h2 : (if hd.id ∈ rev then (0:Int) else netOf hd.lines a) = netOf hd.lines a := by
        simp [show hd.id ∉ rev from by simpa [heq] using hNotRev]
      have hi_eq : i = hd.id := heq.symm
      rw [hi_eq]
      rw [h1, h2]
      have hTlEq : sumOver tl (fun e' => if e'.id ∈ (hd.id :: rev) then (0:Int) else netOf e'.lines a) =
                   sumOver tl (fun e' => if e'.id ∈ rev then (0:Int) else netOf e'.lines a) := by
        apply sumOver_congr
        intro x hx
        have hne : x.id ≠ hd.id := hNotMemTl x hx
        simp [hne]
      rw [hTlEq]; omega
    · simp only [heq, ↓reduceIte] at hFind
      have hNodupTl : (ids tl).Nodup := by
        have hh : (ids (hd :: tl)).Nodup := hNodup
        have h1 : (ids (hd :: tl)) = hd.id :: ids tl := rfl
        rw [h1] at hh; exact (List.nodup_cons.mp hh).2
      have ih' := ih hNodupTl hFind
      simp only [sumOver_cons]
      have hHeadEq : (if hd.id ∈ (i :: rev) then (0:Int) else netOf hd.lines a) =
                     (if hd.id ∈ rev then (0:Int) else netOf hd.lines a) := by simp [heq]
      rw [hHeadEq, ih']; omega

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  unfold step
  have hValid : isValidPost s e = true := by
    unfold isValidPost
    obtain ⟨hne, hacc, hnz, hsum, hnidJ, hnidR⟩ := h
    have h1: (!e.lines.isEmpty) = true := by
      cases he : e.lines with
      | nil => simp [he] at hne
      | cons _ _ => simp
    have h2: (e.lines.all fun l => s.accounts.contains l.1) = true := by
      rw [List.all_eq_true]; intro x hx; simp [List.contains_eq_mem, hacc x hx]
    have h3: (e.lines.all fun l => decide (l.2 ≠ 0)) = true := by
      rw [List.all_eq_true]; intro x hx; simp [hnz x hx]
    have h4: (decide (lineSum e.lines = 0)) = true := by simp [hsum]
    have h5: (! (ids s.journal).contains e.id) = true := by
      simp [List.contains_eq_mem, hnidJ]
    have h6: (! s.reversed.contains e.id) = true := by
      simp [List.contains_eq_mem, hnidR]
    simp only [h1, h2, h3, h4, h5, h6, Bool.and_self]
  simp [hValid]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  obtain ⟨hMem, hNotRev⟩ := h
  unfold step
  have hBool : isValidReverse s i = true := by
    unfold isValidReverse
    simp [List.contains_eq_mem, hMem, hNotRev]
  simp only [hBool, ↓reduceIte]
  obtain ⟨e, hFind⟩ := exists_findEntry_of_mem_ids2 hMem
  simp [hFind]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    have hBool : isValidPost s e = false := by
      by_cases hb : isValidPost s e = true
      · have hVP : ValidPost s e := by
          have hb2 := hb
          unfold isValidPost at hb2
          have hA : (!e.lines.isEmpty) = true := by
            have := hb2
            simp only [Bool.and_eq_true] at this
            exact this.1.1.1.1.1
          have hB : (e.lines.all fun l => s.accounts.contains l.1) = true := by
            have := hb2
            simp only [Bool.and_eq_true] at this
            exact this.1.1.1.1.2
          have hC : (e.lines.all fun l => decide (l.2 ≠ 0)) = true := by
            have := hb2
            simp only [Bool.and_eq_true] at this
            exact this.1.1.1.2
          have hD : (decide (lineSum e.lines = 0)) = true := by
            have := hb2
            simp only [Bool.and_eq_true] at this
            exact this.1.1.2
          have hE : (! (ids s.journal).contains e.id) = true := by
            have := hb2
            simp only [Bool.and_eq_true] at this
            exact this.1.2
          have hF : (! s.reversed.contains e.id) = true := by
            have := hb2
            simp only [Bool.and_eq_true] at this
            exact this.2
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro heq
            rw [heq] at hA
            simp at hA
          · intro l hl
            have hall : ∀ x ∈ e.lines, s.accounts.contains x.1 = true := by
              intro x hx
              exact List.all_eq_true.mp hB x hx
            have hmem := hall l hl
            simp [List.contains_eq_mem] at hmem
            exact hmem
          · intro l hl
            have hall : ∀ x ∈ e.lines, decide (x.2 ≠ 0) = true := by
              intro x hx
              exact List.all_eq_true.mp hC x hx
            have hmem := hall l hl
            simp at hmem
            exact hmem
          · simp at hD
            exact hD
          · intro hm
            simp [hm] at hE
          · intro hm
            simp [hm] at hF
        exact absurd hVP h
      · simp at hb
        cases hv : isValidPost s e with
        | true => simp [hv] at hb
        | false => rfl
    show step s (Command.post e) = (Outcome.rejected, s)
    unfold step
    simp [hBool]
  | reverse i =>
    have hBool : isValidReverse s i = false := by
      by_cases hb : isValidReverse s i = true
      · have hVR : ValidReverse s i := by
          unfold isValidReverse at hb
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.contains_eq_mem] at hb
          exact ⟨by simp at hb; exact hb.1, fun hm => by simp [hm] at hb⟩
        exact absurd hVR h
      · simp at hb
        cases hv : isValidReverse s i with
        | true => simp [hv] at hb
        | false => rfl
    show step s (Command.reverse i) = (Outcome.rejected, s)
    unfold step
    simp [hBool]

theorem req_post_effects     : PostEffects step := by
  intro s e hOk
  have hpostLines : ∀ (ls : List Line) (bal : AccountId → Int) (a : AccountId),
    postLines ls bal a = bal a + netOf ls a := by
    intro ls bal a
    induction ls generalizing bal with
    | nil => simp [postLines, netOf]
    | cons h t ih =>
      simp only [postLines]
      have h1 : adjust bal h.1 h.2 a = bal a + (if h.1 = a then h.2 else 0) := by
        unfold adjust
        by_cases heq : a = h.1
        · subst heq; simp
        · have hne : h.1 ≠ a := fun hh => heq hh.symm
          simp [hne, heq]
      have h2 : netOf (h :: t) a = (if h.1 = a then h.2 else 0) + netOf t a := by
        simp [netOf]
      rw [ih, h1, h2]; omega
  unfold step at hOk
  have hBool : isValidPost s e = true := by
    by_cases hb : isValidPost s e = true
    · exact hb
    · have hbF : isValidPost s e = false := by
        cases hc : isValidPost s e
        · rfl
        · simp [hc] at hb
      simp [hbF] at hOk
  have hStep : step s (Command.post e) =
    (Outcome.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by
    unfold step; simp [hBool]
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
    have heq : (step s (Command.post e)).2.balance a = postLines e.lines s.balance a := by rw [hStep]
    rw [heq, hpostLines]

theorem req_reverse_effects  : ReverseEffects step := by
  intro s i e hOk hFind
  have hIR : isValidReverse s i = true := by
    by_cases hb : (isValidReverse s i = true)
    · exact hb
    · have hf : isValidReverse s i = false := by
        cases hv : isValidReverse s i with
        | true => simp [hv] at hb
        | false => rfl
      have hOk2 : (step s (Command.reverse i)).1 = Outcome.ok := hOk
      unfold step at hOk2
      simp [hf] at hOk2
  have hStepEq : step s (Command.reverse i) =
    (Outcome.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed }) := by
    unfold step
    simp [hIR, hFind]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (step s (Command.reverse i)).2.accounts = s.accounts := by rw [hStepEq]
    exact this
  · have : (step s (Command.reverse i)).2.opening = s.opening := by rw [hStepEq]
    exact this
  · have : (step s (Command.reverse i)).2.journal = s.journal := by rw [hStepEq]
    exact this
  · intro x
    have : (step s (Command.reverse i)).2.reversed = i :: s.reversed := by rw [hStepEq]
    rw [this]
    simp
  · intro a
    have : (step s (Command.reverse i)).2.balance a = s.balance a - netOf e.lines a := by rw [hStepEq]
    exact this

theorem req_reverse_once : ReverseOnce step := by
  intro s i hOk
  have hValid : isValidReverse s i = true := by
    by_cases hb : isValidReverse s i = true
    · exact hb
    · have hf : isValidReverse s i = false := by
        cases hv : isValidReverse s i with
        | true => simp [hv] at hb
        | false => rfl
      unfold step at hOk
      simp [hf] at hOk
  have hMemDec : decide (i ∈ ids s.journal) = true := by
    have hC1 : (ids s.journal).contains i = true := by
      have hh := hValid
      unfold isValidReverse at hh
      simp only [Bool.and_eq_true] at hh
      exact hh.left
    simpa [List.contains_eq_mem] using hC1
  have hMem : i ∈ ids s.journal := of_decide_eq_true hMemDec
  obtain ⟨e, hFind⟩ := exists_findEntry_of_mem_ids2 hMem
  have hStep : step s (Command.reverse i) =
    (Outcome.ok, ({ s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed } : State)) := by
    unfold step; simp [hValid, hFind]
  let s1 : State := { s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed }
  have hs1_eq : (step s (Command.reverse i)).2 = s1 := by rw [hStep]
  have hRevFalse_s1 : isValidReverse s1 i = false := by simp [isValidReverse, s1]
  have hStep2 : step s1 (Command.reverse i) = (Outcome.rejected, s1) := by
    unfold step; simp [hRevFalse_s1]
  have hGoal : step (step s (Command.reverse i)).2 (Command.reverse i) = (Outcome.rejected, (step s (Command.reverse i)).2) := by
    rw [hs1_eq, hStep2]
  exact hGoal

theorem req_roundtrip : RoundTrip step := by
  intro s e hOk
  have hIR_post : isValidPost s e = true := by
    by_cases hb : isValidPost s e = true
    · exact hb
    · have hf : isValidPost s e = false := by cases hv:isValidPost s e <;> simp_all
      unfold step at hOk; simp [hf] at hOk
  have hStepPost : step s (Command.post e) =
    (Outcome.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by
    unfold step; simp [hIR_post]
  have hPostLines : ∀ (ls : List Line) (bal : AccountId → Int) (a : AccountId),
    postLines ls bal a = bal a + netOf ls a := by
    intro ls bal a
    induction ls generalizing bal with
    | nil => simp [postLines, netOf]
    | cons h t ih =>
      simp only [postLines]
      have h1 : adjust bal h.1 h.2 a = bal a + (if h.1 = a then h.2 else 0) := by
        unfold adjust; by_cases heq : a = h.1
        · subst heq; simp
        · have hne : h.1 ≠ a := fun hh => heq hh.symm
          simp [hne, heq]
      have h2 : netOf (h :: t) a = (if h.1 = a then h.2 else 0) + netOf t a := by simp [netOf]
      rw [ih, h1, h2]; omega
  let s' := (step s (Command.post e)).2
  have hs'Eq : s' = { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } := by
    show (step s (Command.post e)).2 = _; rw [hStepPost]
  have hs'_reversed : s'.reversed = s.reversed := by rw [hs'Eq]
  have hs'_balance : ∀ a, s'.balance a = s.balance a + netOf e.lines a := by
    intro a; rw [hs'Eq]; simp [hPostLines]
  have hs'_journal : s'.journal = s.journal ++ [e] := by rw [hs'Eq]
  have hMemIds_s' : e.id ∈ ids s'.journal := by
    rw [hs'_journal]; simp [ids]
  have hNotRev_s' : e.id ∉ s'.reversed := by
    rw [hs'_reversed]
    unfold isValidPost at hIR_post
    simp only [Bool.and_eq_true] at hIR_post
    have hF := hIR_post.2
    simp [List.contains_eq_mem] at hF
    exact hF
  have hIR_rev : isValidReverse s' e.id = true := by
    unfold isValidReverse
    simp [List.contains_eq_mem, hMemIds_s', hNotRev_s']
  have hNotInJ : e.id ∉ ids s.journal := by
    unfold isValidPost at hIR_post
    simp only [Bool.and_eq_true] at hIR_post
    have hE := hIR_post.1.2; simp [List.contains_eq_mem] at hE; exact hE
  have hFind : findEntry s'.journal e.id = some e := by
    rw [hs'_journal]
    have key : ∀ (j : List Entry), e.id ∉ ids j → findEntry (j ++ [e]) e.id = some e := by
      intro j
      induction j with
      | nil => intro _; simp [findEntry]
      | cons hd tl ih =>
        intro hNot
        have hne : hd.id ≠ e.id := by
          intro hEq
          have : e.id ∈ ids (hd :: tl) := by
            show e.id ∈ (ids (hd :: tl))
            rw [show ids (hd :: tl) = hd.id :: ids tl from rfl]
            simp [hEq]
          exact hNot this
        simp only [List.cons_append, findEntry, hne, ↓reduceIte]
        apply ih
        intro hMem
        have : e.id ∈ ids (hd :: tl) := by
          show e.id ∈ (ids (hd :: tl))
          rw [show ids (hd :: tl) = hd.id :: ids tl from rfl]
          exact List.Mem.tail _ hMem
        exact hNot this
    exact key s.journal hNotInJ
  have hStepRev : step s' (Command.reverse e.id) =
    (Outcome.ok, { s' with balance := fun a => s'.balance a - netOf e.lines a, journal := s'.journal, reversed := e.id :: s'.reversed }) := by
    unfold step; simp [hIR_rev, hFind]
  refine ⟨?_, ?_⟩
  · rw [hStepRev]
  · funext a
    have hBalS' : s'.balance a = s.balance a + netOf e.lines a := hs'_balance a
    have hBalS'' : (step s' (Command.reverse e.id)).2.balance a = s'.balance a - netOf e.lines a := by
      rw [hStepRev]
    rw [hBalS'', hBalS']
    simp

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hOk
  have hAccNodup : s.accounts.Nodup := hwf.1
  cases c with
  | post e =>
    unfold step at hOk
    have hValid : isValidPost s e = true := by
      by_cases hb : isValidPost s e = true
      · exact hb
      · have hf : isValidPost s e = false := by
          cases hc : isValidPost s e with
          | true => simp [hc] at hb
          | false => rfl
        simp [hf] at hOk
    have hStepEq : step s (Command.post e) =
      (Outcome.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by
      unfold step; simp [hValid]
    have hPostLines : ∀ (ls : List Line) (bal : AccountId → Int) (a : AccountId),
      postLines ls bal a = bal a + netOf ls a := by
      intro ls bal a
      induction ls generalizing bal with
      | nil => simp [postLines, netOf]
      | cons h t ih =>
        simp only [postLines]
        have h1 : adjust bal h.1 h.2 a = bal a + (if h.1 = a then h.2 else 0) := by
          unfold adjust; by_cases heq : a = h.1
          · subst heq; simp
          · have hne : h.1 ≠ a := fun hh => heq hh.symm
            simp [hne, heq]
        have h2 : netOf (h :: t) a = (if h.1 = a then h.2 else 0) + netOf t a := by simp [netOf]
        rw [ih, h1, h2]; omega
    have hLineSum0 : lineSum e.lines = 0 := by
      unfold isValidPost at hValid
      simp only [Bool.and_eq_true] at hValid
      have hD := hValid.1.1.2
      simp at hD; exact hD
    have hMemAcc : ∀ l ∈ e.lines, l.1 ∈ s.accounts := by
      unfold isValidPost at hValid
      simp only [Bool.and_eq_true] at hValid
      have hB := hValid.1.1.1.1.2
      intro l hl
      have hAll : ∀ x ∈ e.lines, s.accounts.contains x.1 = true := fun x hx => List.all_eq_true.mp hB x hx
      have hm := hAll l hl
      simp [List.contains_eq_mem] at hm; exact hm
    have hBalEq : ∀ a, (step s (Command.post e)).2.balance a = s.balance a + netOf e.lines a := by
      intro a; rw [hStepEq]; simp [hPostLines]
    have hAccEq : (step s (Command.post e)).2.accounts = s.accounts := by rw [hStepEq]
    show total (step s (Command.post e)).2 = total s
    unfold total
    rw [hAccEq]
    have hCon : sumOver s.accounts ((step s (Command.post e)).2.balance) =
                sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
      apply sumOver_congr; intro a _; exact hBalEq a
    rw [hCon, sumOver_add, sumOver_netOf_eq_lineSum_aux2 s.accounts hAccNodup e.lines hMemAcc, hLineSum0]
    simp
  | reverse i =>
    unfold step at hOk
    have hValid : isValidReverse s i = true := by
      by_cases hb : isValidReverse s i = true
      · exact hb
      · have hf : isValidReverse s i = false := by
          cases hc : isValidReverse s i with
          | true => simp [hc] at hb
          | false => rfl
        simp [hf] at hOk
    have hMemIds : i ∈ ids s.journal := by
      unfold isValidReverse at hValid
      simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hValid
      exact hValid.1
    obtain ⟨e, hFind⟩ := exists_findEntry_of_mem_ids2 hMemIds
    have hStepEq : step s (Command.reverse i) =
      (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := i :: s.reversed }) := by
      unfold step; simp [hValid, hFind]
    have hAccEq : (step s (Command.reverse i)).2.accounts = s.accounts := by rw [hStepEq]
    have hBalEq : ∀ a, (step s (Command.reverse i)).2.balance a = s.balance a - netOf e.lines a := by
      intro a; rw [hStepEq]
    have hMemJ : e ∈ s.journal := mem_journal_of_findEntry2 hFind
    have hWFEntries : ∀ e ∈ s.journal, (∀ l ∈ e.lines, l.1 ∈ s.accounts) ∧ lineSum e.lines = 0 := hwf.2.2.2
    have hEntryWF := hWFEntries e hMemJ
    have hMemAcc : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hEntryWF.1
    have hLineSum0 : lineSum e.lines = 0 := hEntryWF.2
    show total (step s (Command.reverse i)).2 = total s
    unfold total
    rw [hAccEq]
    have hCon : sumOver s.accounts ((step s (Command.reverse i)).2.balance) =
                sumOver s.accounts (fun a => s.balance a - netOf e.lines a) := by
      apply sumOver_congr; intro a _; exact hBalEq a
    rw [hCon, sumOver_sub, sumOver_netOf_eq_lineSum_aux2 s.accounts hAccNodup e.lines hMemAcc, hLineSum0]
    simp

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  cases c with
  | post ep =>
    by_cases hV : isValidPost s ep = true
    · have hStep : step s (Command.post ep) = (Outcome.ok, { s with balance := postLines ep.lines s.balance, journal := s.journal ++ [ep] }) := by
        unfold step; simp [hV]
      have h2 : (step s (Command.post ep)).2 = { s with balance := postLines ep.lines s.balance, journal := s.journal ++ [ep] } := by rw [hStep]
      rw [h2]
      obtain ⟨hNodupAcc, hNodupIds, hRevSub, hEntriesWF⟩ := hwf
      refine ⟨hNodupAcc, ?_, ?_, ?_⟩
      · have hNotIn : ep.id ∉ ids s.journal := by
          unfold isValidPost at hV
          simp only [Bool.and_eq_true] at hV
          have := hV.1.2
          simp [List.contains_eq_mem] at this
          exact this
        have hIdsEq : ids (s.journal ++ [ep]) = ids s.journal ++ [ep.id] := by
          unfold ids; simp
        rw [hIdsEq]
        rw [List.nodup_append]
        refine ⟨hNodupIds, ?_, ?_⟩
        · simp
        · intro x hx y hy
          simp at hy; subst hy
          intro hEq
          subst hEq
          exact hNotIn hx
      · intro i hi
        have hIn := hRevSub i hi
        have hIdsEq : ids (s.journal ++ [ep]) = ids s.journal ++ [ep.id] := by unfold ids; simp
        rw [hIdsEq]
        exact List.mem_append.mpr (Or.inl hIn)
      · intro ee hee
        rcases List.mem_append.mp hee with hOld | hNew
        · exact hEntriesWF ee hOld
        · simp at hNew
          have heq : ee = ep := hNew
          rw [heq]
          have hAllContains : List.all ep.lines (fun (l : Line) => s.accounts.contains l.1) = true := by
            have hh := hV
            unfold isValidPost at hh
            simp only [Bool.and_eq_true] at hh
            exact hh.1.1.1.1.2
          have hDecLineSum : decide (lineSum ep.lines = 0) = true := by
            have hh := hV
            unfold isValidPost at hh
            simp only [Bool.and_eq_true] at hh
            exact hh.1.1.2
          have hSum : lineSum ep.lines = 0 := by simp at hDecLineSum; exact hDecLineSum
          refine ⟨?_, hSum⟩
          intro l hl
          have hall : ∀ x ∈ ep.lines, s.accounts.contains x.1 = true := by
            intro x hx
            exact List.all_eq_true.mp hAllContains x hx
          have hm := hall l hl
          simp [List.contains_eq_mem] at hm
          exact hm
    · have hF : isValidPost s ep = false := by cases hv:isValidPost s ep <;> simp_all
      have hStep : step s (Command.post ep) = (Outcome.rejected, s) := by unfold step; simp [hF]
      have h2 : (step s (Command.post ep)).2 = s := by rw [hStep]
      rw [h2]; exact hwf
  | reverse i =>
    by_cases hV : isValidReverse s i = true
    · have hMem : i ∈ ids s.journal := by
        have hh := hV; unfold isValidReverse at hh; simp [Bool.and_eq_true, List.contains_eq_mem] at hh; exact hh.1
      obtain ⟨e', hFind⟩ := exists_findEntry_of_mem_ids2 hMem
      have hStep : step s (Command.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e'.lines a, journal := s.journal, reversed := i :: s.reversed }) := by
        unfold step; simp [hV, hFind]
      have h2 : (step s (Command.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e'.lines a, journal := s.journal, reversed := i :: s.reversed } := by rw [hStep]
      rw [h2]
      obtain ⟨hNodupAcc, hNodupIds, hRevSub, hEntriesWF⟩ := hwf
      refine ⟨hNodupAcc, hNodupIds, ?_, hEntriesWF⟩
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact hMem
      · exact hRevSub x hx
    · have hF : isValidReverse s i = false := by cases hv:isValidReverse s i <;> simp_all
      have hStep : step s (Command.reverse i) = (Outcome.rejected, s) := by unfold step; simp [hF]
      have h2 : (step s (Command.reverse i)).2 = s := by rw [hStep]
      rw [h2]; exact hwf

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hCons
  intro a
  cases c with
  | post e =>
    by_cases hV : isValidPost s e = true
    · have hStep : step s (Command.post e) = (Outcome.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by
        unfold step; simp [hV]
      have hPostLines : ∀ (ls : List Line) (bal : AccountId → Int) (x : AccountId),
          postLines ls bal x = bal x + netOf ls x := by
          intro ls bal x
          induction ls generalizing bal with
          | nil => simp [postLines, netOf]
          | cons hd tl ih =>
            simp only [postLines]
            have h1 : adjust bal hd.1 hd.2 x = bal x + (if hd.1 = x then hd.2 else 0) := by
              unfold adjust; by_cases heq : x = hd.1
              · subst heq; simp
              · have hne : hd.1 ≠ x := fun hh => heq hh.symm
                simp [hne, heq]
            have h2 : netOf (hd :: tl) x = (if hd.1 = x then hd.2 else 0) + netOf tl x := by simp [netOf]
            rw [ih, h1, h2]; omega
      have hBal : (step s (Command.post e)).2.balance = (fun x => s.balance x + netOf e.lines x) := by
        funext x; show (step s (Command.post e)).2.balance x = _; rw [hStep]; exact hPostLines e.lines s.balance x
      show (step s (Command.post e)).2.balance a = (step s (Command.post e)).2.opening a + activeNet (step s (Command.post e)).2 a
      rw [hBal]
      have hCons_a : s.balance a = s.opening a + activeNet s a := hCons a
      have hLHS : (fun x => s.balance x + netOf e.lines x) a = s.opening a + activeNet s a + netOf e.lines a := by simp [hCons_a]
      rw [hLHS]
      have hOpening : (step s (Command.post e)).2.opening = s.opening := by rw [hStep]
      rw [hOpening]
      have hActive : activeNet (step s (Command.post e)).2 a = activeNet s a + if e.id ∈ s.reversed then (0:Int) else netOf e.lines a := by
        have hJ : (step s (Command.post e)).2.journal = s.journal ++ [e] := by rw [hStep]
        have hR : (step s (Command.post e)).2.reversed = s.reversed := by rw [hStep]
        unfold activeNet; rw [hJ, hR, sumOver_append]
        have hOne : sumOver [e] (fun e' => if e'.id ∈ s.reversed then (0:Int) else netOf e'.lines a) = if e.id ∈ s.reversed then (0:Int) else netOf e.lines a := by simp
        rw [hOne]
      rw [hActive]
      have hNotRev : e.id ∉ s.reversed := by
        unfold isValidPost at hV; simp only [Bool.and_eq_true] at hV; have hF := hV.2; simp [List.contains_eq_mem] at hF; exact hF
      simp [hNotRev]; omega
    · have hF : isValidPost s e = false := by cases hv:isValidPost s e <;> simp_all
      have hStep : step s (Command.post e) = (Outcome.rejected, s) := by unfold step; simp [hF]
      have h2 : (step s (Command.post e)).2 = s := by rw [hStep]
      rw [h2]; exact hCons a
  | reverse i =>
    by_cases hV : isValidReverse s i = true
    · have hMemIds : i ∈ ids s.journal := by
        unfold isValidReverse at hV
        have hh : (ids s.journal).contains i = true ∧ (!s.reversed.contains i) = true := by
          simpa [Bool.and_eq_true] using hV
        have h1 := hh.1; simp [List.contains_eq_mem] at h1; exact h1
      have hNotRev : i ∉ s.reversed := by
        unfold isValidReverse at hV
        have hh : (ids s.journal).contains i = true ∧ (!s.reversed.contains i) = true := by
          simpa [Bool.and_eq_true] using hV
        have h2 := hh.2; simp [List.contains_eq_mem] at h2; exact h2
      obtain ⟨e, hFind⟩ := exists_findEntry_of_mem_ids2 hMemIds
      have hStep : step s (Command.reverse i) = (Outcome.ok, { s with balance := fun x => s.balance x - netOf e.lines x, journal := s.journal, reversed := i :: s.reversed }) := by unfold step; simp [hV, hFind]
      have hBal : (step s (Command.reverse i)).2.balance a = s.balance a - netOf e.lines a := by show (step s (Command.reverse i)).2.balance a = _; rw [hStep]
      have hOpening : (step s (Command.reverse i)).2.opening a = s.opening a := by show (step s (Command.reverse i)).2.opening a = _; rw [hStep]
      have hJ : (step s (Command.reverse i)).2.journal = s.journal := by rw [hStep]
      have hR : (step s (Command.reverse i)).2.reversed = i :: s.reversed := by rw [hStep]
      show (step s (Command.reverse i)).2.balance a = (step s (Command.reverse i)).2.opening a + activeNet (step s (Command.reverse i)).2 a
      rw [hBal, hOpening]
      have hCons_a : s.balance a = s.opening a + activeNet s a := hCons a
      have hActive : activeNet (step s (Command.reverse i)).2 a = activeNet s a - netOf e.lines a := by
        unfold activeNet; rw [hJ, hR]; have hNodup : (ids s.journal).Nodup := hwf.2.1; exact activeNet_reverse_lemma2 s.journal s.reversed i e hNodup hFind hNotRev a
      rw [hActive, hCons_a]; omega
    · have hF : isValidReverse s i = false := by cases hv:isValidReverse s i <;> simp_all
      have hStep : step s (Command.reverse i) = (Outcome.rejected, s) := by unfold step; simp [hF]
      have h2 : (step s (Command.reverse i)).2 = s := by rw [hStep]
      rw [h2]; exact hCons a

end Reversal
