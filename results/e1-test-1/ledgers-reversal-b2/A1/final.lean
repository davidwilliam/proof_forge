import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance
def adjust (bal : AccountId -> Int) (a : AccountId) (amt : Int) : AccountId -> Int :=
  fun b => if b = a then bal b + amt else bal b
def postLines : List Line -> (AccountId -> Int) -> (AccountId -> Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)
def negLines (ls : List Line) : List Line := ls.map (fun l => (l.1, -(l.2)))
def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | none => (.rejected, s)
    | some e => if decide (i ∈ s.reversed) then (.rejected, s) else (.ok, { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed })

theorem findEntry_some_of_mem_ids_aux4 : ∀ (j : List Entry) (i : EntryId), i ∈ ids j → ∃ e, findEntry j i = some e := by
  intro j
  induction j with
  | nil => intro i h; simp [ids] at h
  | cons e es ih =>
    intro i h
    simp only [ids, List.map_cons, List.mem_cons] at h
    by_cases he : e.id = i
    · subst he
      exact ⟨e, by simp [findEntry]⟩
    · have hm : i ∈ ids es := by
        cases h with
        | inl hl => exact absurd hl.symm he
        | inr hr => exact hr
      obtain ⟨e', he'⟩ := ih i hm
      exact ⟨e', by simp [findEntry, he, he']⟩

theorem findEntry_none_of_not_mem_aux : ∀ (j : List Entry) (i : EntryId), i ∉ ids j → findEntry j i = none := by
  intro j
  induction j with
  | nil => intro i _; rfl
  | cons e es ih =>
    intro i h
    simp only [ids, List.map_cons, List.mem_cons] at h
    have he : ¬ e.id = i := fun heq => h (Or.inl heq.symm)
    have ht : i ∉ ids es := fun hm => h (Or.inr hm)
    simp [findEntry, he, ih i ht]

theorem findEntry_some_mem_aux3 : ∀ (j : List Entry) (i : EntryId) (e : Entry), findEntry j i = some e → i ∈ ids j := by
  intro j
  induction j with
  | nil => intro i e h; simp [findEntry] at h
  | cons e0 es ih =>
    intro i e h
    simp only [findEntry] at h
    by_cases he : e0.id = i
    · subst he; simp [ids]
    · simp [he] at h
      have hm := ih i e h
      unfold ids at hm ⊢
      simp at hm ⊢
      exact Or.inr hm

theorem invalid_post_helper (s : State) (e : Entry) (h : ¬ Valid s (.post e)) : step s (.post e) = (.rejected, s) := by
  have h2 : ¬ ValidPost s e := h
  unfold step
  simp [h2]

theorem invalid_rev_test (s : State) (i : EntryId) (e : Entry) (he : findEntry s.journal i = some e) (hrev : i ∈ s.reversed) : step s (.reverse i) = (.rejected, s) := by
  simp [step, he, hrev]

theorem postLines_nil_check (bal : AccountId → Int) : postLines [] bal = bal := by rfl

theorem netOf_nil_check (a : AccountId) : netOf [] a = 0 := by rfl

theorem postLines_cons_check (l : Line) (ls : List Line) (bal : AccountId → Int) (a : AccountId) : postLines (l :: ls) bal a = postLines ls (adjust bal l.1 l.2) a := by rfl

theorem adjust_check (bal : AccountId → Int) (x : AccountId) (amt : Int) (a : AccountId) : adjust bal x amt a = (if a = x then bal a + amt else bal a) := by rfl

theorem netOf_cons_check (l : Line) (ls : List Line) (a : AccountId) : netOf (l :: ls) a = ((if l.1 = a then l.2 else 0) + netOf ls a) := by rfl

theorem postLines_neg_test : ∀ (l : Line) (ls : List Line), negLines (l :: ls) = (l.1, -l.2) :: negLines ls := by
  intro l ls; rfl

theorem neg_nil_test2 : negLines [] = ([] : List Line) := by rfl

theorem net_nil_test2 (a : AccountId) : netOf ([] : List Line) a = 0 := by rfl

theorem post_nil_test2 (bal : AccountId → Int) : postLines ([] : List Line) bal = bal := by rfl

theorem neg_cons_test2 (l : Line) (ls : List Line) : negLines (l :: ls) = (l.1, -l.2) :: negLines ls := by rfl

theorem post_cons_test2 (l : Line) (ls : List Line) (bal : AccountId → Int) : postLines (l :: ls) bal = postLines ls (adjust bal l.1 l.2) := by rfl

theorem postLines_neg_lemma3 : ∀ (ls : List Line) (bal : AccountId → Int) (a : AccountId), postLines (negLines ls) bal a = bal a - netOf ls a := by
  intro ls
  induction ls with
  | nil =>
    intro bal a
    have h1 : negLines ([] : List Line) = ([] : List Line) := rfl
    have h2 : postLines ([] : List Line) bal a = bal a := rfl
    have h3 : netOf ([] : List Line) a = 0 := rfl
    calc postLines (negLines []) bal a
        = bal a := by rw [h1, h2]
      _ = bal a - netOf [] a := by rw [h3]; omega
  | cons l ls ih =>
    intro bal a
    have hneg : negLines (l :: ls) = (l.1, -l.2) :: negLines ls := rfl
    have hpost : ∀ (x : Line) (xs : List Line) (b : AccountId → Int), postLines (x :: xs) b = postLines xs (adjust b x.1 x.2) := fun x xs b => rfl
    have hnet : netOf (l :: ls) a = ((if l.1 = a then l.2 else 0) + netOf ls a) := rfl
    calc postLines (negLines (l :: ls)) bal a
        = postLines (negLines ls) (adjust bal l.1 (-l.2)) a := by rw [hneg, hpost]
      _ = (adjust bal l.1 (-l.2)) a - netOf ls a := ih _ _
      _ = bal a - netOf (l :: ls) a := by
            have hadj : (adjust bal l.1 (-l.2)) a = (if a = l.1 then bal a + (-l.2) else bal a) := rfl
            rw [hadj, hnet]
            by_cases h : a = l.1
            · have h2 : l.1 = a := Eq.symm h
              rw [if_pos h, if_pos h2]; omega
            · have h2 : ¬ l.1 = a := fun contra => h (Eq.symm contra)
              rw [if_neg h, if_neg h2]; omega

theorem rev_not_mem_test (s : State) (i : EntryId) (e : Entry) (hfind : findEntry s.journal i = some e) (hok : (step s (.reverse i)).1 = .ok) : i ∉ s.reversed := by
  intro hmem
  have hr : (step s (.reverse i)).1 = .rejected := by simp [step, hfind, hmem]
  rw [hok] at hr
  exact absurd hr (by decide)

theorem rev_state_eq_test (s : State) (i : EntryId) (e : Entry) (hfind : findEntry s.journal i = some e) (hnot : i ∉ s.reversed) : (step s (.reverse i)).2 = { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } := by
  simp [step, hfind, hnot]

theorem req_reverse_once_aux_tmp : ReverseOnce step := by
  intro s i hok
  cases hE : findEntry s.journal i with
  | none => simp [step, hE] at hok
  | some e =>
    have hnot : i ∉ s.reversed := rev_not_mem_test s i e hE hok
    have hs2 := rev_state_eq_test s i e hE hnot
    have hJ : (step s (.reverse i)).2.journal = s.journal := by rw [hs2]
    have hR : i ∈ (step s (.reverse i)).2.reversed := by rw [hs2]; simp
    have hfind2 : findEntry (step s (.reverse i)).2.journal i = some e := by rw [hJ, hE]
    exact invalid_rev_test _ _ _ hfind2 hR

theorem postLines_add_helperRT : ∀ (ls : List Line) (bal : AccountId → Int) (a : AccountId), postLines ls bal a = bal a + netOf ls a := by
  intro ls
  induction ls with
  | nil =>
    intro bal a
    have h1 : postLines ([] : List Line) bal a = bal a := rfl
    have h2 : netOf ([] : List Line) a = 0 := rfl
    omega
  | cons l ls ih =>
    intro bal a
    have hpost : postLines (l :: ls) bal a = postLines ls (adjust bal l.1 l.2) a := rfl
    rw [hpost, ih]
    have hadj : (adjust bal l.1 l.2) a = (if a = l.1 then bal a + l.2 else bal a) := rfl
    rw [hadj]
    have hnet : netOf (l :: ls) a = ((if l.1 = a then l.2 else 0) + netOf ls a) := rfl
    rw [hnet]
    by_cases h : a = l.1
    · have h2 : l.1 = a := Eq.symm h
      rw [if_pos h, if_pos h2]; omega
    · have h2 : ¬ l.1 = a := fun contra => h (Eq.symm contra)
      rw [if_neg h, if_neg h2]; omega

theorem validPost_of_post_ok_RT (s : State) (e : Entry) (hok : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases hV : ValidPost s e
  · exact hV
  · have hr : (step s (.post e)).1 = .rejected := by simp [step, hV]
    rw [hok] at hr
    have hcontra : Outcome.ok = Outcome.rejected → False := by decide
    exact False.elim (hcontra hr)

theorem mem_ids_cons_test (e0 e : Entry) (es : List Entry) (h : e0.id = e.id) : e.id ∈ ids (e0 :: es) := by
  simp [ids, h.symm]

theorem mem_ids_cons_test2b (e0 : Entry) (es : List Entry) (e : Entry) (hm : e.id ∈ ids es) : e.id ∈ ids (e0 :: es) := by
  exact List.mem_cons.mpr (Or.inr hm)

theorem findEntry_append_single_RT (j : List Entry) (e : Entry) (hnin : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons e0 es ih =>
    have heq : ids (e0 :: es) = e0.id :: ids es := rfl
    have hne2 : e0.id ≠ e.id := by
      intro h
      apply hnin
      rw [heq]
      exact List.mem_cons.mpr (Or.inl h.symm)
    have hrest : e.id ∉ ids es := by
      intro hm
      apply hnin
      rw [heq]
      exact List.mem_cons.mpr (Or.inr hm)
    have hih := ih hrest
    calc findEntry ((e0 :: es) ++ [e]) e.id
        = findEntry (es ++ [e]) e.id := by simp [findEntry, hne2]
      _ = some e := hih

theorem sumOver_zero_aux : ∀ (l : List AccountId), sumOver l (fun _ => (0 : Int)) = 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem sum_net_eq_lineSum_aux : ∀ (ls : List Line) (accs : List AccountId),
    (∀ l ∈ ls, l.1 ∈ accs) → accs.Nodup → sumOver accs (fun a => netOf ls a) = lineSum ls := by
  intro ls
  induction ls with
  | nil =>
    intro accs _ _
    have h1 : ∀ a ∈ accs, netOf ([] : List Line) a = (0 : Int) := by intro a _; rfl
    have := sumOver_congr accs (fun a => netOf ([] : List Line) a) (fun _ => (0 : Int)) h1
    rw [this, sumOver_zero_aux]
    rfl
  | cons l ls ih =>
    intro accs hmem hnodu
    have hhead : l.1 ∈ accs := hmem l (by simp)
    have htail : ∀ l' ∈ ls, l'.1 ∈ accs := fun l' hl' => hmem l' (by simp [hl'])
    have hsplit : sumOver accs (fun a => netOf (l :: ls) a) = sumOver accs (fun a => (if l.1 = a then l.2 else 0)) + sumOver accs (fun a => netOf ls a) := by
      have hcongr : ∀ a ∈ accs, (netOf (l :: ls) a) = ((if l.1 = a then l.2 else 0) + netOf ls a) := fun a _ => rfl
      have h := sumOver_congr accs (fun a => netOf (l :: ls) a) (fun a => (if l.1 = a then l.2 else 0) + netOf ls a) hcongr
      rw [h]
      exact sumOver_add accs (fun a => (if l.1 = a then l.2 else 0)) (fun a => netOf ls a)
    rw [hsplit, ih accs htail hnodu]
    have hite : sumOver accs (fun a => (if l.1 = a then l.2 else 0)) = l.2 := by
      have hcongr2 : ∀ a ∈ accs, (if l.1 = a then l.2 else 0) = (if a = l.1 then l.2 else 0) := by
        intro a _
        by_cases h : l.1 = a
        · subst h; simp
        · have h2 : ¬ (a = l.1) := fun hh => h hh.symm
          simp [h, h2]
      have h := sumOver_congr accs (fun a => (if l.1 = a then l.2 else 0)) (fun a => (if a = l.1 then l.2 else 0)) hcongr2
      rw [h]
      have hh := sumOver_ite_eq hnodu l.1 l.2
      simp [hhead] at hh
      exact hh
    have hline_cons : lineSum (l :: ls) = l.2 + lineSum ls := rfl
    rw [hite, hline_cons]

theorem total_postLines_add_aux (accs : List AccountId) (bal : AccountId → Int) (ls : List Line)
    (hmem : ∀ l ∈ ls, l.1 ∈ accs) (hnodup : accs.Nodup) (hbal : lineSum ls = 0) :
    sumOver accs (fun a => bal a + netOf ls a) = sumOver accs bal := by
  have h := sumOver_add accs bal (fun a => netOf ls a)
  have hnet : sumOver accs (fun a => netOf ls a) = 0 := by
    rw [sum_net_eq_lineSum_aux ls accs hmem hnodup, hbal]
  -- rewrite
  have hcongr : ∀ a ∈ accs, (bal a + netOf ls a) = (bal a + netOf ls a) := fun a _ => rfl
  calc sumOver accs (fun a => bal a + netOf ls a)
      = sumOver accs bal + sumOver accs (fun a => netOf ls a) := by
        have := sumOver_add accs bal (fun a => netOf ls a)
        -- sumOver_add states sumOver (fun a => f a + g a) = sumOver f + sumOver g
        exact this
    _ = sumOver accs bal := by rw [hnet, Int.add_zero]

theorem total_postLines_sub_aux (accs : List AccountId) (bal : AccountId → Int) (ls : List Line)
    (hmem : ∀ l ∈ ls, l.1 ∈ accs) (hnodup : accs.Nodup) (hbal : lineSum ls = 0) :
    sumOver accs (fun a => bal a - netOf ls a) = sumOver accs bal := by
  have h := sumOver_sub accs bal (fun a => netOf ls a)
  have hnet : sumOver accs (fun a => netOf ls a) = 0 := by
    rw [sum_net_eq_lineSum_aux ls accs hmem hnodup, hbal]
  calc sumOver accs (fun a => bal a - netOf ls a)
      = sumOver accs bal - sumOver accs (fun a => netOf ls a) := sumOver_sub accs bal (fun a => netOf ls a)
    _ = sumOver accs bal := by rw [hnet, Int.sub_zero]

theorem findEntry_mem_aux (j : List Entry) (i : EntryId) (e : Entry) (h : findEntry j i = some e) : e ∈ j ∧ e.id = i := by
  induction j with
  | nil => simp [findEntry] at h
  | cons e0 es ih =>
    simp only [findEntry] at h
    by_cases he : e0.id = i
    · simp [he] at h
      subst h
      exact ⟨by simp, he⟩
    · simp [he] at h
      obtain ⟨hmem, hid⟩ := ih h
      exact ⟨List.mem_cons.mpr (Or.inr hmem), hid⟩

theorem wf_entry_balanced_aux (s : State) (i : EntryId) (e : Entry) (hwf : WellFormed s) (hfind : findEntry s.journal i = some e) : (∀ l ∈ e.lines, l.1 ∈ s.accounts) ∧ lineSum e.lines = 0 := by
  obtain ⟨hmem, _⟩ := findEntry_mem_aux s.journal i e hfind
  obtain ⟨_, _, _, hbal⟩ := hwf
  exact hbal e hmem

theorem wf_nodup_accounts_aux (s : State) (hwf : WellFormed s) : s.accounts.Nodup := hwf.1

theorem wfAux_nodup_singleton2 (l : List EntryId) (x : EntryId) (hN : l.Nodup) (hNin : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil =>
    simp
  | cons a t ih =>
    have hN1 : a ∉ t := (List.nodup_cons.mp hN).1
    have hN2 : t.Nodup := (List.nodup_cons.mp hN).2
    have hNinT : x ∉ t := fun hm => hNin (List.mem_cons.mpr (Or.inr hm))
    have ihH := ih hN2 hNinT
    have hNe : a ≠ x := by
      intro heq
      subst heq
      exact hNin (List.mem_cons.mpr (Or.inl rfl))
    have hNotMem : a ∉ t ++ [x] := by
      intro hmem
      rw [List.mem_append] at hmem
      cases hmem with
      | inl hlt => exact hN1 hlt
      | inr hr =>
        rw [List.mem_singleton] at hr
        exact hNe hr
    have heq : (a :: t) ++ [x] = a :: (t ++ [x]) := rfl
    rw [heq, List.nodup_cons]
    exact ⟨hNotMem, ihH⟩

theorem wfAux_ids_append2 (j : List Entry) (e : Entry) : ids (j ++ [e]) = ids j ++ [e.id] := by
  simp [ids]

theorem activeNet_post_eq_aux (j : List Entry) (r : List EntryId) (e : Entry) (h : e.id ∉ r) (a : AccountId) :
    sumOver (j ++ [e]) (fun e' => if e'.id ∈ r then (0 : Int) else netOf e'.lines a)
    = sumOver j (fun e' => if e'.id ∈ r then (0 : Int) else netOf e'.lines a) + netOf e.lines a := by
  rw [sumOver_append]
  simp only [sumOver_cons, sumOver_nil]
  simp [h]

theorem activeNet_reverse_diff_aux : ∀ (j : List Entry) (r : List EntryId) (i : EntryId) (e : Entry) (a : AccountId),
    (ids j).Nodup → i ∉ r → findEntry j i = some e →
    sumOver j (fun e' => if e'.id ∈ (i :: r) then (0 : Int) else netOf e'.lines a)
    = sumOver j (fun e' => if e'.id ∈ r then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  intro j
  induction j with
  | nil =>
    intro r i e a _ _ hfind
    simp [findEntry] at hfind
  | cons e0 es ih =>
    intro r i e a hnod hnot hfind
    simp only [findEntry] at hfind
    have hnod2 : (e0.id :: ids es).Nodup := by simpa [ids] using hnod
    rw [List.nodup_cons] at hnod2
    obtain ⟨hnotin, hnod_tail⟩ := hnod2
    by_cases heq : e0.id = i
    · have hee : e0 = e := by simpa [heq] using hfind
      subst hee
      simp only [sumOver_cons]
      have hnot' : e0.id ∉ r := by rw [heq]; exact hnot
      have hhead_old : (if e0.id ∈ r then (0 : Int) else netOf e0.lines a) = netOf e0.lines a :=
        if_neg hnot'
      have hhead_new : (if e0.id ∈ (i :: r) then (0 : Int) else netOf e0.lines a) = (0 : Int) := by
        have hm : e0.id ∈ (i :: r) := by simp [heq]
        exact if_pos hm
      rw [hhead_old, hhead_new]
      have htail_eq : sumOver es (fun e' => if e'.id ∈ (i :: r) then (0 : Int) else netOf e'.lines a)
          = sumOver es (fun e' => if e'.id ∈ r then (0 : Int) else netOf e'.lines a) := by
        apply sumOver_congr
        intro e' he'
        have hmem : e'.id ∈ ids es := List.mem_map.mpr ⟨e', he', rfl⟩
        have hne : e'.id ≠ i := by
          intro hcon
          apply hnotin
          have hEq : e'.id = e0.id := by rw [hcon, ← heq]
          exact hEq ▸ hmem
        have hmem_iff : (e'.id ∈ (i :: r)) ↔ (e'.id ∈ r) := by
          simp only [List.mem_cons]
          constructor
          · intro h
            cases h with
            | inl hl => exact absurd hl hne
            | inr hr => exact hr
          · intro h; exact Or.inr h
        by_cases hm : e'.id ∈ r
        · have hm2 : e'.id ∈ (i :: r) := hmem_iff.mpr hm
          simp [hm, hm2]
        · have hm2 : e'.id ∉ (i :: r) := fun hcon => hm (hmem_iff.mp hcon)
          simp [hm, hm2]
      rw [htail_eq]
      omega
    · have hfind_tail : findEntry es i = some e := by simpa [heq] using hfind
      simp only [sumOver_cons]
      have h0eq : (if e0.id ∈ (i :: r) then (0 : Int) else netOf e0.lines a)
          = (if e0.id ∈ r then (0 : Int) else netOf e0.lines a) := by
        have hiff : (e0.id ∈ (i :: r)) ↔ (e0.id ∈ r) := by
          simp only [List.mem_cons]
          constructor
          · intro h
            cases h with
            | inl hl => exact absurd hl heq
            | inr hr => exact hr
          · intro h; exact Or.inr h
        by_cases hm : e0.id ∈ r
        · have hm2 : e0.id ∈ (i :: r) := List.mem_cons.mpr (Or.inr hm)
          simp [hm, hm2]
        · have hm2 : e0.id ∉ (i :: r) := by
            intro hcon; rw [hiff] at hcon; exact hm hcon
          simp [hm, hm2]
      rw [h0eq]
      have hih := ih r i e a hnod_tail hnot hfind_tail
      omega

theorem req_post_succeeds    : PostSucceeds step := by
  intro s e h
  unfold step
  simp [h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  obtain ⟨hmem, hnot⟩ := h
  obtain ⟨e, he⟩ := findEntry_some_of_mem_ids_aux4 s.journal i hmem
  have : (step s (.reverse i)).1 = .ok := by simp [step, he, hnot]
  exact this

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    have hV : ¬ ValidPost s e := h
    unfold step
    simp [hV]
  | reverse i =>
    cases hE : findEntry s.journal i with
    | none =>
      have : step s (.reverse i) = (.rejected, s) := by simp [step, hE]
      exact this
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · have : step s (.reverse i) = (.rejected, s) := by simp [step, hE, hmem]
        exact this
      · have hids : i ∈ ids s.journal := findEntry_some_mem_aux3 s.journal i e hE
        have hValid : Valid s (.reverse i) := ⟨hids, hmem⟩
        exact False.elim (h hValid)

theorem req_post_effects : PostEffects step := by
  intro s e hok
  have hV : ValidPost s e := validPost_of_post_ok_RT s e hok
  have hs : step s (.post e) = (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] }) := by
    simp [step, hV]
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
    have : (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by
      rw [hs]
      exact postLines_add_helperRT e.lines s.balance a
    exact this

theorem req_reverse_effects  : ReverseEffects step := by
  intro s i e hok hfind
  have hnot : i ∉ s.reversed := rev_not_mem_test s i e hfind hok
  have hs2 : (step s (.reverse i)).2 = { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } := rev_state_eq_test s i e hfind hnot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs2]
  · rw [hs2]
  · rw [hs2]
  · intro x
    rw [hs2]
    simp
  · intro a
    rw [hs2]
    exact postLines_neg_lemma3 e.lines s.balance a

theorem req_reverse_once     : ReverseOnce step := by
  exact req_reverse_once_aux_tmp

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hV : ValidPost s e := validPost_of_post_ok_RT s e hok
  have hs1eq : (step s (.post e)).2 = ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State) := by
    unfold step
    simp [hV]
  have hmem_ids : e.id ∈ ids ((step s (.post e)).2.journal) := by
    rw [hs1eq]
    simp [ids]
  have hnotrev : e.id ∉ (step s (.post e)).2.reversed := by
    rw [hs1eq]
    show e.id ∉ s.reversed
    exact hV.2.2.2.2.2
  have hValidRev : ValidReverse (step s (.post e)).2 e.id := ⟨hmem_ids, hnotrev⟩
  have hok2 : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok :=
    req_reverse_succeeds _ _ hValidRev
  refine ⟨hok2, ?_⟩
  have hfind : findEntry (step s (.post e)).2.journal e.id = some e := by
    rw [hs1eq]
    show findEntry (s.journal ++ [e]) e.id = some e
    exact findEntry_append_single_RT s.journal e hV.2.2.2.2.1
  have heff := req_reverse_effects (step s (.post e)).2 e.id e hok2 hfind
  obtain ⟨_, _, _, _, hbal2⟩ := heff
  have hbal1 : ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by
    intro a
    rw [hs1eq]
    show postLines e.lines s.balance a = s.balance a + netOf e.lines a
    exact postLines_add_helperRT e.lines s.balance a
  have heach : ∀ a, (step (step s (.post e)).2 (.reverse e.id)).2.balance a = s.balance a := by
    intro a
    rw [hbal2 a, hbal1 a]
    omega
  funext a
  exact heach a

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  cases c with
  | post e =>
    have hV : ValidPost s e := validPost_of_post_ok_RT s e hok
    have hs2 : (step s (.post e)).2 = { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } := by
      unfold step
      simp [hV]
    have hmem : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hV.2.1
    have hbal : lineSum e.lines = 0 := hV.2.2.2.1
    have hnod : s.accounts.Nodup := hwf.1
    have hpt : ∀ a, (postLines e.lines s.balance) a = s.balance a + netOf e.lines a := fun a => postLines_add_helperRT e.lines s.balance a
    have htot : sumOver s.accounts (fun a => postLines e.lines s.balance a) = sumOver s.accounts s.balance := by
      have hc := sumOver_congr s.accounts (fun a => postLines e.lines s.balance a) (fun a => s.balance a + netOf e.lines a) (fun a _ => hpt a)
      rw [hc]
      exact total_postLines_add_aux s.accounts s.balance e.lines hmem hnod hbal
    calc total (step s (.post e)).2
        = sumOver s.accounts (fun a => postLines e.lines s.balance a) := by rw [hs2]; rfl
      _ = sumOver s.accounts s.balance := htot
      _ = total s := rfl
  | reverse i =>
    cases hE : findEntry s.journal i with
    | none =>
      have hr : (step s (.reverse i)).1 = .rejected := by simp [step, hE]
      rw [hr] at hok
      exact absurd hok (by decide)
    | some e =>
      have hnot : i ∉ s.reversed := rev_not_mem_test s i e hE hok
      have hs2 : (step s (.reverse i)).2 = { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } := rev_state_eq_test s i e hE hnot
      obtain ⟨hmem, hbal⟩ := wf_entry_balanced_aux s i e hwf hE
      have hnod : s.accounts.Nodup := hwf.1
      have hpt : ∀ a, (postLines (negLines e.lines) s.balance) a = s.balance a - netOf e.lines a := fun a => postLines_neg_lemma3 e.lines s.balance a
      have htot : sumOver s.accounts (fun a => postLines (negLines e.lines) s.balance a) = sumOver s.accounts s.balance := by
        have hc := sumOver_congr s.accounts (fun a => postLines (negLines e.lines) s.balance a) (fun a => s.balance a - netOf e.lines a) (fun a _ => hpt a)
        rw [hc]
        exact total_postLines_sub_aux s.accounts s.balance e.lines hmem hnod hbal
      calc total (step s (.reverse i)).2
          = sumOver s.accounts (fun a => postLines (negLines e.lines) s.balance a) := by rw [hs2]; rfl
        _ = sumOver s.accounts s.balance := htot
        _ = total s := rfl

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hs2 : (step s (.post e)).2 = { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } := by
        unfold step
        simp [hV]
      rw [hs2]
      obtain ⟨hAccNod, hJnod, hRevSub, hBal⟩ := hwf
      obtain ⟨hne, hmemAcc, hneZero, hsumZero, hnidJ, hnidR⟩ := hV
      have hid : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := wfAux_ids_append2 s.journal e
      refine ⟨?_, ?_, ?_, ?_⟩
      · show s.accounts.Nodup
        exact hAccNod
      · show (ids (s.journal ++ [e])).Nodup
        rw [hid]
        exact wfAux_nodup_singleton2 (ids s.journal) e.id hJnod hnidJ
      · intro i hi
        show i ∈ ids (s.journal ++ [e])
        rw [hid]
        apply List.mem_append.mpr
        apply Or.inl
        exact hRevSub i hi
      · intro e' he'
        have heApp : e' ∈ s.journal ++ [e] := he'
        rw [List.mem_append] at heApp
        cases heApp with
        | inl hm =>
          obtain ⟨hacc, hsum⟩ := hBal e' hm
          constructor
          · intro l hl
            exact hacc l hl
          · exact hsum
        | inr hm =>
          rw [List.mem_singleton] at hm
          subst hm
          constructor
          · exact hmemAcc
          · exact hsumZero
    · have h2 : (step s (.post e)).2 = s := by
        unfold step
        simp [hV]
      rw [h2]
      exact hwf
  | reverse i =>
    cases hE : findEntry s.journal i with
    | none =>
      have h2 : (step s (.reverse i)).2 = s := by
        simp [step, hE]
      rw [h2]
      exact hwf
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · have h2 : (step s (.reverse i)).2 = s := by
          simp [step, hE, hmem]
        rw [h2]
        exact hwf
      · have hs2 : (step s (.reverse i)).2 = { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } := by
          simp [step, hE, hmem]
        rw [hs2]
        obtain ⟨hAccNod, hJnod, hRevSub, hBal⟩ := hwf
        have hiMem : i ∈ ids s.journal := findEntry_some_mem_aux3 s.journal i e hE
        refine ⟨?_, ?_, ?_, ?_⟩
        · show s.accounts.Nodup
          exact hAccNod
        · show (ids s.journal).Nodup
          exact hJnod
        · intro x hx
          show x ∈ ids s.journal
          simp only [List.mem_cons] at hx
          cases hx with
          | inl heq => subst heq; exact hiMem
          | inr hr => exact hRevSub x hr
        · intro e' he'
          show ((∀ l ∈ e'.lines, l.1 ∈ s.accounts) ∧ lineSum e'.lines = 0)
          exact hBal e' he'

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hs2bal : ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by
        intro a
        unfold step
        simp only [hV]
        exact postLines_add_helperRT e.lines s.balance a
      have hs2open : (step s (.post e)).2.opening = s.opening := by
        unfold step; simp [hV]
      have hs2jour : (step s (.post e)).2.journal = s.journal ++ [e] := by
        unfold step; simp [hV]
      have hs2rev : (step s (.post e)).2.reversed = s.reversed := by
        unfold step; simp [hV]
      have hnotrev : e.id ∉ s.reversed := hV.2.2.2.2.2
      intro a
      have hold := hcons a
      have hnew_bal := hs2bal a
      have hopen : (step s (.post e)).2.opening a = s.opening a := by rw [hs2open]
      have hact : activeNet (step s (.post e)).2 a
          = activeNet s a + netOf e.lines a := by
        unfold activeNet
        rw [hs2jour, hs2rev]
        exact activeNet_post_eq_aux s.journal s.reversed e hnotrev a
      rw [hnew_bal, hold, hopen, hact]
      omega
    · have h2 : (step s (.post e)).2 = s := by unfold step; simp [hV]
      rw [h2]
      exact hcons
  | reverse i =>
    cases hE : findEntry s.journal i with
    | none =>
      have h2 : (step s (.reverse i)).2 = s := by simp [step, hE]
      rw [h2]
      exact hcons
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · have h2 : (step s (.reverse i)).2 = s := by simp [step, hE, hmem]
        rw [h2]
        exact hcons
      · have hnod : (ids s.journal).Nodup := hwf.2.1
        have hs2bal : ∀ a, (step s (.reverse i)).2.balance a = s.balance a - netOf e.lines a := by
          intro a
          have hs2 : (step s (.reverse i)).2 = { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } := by
            simp [step, hE, hmem]
          rw [hs2]
          exact postLines_neg_lemma3 e.lines s.balance a
        have hs2open : (step s (.reverse i)).2.opening = s.opening := by
          have hs2 : (step s (.reverse i)).2 = { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } := by
            simp [step, hE, hmem]
          rw [hs2]
        have hs2jour : (step s (.reverse i)).2.journal = s.journal := by
          have hs2 : (step s (.reverse i)).2 = { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } := by
            simp [step, hE, hmem]
          rw [hs2]
        have hs2rev : (step s (.reverse i)).2.reversed = i :: s.reversed := by
          have hs2 : (step s (.reverse i)).2 = { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } := by
            simp [step, hE, hmem]
          rw [hs2]
        intro a
        have hold := hcons a
        have hnew_bal := hs2bal a
        have hopen : (step s (.reverse i)).2.opening a = s.opening a := by rw [hs2open]
        have hact : activeNet (step s (.reverse i)).2 a
            = activeNet s a - netOf e.lines a := by
          unfold activeNet
          rw [hs2jour, hs2rev]
          exact activeNet_reverse_diff_aux s.journal s.reversed i e a hnod hmem hE
        rw [hnew_bal, hold, hopen, hact]
        omega

end Reversal
