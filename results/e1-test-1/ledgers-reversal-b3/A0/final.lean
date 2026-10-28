import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost
  infer_instance

def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)

def negLine (l : Line) : Line := (l.1, -l.2)

def negLines (ls : List Line) : List Line := ls.map negLine

def stepPost (s : State) (e : Entry) : Outcome × State :=
  if ValidPost s e then
    (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] })
  else (.rejected, s)

def stepRev (s : State) (i : EntryId) : Outcome × State :=
  match findEntry s.journal i with
  | some e =>
    if i ∈ s.reversed then (.rejected, s)
    else (.ok, { s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed })
  | none => (.rejected, s)

def step : Impl := fun s c =>
  match c with
  | .post e => stepPost s e
  | .reverse i => stepRev s i

theorem sumOver_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have h : sumOver (hd :: tl) (fun _ => (0 : Int)) = (0 : Int) + sumOver tl (fun _ => (0 : Int)) := rfl
    rw [h, ih]
    omega

theorem postLines_spec (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    postLines ls bal a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil =>
    have h1 : postLines ([] : List Line) bal a = bal a := rfl
    have h2 : netOf ([] : List Line) a = 0 := rfl
    rw [h1, h2]
    omega
  | cons hd tl ih =>
    have hEq : postLines (hd :: tl) bal a = postLines tl (adjust bal hd.1 hd.2) a := rfl
    rw [hEq, ih]
    have hnet : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := rfl
    rw [hnet]
    by_cases h : hd.1 = a
    · have ha : a = hd.1 := Eq.symm h
      have e1 : (adjust bal hd.1 hd.2) a = bal a + hd.2 := by unfold adjust; rw [if_pos ha]
      have e2 : (if hd.1 = a then hd.2 else (0 : Int)) = hd.2 := by rw [if_pos h]
      rw [e1, e2]
      omega
    · have ha : ¬ (a = hd.1) := fun hh => h hh.symm
      have e1 : (adjust bal hd.1 hd.2) a = bal a := by unfold adjust; rw [if_neg ha]
      have e2 : (if hd.1 = a then hd.2 else (0 : Int)) = 0 := by rw [if_neg h]
      rw [e1, e2]
      omega

theorem netOf_map_neg (ls : List Line) (a : AccountId) :
    netOf (negLines ls) a = - netOf ls a := by
  unfold negLines
  induction ls with
  | nil => rfl
  | cons hd tl ih =>
    have hh1 : negLine hd = (hd.1, -hd.2) := rfl
    have hmap : List.map negLine (hd :: tl) = negLine hd :: List.map negLine tl := rfl
    have h1 : netOf (List.map negLine (hd :: tl)) a =
      (if hd.1 = a then -hd.2 else 0) + netOf (List.map negLine tl) a := by
      rw [hmap]
      have hnet : netOf (negLine hd :: List.map negLine tl) a =
        (if (negLine hd).1 = a then (negLine hd).2 else 0) + netOf (List.map negLine tl) a := rfl
      rw [hnet, hh1]
    have h2 : netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := rfl
    rw [h1, h2, ih]
    by_cases h : hd.1 = a
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]; omega

theorem postLines_neg_spec (ls : List Line) (bal : AccountId → Int) (a : AccountId) :
    postLines (negLines ls) bal a = bal a - netOf ls a := by
  rw [postLines_spec, netOf_map_neg]
  omega

theorem findEntry_mem {j : List Entry} {i : EntryId} {e : Entry}
    (h : findEntry j i = some e) : e ∈ j ∧ e.id = i := by
  induction j with
  | nil =>
    have hEq : findEntry ([] : List Entry) i = none := rfl
    rw [hEq] at h
    contradiction
  | cons hd tl ih =>
    have hEq : findEntry (hd :: tl) i =
      (if hd.id = i then some hd else findEntry tl i) := rfl
    rw [hEq] at h
    by_cases heq : hd.id = i
    · rw [if_pos heq] at h
      have hhd : hd = e := Option.some_inj.mp h
      subst hhd
      constructor
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact heq
    · rw [if_neg heq] at h
      have hh := ih h
      obtain ⟨hmem, hid⟩ := hh
      exact ⟨List.mem_cons_of_mem hd hmem, hid⟩

theorem findEntry_is_none_of_not_mem {j : List Entry} {i : EntryId}
    (h : i ∉ ids j) : findEntry j i = none := by
  induction j with
  | nil => rfl
  | cons hd tl ih =>
    have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hids] at h
    have hhd : hd.id ≠ i := by
      intro heq
      apply h
      rw [heq]
      exact List.mem_cons.mpr (Or.inl rfl)
    have htl : i ∉ ids tl := by
      intro hmem
      apply h
      exact List.mem_cons_of_mem hd.id hmem
    have hEq : findEntry (hd :: tl) i =
      (if hd.id = i then some hd else findEntry tl i) := rfl
    rw [hEq, if_neg hhd]
    exact ih htl

theorem findEntry_some_of_mem {j : List Entry} {i : EntryId}
    (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil =>
    have hids : ids ([] : List Entry) = [] := rfl
    rw [hids] at h
    cases h
  | cons hd tl ih =>
    have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hids] at h
    have hEq : findEntry (hd :: tl) i =
      (if hd.id = i then some hd else findEntry tl i) := rfl
    by_cases heq : hd.id = i
    · rw [hEq, if_pos heq]
      exact ⟨hd, rfl⟩
    · rw [hEq, if_neg heq]
      have hmem : i ∈ ids tl := by
        cases (List.mem_cons.mp h) with
        | inl heq2 => exact absurd heq2.symm heq
        | inr hm => exact hm
      exact ih hmem

theorem findEntry_append_new {j : List Entry} {e : Entry}
    (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil =>
    have hApp : (([] : List Entry) ++ [e]) = [e] := rfl
    rw [hApp]
    have hIf : findEntry [e] e.id = (if e.id = e.id then some e else none) := rfl
    rw [hIf, if_pos rfl]
  | cons hd tl ih =>
    have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hids] at h
    have hhd : hd.id ≠ e.id := by
      intro heq
      apply h
      rw [heq]
      exact List.mem_cons.mpr (Or.inl rfl)
    have htl : e.id ∉ ids tl := by
      intro hmem
      apply h
      exact List.mem_cons_of_mem hd.id hmem
    have ih' := ih htl
    have hApp : ((hd :: tl) ++ [e]) = hd :: (tl ++ [e]) := rfl
    rw [hApp]
    have hEq : findEntry (hd :: (tl ++ [e])) e.id =
      (if hd.id = e.id then some hd else findEntry (tl ++ [e]) e.id) := rfl
    rw [hEq, if_neg hhd]
    exact ih'

theorem sum_net_eq_lineSum {accounts : List AccountId} {ls : List Line}
    (hnodup : accounts.Nodup) (hmem : ∀ l ∈ ls, l.1 ∈ accounts) :
    sumOver accounts (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have h1 : sumOver accounts (fun a => netOf ([] : List Line) a) =
        sumOver accounts (fun _ => (0 : Int)) := by
      apply sumOver_congr
      intro a _
      rfl
    rw [h1, sumOver_zero]
    rfl
  | cons hd tl ih =>
    have hhd : hd.1 ∈ accounts := hmem hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ l ∈ tl, l.1 ∈ accounts := fun l hl => hmem l (List.mem_cons_of_mem hd hl)
    have iht := ih htl
    have hnetcons : (fun a => netOf (hd :: tl) a) =
        (fun a => ((if hd.1 = a then hd.2 else (0 : Int)) + netOf tl a)) := by
      funext a
      rfl
    have hsplit : sumOver accounts (fun a => ((if hd.1 = a then hd.2 else (0 : Int)) + netOf tl a))
        = sumOver accounts (fun a => (if hd.1 = a then hd.2 else (0 : Int)))
          + sumOver accounts (fun a => netOf tl a) := by
      rw [← sumOver_add]
      apply sumOver_congr
      intro a _
      rfl
    have hite : sumOver accounts (fun a => (if hd.1 = a then hd.2 else (0 : Int)))
        = sumOver accounts (fun a => (if a = hd.1 then hd.2 else (0 : Int))) := by
      apply sumOver_congr
      intro a _
      by_cases hh : a = hd.1
      · have hh2 : hd.1 = a := hh.symm
        rw [if_pos hh, if_pos hh2]
      · have hh2 : ¬ (hd.1 = a) := fun hhh => hh hhh.symm
        rw [if_neg hh, if_neg hh2]
    have hline : lineSum (hd :: tl) = hd.2 + lineSum tl := rfl
    have hif : (if hd.1 ∈ accounts then hd.2 else (0 : Int)) = hd.2 := by rw [if_pos hhd]
    rw [hnetcons, hsplit, hite, sumOver_ite_eq hnodup hd.1 hd.2, hif, iht, hline]

theorem total_post_eq (s : State) (e : Entry) :
    total ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State)
      = total s + sumOver s.accounts (fun a => netOf e.lines a) := by
  have h1 : total ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State)
      = sumOver s.accounts (fun a => postLines e.lines s.balance a) := rfl
  have h2 : total s = sumOver s.accounts s.balance := rfl
  rw [h1, h2]
  have h3 : sumOver s.accounts (fun a => postLines e.lines s.balance a)
      = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := by
    rw [← sumOver_add]
    apply sumOver_congr
    intro a _
    rw [postLines_spec]
  exact h3

theorem total_rev_aux (s : State) (e : Entry) (i : EntryId) :
    total ({ s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } : State)
      = total s - sumOver s.accounts (fun a => netOf e.lines a) := by
  have h1 : total ({ s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } : State)
      = sumOver s.accounts (fun a => postLines (negLines e.lines) s.balance a) := rfl
  have h2 : total s = sumOver s.accounts s.balance := rfl
  rw [h1, h2]
  have h3 : sumOver s.accounts (fun a => postLines (negLines e.lines) s.balance a)
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => netOf e.lines a) := by
    rw [← sumOver_sub]
    apply sumOver_congr
    intro a _
    rw [postLines_neg_spec]
  exact h3

theorem activeNet_no_id (es : List Entry) (rev : List EntryId) (i : EntryId) (a : AccountId)
    (h : i ∉ ids es) :
    sumOver es (fun e => if e.id ∈ (i :: rev) then (0 : Int) else netOf e.lines a) =
    sumOver es (fun e => if e.id ∈ rev then (0 : Int) else netOf e.lines a) := by
  apply sumOver_congr
  intro e hmem
  have hne : e.id ≠ i := by
    intro heq
    apply h
    exact List.mem_map.mpr ⟨e, hmem, heq⟩
  by_cases hm : e.id ∈ rev
  · have hm2 : e.id ∈ (i :: rev) := List.mem_cons_of_mem i hm
    rw [if_pos hm2, if_pos hm]
  · have hm2 : e.id ∉ (i :: rev) := by
      intro hcon
      cases (List.mem_cons.mp hcon) with
      | inl hl => exact hne hl
      | inr hr => exact hm hr
    rw [if_neg hm2, if_neg hm]

theorem activeNet_reverse_aux (j : List Entry) (rev : List EntryId) (i : EntryId)
    (e : Entry) (a : AccountId)
    (hnodup : (ids j).Nodup) (hfind : findEntry j i = some e) (hnotrev : i ∉ rev) :
    sumOver j (fun e' => if e'.id ∈ (i :: rev) then (0 : Int) else netOf e'.lines a) =
    sumOver j (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  induction j with
  | nil =>
    have hEq : findEntry ([] : List Entry) i = none := rfl
    rw [hEq] at hfind
    contradiction
  | cons hd tl ih =>
    have hEq : findEntry (hd :: tl) i =
      (if hd.id = i then some hd else findEntry tl i) := rfl
    rw [hEq] at hfind
    by_cases heq : hd.id = i
    · rw [if_pos heq] at hfind
      subst hfind
      have h1 : hd.id ∉ ids tl := (List.nodup_cons.mp hnodup).1
      have hnotmem_tl : i ∉ ids tl := by
        intro hmem
        exact h1 (heq ▸ hmem)
      have hsc : sumOver (hd :: tl) (fun e' => if e'.id ∈ (i :: rev) then (0 : Int) else netOf e'.lines a)
        = (if hd.id ∈ (i :: rev) then (0 : Int) else netOf hd.lines a)
          + sumOver tl (fun e' => if e'.id ∈ (i :: rev) then (0 : Int) else netOf e'.lines a) := rfl
      have hsc2 : sumOver (hd :: tl) (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a)
        = (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a)
          + sumOver tl (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) := rfl
      rw [hsc, hsc2]
      have hmem_after : hd.id ∈ (i :: rev) := List.mem_cons.mpr (Or.inl heq)
      have hhead_after : (if hd.id ∈ (i :: rev) then (0 : Int) else netOf hd.lines a) = 0 := by
        rw [if_pos hmem_after]
      have hnm : hd.id ∉ rev := by rw [heq]; exact hnotrev
      have hhead_before : (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) = netOf hd.lines a := by
        rw [if_neg hnm]
      rw [hhead_after, hhead_before]
      have htail := activeNet_no_id tl rev i a hnotmem_tl
      omega
    · rw [if_neg heq] at hfind
      have htail_nodup : (ids tl).Nodup := (List.nodup_cons.mp hnodup).2
      have ih' := ih htail_nodup hfind
      have hsc : sumOver (hd :: tl) (fun e' => if e'.id ∈ (i :: rev) then (0 : Int) else netOf e'.lines a)
        = (if hd.id ∈ (i :: rev) then (0 : Int) else netOf hd.lines a)
          + sumOver tl (fun e' => if e'.id ∈ (i :: rev) then (0 : Int) else netOf e'.lines a) := rfl
      have hsc2 : sumOver (hd :: tl) (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a)
        = (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a)
          + sumOver tl (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) := rfl
      rw [hsc, hsc2]
      have hhead_eq : (if hd.id ∈ (i :: rev) then (0 : Int) else netOf hd.lines a)
          = (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) := by
        by_cases hm : hd.id ∈ rev
        · have hm2 : hd.id ∈ (i :: rev) := List.mem_cons_of_mem i hm
          rw [if_pos hm2, if_pos hm]
        · have hm2 : hd.id ∉ (i :: rev) := by
            intro hcon
            cases (List.mem_cons.mp hcon) with
            | inl hl => exact heq hl
            | inr hr => exact hm hr
          rw [if_neg hm2, if_neg hm]
      rw [hhead_eq, ih']
      omega

theorem nodup_append_single {l : List Nat} {a : Nat}
    (hl : l.Nodup) (ha : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil =>
    have hApp : (([] : List Nat) ++ [a]) = [a] := rfl
    rw [hApp]
    rw [List.nodup_cons]
    constructor
    · intro h
      cases h
    · exact List.nodup_nil
  | cons hd tl ih =>
    have hpair := (List.nodup_cons.mp hl)
    obtain ⟨h1, h2⟩ := hpair
    have ha_tl : a ∉ tl := fun hmem => ha (List.mem_cons_of_mem hd hmem)
    have iht := ih h2 ha_tl
    have hApp : ((hd :: tl) ++ [a]) = hd :: (tl ++ [a]) := rfl
    rw [hApp, List.nodup_cons]
    constructor
    · intro hmem
      have hmem2 : hd ∈ tl ++ [a] := hmem
      cases (List.mem_append.mp hmem2) with
      | inl h => exact h1 h
      | inr h =>
        have heq : hd = a := List.mem_singleton.mp h
        subst heq
        exact ha (List.mem_cons.mpr (Or.inl rfl))
    · exact iht

theorem ids_append_single (j : List Entry) (e : Entry) :
    ids (j ++ [e]) = ids j ++ [e.id] := by
  unfold ids
  rw [List.map_append]

theorem post_state_of_valid (s : State) (e : Entry) (h : ValidPost s e) :
    (step s (.post e)).2
      = ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State) := by
  have hP : stepPost s e =
    (Outcome.ok, ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State)) := by
    unfold stepPost
    rw [if_pos h]
  show (stepPost s e).2 = _
  rw [hP]

theorem post_fst_ok_of_valid (s : State) (e : Entry) (h : ValidPost s e) :
    (step s (.post e)).1 = .ok := by
  have hP : stepPost s e =
    (Outcome.ok, ({ s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] } : State)) := by
    unfold stepPost
    rw [if_pos h]
  show (stepPost s e).1 = _
  rw [hP]

theorem rev_state_of_valid (s : State) (i : EntryId) (e : Entry)
    (hfind : findEntry s.journal i = some e) (hnotrev : i ∉ s.reversed) :
    (step s (.reverse i)).2
      = ({ s with balance := postLines (negLines e.lines) s.balance, reversed := i :: s.reversed } : State) := by
  show (stepRev s i).2 = _
  unfold stepRev
  rw [hfind, if_neg hnotrev]

theorem rev_fst_ok_of_valid (s : State) (i : EntryId) (e : Entry)
    (hfind : findEntry s.journal i = some e) (hnotrev : i ∉ s.reversed) :
    (step s (.reverse i)).1 = .ok := by
  show (stepRev s i).1 = _
  unfold stepRev
  rw [hfind, if_neg hnotrev]

theorem get_valid_post_of_ok (s : State) (e : Entry)
    (hok : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases hv : ValidPost s e
  · exact hv
  · have hP : stepPost s e = (Outcome.rejected, s) := by
      unfold stepPost
      rw [if_neg hv]
    have hcon : (step s (.post e)).1 = .rejected := by
      show (stepPost s e).1 = _
      rw [hP]
    rw [hcon] at hok
    exact absurd hok (by decide)

theorem get_rev_info_of_ok (s : State) (i : EntryId)
    (hok : (step s (.reverse i)).1 = .ok) :
    ∃ e, findEntry s.journal i = some e ∧ i ∉ s.reversed := by
  have hcase : ∃ fe, findEntry s.journal i = fe := ⟨_, rfl⟩
  obtain ⟨fe, hfe⟩ := hcase
  cases fe with
  | none =>
    have hcon : (step s (.reverse i)).1 = .rejected := by
      show (stepRev s i).1 = _
      unfold stepRev
      rw [hfe]
    rw [hcon] at hok
    exact absurd hok (by decide)
  | some e =>
    by_cases hrev : i ∈ s.reversed
    · have hcon : (step s (.reverse i)).1 = .rejected := by
        show (stepRev s i).1 = _
        unfold stepRev
        rw [hfe, if_pos hrev]
      rw [hcon] at hok
      exact absurd hok (by decide)
    · exact ⟨e, hfe, hrev⟩

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  exact post_fst_ok_of_valid s e h

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  obtain ⟨hmem, hnotrev⟩ := h
  obtain ⟨e, hfind⟩ := findEntry_some_of_mem hmem
  exact rev_fst_ok_of_valid s i e hfind hnotrev

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    have h' : ¬ ValidPost s e := h
    have hP : stepPost s e = (Outcome.rejected, s) := by
      unfold stepPost
      rw [if_neg h']
    show step s (.post e) = _
    show stepPost s e = _
    exact hP
  | reverse i =>
    have h' : ¬ ValidReverse s i := h
    unfold ValidReverse at h'
    by_cases hrev : i ∈ s.reversed
    · have hcase : ∃ fe, findEntry s.journal i = fe := ⟨_, rfl⟩
      obtain ⟨fe, hfe⟩ := hcase
      cases fe with
      | none =>
        show step s (.reverse i) = _
        show stepRev s i = _
        unfold stepRev
        rw [hfe]
      | some e =>
        show step s (.reverse i) = _
        show stepRev s i = _
        unfold stepRev
        rw [hfe, if_pos hrev]
    · have hnotids : i ∉ ids s.journal := by
        intro hmem
        apply h'
        exact ⟨hmem, hrev⟩
      have hfind := findEntry_is_none_of_not_mem hnotids
      show step s (.reverse i) = _
      show stepRev s i = _
      unfold stepRev
      rw [hfind]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  have hval := get_valid_post_of_ok s e hok
  have hst := post_state_of_valid s e hval
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
  · rw [hst]
  · rw [hst]
  · rw [hst]
  · intro a
    rw [hst]
    exact postLines_spec e.lines s.balance a

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hfind
  obtain ⟨e0, hfind0, hnotrev⟩ := get_rev_info_of_ok s i hok
  have hEq : findEntry s.journal i = some e := hfind
  have heq : e0 = e := by rw [hfind0] at hEq; exact Option.some_inj.mp hEq
  have hst := rev_state_of_valid s i e0 hfind0 hnotrev
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
  · rw [hst]
  · rw [hst]
  · intro x
    rw [hst]
    show x ∈ (i :: s.reversed) ↔ x = i ∨ x ∈ s.reversed
    exact List.mem_cons
  · intro a
    rw [hst]
    show postLines (negLines _) s.balance a = s.balance a - netOf e.lines a
    rw [postLines_neg_spec, heq]

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  obtain ⟨e0, hfind0, hnotrev⟩ := get_rev_info_of_ok s i hok
  have hst := rev_state_of_valid s i e0 hfind0 hnotrev
  have hNeg : ¬ Valid (step s (.reverse i)).2 (.reverse i) := by
    rw [hst]
    intro hV
    exact hV.2 (List.mem_cons.mpr (Or.inl rfl))
  exact req_invalid_noop _ _ hNeg

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hval := get_valid_post_of_ok s e hok
  have hnid : e.id ∉ ids s.journal := hval.2.2.2.2.1
  have hnrev : e.id ∉ s.reversed := hval.2.2.2.2.2
  have hst1 := post_state_of_valid s e hval
  have hmem : e.id ∈ ids (step s (.post e)).2.journal := by
    rw [hst1, ids_append_single]
    exact List.mem_append_right (ids s.journal) (List.mem_cons.mpr (Or.inl rfl))
  have hnotrev1 : e.id ∉ (step s (.post e)).2.reversed := by
    rw [hst1]
    exact hnrev
  have hok2 : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by
    apply req_reverse_succeeds
    exact ⟨hmem, hnotrev1⟩
  refine ⟨hok2, ?_⟩
  have hfind1 : findEntry (step s (.post e)).2.journal e.id = some e := by
    rw [hst1]
    exact findEntry_append_new hnid
  have heff := req_reverse_effects (step s (.post e)).2 e.id e hok2 hfind1
  obtain ⟨hacc, hopen, hjour, hrev, hbal⟩ := heff
  funext a
  have hB : (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by
    rw [hst1]
    exact postLines_spec e.lines s.balance a
  have hA : (step (step s (.post e)).2 (.reverse e.id)).2.balance a =
      (step s (.post e)).2.balance a - netOf e.lines a := hbal a
  omega

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  obtain ⟨haccN, hjN, hrevSub, hent⟩ := hwf
  cases c with
  | post e =>
    have hval := get_valid_post_of_ok s e hok
    have hmemAcc : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hval.2.1
    have hbal0 : lineSum e.lines = 0 := hval.2.2.2.1
    have hst := post_state_of_valid s e hval
    have htot := total_post_eq s e
    rw [hst, htot]
    have hsum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
      sum_net_eq_lineSum haccN hmemAcc
    rw [hsum, hbal0]
    omega
  | reverse i =>
    obtain ⟨e0, hfind0, hnotrev⟩ := get_rev_info_of_ok s i hok
    have hmemE : e0 ∈ s.journal := (findEntry_mem hfind0).1
    have hent0 := hent e0 hmemE
    have hst := rev_state_of_valid s i e0 hfind0 hnotrev
    have htot := total_rev_aux s e0 i
    rw [hst, htot]
    have hsum : sumOver s.accounts (fun a => netOf e0.lines a) = lineSum e0.lines :=
      sum_net_eq_lineSum haccN hent0.1
    rw [hsum, hent0.2]
    omega

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  obtain ⟨haccN, hjN, hrevSub, hent⟩ := hwf
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hmemAcc : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hv.2.1
      have hbal0 : lineSum e.lines = 0 := hv.2.2.2.1
      have hnid : e.id ∉ ids s.journal := hv.2.2.2.2.1
      have hst := post_state_of_valid s e hv
      rw [hst]
      show s.accounts.Nodup ∧ (ids (s.journal ++ [e])).Nodup ∧
        (∀ x ∈ s.reversed, x ∈ ids (s.journal ++ [e])) ∧
        (∀ e' ∈ s.journal ++ [e], (∀ l ∈ e'.lines, l.1 ∈ s.accounts) ∧ lineSum e'.lines = 0)
      refine ⟨haccN, ?_, ?_, ?_⟩
      · rw [ids_append_single]
        exact nodup_append_single hjN hnid
      · intro x hx
        have hxmem : x ∈ ids s.journal := hrevSub x hx
        rw [ids_append_single]
        exact List.mem_append_left [e.id] hxmem
      · intro e' hmem'
        cases (List.mem_append.mp hmem') with
        | inl h => exact hent e' h
        | inr h =>
          have heq : e' = e := List.mem_singleton.mp h
          subst heq
          exact ⟨hmemAcc, hbal0⟩
    · have hP : stepPost s e = (Outcome.rejected, s) := by
        unfold stepPost
        rw [if_neg hv]
      have hstep : step s (.post e) = (.rejected, s) := by
        show stepPost s e = _
        exact hP
      rw [hstep]
      exact ⟨haccN, hjN, hrevSub, hent⟩
  | reverse i =>
    by_cases hok : (step s (.reverse i)).1 = .ok
    · obtain ⟨e0, hfind0, hnotrev⟩ := get_rev_info_of_ok s i hok
      have hmemE : e0 ∈ s.journal := (findEntry_mem hfind0).1
      have hidE : e0.id = i := (findEntry_mem hfind0).2
      have hmemIds : i ∈ ids s.journal := List.mem_map.mpr ⟨e0, hmemE, hidE⟩
      have hst := rev_state_of_valid s i e0 hfind0 hnotrev
      rw [hst]
      show s.accounts.Nodup ∧ (ids s.journal).Nodup ∧
        (∀ x ∈ (i :: s.reversed), x ∈ ids s.journal) ∧
        (∀ e' ∈ s.journal, (∀ l ∈ e'.lines, l.1 ∈ s.accounts) ∧ lineSum e'.lines = 0)
      refine ⟨haccN, hjN, ?_, hent⟩
      intro x hx
      cases (List.mem_cons.mp hx) with
      | inl h =>
        subst h
        exact hmemIds
      | inr h => exact hrevSub x h
    · have hnotvalid : ¬ Valid s (.reverse i) := by
        intro hv
        have hok' : (step s (.reverse i)).1 = .ok := req_reverse_succeeds s i hv
        rw [hok'] at hok
        exact absurd hok (by decide)
      have hstep := req_invalid_noop s (.reverse i) hnotvalid
      rw [hstep]
      exact ⟨haccN, hjN, hrevSub, hent⟩

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  obtain ⟨haccN, hjN, hrevSub, hent⟩ := hwf
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hnrev : e.id ∉ s.reversed := hv.2.2.2.2.2
      have hst := post_state_of_valid s e hv
      intro a
      have hbal_post : (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by
        rw [hst]
        exact postLines_spec e.lines s.balance a
      have hopen_eq : (step s (.post e)).2.opening a = s.opening a := by
        rw [hst]
      have hj_eq : (step s (.post e)).2.journal = s.journal ++ [e] := by rw [hst]
      have hr_eq : (step s (.post e)).2.reversed = s.reversed := by rw [hst]
      have hact : activeNet (step s (.post e)).2 a = activeNet s a + netOf e.lines a := by
        unfold activeNet
        rw [hj_eq, hr_eq, sumOver_append]
        have hsingle : sumOver [e] (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a)
            = netOf e.lines a := by
          have hsc : sumOver [e] (fun e' => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a)
            = (if e.id ∈ s.reversed then (0 : Int) else netOf e.lines a) + 0 := rfl
          rw [hsc, if_neg hnrev]
          omega
        rw [hsingle]
      have hcons_a := hcons a
      rw [hbal_post, hact]
      have hopen2 : (step s (.post e)).2.opening a = s.opening a := hopen_eq
      rw [hopen2, hcons_a]
      omega
    · have hP : stepPost s e = (Outcome.rejected, s) := by
        unfold stepPost
        rw [if_neg hv]
      have hstep : step s (.post e) = (.rejected, s) := by
        show stepPost s e = _
        exact hP
      have h2 : (step s (.post e)).2 = s := by rw [hstep]
      rw [h2]
      exact hcons
  | reverse i =>
    by_cases hok : (step s (.reverse i)).1 = .ok
    · obtain ⟨e0, hfind0, hnotrev⟩ := get_rev_info_of_ok s i hok
      have hst := rev_state_of_valid s i e0 hfind0 hnotrev
      intro a
      have hbal_rev : (step s (.reverse i)).2.balance a = s.balance a - netOf e0.lines a := by
        rw [hst]
        exact postLines_neg_spec e0.lines s.balance a
      have hopen_eq : (step s (.reverse i)).2.opening a = s.opening a := by rw [hst]
      have hj_eq : (step s (.reverse i)).2.journal = s.journal := by rw [hst]
      have hr_eq : (step s (.reverse i)).2.reversed = (i :: s.reversed) := by rw [hst]
      have haux := activeNet_reverse_aux s.journal s.reversed i e0 a hjN hfind0 hnotrev
      have hact : activeNet (step s (.reverse i)).2 a = activeNet s a - netOf e0.lines a := by
        unfold activeNet at haux ⊢
        rw [hj_eq, hr_eq]
        exact haux
      have hcons_a := hcons a
      rw [hbal_rev, hact, hopen_eq, hcons_a]
      omega
    · have hnotvalid : ¬ Valid s (.reverse i) := by
        intro hv
        have hok' : (step s (.reverse i)).1 = .ok := req_reverse_succeeds s i hv
        rw [hok'] at hok
        exact absurd hok (by decide)
      have hstep := req_invalid_noop s (.reverse i) hnotvalid
      have h2 : (step s (.reverse i)).2 = s := by rw [hstep]
      rw [h2]
      exact hcons

end Reversal
