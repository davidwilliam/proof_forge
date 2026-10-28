import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost
  infer_instance

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

theorem step_post_eq (s : State) (e : Entry) (hV : ValidPost s e) :
    step s (.post e) = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by
  unfold step
  simp [hV]

theorem step_post_rej (s : State) (e : Entry) (hV : ¬ ValidPost s e) :
    step s (.post e) = (.rejected, s) := by
  unfold step
  simp [hV]

theorem step_rev_eq (s : State) (i : EntryId) (e : Entry) (hfind : findEntry s.journal i = some e) (hnot : i ∉ s.reversed) :
    step s (.reverse i) = (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
  unfold step
  simp [hfind, hnot]

theorem step_rev_rej_mem (s : State) (i : EntryId) (e : Entry) (hfind : findEntry s.journal i = some e) (hmem : i ∈ s.reversed) :
    step s (.reverse i) = (.rejected, s) := by
  unfold step
  simp [hfind, hmem]

theorem step_rev_rej_none (s : State) (i : EntryId) (hfind : findEntry s.journal i = none) :
    step s (.reverse i) = (.rejected, s) := by
  unfold step
  simp [hfind]

theorem findEntry_none_of_notmem {j : List Entry} {i : EntryId} (h : i ∉ ids j) : findEntry j i = none := by
  induction j with
  | nil => rfl
  | cons hd tl ih =>
    have hcons : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hcons] at h
    have hhd : ¬ (hd.id = i) := fun heq => h (List.mem_cons.mpr (Or.inl heq.symm))
    have htl : i ∉ ids tl := fun hmem => h (List.mem_cons.mpr (Or.inr hmem))
    have hDef : findEntry (hd :: tl) i = (if hd.id = i then some hd else findEntry tl i) := rfl
    rw [hDef]
    simp [hhd, ih htl]

theorem mem_ids_of_findEntry_some {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : i ∈ ids j := by
  induction j with
  | nil =>
    have hnone : findEntry [] i = none := rfl
    rw [hnone] at h
    cases h
  | cons hd tl ih =>
    have hDef : findEntry (hd :: tl) i = (if hd.id = i then some hd else findEntry tl i) := rfl
    rw [hDef] at h
    by_cases heq : hd.id = i
    · have hcons : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [hcons]
      exact List.mem_cons.mpr (Or.inl heq.symm)
    · have h2 : findEntry tl i = some e := by simp [heq] at h; exact h
      have hcons : ids (hd :: tl) = hd.id :: ids tl := rfl
      rw [hcons]
      exact List.mem_cons.mpr (Or.inr (ih h2))

theorem findEntry_id_of_some {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e.id = i := by
  induction j with
  | nil =>
    have hnone : findEntry [] i = none := rfl
    rw [hnone] at h
    cases h
  | cons hd tl ih =>
    have hDef : findEntry (hd :: tl) i = (if hd.id = i then some hd else findEntry tl i) := rfl
    rw [hDef] at h
    by_cases heq : hd.id = i
    · simp [heq] at h
      cases h
      exact heq
    · simp [heq] at h
      exact ih h

theorem findEntry_mem_of_some {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil =>
    have hnone : findEntry [] i = none := rfl
    rw [hnone] at h
    cases h
  | cons hd tl ih =>
    have hDef : findEntry (hd :: tl) i = (if hd.id = i then some hd else findEntry tl i) := rfl
    rw [hDef] at h
    by_cases heq : hd.id = i
    · simp [heq] at h
      cases h
      exact List.mem_cons.mpr (Or.inl rfl)
    · simp [heq] at h
      exact List.mem_cons.mpr (Or.inr (ih h))

theorem exists_findEntry_of_mem {j : List Entry} {i : EntryId} (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil =>
    have hNil : ids ([] : List Entry) = [] := rfl
    rw [hNil] at h
    cases h
  | cons hd tl ih =>
    by_cases heq : hd.id = i
    · refine ⟨hd, ?_⟩
      have hDef : findEntry (hd :: tl) i = (if hd.id = i then some hd else findEntry tl i) := rfl
      rw [hDef]
      simp [heq]
    · have hmem : i ∈ ids tl := by
        have hcons : ids (hd :: tl) = hd.id :: ids tl := rfl
        rw [hcons] at h
        have h_or := List.mem_cons.mp h
        cases h_or with
        | inl hh => exact absurd hh.symm heq
        | inr hh => exact hh
      obtain ⟨e, he⟩ := ih hmem
      refine ⟨e, ?_⟩
      have hDef : findEntry (hd :: tl) i = (if hd.id = i then some hd else findEntry tl i) := rfl
      rw [hDef]
      simp [heq, he]

theorem findEntry_append_new {j : List Entry} {e : Entry} (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil =>
    have hDef : findEntry ([e] : List Entry) e.id = (if e.id = e.id then some e else findEntry [] e.id) := rfl
    have happ : ([] : List Entry) ++ [e] = [e] := rfl
    rw [happ, hDef]
    simp
  | cons hd tl ih =>
    have hcons : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hcons] at h
    have hhd : ¬ (hd.id = e.id) := fun heq => h (List.mem_cons.mpr (Or.inl heq.symm))
    have htl : e.id ∉ ids tl := fun hmem => h (List.mem_cons.mpr (Or.inr hmem))
    have happ : (hd :: tl) ++ [e] = hd :: (tl ++ [e]) := rfl
    rw [happ]
    have hDef : findEntry (hd :: (tl ++ [e])) e.id = (if hd.id = e.id then some hd else findEntry (tl ++ [e]) e.id) := rfl
    rw [hDef]
    simp [hhd, ih htl]

theorem ids_append_eq (j : List Entry) (e : Entry) : ids (j ++ [e]) = ids j ++ [e.id] := by
  induction j with
  | nil => rfl
  | cons hd tl ih =>
    have hA : ids ((hd :: tl) ++ [e]) = hd.id :: ids (tl ++ [e]) := rfl
    have hB : ids (hd :: tl) ++ [e.id] = hd.id :: (ids tl ++ [e.id]) := rfl
    rw [hA, ih, hB]

theorem nodup_append_singleton {l : List Nat} {x : Nat} (hnd : l.Nodup) (hmem : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil =>
    have hNil : ([] : List Nat) ++ [x] = [x] := rfl
    rw [hNil]
    apply List.nodup_cons.mpr
    constructor
    · intro hcon
      cases hcon
    · exact List.nodup_nil
  | cons hd tl ih =>
    have hpair := (List.nodup_cons.mp hnd)
    have hhd : hd ∉ tl := hpair.1
    have hnd2 : tl.Nodup := hpair.2
    have hmem2 : x ∉ tl := fun hm => hmem (List.mem_cons.mpr (Or.inr hm))
    have hne : hd ≠ x := by
      intro he
      apply hmem
      rw [he]
      exact List.mem_cons.mpr (Or.inl rfl)
    have ih' := ih hnd2 hmem2
    have happ : (hd :: tl) ++ [x] = hd :: (tl ++ [x]) := rfl
    rw [happ]
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      have hm_or := List.mem_append.mp hm
      cases hm_or with
      | inl hm2 => exact hhd hm2
      | inr hm2 =>
        have h_or2 := List.mem_cons.mp hm2
        cases h_or2 with
        | inl heq => exact hne heq
        | inr hNil => cases hNil
    · exact ih'

theorem sumOver_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    show (0 : Int) + sumOver tl (fun _ => (0 : Int)) = 0
    rw [ih]
    omega

theorem sumNet_eq_lineSum {ls : List Line} {accs : List AccountId} (hnd : accs.Nodup) (hmem : ∀ l ∈ ls, l.1 ∈ accs) : sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have heq : (fun a : AccountId => netOf [] a) = (fun _ => (0 : Int)) := rfl
    rw [heq, sumOver_zero]
    rfl
  | cons hd tl ih =>
    have hhd_mem : hd.1 ∈ accs := hmem hd (List.mem_cons.mpr (Or.inl rfl))
    have htl_mem : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hmem l (List.mem_cons.mpr (Or.inr hl))
    have ih' := ih htl_mem
    have hLine : lineSum (hd :: tl) = hd.2 + lineSum tl := rfl
    rw [hLine]
    have hcongr : (fun a : AccountId => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := rfl
    rw [hcongr, sumOver_add, ih']
    have hIte : sumOver accs (fun a => (if hd.1 = a then hd.2 else 0)) = hd.2 := by
      have hcongr2 : (fun a : AccountId => (if hd.1 = a then hd.2 else 0)) = (fun a => (if a = hd.1 then hd.2 else 0)) := by
        funext a
        by_cases heq : hd.1 = a
        · have heq2 : a = hd.1 := heq.symm
          simp [heq, heq2]
        · have heq2 : ¬ (a = hd.1) := fun hh => heq hh.symm
          simp [heq, heq2]
      rw [hcongr2, sumOver_ite_eq hnd hd.1 hd.2]
      simp [hhd_mem]
    rw [hIte]

theorem activeNet_post_rw (s2 s : State) (e : Entry) (a : AccountId)
    (hJ : s2.journal = s.journal ++ [e]) (hR : s2.reversed = s.reversed)
    (hmem : e.id ∉ s.reversed) :
    activeNet s2 a = activeNet s a + netOf e.lines a := by
  unfold activeNet
  rw [hJ, hR, sumOver_append]
  have hsingle : sumOver [e] (fun e' : Entry => if e'.id ∈ s.reversed then (0 : Int) else netOf e'.lines a) = netOf e.lines a := by
    simp [hmem]
  rw [hsingle]

theorem activeNet_reverse_aux (j : List Entry) (rev : List EntryId) (i : EntryId) (ent : Entry) (a : AccountId)
    (hfind : findEntry j i = some ent) (hnot : i ∉ rev) (hnd : (ids j).Nodup) :
    sumOver j (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a) =
    sumOver j (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) - netOf ent.lines a := by
  induction j with
  | nil =>
    have hnone : findEntry [] i = none := rfl
    rw [hnone] at hfind
    cases hfind
  | cons d t ih =>
    have hfind' : (if d.id = i then some d else findEntry t i) = some ent := hfind
    have hcons : ids (d :: t) = d.id :: ids t := rfl
    rw [hcons] at hnd
    have hpair := List.nodup_cons.mp hnd
    have hhdnotin : d.id ∉ ids t := hpair.1
    have htlnd : (ids t).Nodup := hpair.2
    by_cases heq : d.id = i
    · have hfind_d : some d = some ent := by simp [heq] at hfind'; exact hfind'
      have hde : d = ent := by cases hfind_d; rfl
      have hhd_not_rev : d.id ∉ rev := by
        intro hm
        apply hnot
        rw [← heq]
        exact hm
      have h_in : d.id ∈ i :: rev := List.mem_cons.mpr (Or.inl heq)
      have hhead1 : (if d.id ∈ i :: rev then (0 : Int) else netOf d.lines a) = 0 := by simp [h_in]
      have hhead2 : (if d.id ∈ rev then (0 : Int) else netOf d.lines a) = netOf d.lines a := by simp [hhd_not_rev]
      have htail_eq : sumOver t (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a) = sumOver t (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) := by
        apply sumOver_congr
        intro e' hmem
        have hmem_id : e'.id ∈ ids t := by
          unfold ids
          exact List.mem_map_of_mem hmem
        have hne : e'.id ≠ i := by
          intro heqi
          apply hhdnotin
          have h_eq : d.id = e'.id := heq.trans heqi.symm
          rw [h_eq]
          exact hmem_id
        by_cases hc : e'.id ∈ rev
        · have h1 : e'.id ∈ i :: rev := List.mem_cons.mpr (Or.inr hc)
          simp [h1, hc]
        · have h1 : e'.id ∉ i :: rev := by
            intro hm
            have hor := List.mem_cons.mp hm
            cases hor with
            | inl h_eq => exact hne h_eq
            | inr h_mem => exact hc h_mem
          simp [h1, hc]
      show (if d.id ∈ i :: rev then (0 : Int) else netOf d.lines a) + sumOver t (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a) = (if d.id ∈ rev then (0 : Int) else netOf d.lines a) + sumOver t (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) - netOf ent.lines a
      rw [hhead1, hhead2, htail_eq, hde]
      omega
    · have hfind_t : findEntry t i = some ent := by simp [heq] at hfind'; exact hfind'
      have ih' := ih hfind_t htlnd
      have hhead_eq : (if d.id ∈ i :: rev then (0 : Int) else netOf d.lines a) = (if d.id ∈ rev then (0 : Int) else netOf d.lines a) := by
        by_cases hc : d.id ∈ rev
        · have h1 : d.id ∈ i :: rev := List.mem_cons.mpr (Or.inr hc)
          simp [h1, hc]
        · have h1 : d.id ∉ i :: rev := by
            intro hm
            have hor := List.mem_cons.mp hm
            cases hor with
            | inl h_eq => exact heq h_eq
            | inr h_mem => exact hc h_mem
          simp [h1, hc]
      show (if d.id ∈ i :: rev then (0 : Int) else netOf d.lines a) + sumOver t (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a) = (if d.id ∈ rev then (0 : Int) else netOf d.lines a) + sumOver t (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) - netOf ent.lines a
      rw [hhead_eq, ih']
      omega

theorem activeNet_reverse_rw (s2 s : State) (i : EntryId) (e : Entry) (a : AccountId)
    (hJ : s2.journal = s.journal) (hR : s2.reversed = i :: s.reversed)
    (hfind : findEntry s.journal i = some e) (hnot : i ∉ s.reversed) (hnd : (ids s.journal).Nodup) :
    activeNet s2 a = activeNet s a - netOf e.lines a := by
  unfold activeNet
  rw [hJ, hR]
  exact activeNet_reverse_aux s.journal s.reversed i e a hfind hnot hnd

theorem post_ok_has_valid (s : State) (e : Entry) (hok : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases hV : ValidPost s e
  · exact hV
  · have hEq := step_post_rej s e hV
    have h1 : (step s (.post e)).1 = Outcome.rejected := by rw [hEq]
    rw [h1] at hok
    exact absurd hok (by decide)

theorem reverse_ok_has_find (s : State) (i : EntryId) (hok : (step s (.reverse i)).1 = .ok) : ∃ e, findEntry s.journal i = some e ∧ i ∉ s.reversed := by
  by_cases hfind : findEntry s.journal i = none
  · have hEq := step_rev_rej_none s i hfind
    have h1 : (step s (.reverse i)).1 = Outcome.rejected := by rw [hEq]
    rw [h1] at hok
    exact absurd hok (by decide)
  · have hne : findEntry s.journal i ≠ none := hfind
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists.mp hne
    have he' : findEntry s.journal i = some e := he.symm
    by_cases hmem : i ∈ s.reversed
    · have hEq := step_rev_rej_mem s i e he' hmem
      have h1 : (step s (.reverse i)).1 = Outcome.rejected := by rw [hEq]
      rw [h1] at hok
      exact absurd hok (by decide)
    · exact ⟨e, he', hmem⟩

theorem req_post_succeeds : PostSucceeds step := by
  unfold PostSucceeds
  intro s e h
  have hEq := step_post_eq s e h
  rw [hEq]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  unfold ReverseSucceeds ValidReverse
  intro s i h
  have hmem : i ∈ ids s.journal := h.1
  have hnot : i ∉ s.reversed := h.2
  obtain ⟨e, he⟩ := exists_findEntry_of_mem hmem
  have hEq := step_rev_eq s i e he hnot
  rw [hEq]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s c h
  cases c with
  | post e =>
    have h2 : ¬ ValidPost s e := h
    exact step_post_rej s e h2
  | reverse i =>
    have h2 : ¬ Valid s (.reverse i) := h
    have h2' : ¬ ValidReverse s i := h2
    by_cases hmem : i ∈ ids s.journal
    · have hrev : i ∈ s.reversed := by
        by_cases hr : i ∈ s.reversed
        · exact hr
        · have hv : ValidReverse s i := ⟨hmem, hr⟩
          exact absurd hv h2'
      obtain ⟨e, he⟩ := exists_findEntry_of_mem hmem
      exact step_rev_rej_mem s i e he hrev
    · have hnone := findEntry_none_of_notmem hmem
      exact step_rev_rej_none s i hnone

theorem req_post_effects : PostEffects step := by
  unfold PostEffects
  intro s e hok
  have hV := post_ok_has_valid s e hok
  have heq := step_post_eq s e hV
  have h1 : (step s (.post e)).2.accounts = s.accounts := by rw [heq]
  have h2 : (step s (.post e)).2.opening = s.opening := by rw [heq]
  have h3 : (step s (.post e)).2.journal = s.journal ++ [e] := by rw [heq]
  have h4 : (step s (.post e)).2.reversed = s.reversed := by rw [heq]
  have h5 : ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by
    intro a
    rw [heq]
  exact ⟨h1, h2, h3, h4, h5⟩

theorem req_reverse_effects : ReverseEffects step := by
  unfold ReverseEffects
  intro s i e hok hfind
  have hnot : i ∉ s.reversed := by
    by_cases hc : i ∈ s.reversed
    · have hstep := step_rev_rej_mem s i e hfind hc
      have h1 : (step s (.reverse i)).1 = Outcome.rejected := by rw [hstep]
      rw [h1] at hok
      exact absurd hok (by decide)
    · exact hc
  have heq := step_rev_eq s i e hfind hnot
  have h1 : (step s (.reverse i)).2.accounts = s.accounts := by rw [heq]
  have h2 : (step s (.reverse i)).2.opening = s.opening := by rw [heq]
  have h3 : (step s (.reverse i)).2.journal = s.journal := by rw [heq]
  have h4 : ∀ x, x ∈ (step s (.reverse i)).2.reversed ↔ x = i ∨ x ∈ s.reversed := by
    intro x
    rw [heq]
    simp only [List.mem_cons]
  have h5 : ∀ a, (step s (.reverse i)).2.balance a = s.balance a - netOf e.lines a := by
    intro a
    rw [heq]
  exact ⟨h1, h2, h3, h4, h5⟩

theorem req_reverse_once : ReverseOnce step := by
  unfold ReverseOnce
  intro s i hok
  obtain ⟨e, hfind, hnot⟩ := reverse_ok_has_find s i hok
  have heq := step_rev_eq s i e hfind hnot
  have hjour : (step s (.reverse i)).2.journal = s.journal := by rw [heq]
  have hrev : (step s (.reverse i)).2.reversed = i :: s.reversed := by rw [heq]
  have hfind2 : findEntry (step s (.reverse i)).2.journal i = some e := by rw [hjour, hfind]
  have hmem2 : i ∈ (step s (.reverse i)).2.reversed := by
    rw [hrev]
    exact List.mem_cons.mpr (Or.inl rfl)
  exact step_rev_rej_mem _ i e hfind2 hmem2

theorem req_roundtrip : RoundTrip step := by
  unfold RoundTrip
  intro s e hok
  have hVpost : ValidPost s e := post_ok_has_valid s e hok
  have heq := step_post_eq s e hVpost
  have hmidJ : (step s (.post e)).2.journal = s.journal ++ [e] := by rw [heq]
  have hmidR : (step s (.post e)).2.reversed = s.reversed := by rw [heq]
  have hmidB : (step s (.post e)).2.balance = (fun a => s.balance a + netOf e.lines a) := by rw [heq]
  obtain ⟨hne, hacc, hnz, hsum, hids, hrev⟩ := hVpost
  have hfind : findEntry (step s (.post e)).2.journal e.id = some e := by
    rw [hmidJ]
    exact findEntry_append_new hids
  have hnot : e.id ∉ (step s (.post e)).2.reversed := by rw [hmidR]; exact hrev
  have heq2 := step_rev_eq (step s (.post e)).2 e.id e hfind hnot
  have hok2 : (step (step s (.post e)).2 (.reverse e.id)).1 = Outcome.ok := by rw [heq2]
  apply And.intro hok2
  have hSnd : (step (step s (.post e)).2 (.reverse e.id)).2.balance = (fun a => (step s (.post e)).2.balance a - netOf e.lines a) := by rw [heq2]
  rw [hSnd, hmidB]
  funext a
  show (s.balance a + netOf e.lines a) - netOf e.lines a = s.balance a
  omega

theorem req_trial_balance : TrialBalance step := by
  unfold TrialBalance
  intro s c hwf hok
  cases c with
  | post e =>
    have hAccNd : s.accounts.Nodup := hwf.1
    have hVpb : ValidPost s e := post_ok_has_valid s e hok
    have heq := step_post_eq s e hVpb
    have hacc : ∀ l ∈ e.lines, l.1 ∈ s.accounts := (hVpb.2.1)
    have hsum : lineSum e.lines = 0 := (hVpb.2.2.2.1)
    have hA : (step s (.post e)).2.accounts = s.accounts := by rw [heq]
    have hB : (step s (.post e)).2.balance = (fun a => s.balance a + netOf e.lines a) := by rw [heq]
    have hTot : total (step s (.post e)).2 = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
      unfold total
      rw [hA, hB]
    rw [hTot, sumOver_add, sumNet_eq_lineSum hAccNd hacc, hsum]
    unfold total
    omega
  | reverse i =>
    have hAccNd : s.accounts.Nodup := hwf.1
    have hBal : ∀ e2 ∈ s.journal, (∀ l ∈ e2.lines, l.1 ∈ s.accounts) ∧ lineSum e2.lines = 0 := hwf.2.2.2
    obtain ⟨e, hfind, hnot⟩ := reverse_ok_has_find s i hok
    have heq := step_rev_eq s i e hfind hnot
    have hA : (step s (.reverse i)).2.accounts = s.accounts := by rw [heq]
    have hB : (step s (.reverse i)).2.balance = (fun a => s.balance a - netOf e.lines a) := by rw [heq]
    have hemem := findEntry_mem_of_some hfind
    have hentry := hBal e hemem
    have hacc_e : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hentry.1
    have hsum_e : lineSum e.lines = 0 := hentry.2
    have hTot : total (step s (.reverse i)).2 = sumOver s.accounts (fun a => s.balance a - netOf e.lines a) := by
      unfold total
      rw [hA, hB]
    rw [hTot, sumOver_sub, sumNet_eq_lineSum hAccNd hacc_e, hsum_e]
    unfold total
    omega

theorem req_well_formed : StaysWellFormed step := by
  unfold StaysWellFormed
  intro s c hwf
  have hAccNd : s.accounts.Nodup := hwf.1
  have hIdsNd : (ids s.journal).Nodup := hwf.2.1
  have hRevSub : ∀ i ∈ s.reversed, i ∈ ids s.journal := hwf.2.2.1
  have hBal : ∀ e ∈ s.journal, (∀ l ∈ e.lines, l.1 ∈ s.accounts) ∧ lineSum e.lines = 0 := hwf.2.2.2
  cases c with
  | post e =>
    by_cases hVp : ValidPost s e
    · have heq := step_post_eq s e hVp
      have hSnd : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by rw [heq]
      obtain ⟨hne, hacc, hnz, hsum, hids, hrev⟩ := hVp
      rw [hSnd]
      show WellFormed _
      unfold WellFormed
      show s.accounts.Nodup ∧ (ids (s.journal ++ [e])).Nodup ∧ (∀ i ∈ s.reversed, i ∈ ids (s.journal ++ [e])) ∧ ∀ e' ∈ s.journal ++ [e], (∀ l ∈ e'.lines, l.1 ∈ s.accounts) ∧ lineSum e'.lines = 0
      refine ⟨hAccNd, ?_, ?_, ?_⟩
      · rw [ids_append_eq]
        exact nodup_append_singleton hIdsNd hids
      · intro x hx
        rw [ids_append_eq]
        exact List.mem_append.mpr (Or.inl (hRevSub x hx))
      · intro e' hmem
        have h_or := List.mem_append.mp hmem
        cases h_or with
        | inl hmem2 => exact hBal e' hmem2
        | inr hmem2 =>
          have h_or2 := List.mem_cons.mp hmem2
          cases h_or2 with
          | inl heq2 =>
            have heq3 : e' = e := by simpa using heq2.symm
            rw [heq3]
            exact ⟨hacc, hsum⟩
          | inr hNil => cases hNil
    · have heq := step_post_rej s e hVp
      rw [heq]
      exact ⟨hAccNd, hIdsNd, hRevSub, hBal⟩
  | reverse i =>
    by_cases hEq : findEntry s.journal i = none
    · have heq := step_rev_rej_none s i hEq
      rw [heq]
      exact ⟨hAccNd, hIdsNd, hRevSub, hBal⟩
    · have hne : findEntry s.journal i ≠ none := hEq
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists.mp hne
      have he' : findEntry s.journal i = some e := he.symm
      by_cases hmem : i ∈ s.reversed
      · have heq := step_rev_rej_mem s i e he' hmem
        rw [heq]
        exact ⟨hAccNd, hIdsNd, hRevSub, hBal⟩
      · have heq := step_rev_eq s i e he' hmem
        have hSnd : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by rw [heq]
        have hmem_ids := mem_ids_of_findEntry_some he'
        rw [hSnd]
        show WellFormed _
        unfold WellFormed
        show s.accounts.Nodup ∧ (ids s.journal).Nodup ∧ (∀ y ∈ i :: s.reversed, y ∈ ids s.journal) ∧ ∀ e' ∈ s.journal, (∀ l ∈ e'.lines, l.1 ∈ s.accounts) ∧ lineSum e'.lines = 0
        refine ⟨hAccNd, hIdsNd, ?_, hBal⟩
        intro y hy
        have h_or := List.mem_cons.mp hy
        cases h_or with
        | inl heq2 =>
          rw [heq2]
          exact hmem_ids
        | inr hmem2 => exact hRevSub y hmem2

theorem req_consistent : StaysConsistent step := by
  unfold StaysConsistent
  intro s c hwf hcon
  have hIdsNd : (ids s.journal).Nodup := hwf.2.1
  cases c with
  | post e =>
    by_cases hVp : ValidPost s e
    · have heq := step_post_eq s e hVp
      obtain ⟨hne, hacc, hnz, hsum, hids, hrev⟩ := hVp
      have hJ : (step s (.post e)).2.journal = s.journal ++ [e] := by rw [heq]
      have hR : (step s (.post e)).2.reversed = s.reversed := by rw [heq]
      intro a
      have hEq2 : (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by rw [heq]
      have hEqO : (step s (.post e)).2.opening = s.opening := by rw [heq]
      have hEqA : activeNet (step s (.post e)).2 a = activeNet s a + netOf e.lines a :=
        activeNet_post_rw _ s e a hJ hR hrev
      have hcon_a := hcon a
      show (step s (.post e)).2.balance a = (step s (.post e)).2.opening a + activeNet (step s (.post e)).2 a
      rw [hEq2, hEqO, hEqA, hcon_a]
      omega
    · have heq := step_post_rej s e hVp
      rw [heq]
      exact hcon
  | reverse i =>
    by_cases hEq : findEntry s.journal i = none
    · have heq := step_rev_rej_none s i hEq
      rw [heq]
      exact hcon
    · have hne : findEntry s.journal i ≠ none := hEq
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists.mp hne
      have he' : findEntry s.journal i = some e := he.symm
      by_cases hmem : i ∈ s.reversed
      · have heq := step_rev_rej_mem s i e he' hmem
        rw [heq]
        exact hcon
      · have heq := step_rev_eq s i e he' hmem
        have hJ : (step s (.reverse i)).2.journal = s.journal := by rw [heq]
        have hR : (step s (.reverse i)).2.reversed = i :: s.reversed := by rw [heq]
        intro a
        have hEq2 : (step s (.reverse i)).2.balance a = s.balance a - netOf e.lines a := by rw [heq]
        have hEqO : (step s (.reverse i)).2.opening = s.opening := by rw [heq]
        have hEqA : activeNet (step s (.reverse i)).2 a = activeNet s a - netOf e.lines a :=
          activeNet_reverse_rw _ s i e a hJ hR he' hmem hIdsNd
        have hcon_a := hcon a
        show (step s (.reverse i)).2.balance a = (step s (.reverse i)).2.opening a + activeNet (step s (.reverse i)).2 a
        rw [hEq2, hEqO, hEqA, hcon_a]
        omega

end Reversal
