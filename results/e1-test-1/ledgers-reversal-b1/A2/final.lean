import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance
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
      else (.ok, { s with balance := fun a => s.balance a - netOf e.lines a,
                          reversed := i :: s.reversed })
    | none => (.rejected, s)

private theorem myhelper1 : True := trivial

theorem myhelper2 : True := trivial

theorem findEntry_some_of_mem_aux (js : List Entry) (i : EntryId) (h : i ∈ ids js) :
    ∃ e, findEntry js i = some e := by
  induction js with
  | nil => simp [ids] at h
  | cons e es ih =>
    simp only [ids, List.map_cons, List.mem_cons] at h
    unfold findEntry
    by_cases he : e.id = i
    · simp [he]
    · have he' : ¬ (i = e.id) := fun hh => he hh.symm
      simp [he]
      exact ih (h.resolve_left he')

theorem findEntry_none_of_not_mem (js : List Entry) (i : EntryId) (h : i ∉ ids js) :
    findEntry js i = none := by
  induction js with
  | nil => rfl
  | cons e es ih =>
    simp only [ids, List.map_cons, List.mem_cons] at h
    have h1 : e.id ≠ i := fun hh => h (Or.inl hh.symm)
    have h2 : i ∉ ids es := fun hm => h (Or.inr hm)
    unfold findEntry
    simp [h1, ih h2]

theorem req_reverse_once_fix : True := trivial

theorem req_reverse_once3 : ReverseOnce step := by
  intro s i h_ok
  cases hfind : findEntry s.journal i with
  | none =>
    unfold step at h_ok
    simp [hfind] at h_ok
  | some e =>
    by_cases hr : i ∈ s.reversed
    · unfold step at h_ok
      simp [hfind, hr] at h_ok
    · have h_step : step s (.reverse i) = (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
        unfold step
        simp [hfind, hr]
      have h2eq : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
        rw [h_step]
      have h_step2 : step (step s (.reverse i)).2 (.reverse i) = (.rejected, (step s (.reverse i)).2) := by
        rw [h2eq]
        unfold step
        simp [hfind]
      exact h_step2

theorem ids_cons_eq (j : Entry) (t : List Entry) : ids (j :: t) = j.id :: ids t := rfl

theorem findEntry_append_fresh3 (js : List Entry) (e : Entry) (h : e.id ∉ ids js) :
    findEntry (js ++ [e]) e.id = some e := by
  induction js with
  | nil => unfold findEntry; simp
  | cons j t ih =>
    have hcons : ids (j :: t) = j.id :: ids t := rfl
    rw [hcons] at h
    simp only [List.mem_cons, not_or] at h
    obtain ⟨hj, hmem⟩ := h
    have hj2 : j.id ≠ e.id := fun hh => hj hh.symm
    have heq : (j :: t) ++ [e] = j :: (t ++ [e]) := rfl
    rw [heq]
    unfold findEntry
    simp [hj2, ih hmem]

theorem roundtrip_probe (s : State) (e : Entry) (hV : ValidPost s e) :
    (step s (.post e)).2.journal = s.journal ++ [e] := by
  unfold step
  simp [hV]

theorem rev_ok_aux (s' : State) (e : Entry) (hfind : findEntry s'.journal e.id = some e) (hnm : e.id ∉ s'.reversed) :
    (step s' (.reverse e.id)).1 = .ok := by
  unfold step
  simp [hfind, hnm]

theorem roundtrip_probe4 (s : State) (e : Entry) (hV : ValidPost s e) :
    (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by
  have h2 : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by
    unfold step
    simp [hV]
  have h_find : findEntry (step s (.post e)).2.journal e.id = some e := by
    rw [h2]
    exact findEntry_append_fresh3 s.journal e hV.2.2.2.2.1
  have h_nmem : e.id ∉ (step s (.post e)).2.reversed := by
    rw [h2]
    simp
    exact hV.2.2.2.2.2
  exact rev_ok_aux _ e h_find h_nmem

theorem rev_bal_aux2 (s' : State) (e : Entry) (hfind : findEntry s'.journal e.id = some e) (hnm : e.id ∉ s'.reversed) :
    (step s' (.reverse e.id)).2.balance = (fun a => s'.balance a - netOf e.lines a) := by
  have h : step s' (.reverse e.id) = (.ok, ({ s' with balance := fun a => s'.balance a - netOf e.lines a, reversed := e.id :: s'.reversed } : State)) := by
    unfold step
    simp [hfind, hnm]
  rw [h]

theorem roundtrip_probe6 (s : State) (e : Entry) (hV : ValidPost s e) :
    (step (step s (.post e)).2 (.reverse e.id)).2.balance = s.balance := by
  have h2 : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by
    unfold step
    simp [hV]
  have h_find : findEntry (step s (.post e)).2.journal e.id = some e := by
    rw [h2]
    exact findEntry_append_fresh3 s.journal e hV.2.2.2.2.1
  have h_nmem : e.id ∉ (step s (.post e)).2.reversed := by
    rw [h2]
    simp
    exact hV.2.2.2.2.2
  have hbal : (step (step s (.post e)).2 (.reverse e.id)).2.balance = (fun a => (step s (.post e)).2.balance a - netOf e.lines a) :=
    rev_bal_aux2 _ e h_find h_nmem
  have hbal1 : (step s (.post e)).2.balance = (fun a => s.balance a + netOf e.lines a) := by
    rw [h2]
  rw [hbal, hbal1]
  funext a
  simp

theorem tb_ite_swap (l1 : AccountId) (a : AccountId) (v : Int) :
    (if l1 = a then v else 0) = (if a = l1 then v else 0) := by
  by_cases h : a = l1
  · subst h; simp
  · have h' : ¬ (l1 = a) := fun hh => h hh.symm
    simp [h, h']

theorem findEntry_mem_of_some (js : List Entry) (i : EntryId) (e : Entry)
    (h : findEntry js i = some e) : e ∈ js ∧ e.id = i := by
  induction js with
  | nil => unfold findEntry at h; simp at h
  | cons j t ih =>
    unfold findEntry at h
    by_cases hj : j.id = i
    · simp [hj] at h
      subst h
      exact ⟨by simp, hj⟩
    · simp [hj] at h
      obtain ⟨hmem, hid⟩ := ih h
      exact ⟨by simp [hmem], hid⟩

theorem sumOver_zero {α : Type} (l : List α) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem sumNet_eq_lineSum2 (ls : List Line) (accs : List AccountId)
    (hnodup : accs.Nodup) (hmem : ∀ l ∈ ls, l.1 ∈ accs) :
    sumOver accs (netOf ls ·) = lineSum ls := by
  induction ls with
  | nil =>
    have h : (fun a : AccountId => netOf [] a) = (fun _ => (0 : Int)) := by
      funext a; rfl
    rw [h, sumOver_zero]
    rfl
  | cons p t ih =>
    have hmem_t : ∀ l ∈ t, l.1 ∈ accs := fun l hl => hmem l (by simp [hl])
    have hmem_p : p.1 ∈ accs := hmem p (by simp)
    have h1 : ∀ a ∈ accs, netOf (p :: t) a = (if a = p.1 then p.2 else 0) + netOf t a := by
      intro a _
      unfold netOf
      simp only [sumOver_cons]
      rw [tb_ite_swap p.1 a p.2]
    have h2 : sumOver accs (netOf (p :: t) ·) = sumOver accs (fun a => if a = p.1 then p.2 else 0) + sumOver accs (netOf t ·) := by
      have := sumOver_add accs (fun a => if a = p.1 then p.2 else 0) (fun a => netOf t a)
      rw [← this]
      exact sumOver_congr accs _ _ (fun a ha => (h1 a ha).symm ▸ rfl)
    rw [h2, sumOver_ite_eq hnodup p.1 p.2, if_pos hmem_p, ih hmem_t]
    simp [lineSum, sumOver_cons]

theorem total_post_add (s : State) (e : Entry) :
    total ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State)
    = total s + sumOver s.accounts (netOf e.lines ·) := by
  unfold total sumOver
  simp only []
  have h := sumOver_add s.accounts s.balance (fun a => netOf e.lines a)
  unfold sumOver at h
  simp only [] at h
  have h2 : ((s.accounts.foldr (fun a acc => s.balance a + netOf e.lines a + acc) 0))
    = ((s.accounts.foldr (fun a acc => (s.balance a + netOf e.lines a) + acc) 0)) := rfl
  omega
-- check shape

theorem total_post_eq (s : State) (e : Entry) :
    total ({ s with balance := fun a => s.balance a + netOf e.lines a } : State)
    = total s + sumOver s.accounts (netOf e.lines ·) := by
  unfold total
  simp only []
  have h := sumOver_add s.accounts s.balance (fun a => netOf e.lines a)
  -- s.accounts foldr with combined fun equals h lhs
  have hc : (fun a : AccountId => s.balance a + netOf e.lines a) = (fun a => s.balance a + (fun a => netOf e.lines a) a) := rfl
  rw [hc]
  exact h

theorem total_rev_eq (s : State) (e : Entry) (rs : List EntryId) :
    total ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := rs } : State)
    = total s - sumOver s.accounts (netOf e.lines ·) := by
  unfold total
  simp only []
  have h := sumOver_sub s.accounts s.balance (fun a => netOf e.lines a)
  have hc : (fun a : AccountId => s.balance a - netOf e.lines a) = (fun a => s.balance a - (fun a => netOf e.lines a) a) := rfl
  rw [hc]
  exact h

theorem ids_append_single (js : List Entry) (e : Entry) : ids (js ++ [e]) = ids js ++ [e.id] := by unfold ids; simp

#check @List.Nodup
#check @List.nodup_append

theorem nodup_append_single_thm3 (l : List Nat) (x : Nat) (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨h1, by simp, ?_⟩
  intro a ha b hb
  simp at hb
  subst hb
  intro h
  exact h2 (h ▸ ha)

theorem activeNet_rev_aux5 (js : List Entry) (rs : List EntryId) (i : EntryId) (e : Entry) (a : AccountId)
    (hnodup : (ids js).Nodup) (hfind : findEntry js i = some e) (hnmem : i ∉ rs) :
    sumOver js (fun e' => if e'.id ∈ i :: rs then (0 : Int) else netOf e'.lines a)
    = sumOver js (fun e' => if e'.id ∈ rs then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  induction js generalizing e with
  | nil => unfold findEntry at hfind; simp at hfind
  | cons j t ih =>
    have hfe : e.id = i := (findEntry_mem_of_some (j :: t) i e hfind).2
    unfold findEntry at hfind
    by_cases hj : j.id = i
    · simp only [hj, ↓reduceIte] at hfind
      cases hfind
      simp only [sumOver_cons]
      have hnodup_t : (ids t).Nodup := by
        have h : ids (j :: t) = j.id :: ids t := rfl
        rw [h] at hnodup
        exact (List.nodup_cons.mp hnodup).2
      have hnotin : j.id ∉ ids t := by
        have h : ids (j :: t) = j.id :: ids t := rfl
        rw [h] at hnodup
        exact (List.nodup_cons.mp hnodup).1
      have hhead1 : (if j.id ∈ i :: rs then (0:Int) else netOf j.lines a) = 0 := by
        have : j.id ∈ i :: rs := by simp [hj]
        simp [this]
      have hhead2 : (if j.id ∈ rs then (0:Int) else netOf j.lines a) = netOf j.lines a := by
        have : j.id ∉ rs := by rw [hj]; exact hnmem
        simp [this]
      rw [hhead1, hhead2]
      have htail : sumOver t (fun e' => if e'.id ∈ i :: rs then (0:Int) else netOf e'.lines a)
          = sumOver t (fun e' => if e'.id ∈ rs then (0:Int) else netOf e'.lines a) := by
        apply sumOver_congr
        intro e' he'
        have hne : e'.id ≠ i := by
          intro hcon
          have hmem2 : e'.id ∈ ids t := by
            unfold ids
            apply List.mem_map.mpr
            exact ⟨e', he', rfl⟩
          rw [hcon] at hmem2
          rw [← hj] at hmem2
          exact hnotin hmem2
        by_cases hm : e'.id ∈ rs
        · have hm2 : e'.id ∈ i :: rs := List.mem_cons_of_mem _ hm
          simp only [hm, hm2, ↓reduceIte]
        · have hm2 : e'.id ∉ i :: rs := by simp [hne, hm]
          simp only [hm, hm2, ↓reduceIte]
      rw [htail]
      omega
    · simp only [hj, ↓reduceIte] at hfind
      simp only [sumOver_cons]
      have hnodup_t : (ids t).Nodup := by
        have h : ids (j :: t) = j.id :: ids t := rfl
        rw [h] at hnodup
        exact (List.nodup_cons.mp hnodup).2
      have ih' := ih (e := e) hnodup_t hfind
      have hj_eq : (if j.id ∈ i :: rs then (0:Int) else netOf j.lines a)
          = (if j.id ∈ rs then (0:Int) else netOf j.lines a) := by
        have hne : j.id ≠ i := hj
        by_cases hm : j.id ∈ rs
        · have hm2 : j.id ∈ i :: rs := List.mem_cons_of_mem _ hm
          simp only [hm, hm2, ↓reduceIte]
        · have hm2 : j.id ∉ i :: rs := by simp [hne, hm]
          simp only [hm, hm2, ↓reduceIte]
      rw [hj_eq, ih']
      omega

theorem findEntry_mem_ids_aux4 (js : List Entry) (i : EntryId) (e : Entry)
    (h : findEntry js i = some e) : i ∈ ids js := by
  have ⟨hmem, hid⟩ := findEntry_mem_of_some js i e h
  unfold ids
  rw [List.mem_map]
  exact ⟨e, hmem, hid⟩

theorem activeNet_post_eq4 (js : List Entry) (rs : List EntryId) (e : Entry) (a : AccountId)
    (h : e.id ∉ rs) :
    sumOver (js ++ [e]) (fun e' => if e'.id ∈ rs then (0 : Int) else netOf e'.lines a)
    = sumOver js (fun e' => if e'.id ∈ rs then (0 : Int) else netOf e'.lines a) + netOf e.lines a := by
  have h2 : sumOver ([e] : List Entry) (fun e' => if e'.id ∈ rs then (0:Int) else netOf e'.lines a) = netOf e.lines a := by
    simp only [sumOver_cons, sumOver_nil]
    simp [h]
  have happ := sumOver_append js [e] (fun e' => if e'.id ∈ rs then (0:Int) else netOf e'.lines a)
  rw [h2] at happ
  exact happ

theorem wellformed_post_aux2 (s : State) (e : Entry) (hwf : WellFormed s) (hv : ValidPost s e) :
    WellFormed ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by
  obtain ⟨hacc, hjid, hrev, hjwf⟩ := hwf
  obtain ⟨hne, hmem, hnz, hbal, hfreshJ, hfreshR⟩ := hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hacc
  · have hids : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := ids_append_single s.journal e
    rw [hids]
    exact nodup_append_single_thm3 (ids s.journal) e.id hjid hfreshJ
  · intro i hi
    have hids : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := ids_append_single s.journal e
    rw [hids]
    have hsub : i ∈ ids s.journal := hrev i hi
    exact List.mem_append.mpr (Or.inl hsub)
  · intro e' he'
    simp only [List.mem_append] at he'
    cases he' with
    | inl h =>
      exact hjwf e' h
    | inr h =>
      simp at h
      subst h
      exact ⟨hmem, hbal⟩

theorem req_post_succeeds    : PostSucceeds step := by
  intro s e h
  unfold step
  simp [h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  obtain ⟨hmem, hnot⟩ := h
  obtain ⟨e, he⟩ := findEntry_some_of_mem_aux s.journal i hmem
  show (step s (.reverse i)).1 = .ok
  unfold step
  simp [he, hnot]

theorem req_invalid_noop     : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    simp only [Valid] at h
    show step s (.post e) = _
    unfold step
    simp [h]
  | reverse i =>
    simp only [Valid, ValidReverse] at h
    show step s (.reverse i) = _
    unfold step
    by_cases hm : i ∈ ids s.journal
    · by_cases hr : i ∈ s.reversed
      · obtain ⟨e, he⟩ := findEntry_some_of_mem_aux s.journal i hm
        simp [he, hr]
      · exact absurd ⟨hm, hr⟩ h
    · have hnone : findEntry s.journal i = none :=
        findEntry_none_of_not_mem s.journal i hm
      simp [hnone]

theorem req_post_effects : PostEffects step := by
  intro s e h
  unfold step at h ⊢
  by_cases hv : ValidPost s e
  · simp [hv] at h ⊢
  · simp [hv] at h

theorem req_reverse_effects  : ReverseEffects step := by
  intro s i e h_ok h_find
  have h_nmem : i ∉ s.reversed := by
    intro hm
    unfold step at h_ok
    simp [h_find, hm] at h_ok
  have h_step : step s (.reverse i) = (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
    unfold step
    simp [h_find, h_nmem]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h_step]
  · rw [h_step]
  · rw [h_step]
  · intro x
    rw [h_step]
    simp
  · intro a
    rw [h_step]

theorem req_reverse_once : ReverseOnce step := by
  intro s i h_ok
  cases hfind : findEntry s.journal i with
  | none =>
    unfold step at h_ok
    simp [hfind] at h_ok
  | some e =>
    by_cases hr : i ∈ s.reversed
    · unfold step at h_ok
      simp [hfind, hr] at h_ok
    · have h_step : step s (.reverse i) = (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
        unfold step
        simp [hfind, hr]
      have h2eq : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
        rw [h_step]
      have h_step2 : step (step s (.reverse i)).2 (.reverse i) = (.rejected, (step s (.reverse i)).2) := by
        rw [h2eq]
        unfold step
        simp [hfind]
      exact h_step2

theorem req_roundtrip        : RoundTrip step := by
  intro s e h_ok
  have hV : ValidPost s e := by
    by_cases hv : ValidPost s e
    · exact hv
    · unfold step at h_ok
      simp [hv] at h_ok
  exact ⟨roundtrip_probe4 s e hV, roundtrip_probe6 s e hV⟩

theorem req_trial_balance    : TrialBalance step := by
  intro s c hwf hok
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have h2 : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by
        unfold step; simp [hv]
      have hsum : sumOver s.accounts (netOf e.lines ·) = 0 := by
        rw [sumNet_eq_lineSum2 e.lines s.accounts hwf.1 hv.2.1, hv.2.2.2.1]
      rw [h2]
      unfold total
      simp only []
      have h := sumOver_add s.accounts s.balance (fun a => netOf e.lines a)
      have hc : (fun a : AccountId => s.balance a + netOf e.lines a) = (fun a => s.balance a + (fun a => netOf e.lines a) a) := rfl
      rw [hc, h, hsum]
      omega
    · unfold step at hok
      simp [hv] at hok
  | reverse i =>
    cases hfind : findEntry s.journal i with
    | none =>
      unfold step at hok
      simp [hfind] at hok
    | some e =>
      by_cases hr : i ∈ s.reversed
      · unfold step at hok
        simp [hfind, hr] at hok
      · have h2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
          unfold step; simp [hfind, hr]
        obtain ⟨hemem, _⟩ := findEntry_mem_of_some s.journal i e hfind
        have heWF := hwf.2.2.2 e hemem
        have hsum : sumOver s.accounts (netOf e.lines ·) = 0 := by
          rw [sumNet_eq_lineSum2 e.lines s.accounts hwf.1 heWF.1, heWF.2]
        rw [h2]
        unfold total
        simp only []
        have h := sumOver_sub s.accounts s.balance (fun a => netOf e.lines a)
        have hc : (fun a : AccountId => s.balance a - netOf e.lines a) = (fun a => s.balance a - (fun a => netOf e.lines a) a) := rfl
        rw [hc, h, hsum]
        omega

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have h2 : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by
        unfold step; simp [hv]
      rw [h2]
      exact wellformed_post_aux2 s e hwf hv
    · have h2 : (step s (.post e)).2 = s := by
        unfold step; simp [hv]
      rw [h2]
      exact hwf
  | reverse i =>
    cases hfind : findEntry s.journal i with
    | none =>
      have h2 : (step s (.reverse i)).2 = s := by
        unfold step; simp [hfind]
      rw [h2]
      exact hwf
    | some e =>
      by_cases hr : i ∈ s.reversed
      · have h2 : (step s (.reverse i)).2 = s := by
          unfold step; simp [hfind, hr]
        rw [h2]
        exact hwf
      · have h2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
          unfold step; simp [hfind, hr]
        rw [h2]
        obtain ⟨hacc, hjid, hrev, hjwf⟩ := hwf
        have hi_mem : i ∈ ids s.journal := findEntry_mem_ids_aux4 s.journal i e hfind
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa using hacc
        · simpa using hjid
        · intro x hx
          simp only [List.mem_cons] at hx
          cases hx with
          | inl h => subst h; exact hi_mem
          | inr h => exact hrev x h
        · intro e' he'
          exact hjwf e' he'

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcon
  cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have h2 : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by
        unfold step; simp [hv]
      rw [h2]
      intro a
      simp only
      have hcon_a := hcon a
      unfold activeNet at hcon_a ⊢
      simp only at hcon_a ⊢
      have hnot : e.id ∉ s.reversed := hv.2.2.2.2.2
      have hpost := activeNet_post_eq4 s.journal s.reversed e a hnot
      -- hcon_a : s.balance a = s.opening a + sumOver ...
      omega
    · have h2 : (step s (.post e)).2 = s := by
        unfold step; simp [hv]
      rw [h2]
      exact hcon
  | reverse i =>
    cases hfind : findEntry s.journal i with
    | none =>
      have h2 : (step s (.reverse i)).2 = s := by
        unfold step; simp [hfind]
      rw [h2]
      exact hcon
    | some e =>
      by_cases hr : i ∈ s.reversed
      · have h2 : (step s (.reverse i)).2 = s := by
          unfold step; simp [hfind, hr]
        rw [h2]
        exact hcon
      · have h2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
          unfold step; simp [hfind, hr]
        rw [h2]
        intro a
        simp only
        have hcon_a := hcon a
        unfold activeNet at hcon_a ⊢
        simp only at hcon_a ⊢
        have hnodup : (ids s.journal).Nodup := hwf.2.1
        have hrev := activeNet_rev_aux5 s.journal s.reversed i e a hnodup hfind hr
        omega

end Reversal
