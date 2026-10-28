import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance
instance instDecidableValidReverse (s : State) (i : EntryId) : Decidable (ValidReverse s i) := by
  unfold ValidReverse; infer_instance
instance instDecidableValid (s : State) (c : Command) : Decidable (Valid s c) := by
  cases c with
  | post e => exact instDecidableValidPost s e
  | reverse i => exact instDecidableValidReverse s i
/-- Lines of the entry found by ID, or [] if none. -/
def revLines (s : State) (i : EntryId) : List Line :=
  match findEntry s.journal i with
  | some e => e.lines
  | none => []
def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    if ValidReverse s i then
      (.ok, { s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed })
    else (.rejected, s)

theorem req_invalid_noop_tmp : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    have h2 : ¬ ValidPost s e := h
    simp [step, h2]
  | reverse i =>
    have h2 : ¬ ValidReverse s i := h
    simp [step, h2]

theorem myHelperTest : True := by trivial

theorem myHelperTest2 : True := by trivial

theorem helper_mem_ids_test : ids ([] : List Entry) = [] := by rfl

theorem helper_lemma_test3 : 1 = 1 := rfl

theorem my_foo_aux : 1 = 1 := rfl

theorem my_foo_aux2 : 2 = 2 := rfl

theorem aux_ids_append_singleton (l : List Entry) (e : Entry) : ids (l ++ [e]) = ids l ++ [e.id] := by simp [ids]

theorem aux_find_singleton_test (e : Entry) : findEntry [e] e.id = some e := by simp [findEntry]

theorem aux_find_mem {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; rw [h]; simp
    · simp [heq] at h; exact List.mem_cons_of_mem hd (ih h)

theorem aux_find_id {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e.id = i := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; rw [← h]; exact heq
    · simp [heq] at h; exact ih h

theorem aux_if_comm (x a : AccountId) (c : Int) :
    (if x = a then c else 0) = (if a = x then c else 0) := by
  by_cases h : x = a
  · subst h; simp
  · have h2 : ¬ (a = x) := fun hh => h hh.symm
    simp [h, h2]

theorem aux_single_sum_nd (accs : List AccountId) (hnd : accs.Nodup) (x : AccountId) (c : Int) :
    sumOver accs (fun a => if x = a then c else 0) = if x ∈ accs then c else 0 := by
  have hcon : sumOver accs (fun a => if x = a then c else (0 : Int)) =
      sumOver accs (fun a => if a = x then c else (0 : Int)) := by
    apply sumOver_congr
    intro a _; exact aux_if_comm x a c
  rw [hcon]
  exact sumOver_ite_eq hnd x c

theorem aux_zero_sumx (accs : List AccountId) :
    sumOver accs (fun _ : AccountId => (0 : Int)) = 0 := by
  induction accs with
  | nil => rfl
  | cons hd tl ih => simp [ih]

theorem aux_net_swapx (accs : List AccountId) (hnd : accs.Nodup) (ls : List Line) :
    sumOver accs (fun a => netOf ls a) =
    sumOver ls (fun l => if l.1 ∈ accs then l.2 else 0) := by
  induction ls with
  | nil => simp [netOf, aux_zero_sumx]
  | cons hd tl ih =>
    have h1 : (fun a => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      funext a; rfl
    rw [h1, sumOver_add, ih]
    have h2 : sumOver accs (fun a => if hd.1 = a then hd.2 else (0 : Int)) =
        (if hd.1 ∈ accs then hd.2 else 0) := aux_single_sum_nd accs hnd hd.1 hd.2
    rw [h2]
    simp [sumOver_cons]

theorem aux_net_zero_of_wf2 (accs : List AccountId) (hnd : accs.Nodup)
    (ls : List Line) (hmem : ∀ l ∈ ls, l.1 ∈ accs) (hsum : lineSum ls = 0) :
    sumOver accs (fun a => netOf ls a) = 0 := by
  rw [aux_net_swapx accs hnd ls]
  have hc : ∀ l ∈ ls, (if l.1 ∈ accs then l.2 else (0 : Int)) = l.2 := by
    intro l hl; simp [hmem l hl]
  have hcon := sumOver_congr ls _ _ hc
  have hdef : sumOver ls (fun l => (·.2 : Line → Int) l) = sumOver ls (·.2) := rfl
  unfold lineSum at hsum
  rw [hcon]; exact hsum

theorem aux_activeNet_post (j : List Entry) (rev : List EntryId) (e : Entry) (a : AccountId)
    (h : e.id ∉ rev) :
    sumOver (j ++ [e]) (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a)
    = sumOver j (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) + netOf e.lines a := by
  rw [sumOver_append]
  simp [h]

theorem aux_mem_rev_cons_ne2 {x i : EntryId} {rev : List EntryId} (h : x ≠ i) :
    (x ∈ i :: rev) = (x ∈ rev) := by simp [h]

theorem aux_rev_head_ne3 {hd : Entry} {i : EntryId} {rev : List EntryId} (h1 : hd.id ≠ i) (a : AccountId) :
    (if hd.id ∈ i :: rev then (0 : Int) else netOf hd.lines a)
    = (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) := by
  have h : (hd.id ∈ i :: rev) = (hd.id ∈ rev) := aux_mem_rev_cons_ne2 h1
  simp only [h]

theorem aux_ids_cons_eq (hd : Entry) (tl : List Entry) : ids (hd :: tl) = hd.id :: ids tl := rfl

theorem aux_nodup_tail2 {hd : Entry} {tl : List Entry} (h : (ids (hd :: tl)).Nodup) : (ids tl).Nodup := by
  have h2 : (hd.id :: ids tl).Nodup := h
  exact (List.nodup_cons.mp h2).2

theorem aux_nodup_head_notmem2 {hd : Entry} {tl : List Entry} (h : (ids (hd :: tl)).Nodup) : hd.id ∉ ids tl := by
  have h2 : (hd.id :: ids tl).Nodup := h
  exact (List.nodup_cons.mp h2).1

theorem aux_find_of_mem_ids2 (j : List Entry) (i : EntryId) (h : i ∈ ids j) :
    ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons hd tl ih =>
    simp only [findEntry]
    by_cases heq : hd.id = i
    · exact ⟨hd, by simp [heq]⟩
    · have h2 : (if hd.id = i then (some hd : Option Entry) else findEntry tl i) = findEntry tl i := by simp [heq]
      rw [h2]
      have hmem : i ∈ ids tl := by
        have h3 : i ∈ hd.id :: ids tl := h
        simp only [List.mem_cons] at h3
        rcases h3 with h33 | h34
        · exact absurd h33.symm heq
        · exact h34
      exact ih hmem

theorem aux_notmem_ids_ne (tl : List Entry) (i : EntryId) (h : i ∉ ids tl) :
    ∀ e' ∈ tl, e'.id ≠ i := by
  intro e' he' heq
  apply h
  have hm : e'.id ∈ tl.map (·.id) := List.mem_map.mpr ⟨e', he', rfl⟩
  rw [heq] at hm
  exact hm

theorem aux_tl_congr (tl : List Entry) (rev : List EntryId) (i : EntryId) (a : AccountId)
    (h : i ∉ ids tl) :
    sumOver tl (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a)
    = sumOver tl (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) := by
  apply sumOver_congr
  intro e' he'
  have hne : e'.id ≠ i := aux_notmem_ids_ne tl i h e' he'
  exact aux_rev_head_ne3 hne a

theorem aux_chk3 (hd : Entry) (tl : List Entry) (e : Entry) : ((hd :: tl) ++ [e]) = hd :: (tl ++ [e]) := by rfl

theorem aux_probe1 (hd : Entry) (tl : List Entry) (e : Entry) (hne : hd.id ≠ e.id) : (if hd.id = e.id then (some hd : Option Entry) else findEntry (tl ++ [e]) e.id) = findEntry (tl ++ [e]) e.id := by simp [hne]

theorem aux_probe2 (hd : Entry) (tl : List Entry) (e : Entry) (hne : hd.id ≠ e.id) (ih : findEntry (tl ++ [e]) e.id = some e) : findEntry (hd :: (tl ++ [e])) e.id = some e := by unfold findEntry; simp [hne, ih]



theorem plan0_validPost_of_post_ok (s : State) (e : Entry) (h : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases hV : ValidPost s e
  · exact hV
  · have hcon : (step s (.post e)).1 = .rejected := by simp [step, hV]
    rw [hcon] at h
    contradiction






theorem plan0_reverse_after_post_ok (s : State) (e : Entry) (h : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by
  have hS : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
    simp [step, h]
  have hmem : e.id ∈ ids (s.journal ++ [e]) := by simp [ids]
  have hnot : e.id ∉ s.reversed := h.2.2.2.2.2
  have hVR2 : ValidReverse ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) e.id := ⟨hmem, hnot⟩
  rw [hS]
  simp [step, hVR2]




theorem plan0_findEntry_append_self_aux_test123 : True := by trivial

theorem plan0_findEntry_append_self_check2 (j : List Entry) (e : Entry) (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
    have hne : hd.id ≠ e.id := by
      intro hcontra
      apply h
      rw [hids]
      exact List.mem_cons.mpr (Or.inl hcontra.symm)
    have htl : e.id ∉ ids tl := by
      intro hmem
      apply h
      rw [hids]
      exact List.mem_cons.mpr (Or.inr hmem)
    have heq : (hd :: tl) ++ [e] = hd :: (tl ++ [e]) := rfl
    rw [heq]
    simp only [findEntry, hne, ↓reduceIte]
    exact ih htl

theorem plan0_findEntry_append_self (j : List Entry) (e : Entry) (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have hids : ids (hd :: tl) = hd.id :: ids tl := rfl
    have hne : hd.id ≠ e.id := by
      intro hcontra
      apply h
      rw [hids]
      exact List.mem_cons.mpr (Or.inl hcontra.symm)
    have htl : e.id ∉ ids tl := by
      intro hmem
      apply h
      rw [hids]
      exact List.mem_cons.mpr (Or.inr hmem)
    have heq : (hd :: tl) ++ [e] = hd :: (tl ++ [e]) := rfl
    rw [heq]
    simp only [findEntry, hne, ↓reduceIte]
    exact ih htl

theorem plan0_validPost_of_post_ok_proof : ∀ (s : State) (e : Entry), (step s (.post e)).1 = .ok → ValidPost s e := by
  intro s e h
  by_cases hV : ValidPost s e
  · exact hV
  · have hcon : (step s (.post e)).1 = .rejected := by simp [step, hV]
    rw [hcon] at h
    contradiction

theorem plan0_validReverse_after_post (s : State) (e : Entry) (h : ValidPost s e) : ValidReverse (step s (.post e)).2 e.id := by
  have hV : ValidPost s e := h
  have hstep2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
    simp [step, hV]
  rw [hstep2]
  obtain ⟨hne, hmem, hne0, hsum, hnidJ, hnidR⟩ := h
  constructor
  · simp [ids]
  · simp only
    exact hnidR

theorem plan0_revLines_after_post (s : State) (e : Entry) (h : ValidPost s e) : revLines (step s (.post e)).2 e.id = e.lines := by
  have hJ : (step s (.post e)).2.journal = s.journal ++ [e] := by simp [step, h]
  have hnid : e.id ∉ ids s.journal := h.2.2.2.2.1
  have hfind : findEntry (s.journal ++ [e]) e.id = some e :=
    plan0_findEntry_append_self s.journal e hnid
  have hfind2 : findEntry (step s (.post e)).2.journal e.id = some e := by
    rw [hJ]; exact hfind
  unfold revLines
  rw [hfind2]

theorem tmp_ok2 (s : State) (e : Entry) (h : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by
  have hS : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
    simp [step, h]
  have hmem : e.id ∈ ids (s.journal ++ [e]) := by simp [ids]
  have hnot : e.id ∉ s.reversed := h.2.2.2.2.2
  have hVR2 : ValidReverse ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) e.id := ⟨hmem, hnot⟩
  rw [hS]
  simp [step, hVR2]

theorem tmp_bal2 (s : State) (e : Entry) (h : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).2.balance = s.balance := by
  have hS : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
    simp [step, h]
  have hfind : findEntry (s.journal ++ [e]) e.id = some e :=
    plan0_findEntry_append_self s.journal e h.2.2.2.2.1
  have hRL : revLines ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) e.id = e.lines := by
    unfold revLines
    rw [hfind]
  have hmem : e.id ∈ ids (s.journal ++ [e]) := by simp [ids]
  have hVR2 : ValidReverse ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) e.id :=
    ⟨hmem, h.2.2.2.2.2⟩
  have hS2 : (step (step s (.post e)).2 (.reverse e.id)).2 =
      ({ ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) with
        balance := fun a => s.balance a + netOf e.lines a - netOf e.lines a,
        reversed := e.id :: s.reversed } : State) := by
    rw [hS]
    have hstep : step ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) (.reverse e.id) =
        (.ok, ({ ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) with
          balance := fun a => ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State).balance a - netOf (revLines ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) e.id) a,
          reversed := e.id :: ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State).reversed } : State)) := by
      simp [step, hVR2]
    have hbalrw : (fun a => ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State).balance a - netOf (revLines ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) e.id) a) =
        (fun a => s.balance a + netOf e.lines a - netOf e.lines a) := by
      funext a
      rw [hRL]
    rw [hstep, hbalrw]
  rw [hS2]
  funext a
  show s.balance a + netOf e.lines a - netOf e.lines a = s.balance a
  omega

theorem plan1_step_post_eq (s : State) (e : Entry) (h : ValidPost s e) :
    step s (.post e) =
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a,
                     journal := s.journal ++ [e] }) := by simp [step, h]




theorem plan1_validReverse_after_post (s : State) (e : Entry) (h : ValidPost s e) :
    ValidReverse (step s (.post e)).2 e.id := by
  exact plan0_validReverse_after_post s e h




theorem plan1_step_post_eq_proof (s : State) (e : Entry) (h : ValidPost s e) :
    step s (.post e) =
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a,
                     journal := s.journal ++ [e] }) := by simp [step, h]

theorem plan1_mem_ids_append_self (j : List Entry) (e : Entry) :
    e.id ∈ ids (j ++ [e]) := by
  rw [aux_ids_append_singleton]
  simp

theorem plan1_validReverse_after_post_proof (s : State) (e : Entry) (h : ValidPost s e) :
    ValidReverse (step s (.post e)).2 e.id :=
  plan0_validReverse_after_post s e h

theorem plan1_reverse_ok_of_valid (s : State) (i : EntryId) (h : ValidReverse s i) :
    (step s (.reverse i)).1 = .ok := by simp [step, h]

theorem plan0_reverse_after_post_balance (s : State) (e : Entry) (h : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).2.balance = s.balance := by
  exact tmp_bal2 s e h

theorem plan0_reverse_after_post_ok_aux : ∀ (s : State) (e : Entry), ValidPost s e → (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by
  intro s e h
  exact tmp_ok2 s e h

theorem plan0_reverse_after_post_ok_testuniq (s : State) (e : Entry) (h : ValidPost s e) : True := by trivial

theorem aux_validReverse_of_reverse_ok (s : State) (i : EntryId) (h : (step s (.reverse i)).1 = .ok) : ValidReverse s i := by
  by_cases hV : ValidReverse s i
  · exact hV
  · have hcon : (step s (.reverse i)).1 = .rejected := by simp [step, hV]
    rw [hcon] at h
    contradiction

theorem tmp_trial_post_total (s : State) (e : Entry) (hWF : WellFormed s)
    (hV : ValidPost s e) :
    total ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) = total s := by
  obtain ⟨hAcc, hIds, hRevSub, hJWF⟩ := hWF
  obtain ⟨hne, hmem, hne0, hsum, hnidJ, hnidR⟩ := hV
  unfold total
  have hcongr : sumOver s.accounts (({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State).balance) =
      sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    apply sumOver_congr
    intro a _; rfl
  rw [hcongr]
  rw [sumOver_add]
  have hzero : sumOver s.accounts (fun a => netOf e.lines a) = 0 :=
    aux_net_zero_of_wf2 s.accounts hAcc e.lines hmem hsum
  rw [hzero]
  simp

theorem tmp_revLines_mem (s : State) (i : EntryId) (hWF : WellFormed s) (hV : ValidReverse s i) :
    ∀ l ∈ revLines s i, l.1 ∈ s.accounts := by
  obtain ⟨hAcc, hIds, hRevSub, hJWF⟩ := hWF
  obtain ⟨hmemJ, hnotrev⟩ := hV
  obtain ⟨e, he⟩ := aux_find_of_mem_ids2 s.journal i hmemJ
  have hRL : revLines s i = e.lines := by unfold revLines; rw [he]
  have hemem : e ∈ s.journal := aux_find_mem he
  have hWFe := hJWF e hemem
  rw [hRL]
  exact hWFe.1

theorem tmp_revLines_sum (s : State) (i : EntryId) (hWF : WellFormed s) (hV : ValidReverse s i) :
    lineSum (revLines s i) = 0 := by
  obtain ⟨hAcc, hIds, hRevSub, hJWF⟩ := hWF
  obtain ⟨hmemJ, hnotrev⟩ := hV
  obtain ⟨e, he⟩ := aux_find_of_mem_ids2 s.journal i hmemJ
  have hRL : revLines s i = e.lines := by unfold revLines; rw [he]
  have hemem : e ∈ s.journal := aux_find_mem he
  have hWFe := hJWF e hemem
  rw [hRL]
  exact hWFe.2

theorem tmp_trial_reverse_total2 (s : State) (i : EntryId) (hWF : WellFormed s)
    (hV : ValidReverse s i) :
    total ({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State) = total s := by
  obtain ⟨hAcc, hIds, hRevSub, hJWF⟩ := hWF
  have hmem : ∀ l ∈ revLines s i, l.1 ∈ s.accounts :=
    tmp_revLines_mem s i ⟨hAcc, hIds, hRevSub, hJWF⟩ hV
  have hsum : lineSum (revLines s i) = 0 :=
    tmp_revLines_sum s i ⟨hAcc, hIds, hRevSub, hJWF⟩ hV
  unfold total
  have hcongr : sumOver s.accounts (({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State).balance) =
      sumOver s.accounts (fun a => s.balance a - netOf (revLines s i) a) := by
    apply sumOver_congr
    intro a _; rfl
  rw [hcongr]
  rw [sumOver_sub]
  have hzero : sumOver s.accounts (fun a => netOf (revLines s i) a) = 0 :=
    aux_net_zero_of_wf2 s.accounts hAcc (revLines s i) hmem hsum
  rw [hzero]
  simp

theorem aux_active_reverse_uniq2 (j : List Entry) (rev : List EntryId) (i : EntryId) (e : Entry) (a : AccountId)
    (hNodup : (ids j).Nodup) (hNotRev : i ∉ rev) (hFind : findEntry j i = some e) :
    sumOver j (fun e' => if e'.id ∈ i :: rev then (0 : Int) else netOf e'.lines a)
    = sumOver j (fun e' => if e'.id ∈ rev then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  induction j with
  | nil => simp [findEntry] at hFind
  | cons hd tl ih =>
    simp only [findEntry] at hFind
    by_cases heq : hd.id = i
    · simp [heq] at hFind
      subst hFind
      have hNodup' : (ids (hd :: tl)).Nodup := by simpa [ids] using hNodup
      have hNotIn : i ∉ ids tl := by
        have hnm : hd.id ∉ ids tl := aux_nodup_head_notmem2 hNodup'
        -- heq : hd.id = i, need rewrite
        have : hd.id = i := heq
        rw [this] at hnm
        exact hnm
      have hTailEq := aux_tl_congr tl rev i a hNotIn
      simp only [sumOver_cons]
      have hHeadNew : (if hd.id ∈ i :: rev then (0 : Int) else netOf hd.lines a) = 0 := by
        simp [heq]
      have hHeadOld : (if hd.id ∈ rev then (0 : Int) else netOf hd.lines a) = netOf hd.lines a := by
        have hnr : hd.id ∉ rev := by rw [heq]; exact hNotRev
        simp [hnr]
      rw [hHeadNew, hHeadOld, hTailEq]
      omega
    · simp [heq] at hFind
      have hNodup' : (ids (hd :: tl)).Nodup := by simpa [ids] using hNodup
      have hNodupTl : (ids tl).Nodup := aux_nodup_tail2 hNodup'
      have hIH := ih hNodupTl hFind
      have hHeadEq := aux_rev_head_ne3 (a := a) (rev := rev) heq
      simp only [sumOver_cons]
      rw [hHeadEq, hIH]
      omega

theorem aux_revLines_of_find (s : State) (i : EntryId) (e : Entry) (h : findEntry s.journal i = some e) :
    revLines s i = e.lines := by unfold revLines; rw [h]

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  simp [step, h]

theorem req_invalid_noop     : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    have h2 : ¬ ValidPost s e := h
    simp [step, h2]
  | reverse i =>
    have h2 : ¬ ValidReverse s i := h
    simp [step, h2]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  by_cases hV : ValidPost s e
  · have hstep : step s (.post e) = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by
      simp [step, hV]
    have h2 : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by
      rw [hstep]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h2]
    · rw [h2]
    · rw [h2]
    · rw [h2]
    · intro a; rw [h2]
  · have hcon : (step s (.post e)).1 = .rejected := by simp [step, hV]
    rw [hcon] at hok
    contradiction

theorem req_reverse_effects  : ReverseEffects step := by
  intro s i e hok hfind
  have hRev : revLines s i = e.lines := by
    unfold revLines
    rw [hfind]
  by_cases hV : ValidReverse s i
  · have hstep : step s (.reverse i) = (.ok, ({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State)) := by
      simp [step, hV]
    have h2 : (step s (.reverse i)).2 = (({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State)) := by
      rw [hstep]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h2]
    · rw [h2]
    · rw [h2]
    · intro x; rw [h2]; simp
    · intro a; rw [h2]; simp only
      rw [hRev]
  · have hcon : (step s (.reverse i)).1 = .rejected := by simp [step, hV]
    rw [hcon] at hok
    contradiction

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  by_cases hV : ValidReverse s i
  · have hstep : step s (.reverse i) = (.ok, ({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State)) := by
      simp [step, hV]
    have h2 : (step s (.reverse i)).2 = (({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State)) := by
      rw [hstep]
    have hNot : ¬ ValidReverse ((step s (.reverse i)).2) i := by
      rw [h2]
      intro hc
      have hmem := hc.2
      simp at hmem
    have hni : ¬ Valid ((step s (.reverse i)).2) (.reverse i) := by
      simp only [Valid]
      exact hNot
    have hnoop := req_invalid_noop _ _ hni
    exact hnoop
  · have hcon : (step s (.reverse i)).1 = .rejected := by simp [step, hV]
    rw [hcon] at hok
    contradiction

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hV : ValidPost s e := plan0_validPost_of_post_ok s e hok
  exact ⟨plan0_reverse_after_post_ok s e hV, plan0_reverse_after_post_balance s e hV⟩

theorem req_trial_balance : TrialBalance step := by
  intro s c hWF hok
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hstep2 : (step s (.post e)).2 = ({ s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } : State) := by
        simp [step, hV]
      rw [hstep2]
      exact tmp_trial_post_total s e hWF hV
    · have hcon : (step s (.post e)).1 = .rejected := by simp [step, hV]
      rw [hcon] at hok
      contradiction
  | reverse i =>
    by_cases hV : ValidReverse s i
    · have hstep2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State) := by
        simp [step, hV]
      rw [hstep2]
      exact tmp_trial_reverse_total2 s i hWF hV
    · have hcon : (step s (.reverse i)).1 = .rejected := by simp [step, hV]
      rw [hcon] at hok
      contradiction

theorem req_well_formed : StaysWellFormed step := by
  intro s c hWF
  obtain ⟨hAcc, hIds, hRevSub, hJWF⟩ := hWF
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hstep2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        simp [step, hV]
      rw [hstep2]
      obtain ⟨hne, hmem, hne0, hsum, hnidJ, hnidR⟩ := hV
      have hidsEq : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := by simp [ids]
      refine ⟨hAcc, ?_, ?_, ?_⟩
      · rw [hidsEq]
        rw [List.nodup_append]
        refine ⟨hIds, by simp, fun a ha b hb heq => ?_⟩
        simp at hb
        subst hb
        exact hnidJ (heq ▸ ha)
      · intro i hi
        rw [hidsEq]
        apply List.mem_append.mpr
        exact Or.inl (hRevSub i hi)
      · intro e' he'
        have heJ : e' ∈ s.journal ++ [e] := he'
        rw [List.mem_append] at heJ
        rcases heJ with hmemJ | hsing
        · exact hJWF e' hmemJ
        · simp at hsing; subst hsing; exact ⟨hmem, hsum⟩
    · have hstep2 : (step s (.post e)).2 = s := by simp [step, hV]
      rw [hstep2]; exact ⟨hAcc, hIds, hRevSub, hJWF⟩
  | reverse i =>
    by_cases hV : ValidReverse s i
    · have hstep2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State) := by
        simp [step, hV]
      rw [hstep2]
      obtain ⟨hmemJ, hnotrev⟩ := hV
      refine ⟨hAcc, hIds, ?_, hJWF⟩
      · intro x hx
        simp at hx
        rcases hx with rfl | hx
        · exact hmemJ
        · exact hRevSub x hx
    · have hstep2 : (step s (.reverse i)).2 = s := by simp [step, hV]
      rw [hstep2]; exact ⟨hAcc, hIds, hRevSub, hJWF⟩

theorem req_consistent : StaysConsistent step := by
  intro s c hWF hCons
  cases c with
  | post e =>
    by_cases hV : ValidPost s e
    · have hstep2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        simp [step, hV]
      rw [hstep2]
      obtain ⟨hAcc, hIds, hRevSub, hJWF⟩ := hWF
      obtain ⟨hne, hmem, hne0, hsum, hnidJ, hnidR⟩ := hV
      intro a
      show (({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State).balance a) =
        ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State).opening a +
        activeNet ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) a
      simp only
      have hOld : s.balance a = s.opening a + activeNet s a := hCons a
      have hAct : activeNet ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) a
          = activeNet s a + netOf e.lines a := by
        unfold activeNet
        simp only
        exact aux_activeNet_post s.journal s.reversed e a hnidR
      rw [hAct, hOld]
      omega
    · have hstep2 : (step s (.post e)).2 = s := by simp [step, hV]
      rw [hstep2]
      exact hCons
  | reverse i =>
    by_cases hV : ValidReverse s i
    · have hstep2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State) := by
        simp [step, hV]
      rw [hstep2]
      obtain ⟨hAcc, hIds, hRevSub, hJWF⟩ := hWF
      obtain ⟨hmemJ, hnotrev⟩ := hV
      obtain ⟨e, he⟩ := aux_find_of_mem_ids2 s.journal i hmemJ
      have hRL : revLines s i = e.lines := aux_revLines_of_find s i e he
      intro a
      show (({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State).balance a) =
        (({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State).opening a) +
        activeNet ({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State) a
      simp only
      have hOld : s.balance a = s.opening a + activeNet s a := hCons a
      have hAct : activeNet ({ s with balance := fun a => s.balance a - netOf (revLines s i) a, reversed := i :: s.reversed } : State) a
          = activeNet s a - netOf e.lines a := by
        unfold activeNet
        simp only
        exact aux_active_reverse_uniq2 s.journal s.reversed i e a hIds hnotrev he
      rw [hAct, hRL] at *
      -- goal: s.balance a - netOf e.lines a = s.opening a + (activeNet s a - netOf e.lines a)
      rw [hOld]
      omega
    · have hstep2 : (step s (.reverse i)).2 = s := by simp [step, hV]
      rw [hstep2]
      exact hCons

end Reversal
