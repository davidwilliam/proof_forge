import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow
instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if (s.clients.map Client.id).Nodup then
    match lookup s.clients r.client with
    | some c =>
      if c.start ≤ r.time ∧ windowCount s c r.time < s.limit then
        (.ok, { s with clients := s.clients.map fun x =>
          if x.id = r.client then advance s x r.time else x })
      else (.rejected, s)
    | none => (.rejected, s)
  else (.rejected, s)

theorem aux_valid : ValidSucceeds step := by
  intro s r h
  unfold Admissible at h
  obtain ⟨hnodup, hadm⟩ := h
  show (step s r).1 = .ok
  unfold step
  simp only [hnodup, ↓reduceIte]
  have hlook : ∃ c, lookup s.clients r.client = some c := by
    cases he : lookup s.clients r.client with
    | none =>
      rw [he] at hadm
      simp [Admits] at hadm
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hlook
  rw [hc] at hadm ⊢
  simp only [Admits] at hadm
  obtain ⟨hle, hlt⟩ := hadm
  simp only [hle, hlt, and_self, ↓reduceIte]

theorem foo_test : True := trivial

theorem myLem2 (n : Nat) : n = n := rfl

theorem mapAdvLookupNe3 (s : State) (j t i : Nat) (l : List Client) (hne : i ≠ j) :
    lookup (l.map fun x => if x.id = j then advance s x t else x) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hji : j ≠ i := fun h => hne h.symm
    by_cases hx : x.id = j
    · have hxi : x.id ≠ i := by intro h; apply hne; rw [← hx, h]
      have hmapped : (advance s x t).id ≠ i := hxi
      have e1 : (List.map (fun x => if x.id = j then advance s x t else x) (x :: xs)) =
          (advance s x t) :: (List.map (fun x => if x.id = j then advance s x t else x) xs) := by
        simp [hx]
      rw [e1]
      rw [lookup_cons, lookup_cons]
      simp [hxi, hmapped, ih]
    · have e1 : (List.map (fun x => if x.id = j then advance s x t else x) (x :: xs)) =
          x :: (List.map (fun x => if x.id = j then advance s x t else x) xs) := by
        simp [hx]
      rw [e1]
      rw [lookup_cons, lookup_cons]
      by_cases heq : x.id = i
      · simp [heq]
      · simp [heq, ih]

theorem lookup_map_adv_same6 (s : State) (l : List Client) (j t : Nat) (c : Client)
    (h : lookup l j = some c) :
    lookup (l.map fun x => if x.id = j then advance s x t else x) j = some (advance s c t) := by
  induction l with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons] at h ⊢
    by_cases hx : x.id = j
    · simp only [hx, ↓reduceIte] at h
      simp at h
      subst h
      simp only [hx, ↓reduceIte, advance]
    · simp only [hx, ↓reduceIte] at h ⊢
      exact ih h

theorem tmp_nodup_test (a : Nat) (l : List Nat) : ((a :: l : List Nat).Nodup ↔ a ∉ l ∧ l.Nodup) := by exact List.nodup_cons
#check List.nodup_cons
#check List.mem_map
#check List.mem_cons

theorem tmp_check_sig : True := by
  have h1 : ∀ {α β : Type} {f : α → β} {l : List α} {y : β}, y ∈ l.map f → ∃ x ∈ l, f x = y := by
    intro α β f l y h
    exact (List.mem_map.mp h)
  trivial

theorem adv_count_le_aux (s : State) (c : Client) (t : Nat)
    (hlt : windowCount s c t < s.limit) :
    (advance s c t).count ≤ s.limit := by
  unfold advance
  simp only
  omega

theorem tmp_inj1 (s : State) (c : Client) (t : Nat)
    (hlt : windowCount s c t < s.limit) :
    (advance s c t).count ≤ s.limit := by
  simp only [advance] at *
  omega

theorem nodup_unique_mem (l : List Client) (hnod : (l.map Client.id).Nodup)
    (j : Nat) (c x : Client) (hc : lookup l j = some c) (hxmem : x ∈ l) (hxid : x.id = j) :
    x = c := by
  induction l generalizing j c x with
  | nil =>
    simp at hxmem
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnod
    obtain ⟨hnotin, hnod_tl⟩ := hnod
    rw [lookup_cons] at hc
    simp only [List.mem_cons] at hxmem
    by_cases hhd : hd.id = j
    · simp only [hhd, ↓reduceIte] at hc
      cases hc
      rcases hxmem with rfl | hmem
      · rfl
      · exfalso
        have hmem_map : x.id ∈ tl.map Client.id := List.mem_map.mpr ⟨x, hmem, rfl⟩
        have heq : x.id = hd.id := by rw [hxid, hhd]
        rw [heq] at hmem_map
        exact hnotin hmem_map
    · simp only [hhd, ↓reduceIte] at hc
      rcases hxmem with rfl | hmem
      · exfalso; exact hhd hxid
      · exact ih hnod_tl j c x hc hmem hxid

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold Admissible at h
  obtain ⟨hnodup, hadm⟩ := h
  show (step s r).1 = .ok
  unfold step
  simp only [hnodup, ↓reduceIte]
  have hlook : ∃ c, lookup s.clients r.client = some c := by
    cases he : lookup s.clients r.client with
    | none =>
      rw [he] at hadm
      simp [Admits] at hadm
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hlook
  rw [hc] at hadm ⊢
  simp only [Admits] at hadm
  obtain ⟨hle, hlt⟩ := hadm
  simp only [hle, hlt, and_self, ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r hna
  unfold Admissible at hna
  by_cases hnodup : (s.clients.map Client.id).Nodup
  · cases he : lookup s.clients r.client with
    | none =>
      have hstep : step s r = (.rejected, s) := by
        unfold step
        simp only [hnodup, ↓reduceIte, he]
      exact hstep
    | some c =>
      by_cases hcond : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
      · exfalso; apply hna
        constructor
        · exact hnodup
        · rw [he]
          simp only [Admits]
          exact hcond
      · have hstep : step s r = (.rejected, s) := by
          unfold step
          simp only [hnodup, ↓reduceIte, he, hcond, ↓reduceIte]
        exact hstep
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp only [hnodup, ↓reduceIte]
    exact hstep

theorem req_isolation : Isolation step := by
  intro s r i hne
  by_cases hnodup : (s.clients.map Client.id).Nodup
  · cases he : lookup s.clients r.client with
    | none =>
      have hstep : step s r = (.rejected, s) := by
        unfold step
        simp [hnodup, he]
      rw [hstep]
    | some c =>
      by_cases hcond : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
      · have hstep : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
          unfold step
          simp [hnodup, he, hcond]
        rw [hstep]
        simp only
        exact mapAdvLookupNe3 s r.client r.time i s.clients hne
      · have hstep : step s r = (.rejected, s) := by
          unfold step
          simp [hnodup, he, hcond]
        rw [hstep]
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hnodup]
    rw [hstep]

theorem req_reset : ResetRule step := by
  intro s r hOk c hc
  have hNodup : (s.clients.map Client.id).Nodup := by
    by_cases hnn : (s.clients.map Client.id).Nodup
    · exact hnn
    · have hstep : step s r = (.rejected, s) := by unfold step; simp only [hnn, ↓reduceIte]
      rw [hstep] at hOk
      simp at hOk
  have hcond : c.start ≤ r.time ∧ windowCount s c r.time < s.limit := by
    by_cases hcc : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
    · exact hcc
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        simp only [hNodup, ↓reduceIte, hc]
        simp only [hcc, ↓reduceIte]
      rw [hstep] at hOk
      simp at hOk
  obtain ⟨hle, hlt⟩ := hcond
  have hstep2 : (step s r).2 = { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x } := by
    unfold step
    simp only [hNodup, ↓reduceIte, hc, hle, hlt, and_self, ↓reduceIte]
  have hlook2 : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
    rw [hstep2]
    exact lookup_map_adv_same6 s s.clients r.client r.time c hc
  refine ⟨advance s c r.time, hlook2, ?_, ?_⟩
  · intro hexp
    constructor
    · unfold advance windowStart
      simp [hexp]
    · unfold advance windowCount
      simp [hexp]
  · intro hlt2
    have hexp_neg : ¬ (c.start + s.window ≤ r.time) := by omega
    constructor
    · unfold advance windowStart
      simp [hexp_neg]
    · unfold advance windowCount
      simp [hexp_neg]

theorem req_effects : Effects step := by
  intro s r hOk
  have hNodup : (s.clients.map Client.id).Nodup := by
    by_cases hnn : (s.clients.map Client.id).Nodup
    · exact hnn
    · have hstep : step s r = (.rejected, s) := by unfold step; simp only [hnn, ↓reduceIte]
      rw [hstep] at hOk
      simp at hOk
  have hEx : ∃ c, lookup s.clients r.client = some c := by
    cases he : lookup s.clients r.client with
    | none =>
      have hstep : step s r = (.rejected, s) := by unfold step; simp only [hNodup, ↓reduceIte, he]
      rw [hstep] at hOk
      simp at hOk
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hEx
  have hcond : c.start ≤ r.time ∧ windowCount s c r.time < s.limit := by
    by_cases hcc : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
    · exact hcc
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        simp only [hNodup, ↓reduceIte, hc]
        simp only [hcc, ↓reduceIte]
      rw [hstep] at hOk
      simp at hOk
  obtain ⟨hle, hlt⟩ := hcond
  have h2 : (step s r).2 = { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x } := by
    unfold step
    simp only [hNodup, ↓reduceIte, hc, hle, hlt, and_self, ↓reduceIte]
  have hadv_id : ∀ (x : Client), (if x.id = r.client then advance s x r.time else x).id = x.id := by
    intro x
    by_cases hx : x.id = r.client <;> simp [hx, advance]
  have hmap_ids : ((s.clients.map fun x => if x.id = r.client then advance s x r.time else x).map Client.id) = s.clients.map Client.id := by
    have h : List.map (fun x => (if x.id = r.client then advance s x r.time else x).id) s.clients = List.map Client.id s.clients := by
      apply List.map_congr_left
      intro x _
      exact hadv_id x
    simpa [List.map_map] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [h2]
  · rw [h2]
    exact hmap_ids
  · intro i
    rw [h2]
    simp only
    by_cases hi : i = r.client
    · subst hi
      rw [lookup_map_adv_same6 s s.clients r.client r.time c hc]
      unfold expectedLookup
      simp [hc]
    · rw [mapAdvLookupNe3 s r.client r.time i s.clients hi]
      unfold expectedLookup
      simp [hi]

theorem req_window_bound   : WindowBound step := by
  unfold WindowBound
  intro s r hbound c' hmem
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · cases he : lookup s.clients r.client with
    | none =>
      have hstep : step s r = (.rejected, s) := by unfold step; simp only [hNodup, ↓reduceIte, he]
      rw [hstep] at hmem ⊢
      exact hbound c' hmem
    | some c =>
      by_cases hcond : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
      · obtain ⟨hle, hlt⟩ := hcond
        have hstep2 : (step s r).2 = { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x } := by
          unfold step; simp only [hNodup, ↓reduceIte, he, hle, hlt, and_self, ↓reduceIte]
        rw [hstep2] at hmem ⊢
        simp at hmem ⊢
        obtain ⟨x, hxmem, hfx⟩ := hmem
        by_cases hxeq : x.id = r.client
        · have hx_eq_c : x = c := nodup_unique_mem s.clients hNodup r.client c x he hxmem hxeq
          rw [hx_eq_c] at hxeq
          rw [hx_eq_c] at hfx
          simp only [hxeq, ↓reduceIte] at hfx
          subst hfx
          exact adv_count_le_aux s c r.time hlt
        · simp only [hxeq, ↓reduceIte] at hfx
          subst hfx
          exact hbound x hxmem
      · have hstep : step s r = (.rejected, s) := by
          unfold step; simp only [hNodup, ↓reduceIte, he, hcond, ↓reduceIte]
        rw [hstep] at hmem ⊢
        exact hbound c' hmem
  · have hstep : step s r = (.rejected, s) := by unfold step; simp only [hNodup, ↓reduceIte]
    rw [hstep] at hmem ⊢
    exact hbound c' hmem

end FixedWindow
