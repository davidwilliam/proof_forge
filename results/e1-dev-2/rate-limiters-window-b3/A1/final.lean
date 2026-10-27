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

theorem tmp_debug3 : ValidSucceeds step := by
  intro s r h
  obtain ⟨hNodup, hAdm⟩ := h
  unfold step
  rw [if_pos hNodup]
  cases hLc : lookup s.clients r.client with
  | none =>
    rw [hLc] at hAdm
    simp [Admits] at hAdm
  | some c =>
    rw [hLc] at hAdm
    simp [Admits] at hAdm
    obtain ⟨h1, h2⟩ := hAdm
    simp [h1, h2]

theorem foo_test : True := trivial

theorem advance_id_thm (s : State) (c : Client) (t : Nat) : (advance s c t).id = c.id := by
  unfold advance
  simp

theorem lookup_map_advance_ne_thm (l : List Client) (s : State) (r : Request) (i : ClientId) (h : i ≠ r.client) :
    lookup (l.map fun x => if x.id = r.client then advance s x r.time else x) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    show lookup ((if x.id = r.client then advance s x r.time else x) :: List.map _ _) i = lookup (x :: xs) i
    have e1 : lookup ((if x.id = r.client then advance s x r.time else x) :: List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) i
      = if (if x.id = r.client then advance s x r.time else x).id = i then some (if x.id = r.client then advance s x r.time else x) else lookup (List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) i := rfl
    have e2 : lookup (x :: xs) i = if x.id = i then some x else lookup xs i := rfl
    rw [e1, ih]
    have hid : (if x.id = r.client then advance s x r.time else x).id = x.id := by
      by_cases hx : x.id = r.client
      · simp [hx, advance_id_thm]
      · simp [hx]
    rw [hid, e2]
    by_cases hx2 : x.id = i
    · have hxr : x.id ≠ r.client := hx2 ▸ h
      rw [if_pos hx2, if_pos hx2, if_neg hxr]
    · rw [if_neg hx2, if_neg hx2]

theorem advance_start_expired (s : State) (c : Client) (t : Nat)
    (h : c.start + s.window ≤ t) : (advance s c t).start = t := by
  unfold advance windowStart
  simp [h]

theorem advance_count_expired (s : State) (c : Client) (t : Nat)
    (h : c.start + s.window ≤ t) : (advance s c t).count = 1 := by
  unfold advance windowCount
  simp [h]

theorem advance_start_kept (s : State) (c : Client) (t : Nat)
    (h : t < c.start + s.window) : (advance s c t).start = c.start := by
  unfold advance windowStart
  have h' : ¬ (c.start + s.window ≤ t) := by omega
  simp [h']

theorem advance_count_kept (s : State) (c : Client) (t : Nat)
    (h : t < c.start + s.window) : (advance s c t).count = c.count + 1 := by
  unfold advance windowCount
  have h' : ¬ (c.start + s.window ≤ t) := by omega
  simp [h']

theorem lookup_map_advance_eq_aux (l : List Client) (s : State) (r : Request) (c : Client)
    (h : lookup l r.client = some c) :
    lookup (l.map fun x => if x.id = r.client then advance s x r.time else x) r.client =
      some (advance s c r.time) := by
  induction l with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    have hid : (if x.id = r.client then advance s x r.time else x).id = x.id := by
      by_cases hx : x.id = r.client
      · simp only [hx, ↓reduceIte, advance_id_thm]
      · simp only [hx, ↓reduceIte]
    have e1 : lookup ((if x.id = r.client then advance s x r.time else x) :: List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) r.client
      = if (if x.id = r.client then advance s x r.time else x).id = r.client then some (if x.id = r.client then advance s x r.time else x) else lookup (List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) r.client := rfl
    have e2 : lookup (x :: xs) r.client = if x.id = r.client then some x else lookup xs r.client := rfl
    have hmap : (x :: xs).map (fun x => if x.id = r.client then advance s x r.time else x) = ((if x.id = r.client then advance s x r.time else x) :: List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) := rfl
    rw [hmap, e1, hid] at ⊢
    rw [e2] at h
    by_cases hx : x.id = r.client
    · simp only [hx, ↓reduceIte] at h ⊢
      cases h
      rfl
    · simp only [hx, ↓reduceIte] at h ⊢
      exact ih h

theorem dbg_reset_step_neg (s : State) (r : Request) (hNodup : ¬ (s.clients.map Client.id).Nodup) :
    step s r = (.rejected, s) := by
  unfold step
  rw [if_neg hNodup]

theorem step_fst_rejected_of_not_nodup (s : State) (r : Request)
    (h : ¬ (s.clients.map Client.id).Nodup) : (step s r).1 = .rejected := by
  unfold step
  simp [h]

theorem map_ids_advance (l : List Client) (s : State) (r : Request) :
    ((l.map fun x => if x.id = r.client then advance s x r.time else x).map Client.id) = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    have hid : (if x.id = r.client then advance s x r.time else x).id = x.id := by
      by_cases hx : x.id = r.client
      · simp [hx, advance_id_thm]
      · simp [hx]
    rw [hid, ih]

theorem tmp_list_check (l : List Nat) (a : Nat) (h : (a :: l).Nodup) : a ∉ l := by
  simp at h
  exact h.1

theorem tmp_mem_map_test (l : List Client) (f : Client → Client) (c : Client)
    (h : c ∈ l.map f) : ∃ x ∈ l, f x = c := by
  rw [List.mem_map] at h
  exact h
#check List.mem_map
#check List.nodup_cons

theorem tmp_nodup_unfold {α : Type} [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    (a :: l).Nodup ↔ a ∉ l ∧ l.Nodup := by
  exact List.nodup_cons

theorem wb_advance_le2 (s : State) (c : Client) (t : Nat)
    (h2 : windowCount s c t < s.limit) :
    (advance s c t).count ≤ s.limit := by
  simp only [advance, windowCount] at h2 ⊢
  by_cases hE : c.start + s.window ≤ t
  · simp [hE]
    omega
  · simp [hE] at h2 ⊢
    omega

theorem wb_uniq_mem (l : List Client) : (l.map Client.id).Nodup → ∀ (i : ClientId) (c0 : Client), lookup l i = some c0 → ∀ (x : Client), x ∈ l → x.id = i → x = c0 := by
  induction l with
  | nil =>
    intro _ i c0 hL x hx _
    simp at hx
  | cons hd tl ih =>
    intro hN i c0 hL x hx hxi
    have hCons : ((hd :: tl).map Client.id) = hd.id :: (tl.map Client.id) := rfl
    rw [hCons, List.nodup_cons] at hN
    obtain ⟨hNot, hTail⟩ := hN
    have hLcons : lookup (hd :: tl) i = if hd.id = i then some hd else lookup tl i := rfl
    rw [hLcons] at hL
    simp at hx
    by_cases hhd : hd.id = i
    · simp [hhd] at hL
      subst hL
      cases hx with
      | inl heq => exact heq
      | inr hmem =>
        have hmemId : hd.id ∈ tl.map Client.id := by
          rw [List.mem_map]
          exact ⟨x, hmem, hhd ▸ hxi⟩
        exact absurd hmemId hNot
    · simp [hhd] at hL
      cases hx with
      | inl heq =>
        subst heq
        simp [hhd] at hxi
      | inr hmem =>
        exact ih hTail i c0 hL x hmem hxi

theorem wb_try1 (s : State) (r : Request) (hNodup : (s.clients.map Client.id).Nodup)
    (cc : Client) (hLc : lookup s.clients r.client = some cc)
    (hC1 : cc.start ≤ r.time) (hC2 : windowCount s cc r.time < s.limit) :
    (step s r).2.clients = s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) := by
  unfold step
  rw [if_pos hNodup, hLc]
  simp [hC1, hC2]

theorem wb_try2 (s : State) (r : Request) (hNodup : (s.clients.map Client.id).Nodup)
    (cc : Client) (hLc : lookup s.clients r.client = some cc)
    (hC1 : cc.start ≤ r.time) (hC2 : windowCount s cc r.time < s.limit) :
    (step s r).2.limit = s.limit := by
  unfold step
  rw [if_pos hNodup, hLc]
  simp [hC1, hC2]

theorem wb_try3 (s : State) (r : Request) (hNodup : (s.clients.map Client.id).Nodup)
    (hLc : lookup s.clients r.client = none) :
    (step s r).2 = s := by
  unfold step
  rw [if_pos hNodup, hLc]

theorem wb_step_rej_eq2 (s : State) (r : Request) (hNodup : (s.clients.map Client.id).Nodup)
    (cc : Client) (hLc : lookup s.clients r.client = some cc)
    (hC : ¬ (cc.start ≤ r.time ∧ windowCount s cc r.time < s.limit)) :
    (step s r).2 = s := by
  unfold step
  rw [if_pos hNodup, hLc]
  simp [hC]

theorem wb_case_test (s : State) (r : Request) (hNodup : (s.clients.map Client.id).Nodup) : True := by
  cases hlo : lookup s.clients r.client with
  | none => trivial
  | some cc =>
    by_cases hC : (cc.start ≤ r.time ∧ windowCount s cc r.time < s.limit)
    · trivial
    · have h2 : (step s r).2 = s := wb_step_rej_eq2 s r hNodup cc hlo hC
      trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨hNodup, hAdm⟩ := h
  unfold step
  rw [if_pos hNodup]
  cases hLc : lookup s.clients r.client with
  | none =>
    rw [hLc] at hAdm
    simp [Admits] at hAdm
  | some c =>
    rw [hLc] at hAdm
    simp [Admits] at hAdm
    obtain ⟨h1, h2⟩ := hAdm
    simp [h1, h2]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold Admissible at h
  unfold step
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · rw [if_pos hNodup]
    cases hLc : lookup s.clients r.client with
    | none => rfl
    | some c =>
      have hNot : ¬ Admits s r.time (lookup s.clients r.client) :=
        fun ha => h ⟨hNodup, ha⟩
      rw [hLc] at hNot
      simp only [Admits] at hNot
      simp [hNot]
  · rw [if_neg hNodup]

theorem req_isolation : Isolation step := by
  intro s r i hne
  unfold step
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · simp only [hNodup, ↓reduceIte]
    cases hLc : lookup s.clients r.client with
    | none => rfl
    | some c =>
      by_cases hC : (c.start ≤ r.time ∧ windowCount s c r.time < s.limit)
      · simp only [hC.1, hC.2]
        have h := lookup_map_advance_ne_thm s.clients s r i hne
        simpa using h
      · simp only [hC]
        rfl
  · simp only [hNodup, ↓reduceIte]

theorem req_reset : ResetRule step := by
  intro s r hOk c hLc
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · by_cases hC : (c.start ≤ r.time ∧ windowCount s c r.time < s.limit)
    · have hStep : step s r = (.ok, { s with clients := s.clients.map (fun x =>
        if x.id = r.client then advance s x r.time else x) }) := by
        unfold step
        rw [if_pos hNodup, hLc]
        simp [hC.1, hC.2]
      refine ⟨advance s c r.time, ?_, ?_, ?_⟩
      · have h2 : (step s r).2 = { s with clients := s.clients.map (fun x =>
          if x.id = r.client then advance s x r.time else x) } := by
          rw [hStep]
        rw [h2]
        exact lookup_map_advance_eq_aux _ _ _ _ hLc
      · intro hExp
        exact ⟨advance_start_expired s c r.time hExp, advance_count_expired s c r.time hExp⟩
      · intro hKept
        exact ⟨advance_start_kept s c r.time hKept, advance_count_kept s c r.time hKept⟩
    · have hStepRej : step s r = (.rejected, s) := by
        unfold step
        rw [if_pos hNodup, hLc]
        simp [hC]
      rw [hStepRej] at hOk
      simp at hOk
  · have hStepRej : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hNodup]
    rw [hStepRej] at hOk
    simp at hOk

theorem req_effects : Effects step := by
  intro s r hOk
  unfold step at hOk
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · rw [if_pos hNodup] at hOk
    cases hLc : lookup s.clients r.client with
    | none =>
      simp [hLc] at hOk
    | some c =>
      simp only [hLc] at hOk
      by_cases hC : (c.start ≤ r.time ∧ windowCount s c r.time < s.limit)
      · have hStep : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
          unfold step
          rw [if_pos hNodup, hLc]
          simp [hC.1, hC.2]
        rw [hStep]
        refine ⟨rfl, rfl, map_ids_advance _ _ _, ?_⟩
        intro i
        unfold expectedLookup
        by_cases hi : i = r.client
        · subst hi
          rw [if_pos rfl]
          have h1 : lookup (s.clients.map fun x => if x.id = r.client then advance s x r.time else x) r.client = some (advance s c r.time) :=
            lookup_map_advance_eq_aux _ _ _ _ hLc
          rw [h1, hLc, Option.map_some]
        · rw [if_neg hi]
          exact lookup_map_advance_ne_thm _ _ _ _ hi
      · simp [hC] at hOk
  · rw [if_neg hNodup] at hOk
    simp at hOk

theorem req_window_bound : WindowBound step := by
  intro s r hBound c hMem
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · cases hLc : lookup s.clients r.client with
    | none =>
      have hEq : (step s r).2 = s := by
        unfold step
        rw [if_pos hNodup, hLc]
      rw [hEq] at hMem ⊢
      exact hBound c hMem
    | some cc =>
      by_cases hC : (cc.start ≤ r.time ∧ windowCount s cc r.time < s.limit)
      · obtain ⟨hC1, hC2⟩ := hC
        have hClients : (step s r).2.clients = s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) :=
          wb_try1 s r hNodup cc hLc hC1 hC2
        have hLim : (step s r).2.limit = s.limit := wb_try2 s r hNodup cc hLc hC1 hC2
        rw [hClients] at hMem
        rw [hLim]
        rw [List.mem_map] at hMem
        obtain ⟨x, hxMem, hxEq⟩ := hMem
        by_cases hxId : x.id = r.client
        · have hxEqCC : x = cc := wb_uniq_mem s.clients hNodup r.client cc hLc x hxMem hxId
          rw [hxEqCC] at hxEq hxId
          simp [hxId] at hxEq
          rw [← hxEq]
          exact wb_advance_le2 s cc r.time hC2
        · simp [hxId] at hxEq
          rw [← hxEq]
          exact hBound x hxMem
      · have hEq : (step s r).2 = s := wb_step_rej_eq2 s r hNodup cc hLc hC
        rw [hEq] at hMem ⊢
        exact hBound c hMem
  · have hEq : (step s r).2 = s := by
      unfold step
      rw [if_neg hNodup]
    rw [hEq] at hMem ⊢
    exact hBound c hMem

end FixedWindow
