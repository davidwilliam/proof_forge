import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow
instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { window := s.window, limit := s.limit, clients := s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) })
  else (.rejected, s)

theorem foo_test : True := trivial

theorem myhelper1 (n : Nat) : n = n := rfl

theorem iso_map_aux_thm (f : Client → Client) (h_id : ∀ x, (f x).id = x.id) (l : List Client) (i : ClientId)
    (h_f : ∀ x ∈ l, x.id = i → f x = x) :
    lookup (l.map f) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    rw [lookup_cons, lookup_cons]
    by_cases hc : c.id = i
    · have hfc : f c = c := h_f c (by simp) hc
      have hid : (f c).id = c.id := h_id c
      rw [hid, hc]
      simp [hfc]
    · have hid : (f c).id = c.id := h_id c
      rw [hid]
      simp [hc]
      apply ih
      intro x hx hxi
      exact h_f x (List.Mem.tail c hx) hxi

theorem hmap_lemma2 (s : State) (r : Request) (l : List Client) :
    lookup (l.map (fun x => if x.id = r.client then advance s x r.time else x)) r.client
      = (lookup l r.client).map (fun x => advance s x r.time) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, lookup_cons]
    have hy : (if y.id = r.client then advance s y r.time else y).id = y.id := by
      by_cases hyeq : y.id = r.client
      · simp [hyeq, advance]
      · simp [hyeq]
    rw [hy]
    by_cases hyeq : y.id = r.client
    · simp [hyeq]
    · simp [hyeq, ih]

theorem wb_mem_map_ids (l : List Client) (x : Client) (h : x ∈ l) : x.id ∈ l.map Client.id := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.map_cons]
    simp only [List.mem_cons] at h ⊢
    rcases h with rfl | hmem
    · left; rfl
    · right; exact ih hmem

theorem wb_nodup_tail (a : Nat) (l : List Nat) (h : List.Nodup (a :: l)) : List.Nodup l := by
  simp [List.nodup_cons] at h
  exact h.2

theorem wb_nodup_notmem (a : Nat) (l : List Nat) (h : List.Nodup (a :: l)) : a ∉ l := by
  simp [List.nodup_cons] at h
  exact h.1

theorem test_mem_map (l : List Client) (f : Client → Client) (y : Client) (h : y ∈ l.map f) : ∃ x ∈ l, f x = y := by
  exact List.mem_map.mp h



theorem plan0_lookup_self_of_nodup (l : List Client) (x : Client)
    (hnd : List.Nodup (l.map Client.id)) (hmem : x ∈ l) :
    lookup l x.id = some x := by
  induction l with
  | nil => simp at hmem
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotmem, htail⟩ := hnd
    simp only [List.mem_cons] at hmem
    rw [lookup_cons]
    by_cases hyeq : y.id = x.id
    · simp only [hyeq, ↓reduceIte]
      rcases hmem with rfl | hmem2
      · rfl
      · exfalso
        apply hnotmem
        have h : x.id ∈ ys.map Client.id := List.mem_map.mpr ⟨x, hmem2, rfl⟩
        rw [← hyeq] at h
        exact h
    · simp only [hyeq, ↓reduceIte]
      rcases hmem with rfl | hmem2
      · exfalso; exact hyeq (congrArg Client.id rfl)
      · exact ih htail hmem2








theorem plan0_id_mem_map (l : List Client) (x : Client) (h : x ∈ l) :
    x.id ∈ l.map Client.id := List.mem_map.mpr ⟨x, h, rfl⟩

theorem plan0_lookup_self_of_nodup_aux (l : List Client) (x : Client)
    (hnd : List.Nodup (l.map Client.id)) (hmem : x ∈ l) :
    lookup l x.id = some x := by
  induction l with
  | nil => simp at hmem
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotmem, htail⟩ := hnd
    simp only [List.mem_cons] at hmem
    rw [lookup_cons]
    by_cases hyeq : y.id = x.id
    · simp only [hyeq, ↓reduceIte]
      rcases hmem with rfl | hmem2
      · rfl
      · exfalso
        apply hnotmem
        have h : x.id ∈ ys.map Client.id := List.mem_map.mpr ⟨x, hmem2, rfl⟩
        rw [← hyeq] at h
        exact h
    · simp only [hyeq, ↓reduceIte]
      rcases hmem with rfl | hmem2
      · exfalso; exact hyeq (congrArg Client.id rfl)
      · exact ih htail hmem2

theorem plan0_lookup_self_of_nodup_direct (l : List Client) (x : Client)
    (hnd : List.Nodup (l.map Client.id)) (hmem : x ∈ l) :
    lookup l x.id = some x := by
  induction l with
  | nil => simp at hmem
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotmem, htail⟩ := hnd
    simp only [List.mem_cons] at hmem
    rw [lookup_cons]
    by_cases hyeq : y.id = x.id
    · simp only [hyeq, ↓reduceIte]
      rcases hmem with rfl | hmem2
      · rfl
      · exfalso
        apply hnotmem
        have h : x.id ∈ ys.map Client.id := List.mem_map.mpr ⟨x, hmem2, rfl⟩
        rw [← hyeq] at h
        exact h
    · simp only [hyeq, ↓reduceIte]
      rcases hmem with rfl | hmem2
      · exfalso; exact hyeq (congrArg Client.id rfl)
      · exact ih htail hmem2

theorem plan0_advance_count_le (s : State) (c : Client) (t : Nat)
    (h : windowCount s c t < s.limit) :
    (advance s c t).count ≤ s.limit := by
  unfold advance
  simp only
  exact Nat.succ_le_of_lt h

theorem plan0_windowCount_lt_of_admissible (s : State) (r : Request) (x : Client)
    (hadm : Admissible s r) (hmem : x ∈ s.clients) (hid : x.id = r.client) :
    windowCount s x r.time < s.limit := by
  unfold Admissible at hadm
  obtain ⟨hNodup, hAdm⟩ := hadm
  have hlook : lookup s.clients x.id = some x :=
    plan0_lookup_self_of_nodup s.clients x hNodup hmem
  have h2 : lookup s.clients r.client = some x := by
    rwa [hid] at hlook
  rw [h2] at hAdm
  exact (hAdm : x.start ≤ r.time ∧ windowCount s x r.time < s.limit).2

theorem plan0_mapped_count_le (s : State) (r : Request)
    (hadm : Admissible s r)
    (hbound : ∀ c ∈ s.clients, c.count ≤ s.limit)
    (c : Client)
    (hc : c ∈ s.clients.map (fun x => if x.id = r.client then advance s x r.time else x)) :
    c.count ≤ s.limit := by
  obtain ⟨x, hxmem, hxc⟩ := List.mem_map.mp hc
  by_cases hx : x.id = r.client
  · have hc_eq : c = advance s x r.time := by
      simp [hx] at hxc
      exact hxc.symm
    rw [hc_eq]
    apply plan0_advance_count_le
    exact plan0_windowCount_lt_of_admissible s r x hadm hxmem hx
  · have hc_eq : c = x := by
      simp [hx] at hxc
      exact hxc.symm
    rw [hc_eq]
    exact hbound x hxmem

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_isolation : Isolation step := by
  intro s r i hne
  unfold step
  by_cases h : Admissible s r
  · simp only [h, ↓reduceIte]
    apply iso_map_aux_thm
    · intro x
      by_cases hx : x.id = r.client <;> simp [hx, advance]
    · intro x _ hx_id
      have hx_ne : x.id ≠ r.client := by
        intro heq
        rw [heq] at hx_id
        exact hne hx_id.symm
      simp [hx_ne]
  · simp [h]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  have hAdm : Admissible s r := by
    by_cases hN : Admissible s r
    · exact hN
    · have hcon : (step s r).1 = .rejected := by unfold step; simp [hN]
      rw [hcon] at hok
      cases hok
  have hlook : lookup (s.clients.map (fun x => if x.id = r.client then advance s x r.time else x)) r.client
      = some (advance s c r.time) := by
    rw [hmap_lemma2 s r s.clients, hc]
    rfl
  have hstate : (step s r).2.clients = s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) := by
    unfold step
    simp [hAdm]
  rw [← hstate] at hlook
  refine ⟨advance s c r.time, hlook, ?_, ?_⟩
  · intro hexp
    unfold advance windowStart windowCount
    simp [hexp]
  · intro hlt
    have hnot : ¬ (c.start + s.window ≤ r.time) := by omega
    unfold advance windowStart windowCount
    simp [hnot]

theorem req_effects : Effects step := by
  intro s r hok
  have hAdm : Admissible s r := by
    by_cases hN : Admissible s r
    · exact hN
    · have hcon : (step s r).1 = .rejected := by unfold step; simp [hN]
      rw [hcon] at hok
      cases hok
  have hstate_eq : (step s r).2 = { window := s.window, limit := s.limit, clients := s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) } := by
    unfold step
    simp [hAdm]
  have hclients : (step s r).2.clients = s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) := by
    rw [hstate_eq]
  have hwin : (step s r).2.window = s.window := by rw [hstate_eq]
  have hlim : (step s r).2.limit = s.limit := by rw [hstate_eq]
  refine ⟨hwin, hlim, ?_, ?_⟩
  · rw [hclients]
    have hid : ∀ x : Client, (if x.id = r.client then advance s x r.time else x).id = x.id := by
      intro x
      by_cases hx : x.id = r.client <;> simp [hx, advance]
    induction s.clients with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons, hid]
      rw [ih]
  · intro i
    rw [hclients]
    unfold expectedLookup
    by_cases heq : i = r.client
    · subst heq
      simp only [↓reduceIte]
      exact hmap_lemma2 s r s.clients
    · have h2 : (if i = r.client then (lookup s.clients i).map (fun c => advance s c r.time) else lookup s.clients i) = lookup s.clients i := by simp [heq]
      rw [h2]
      apply iso_map_aux_thm
      · intro x
        by_cases hx : x.id = r.client <;> simp [hx, advance]
      · intro x _ hx_id
        have hx_ne : x.id ≠ r.client := by
          intro heq2
          rw [heq2] at hx_id
          exact heq hx_id.symm
        simp [hx_ne]

theorem req_window_bound : WindowBound step := by
  intro s r hbound c hc
  by_cases hAdm : Admissible s r
  · have h2 : (step s r).2.clients
        = s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) := by
      unfold step
      simp [hAdm]
    have hlim : (step s r).2.limit = s.limit := by
      unfold step
      simp [hAdm]
    rw [hlim]
    rw [h2] at hc
    exact plan0_mapped_count_le s r hAdm hbound c hc
  · have h2 : (step s r).2 = s := by
      unfold step
      simp [hAdm]
    rw [h2] at hc ⊢
    exact hbound c hc

end FixedWindow
