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
    (.ok, { s with clients := s.clients.map fun c =>
      if c.id = r.client then advance s c r.time
      else c })
  else (.rejected, s)

def fooTest : Nat := 1

theorem fooLemma2 : 1 + 1 = 2 := by rfl

theorem lookup_map_advance_ne_aux3 (s : State) (r : Request) (l : List Client) (i : ClientId) (hi : i ≠ r.client) :
    lookup (l.map fun c => if c.id = r.client then advance s c r.time else c) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, lookup_cons]
    have hid : (if c.id = r.client then advance s c r.time else c).id = c.id := by
      split
      · simp [advance]
      · rfl
    rw [hid]
    by_cases hc : c.id = i
    · rw [if_pos hc, if_pos hc]
      have hcr : ¬ (c.id = r.client) := by
        intro hcon
        rw [hcon] at hc
        exact hi hc.symm
      rw [if_neg hcr]
    · rw [if_neg hc, if_neg hc, ih]

theorem lookup_map_advance_some_auxR (s : State) (r : Request) (l : List Client) (c : Client)
    (h : lookup l r.client = some c) :
    lookup (l.map fun c => if c.id = r.client then advance s c r.time else c) r.client = some (advance s c r.time) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [lookup_cons] at h
    simp only [List.map_cons, lookup_cons]
    have hid : (if x.id = r.client then advance s x r.time else x).id = x.id := by
      by_cases hx : x.id = r.client <;> simp [hx, advance]
    rw [hid]
    by_cases hx : x.id = r.client
    · simp [hx] at h
      subst h
      simp [hx]
    · simp [hx] at h ⊢
      exact ih h

theorem req_reset_test : ResetRule step := by
  intro s r hOk c hc
  by_cases hAdm : Admissible s r
  · have hUpd : (step s r).2 = { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c } := by
      unfold step; simp [hAdm]
    refine ⟨advance s c r.time, ?_, ?_, ?_⟩
    · rw [hUpd]
      exact lookup_map_advance_some_auxR s r s.clients c hc
    · intro hexp
      unfold advance windowStart windowCount
      simp [hexp]
    · intro hlt
      have hne : ¬ (c.start + s.window ≤ r.time) := Nat.not_le.mpr hlt
      unfold advance windowStart windowCount
      simp [hne]
  · have h1 : (step s r).1 = .rejected := by unfold step; simp [hAdm]
    rw [h1] at hOk
    contradiction

theorem req_reset_aux_proof : True := trivial

theorem map_ids_advance_auxE2 (s : State) (r : Request) (l : List Client) :
    ((l.map fun c => if c.id = r.client then advance s c r.time else c).map Client.id) = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    have hid : (if x.id = r.client then advance s x r.time else x).id = x.id := by
      by_cases hx : x.id = r.client <;> simp [hx, advance]
    rw [hid, ih]

theorem admissible_of_ok_auxE2 (s : State) (r : Request) (h : (step s r).1 = .ok) : Admissible s r := by
  by_cases hAdm : Admissible s r
  · exact hAdm
  · have h1 : (step s r).1 = .rejected := by unfold step; simp [hAdm]
    rw [h1] at h
    contradiction

theorem lookup_some_of_adm_auxE2 (s : State) (r : Request) (h : Admissible s r) :
    ∃ c, lookup s.clients r.client = some c := by
  unfold Admissible at h
  obtain ⟨_, hAdm⟩ := h
  cases hL : lookup s.clients r.client with
  | none =>
    rw [hL] at hAdm
    simp [Admits] at hAdm
  | some c => exact ⟨c, rfl⟩

theorem wb_uniq_aux : ∀ (l : List Client) (a c : Client),
    (l.map Client.id).Nodup → a ∈ l → lookup l a.id = some c → a = c := by
  intro l
  induction l with
  | nil => intro a c hn hm hl; simp at hm
  | cons x xs ih =>
    intro a c hn hm hl
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hNotIn, hNodup⟩ := hn
    rw [lookup_cons] at hl
    by_cases hx : x.id = a.id
    · simp [hx] at hl
      subst hl
      simp at hm
      cases hm with
      | inl he => exact he
      | inr hmem =>
        exfalso
        apply hNotIn
        have : a.id ∈ List.map Client.id xs := List.mem_map_of_mem hmem
        rwa [← hx] at this
    · simp [hx] at hl
      have hmem : a ∈ xs := by
        simp at hm
        cases hm with
        | inl he => exfalso; apply hx; rw [he]
        | inr hmem => exact hmem
      exact ih a c hNodup hmem hl

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_isolation : Isolation step := by
  intro s r i hi
  unfold step
  by_cases hAdm : Admissible s r
  · simp only [hAdm, ↓reduceIte]
    exact lookup_map_advance_ne_aux3 s r s.clients i hi
  · simp [hAdm]

theorem req_reset : ResetRule step := by
  intro s r hOk c hc
  by_cases hAdm : Admissible s r
  · have hUpd : (step s r).2 = { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c } := by
      unfold step; simp [hAdm]
    refine ⟨advance s c r.time, ?_, ?_, ?_⟩
    · rw [hUpd]
      exact lookup_map_advance_some_auxR s r s.clients c hc
    · intro hexp
      unfold advance windowStart windowCount
      simp [hexp]
    · intro hlt
      have hne : ¬ (c.start + s.window ≤ r.time) := Nat.not_le.mpr hlt
      unfold advance windowStart windowCount
      simp [hne]
  · have h1 : (step s r).1 = .rejected := by unfold step; simp [hAdm]
    rw [h1] at hOk
    contradiction

theorem req_effects : Effects step := by
  intro s r hOk
  have hAdm : Admissible s r := admissible_of_ok_auxE2 s r hOk
  have hStep2 : (step s r).2 = { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c } := by
    unfold step; simp [hAdm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hStep2]
  · rw [hStep2]
  · rw [hStep2]
    simp only
    exact map_ids_advance_auxE2 s r s.clients
  · intro i
    rw [hStep2]
    simp only
    unfold expectedLookup
    by_cases heq : i = r.client
    · subst heq
      obtain ⟨c, hc⟩ := lookup_some_of_adm_auxE2 s r hAdm
      have hleft := lookup_map_advance_some_auxR s r s.clients c hc
      simp [hc, hleft]
    · simp [heq, lookup_map_advance_ne_aux3 s r s.clients i heq]

theorem req_window_bound : WindowBound step := by
  intro s r hAll c hmem
  have hStep2ok : ∀ (hAdm : Admissible s r),
    (step s r).2 = ({ s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c } : State) := by
    intro hAdm; unfold step; simp [hAdm]
  by_cases hAdm : Admissible s r
  · rw [hStep2ok hAdm] at hmem ⊢
    simp only at hmem ⊢
    have hNodup : (s.clients.map Client.id).Nodup := hAdm.1
    have hAdmits : Admits s r.time (lookup s.clients r.client) := hAdm.2
    obtain ⟨b, hb⟩ : ∃ b, lookup s.clients r.client = some b := by
      cases hL : lookup s.clients r.client with
      | none => rw [hL] at hAdmits; simp [Admits] at hAdmits
      | some b => exact ⟨b, rfl⟩
    have hbLt : windowCount s b r.time < s.limit := by
      rw [hb] at hAdmits; exact hAdmits.2
    obtain ⟨a, haMem, haEq⟩ := List.mem_map.mp hmem
    by_cases haId : a.id = r.client
    · have haLookup : lookup s.clients a.id = some b := by rw [haId]; exact hb
      have haEqB : a = b := wb_uniq_aux s.clients a b hNodup haMem haLookup
      have hAdvEq : advance s a r.time = c := by simpa [haId] using haEq
      rw [haEqB] at hAdvEq
      rw [← hAdvEq]
      show (advance s b r.time).count ≤ s.limit
      unfold advance
      simp only
      exact Nat.succ_le_of_lt hbLt
    · have haEq2 : c = a := by simpa [haId] using haEq.symm
      rw [haEq2]
      exact hAll a haMem
  · have hEq : step s r = (.rejected, s) := by unfold step; simp [hAdm]
    rw [hEq] at hmem ⊢
    simp only at hmem ⊢
    exact hAll c hmem

end FixedWindow
