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
    (.ok, { s with clients := s.clients.map fun x =>
      if x.id = r.client then advance s x r.time else x })
  else (.rejected, s)

private theorem map_adv_iso_aux (l : List Client) (s : State) (rc : ClientId) (t : Nat) (i : ClientId) (h : i ≠ rc) :
    lookup (l.map (fun x => if x.id = rc then advance s x t else x)) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    have hid : (if x.id = rc then advance s x t else x).id = x.id := by
      by_cases hx : x.id = rc <;> simp [hx, advance]
    rw [lookup_cons, lookup_cons, hid, ih]
    by_cases hx : x.id = i
    · simp [hx, h]
    · simp [hx]

theorem mapHit_aux6 (l : List Client) (s : State) (rc : ClientId) (t : Nat) (c : Client)
    (hNodup : (l.map Client.id).Nodup) (hlook : lookup l rc = some c) :
    lookup (l.map (fun x => if x.id = rc then advance s x t else x)) rc = some (advance s c t) := by
  induction l with
  | nil => simp [lookup] at hlook
  | cons x xs ih =>
    have hid : (if x.id = rc then advance s x t else x).id = x.id := by
      by_cases hx : x.id = rc <;> simp [hx, advance]
    simp only [List.map_cons, lookup_cons, hid] at hlook ⊢
    by_cases hx : x.id = rc
    · simp [hx] at hlook ⊢
      cases hlook
      simp [hx]
    · simp [hx] at hlook ⊢
      exact ih (List.nodup_cons.mp hNodup).2 hlook

theorem tmp_effects_check : True := by
  trivial

theorem ok_imp_adm_aux (s : State) (r : Request) (hOk : (step s r).1 = .ok) : Admissible s r := by
  unfold step at hOk
  by_cases h : Admissible s r
  · exact h
  · simp [h] at hOk

theorem foo_test : True := by trivial

theorem uniq_mem_id_eq : ∀ (l : List Client) (rc : ClientId) (c0 : Client),
    (l.map Client.id).Nodup → lookup l rc = some c0 →
    ∀ x ∈ l, x.id = rc → x = c0 := by
  intro l
  induction l with
  | nil =>
    intro rc c0 _ hL x hx _
    simp at hx
  | cons y ys ih =>
    intro rc c0 hN hL x hx hId
    have hNtail : (ys.map Client.id).Nodup := (List.nodup_cons.mp hN).2
    have hNotMem : y.id ∉ ys.map Client.id := (List.nodup_cons.mp hN).1
    by_cases hy : y.id = rc
    · simp [lookup_cons, hy] at hL
      subst hL
      simp at hx
      cases hx with
      | inl heq =>
        exact heq
      | inr hmem =>
        have hmemId : rc ∈ ys.map Client.id := by
          have : x.id ∈ ys.map Client.id := List.mem_map_of_mem hmem
          rwa [hId] at this
        rw [← hy] at hmemId
        exact absurd hmemId hNotMem
    · simp [lookup_cons, hy] at hL
      simp at hx
      cases hx with
      | inl heq =>
        subst heq
        exact absurd hId hy
      | inr hmem =>
        exact ih rc c0 hNtail hL x hmem hId

theorem map_mem_bound_aux : ∀ (l : List Client) (s : State) (rc t : Nat) (c0 : Client),
    (l.map Client.id).Nodup → lookup l rc = some c0 →
    (c0.start ≤ t ∧ windowCount s c0 t < s.limit) →
    (∀ c ∈ l, c.count ≤ s.limit) →
    ∀ y ∈ l.map (fun x => if x.id = rc then advance s x t else x), y.count ≤ s.limit := by
  intro l s rc t c0 hN hL hAdm hB y hy
  rw [List.mem_map] at hy
  obtain ⟨x, hxMem, hxEq⟩ := hy
  by_cases hxx : x.id = rc
  · have hx0 : x = c0 := uniq_mem_id_eq l rc c0 hN hL x hxMem hxx
    subst hx0
    simp [hxx] at hxEq
    rw [← hxEq]
    simp [advance]
    exact Nat.succ_le_of_lt hAdm.2
  · simp [hxx] at hxEq
    rw [← hxEq]
    exact hB x hxMem

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_isolation : Isolation step := by
  intro s r i hi
  unfold step
  by_cases h : Admissible s r
  · simp only [h, ↓reduceIte]
    show lookup ((s.clients.map fun x => if x.id = r.client then advance s x r.time else x)) i = lookup s.clients i
    exact map_adv_iso_aux s.clients s r.client r.time i hi
  · simp only [h, ↓reduceIte]

theorem req_reset : ResetRule step := by
  intro s r hOk c hLook
  have hAdm : Admissible s r := ok_imp_adm_aux s r hOk
  have hNodup : (s.clients.map Client.id).Nodup := hAdm.1
  have heq : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
    unfold step
    simp [hAdm]
  have hMap : lookup (s.clients.map fun x => if x.id = r.client then advance s x r.time else x) r.client = some (advance s c r.time) := by
    exact mapHit_aux6 s.clients s r.client r.time c hNodup hLook
  have hLook2 : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
    rw [heq]
    exact hMap
  refine ⟨advance s c r.time, hLook2, ?_, ?_⟩
  · intro hExp
    unfold advance windowStart windowCount
    simp [hExp]
  · intro hNot
    have hExp : ¬ (c.start + s.window ≤ r.time) := by omega
    unfold advance windowStart windowCount
    simp [hExp]

theorem req_effects : Effects step := by
  intro s r hOk
  have hAdm : Admissible s r := ok_imp_adm_aux s r hOk
  have heq : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
    unfold step
    simp [hAdm]
  have hw : (step s r).2.window = s.window := by rw [heq]
  have hl : (step s r).2.limit = s.limit := by rw [heq]
  have hids : (step s r).2.clients.map Client.id = s.clients.map Client.id := by
    rw [heq]
    simp only
    induction s.clients with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons]
      have hid : (if x.id = r.client then advance s x r.time else x).id = x.id := by
        by_cases hx : x.id = r.client <;> simp [hx, advance]
      simp [hid, ih]
  have hlook : ∀ i, lookup (step s r).2.clients i = expectedLookup s r i := by
    intro i
    rw [heq]
    simp only
    unfold expectedLookup
    by_cases hi : i = r.client
    · subst hi
      have hNodup : (s.clients.map Client.id).Nodup := hAdm.1
      cases hL : lookup s.clients r.client with
      | none =>
        have hA := hAdm.2
        rw [hL] at hA
        cases hA
      | some c =>
        have hMap := mapHit_aux6 s.clients s r.client r.time c hNodup hL
        simp [hMap]
    · simp [hi]
      exact map_adv_iso_aux s.clients s r.client r.time i hi
  exact ⟨hw, hl, hids, hlook⟩

theorem req_window_bound : WindowBound step := by
  intro s r hB c hc
  by_cases h : Admissible s r
  · have heq : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
      unfold step
      simp [h]
    have hN : (s.clients.map Client.id).Nodup := h.1
    have hAdm : Admits s r.time (lookup s.clients r.client) := h.2
    cases hLc : lookup s.clients r.client with
    | none =>
      unfold Admits at hAdm
      rw [hLc] at hAdm
      cases hAdm
    | some c0 =>
      simp [hLc] at hAdm
      have hclients : (step s r).2.clients = s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) := by
        rw [heq]
      have hlim : (step s r).2.limit = s.limit := by
        rw [heq]
      rw [hclients] at hc
      rw [hlim]
      exact map_mem_bound_aux s.clients s r.client r.time c0 hN hLc hAdm hB _ hc
  · have heq2 : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    have hclients : (step s r).2.clients = s.clients := by
      rw [heq2]
    have hlim : (step s r).2.limit = s.limit := by
      rw [heq2]
    rw [hclients] at hc
    rw [hlim]
    exact hB c hc

end FixedWindow
