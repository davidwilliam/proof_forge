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
    (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x })
  else (.rejected, s)

private theorem adv_id_test (s : State) (c : Client) (t : Nat) : (advance s c t).id = c.id := rfl

private theorem map_id_test (s : State) (rc t : Nat) (x : Client) :
    (if x.id = rc then advance s x t else x).id = x.id := by
  by_cases h : x.id = rc
  · simp only [if_pos h]
    rw [adv_id_test]
  · simp only [if_neg h]

private theorem lookup_map_gen (f : Client → Client) (hid : ∀ y, (f y).id = y.id)
    (l : List Client) (i : Nat) :
    lookup (l.map f) i = (lookup l i).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons, hid]
    by_cases hx : x.id = i
    · simp [hx]
    · simp [hx, ih]

theorem req_reset_aux_test : True := trivial

private theorem wb_uniq_aux : (List.map Client.id ([] : List Client)).Nodup := by simp

#check @List.mem_map
#check @List.mem_cons_self
#check List.nodup_cons

private theorem wb_mem_map_obtain (s : State) (r : Request) (c' : Client)
    (h : c' ∈ s.clients.map fun x => if x.id = r.client then advance s x r.time else x) :
    ∃ x, x ∈ s.clients ∧ (if x.id = r.client then advance s x r.time else x) = c' := by
  have h2 := (List.mem_map).mp h
  obtain ⟨x, hxmem, hxeq⟩ := h2
  exact ⟨x, hxmem, hxeq ▸ rfl⟩

private theorem wb_hid_test (s : State) (r : Request) :
    ∀ y : Client, ((if y.id = r.client then advance s y r.time else y).id = y.id) := by
  intro y
  by_cases hh : y.id = r.client
  · simp only [if_pos hh, advance]
  · simp only [if_neg hh]

private theorem wb_test_omega : ∀ (a b : Nat), a < b → a + 1 ≤ b := by intro a b h; omega

private theorem wb_uniq_mem_eq (l : List Client) :
    ∀ (c0 x : Client) (i : ClientId),
    (l.map Client.id).Nodup → lookup l i = some c0 → x ∈ l → x.id = i → x = c0 := by
  induction l with
  | nil =>
    intro c0 x i hn hlook hx hid
    simp at hlook
  | cons y ys ih =>
    intro c0 x i hn hlook hx hid
    simp only [List.map_cons] at hn
    rw [List.nodup_cons] at hn
    obtain ⟨hn_not, hn_tail⟩ := hn
    rw [lookup_cons] at hlook
    by_cases hy : y.id = i
    · rw [if_pos hy] at hlook
      have hyc : y = c0 := by simpa using hlook
      have hx' : x = y ∨ x ∈ ys := by simpa using hx
      cases hx' with
      | inl heq => rw [heq, hyc]
      | inr hmem =>
        have hmem_map : y.id ∈ List.map Client.id ys := by
          apply List.mem_map.mpr
          exact ⟨x, hmem, by rw [hid, hy]⟩
        exact absurd hmem_map hn_not
    · rw [if_neg hy] at hlook
      have hx' : x = y ∨ x ∈ ys := by simpa using hx
      cases hx' with
      | inl heq =>
        subst heq
        simp [hy] at hid
      | inr hmem => exact ih c0 x i hn_tail hlook hmem hid

private theorem wb_admits_unfold_test (s : State) (t : Nat) (c : Client)
    (h : Admits s t (some c)) : c.start ≤ t ∧ windowCount s c t < s.limit := h

private theorem wb_admits_rw_test (s : State) (r : Request) (c0 : Client)
    (hAd : Admits s r.time (lookup s.clients r.client))
    (hLk : lookup s.clients r.client = some c0) :
    c0.start ≤ r.time ∧ windowCount s c0 r.time < s.limit := by
  have hAd' : Admits s r.time (some c0) := hLk ▸ hAd
  exact hAd'

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_isolation : Isolation step := by
  intro s r i hne
  by_cases hAdm : Admissible s r
  · have hstep2 : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
      simp [step, hAdm]
    have h2eq : (step s r).2 = { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x } := by
      rw [hstep2]
    rw [h2eq]
    simp only
    have hid := wb_hid_test s r
    have hlook : lookup (s.clients.map fun x => if x.id = r.client then advance s x r.time else x) i
        = (lookup s.clients i).map (fun x => if x.id = r.client then advance s x r.time else x) :=
      lookup_map_gen (fun x => if x.id = r.client then advance s x r.time else x) hid s.clients i
    rw [hlook]
    cases hLk : lookup s.clients i with
    | none => rfl
    | some c =>
      have hcid : c.id = i := lookup_id hLk
      have hne2 : ¬ (c.id = r.client) := by
        rw [hcid]
        exact hne
      simp [hne2]
  · have hstep : step s r = (.rejected, s) := by simp [step, hAdm]
    have h2eq : (step s r).2 = s := by rw [hstep]
    rw [h2eq]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  by_cases hAdm : Admissible s r
  · have hstep2 : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
      simp [step, hAdm]
    have hid : ∀ y : Client, ((if y.id = r.client then advance s y r.time else y).id = y.id) := by
      intro y
      by_cases hh : y.id = r.client
      · rw [if_pos hh]
        rfl
      · rw [if_neg hh]
    have hlook : lookup (s.clients.map fun x => if x.id = r.client then advance s x r.time else x) r.client = (lookup s.clients r.client).map (fun x => if x.id = r.client then advance s x r.time else x) := by
      exact lookup_map_gen (fun x => if x.id = r.client then advance s x r.time else x) hid s.clients r.client
    rw [hstep2]
    simp only
    rw [hlook, hc]
    simp only [Option.map_some]
    have hcid : c.id = r.client := lookup_id hc
    have hf_c : (if c.id = r.client then advance s c r.time else c) = advance s c r.time := by
      rw [if_pos hcid]
    rw [hf_c]
    refine ⟨advance s c r.time, rfl, ?_, ?_⟩
    · intro hexp
      constructor
      · simp [advance, windowStart, hexp]
      · simp [advance, windowCount, hexp]
    · intro hlt
      have hneg : ¬ (c.start + s.window ≤ r.time) := by omega
      constructor
      · simp [advance, windowStart, hneg]
      · simp [advance, windowCount, hneg]
  · have hstep : step s r = (.rejected, s) := by simp [step, hAdm]
    rw [hstep] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s r hok
  have hAdm : Admissible s r := by
    by_cases h : Admissible s r
    · exact h
    · have hstep : step s r = (.rejected, s) := by simp [step, h]
      rw [hstep] at hok
      simp at hok
  have hstep2 : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
    simp [step, hAdm]
  have hid : ∀ y : Client, ((if y.id = r.client then advance s y r.time else y).id = y.id) := by
    intro y
    by_cases hh : y.id = r.client
    · simp only [if_pos hh, advance]
    · simp only [if_neg hh]
  have h2 : (step s r).2 = { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x } := by
    rw [hstep2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [h2]
  · rw [h2]
    simp only
    induction s.clients with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, ih, hid x]
  · intro i
    rw [h2]
    simp only
    have hlook : lookup (s.clients.map fun x => if x.id = r.client then advance s x r.time else x) i = (lookup s.clients i).map (fun x => if x.id = r.client then advance s x r.time else x) :=
      lookup_map_gen (fun x => if x.id = r.client then advance s x r.time else x) hid s.clients i
    rw [hlook]
    unfold expectedLookup
    by_cases hi : i = r.client
    · subst hi
      rw [if_pos rfl]
      cases hLk : lookup s.clients r.client with
      | none => rfl
      | some c =>
        have hcid : c.id = r.client := lookup_id hLk
        simp only [Option.map_some]
        rw [if_pos hcid]
    · rw [if_neg hi]
      cases hLk : lookup s.clients i with
      | none => rfl
      | some c =>
        have hcid : c.id = i := lookup_id hLk
        have hne : ¬ (c.id = r.client) := by rw [hcid]; exact hi
        simp only [Option.map_some]
        rw [if_neg hne]

theorem req_window_bound   : WindowBound step := by
  intro s r hbound c' hmem
  by_cases hAdm : Admissible s r
  · have hstep2 : (step s r).2 = { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x } := by
      simp [step, hAdm]
    have hlim : (step s r).2.limit = s.limit := by rw [hstep2]
    rw [hlim]
    rw [hstep2] at hmem
    simp only at hmem
    obtain ⟨x, hxmem, hfx⟩ := wb_mem_map_obtain s r c' hmem
    have hNodup : (s.clients.map Client.id).Nodup := hAdm.1
    have hAd : Admits s r.time (lookup s.clients r.client) := hAdm.2
    cases hLk : lookup s.clients r.client with
    | none =>
      have hF : (Admits s r.time none) := hLk ▸ hAd
      simp [Admits] at hF
    | some cc =>
      have hAd2 : cc.start ≤ r.time ∧ windowCount s cc r.time < s.limit :=
        wb_admits_rw_test s r cc hAd hLk
      by_cases hxeq : x.id = r.client
      · have hxc0 : x = cc := wb_uniq_mem_eq s.clients cc x r.client hNodup hLk hxmem hxeq
        rw [hxc0] at hfx
        have hccid : cc.id = r.client := lookup_id hLk
        have hfc : (if cc.id = r.client then advance s cc r.time else cc) = advance s cc r.time := by
          rw [if_pos hccid]
        rw [hfc] at hfx
        rw [← hfx]
        simp only [advance]
        have hlt := hAd2.2
        omega
      · have hfx2 : (if x.id = r.client then advance s x r.time else x) = x := by
          rw [if_neg hxeq]
        rw [hfx2] at hfx
        rw [← hfx]
        exact hbound x hxmem
  · have hstep : step s r = (.rejected, s) := by simp [step, hAdm]
    have h2eq : (step s r).2 = s := by rw [hstep]
    have hlim2 : (step s r).2.limit = s.limit := by rw [h2eq]
    rw [hlim2]
    rw [h2eq] at hmem
    exact hbound c' hmem

end FixedWindow
