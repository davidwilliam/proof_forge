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

private theorem iso_fid2 (s : State) (r : Request) (y : Client) :
    (if y.id = r.client then advance s y r.time else y).id = y.id := by
  by_cases h : y.id = r.client <;> simp [h, advance]

private theorem iso_helper6 : ∀ (l : List Client) (s : State) (r : Request) (i : ClientId),
    i ≠ r.client →
    lookup (l.map fun x => if x.id = r.client then advance s x r.time else x) i = lookup l i := by
  intro l s r i hi
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons, iso_fid2 s r x]
    rw [ih]
    by_cases hxi : x.id = i
    · simp [hxi, hi]
    · simp [hxi]

theorem req_reset_aux_check : True := trivial

theorem lookup_map_adv_test2 (l : List Client) (s : State) (r : Request) (i : ClientId) :
    lookup (l.map fun x => if x.id = r.client then advance s x r.time else x) i =
    if i = r.client then (lookup l i).map (fun c => advance s c r.time)
    else lookup l i := by
  induction l with
  | nil =>
    simp only [List.map_nil, lookup_nil]
    split
    · rfl
    · rfl
  | cons x xs ih =>
    have hfid : (if x.id = r.client then advance s x r.time else x).id = x.id := by
      split
      · rfl
      · rfl
    simp only [List.map_cons, lookup_cons, hfid]
    by_cases hx : x.id = i
    · rw [if_pos hx]
      have hx_lookup : (if x.id = i then some x else lookup xs i) = some x := if_pos hx
      rw [hx_lookup]
      simp only [Option.map_some]
      by_cases hi : i = r.client
      · rw [if_pos hi]
        have hx2 : x.id = r.client := hx.trans hi
        rw [if_pos hx2]
      · rw [if_neg hi]
        have hx2 : x.id ≠ r.client := fun h => hi (hx.symm.trans h)
        rw [if_neg hx2]
    · rw [if_neg hx]
      have hx_lookup : (if x.id = i then some x else lookup xs i) = lookup xs i := if_neg hx
      rw [hx_lookup]
      rw [ih]

private theorem lookup_nodup_unique_aux : ∀ (l : List Client), (l.map Client.id).Nodup → ∀ (i : ClientId) (c1 c2 : Client), lookup l i = some c1 → c2 ∈ l → c2.id = i → c1 = c2 := by
  intro l
  induction l with
  | nil =>
    intro hnd i c1 c2 hlook hmem hid
    simp at hmem
  | cons y ys ih =>
    intro hnd i c1 c2 hlook hmem hid
    simp only [List.map_cons] at hnd
    have htail : (ys.map Client.id).Nodup := (List.nodup_cons.mp hnd).2
    have hnotmem : y.id ∉ ys.map Client.id := (List.nodup_cons.mp hnd).1
    rw [lookup_cons] at hlook
    by_cases hyeq : y.id = i
    · simp [hyeq] at hlook
      subst hlook
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl heq => exact heq.symm
      | inr hmem2 =>
        exfalso
        apply hnotmem
        rw [hyeq, ← hid]
        exact List.mem_map_of_mem hmem2
    · simp [hyeq] at hlook
      have hlook2 : lookup ys i = some c1 := hlook
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
        exfalso; apply hyeq; have h2 : y.id = i := heq ▸ hid; exact h2
      | inr hmem2 => exact ih htail i c1 c2 hlook2 hmem2 hid

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
    exact iso_helper6 s.clients s r i hi
  · simp [h]

theorem req_reset : ResetRule step := by
  intro s r hok c hc
  have hadm : Admissible s r := by
    by_cases h : Admissible s r
    · exact h
    · have hstep : step s r = (.rejected, s) := by unfold step; simp [h]
      rw [hstep] at hok
      simp at hok
  have hmap : (step s r).2.clients =
      s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) := by
    unfold step; simp [hadm]
  refine ⟨advance s c r.time, ?_, ?_, ?_⟩
  · rw [hmap, lookup_map_adv_test2, if_pos rfl, hc, Option.map_some]
  · intro hexp
    unfold advance windowStart windowCount
    simp [hexp]
  · intro hlt
    have hne : ¬ (c.start + s.window ≤ r.time) := Nat.not_le_of_gt hlt
    unfold advance windowStart windowCount
    simp [hne]

theorem req_effects : Effects step := by
  intro s r hok
  have hadm : Admissible s r := by
    by_cases h : Admissible s r
    · exact h
    · have hstep : (step s r).1 = .rejected := by unfold step; simp [h]
      rw [hstep] at hok
      simp at hok
  have h2 : (step s r).2 = { s with clients := (s.clients.map (fun x =>
      if x.id = r.client then advance s x r.time else x)) } := by
    unfold step; simp [hadm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [h2]
  · rw [h2]
    simp only
    induction s.clients with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, iso_fid2 s r x, ih]
  · intro i
    rw [h2]
    simp only
    rw [lookup_map_adv_test2]
    rfl

theorem req_window_bound : WindowBound step := by
  intro s r hbound c hmem
  by_cases hadm : Admissible s r
  · have hcli : (step s r).2.clients = s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) := by
      unfold step; simp [hadm]
    have hlim : (step s r).2.limit = s.limit := by
      unfold step; simp [hadm]
    rw [hlim]
    rw [hcli] at hmem
    rw [List.mem_map] at hmem
    obtain ⟨x, hxmem, hxc⟩ := hmem
    have hxbound : x.count ≤ s.limit := hbound x hxmem
    obtain ⟨hnd, hadmits⟩ := hadm
    by_cases hxeq : x.id = r.client
    · have hxc2 : c = advance s x r.time := by simp [hxeq] at hxc; exact hxc.symm
      cases heq : lookup s.clients r.client with
      | none =>
        have hfalse : Admits s r.time none := by rw [← heq]; exact hadmits
        exact False.elim hfalse
      | some c0 =>
        have hadmits2 : c0.start ≤ r.time ∧ windowCount s c0 r.time < s.limit := by
          have h : Admits s r.time (some c0) := by rw [← heq]; exact hadmits
          exact h
        obtain ⟨hle, hlt⟩ := hadmits2
        have hx_eq : c0 = x := lookup_nodup_unique_aux s.clients hnd r.client c0 x heq hxmem hxeq
        have hwc : windowCount s x r.time < s.limit := by rw [← hx_eq]; exact hlt
        rw [hxc2]
        unfold advance
        simp only
        exact Nat.succ_le_of_lt hwc
    · have hxc2 : c = x := by simp [hxeq] at hxc; exact hxc.symm
      rw [hxc2]
      exact hxbound
  · have hstep2 : (step s r).2 = s := by unfold step; simp [hadm]
    rw [hstep2] at hmem ⊢
    exact hbound c hmem

end FixedWindow
