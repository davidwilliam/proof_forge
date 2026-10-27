import FixedWindow.Spec
import FixedWindow.Lemmas
namespace FixedWindow

instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance

def upd (s : State) (r : Request) (x : Client) : Client :=
  if x.id = r.client then advance s x r.time else x

theorem upd_id (s : State) (r : Request) (x : Client) : (upd s r x).id = x.id := by
  unfold upd advance
  by_cases h : x.id = r.client <;> simp [h]

theorem upd_adv (s : State) (r : Request) (x : Client) (h : x.id = r.client) :
    upd s r x = advance s x r.time := by
  unfold upd
  simp [h]

theorem upd_self (s : State) (r : Request) (x : Client) (h : x.id ≠ r.client) :
    upd s r x = x := by
  unfold upd
  simp [h]

theorem map_upd_ids (s : State) (r : Request) (l : List Client) :
    (l.map (upd s r)).map Client.id = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [upd_id s r x, ih]

theorem lookup_upd_target (s : State) (r : Request) (l : List Client) :
    lookup (l.map (upd s r)) r.client = (lookup l r.client).map (fun c => advance s c r.time) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [lookup_cons, lookup_cons]
    have hid : (upd s r x).id = x.id := upd_id s r x
    rw [hid]
    by_cases hx : x.id = r.client
    · have hupd : upd s r x = advance s x r.time := upd_adv s r x hx
      simp [hx, hupd]
    · simp [hx, ih]

theorem lookup_upd_other (s : State) (r : Request) (l : List Client) (i : ClientId)
    (hne : i ≠ r.client) :
    lookup (l.map (upd s r)) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [lookup_cons, lookup_cons]
    have hid : (upd s r x).id = x.id := upd_id s r x
    rw [hid]
    by_cases hx : x.id = i
    · have hxr : x.id ≠ r.client := by rw [hx]; exact hne
      have hupd : upd s r x = x := upd_self s r x hxr
      simp [hx, hupd, ih]
    · simp [hx, ih]

theorem mem_of_map_upd (s : State) (r : Request) (l : List Client) (y : Client)
    (h : y ∈ l.map (upd s r)) : ∃ x, x ∈ l ∧ upd s r x = y := by
  have h2 := List.mem_map.mp h
  obtain ⟨a, ha1, ha2⟩ := h2
  exact ⟨a, ha1, ha2⟩

theorem nodup_unique (l : List Client) : (l.map Client.id).Nodup →
    ∀ (x y : Client), x ∈ l → y ∈ l → x.id = y.id → x = y := by
  induction l with
  | nil =>
    intro hn x y hx _ _
    cases hx
  | cons hd tl ih =>
    intro hn x y hx hy hid
    simp only [List.mem_cons] at hx hy
    have hnmap : List.map Client.id (hd :: tl) = hd.id :: List.map Client.id tl := rfl
    rw [hnmap, List.nodup_cons] at hn
    obtain ⟨hnotin, htail⟩ := hn
    cases hx with
    | inl hxeq =>
      cases hy with
      | inl hyeq => rw [hxeq, hyeq]
      | inr hymem =>
        exfalso
        have heq : hd.id = y.id := by rw [← hxeq]; exact hid
        rw [heq] at hnotin
        exact hnotin (List.mem_map_of_mem hymem)
    | inr hxmem =>
      cases hy with
      | inl hyeq =>
        exfalso
        have heq : hd.id = x.id := by rw [← hyeq]; exact hid.symm
        rw [heq] at hnotin
        exact hnotin (List.mem_map_of_mem hxmem)
      | inr hymem => exact ih htail x y hxmem hymem hid

def step : Impl := fun s r =>
  if Admissible s r then (.ok, { s with clients := s.clients.map (upd s r) })
  else (.rejected, s)

theorem step_eq_ok (s : State) (r : Request) (h : Admissible s r) :
    step s r = (.ok, { s with clients := s.clients.map (upd s r) }) := by
  unfold step
  exact if_pos h

theorem step_eq_rej (s : State) (r : Request) (h : ¬ Admissible s r) :
    step s r = (.rejected, s) := by
  unfold step
  exact if_neg h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hstep := step_eq_ok s r h
  rw [hstep]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  exact step_eq_rej s r h

theorem step_ok_imp_adm (s : State) (r : Request) (hOk : (step s r).1 = .ok) :
    Admissible s r := by
  by_cases h : Admissible s r
  · exact h
  · have hstep := step_eq_rej s r h
    rw [hstep] at hOk
    exact Outcome.noConfusion hOk

theorem req_isolation : Isolation step := by
  intro s r i hne
  by_cases h : Admissible s r
  · have hEq := step_eq_ok s r h
    have hstep : (step s r).2.clients = s.clients.map (upd s r) := by rw [hEq]
    rw [hstep]
    exact lookup_upd_other s r s.clients i hne
  · have hEq := step_eq_rej s r h
    have hstep : (step s r).2.clients = s.clients := by rw [hEq]
    rw [hstep]

theorem req_reset : ResetRule step := by
  intro s r hOk c hlook
  have hAdm0 : Admissible s r := step_ok_imp_adm s r hOk
  have hstep := step_eq_ok s r hAdm0
  have htarget : lookup (s.clients.map (upd s r)) r.client = some (advance s c r.time) := by
    have h1 := lookup_upd_target s r s.clients
    rw [hlook] at h1
    exact h1
  have hafter : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
    have h2 : (step s r).2.clients = s.clients.map (upd s r) := by rw [hstep]
    rw [h2, htarget]
  refine ⟨advance s c r.time, hafter, ?_, ?_⟩
  · intro hexp
    have hW : windowStart s c r.time = r.time := by
      unfold windowStart
      exact if_pos hexp
    have hC0 : windowCount s c r.time = 0 := by
      unfold windowCount
      exact if_pos hexp
    constructor
    · have hs : (advance s c r.time).start = windowStart s c r.time := rfl
      rw [hs, hW]
    · have hc : (advance s c r.time).count = windowCount s c r.time + 1 := rfl
      rw [hc, hC0]
  · intro hlt
    have hnot : ¬ c.start + s.window ≤ r.time := by omega
    have hW : windowStart s c r.time = c.start := by
      unfold windowStart
      exact if_neg hnot
    have hC0 : windowCount s c r.time = c.count := by
      unfold windowCount
      exact if_neg hnot
    constructor
    · have hs : (advance s c r.time).start = windowStart s c r.time := rfl
      rw [hs, hW]
    · have hc : (advance s c r.time).count = windowCount s c r.time + 1 := rfl
      rw [hc, hC0]

theorem req_effects : Effects step := by
  intro s r hOk
  have hAdm0 : Admissible s r := step_ok_imp_adm s r hOk
  have hstep := step_eq_ok s r hAdm0
  have hwin : (step s r).2.window = s.window := by rw [hstep]
  have hlim : (step s r).2.limit = s.limit := by rw [hstep]
  have hmap : (step s r).2.clients.map Client.id = s.clients.map Client.id := by
    have h2 : (step s r).2.clients = s.clients.map (upd s r) := by rw [hstep]
    rw [h2]
    exact map_upd_ids s r s.clients
  have hlookup : ∀ i, lookup (step s r).2.clients i = expectedLookup s r i := by
    intro i
    have h2 : (step s r).2.clients = s.clients.map (upd s r) := by rw [hstep]
    rw [h2]
    unfold expectedLookup
    by_cases hi : i = r.client
    · simp only [hi, ↓reduceIte]
      exact lookup_upd_target s r s.clients
    · simp only [hi, ↓reduceIte]
      exact lookup_upd_other s r s.clients i hi
  exact ⟨hwin, hlim, hmap, hlookup⟩

theorem req_window_bound : WindowBound step := by
  intro s r hbound c hmem
  by_cases h : Admissible s r
  · have hEq := step_eq_ok s r h
    have hclients : (step s r).2.clients = s.clients.map (upd s r) := by rw [hEq]
    have hlimit : (step s r).2.limit = s.limit := by rw [hEq]
    rw [hlimit]
    rw [hclients] at hmem
    obtain ⟨x, hxmem, hxeq⟩ := mem_of_map_upd s r s.clients c hmem
    have hxle : x.count ≤ s.limit := hbound x hxmem
    have hNodup : (s.clients.map Client.id).Nodup := h.1
    have hAdmits : Admits s r.time (lookup s.clients r.client) := h.2
    cases hm : lookup s.clients r.client with
    | none =>
      rw [hm] at hAdmits
      cases hAdmits
    | some c0 =>
      have hc0mem : c0 ∈ s.clients := lookup_mem hm
      have hc0id : c0.id = r.client := lookup_id hm
      have hlt : windowCount s c0 r.time < s.limit := by
        have hA : Admits s r.time (some c0) := by rw [← hm]; exact hAdmits
        exact hA.2
      by_cases hxr : x.id = r.client
      · have hid_eq : x.id = c0.id := by rw [hxr, hc0id]
        have x_eq : x = c0 := nodup_unique s.clients hNodup x c0 hxmem hc0mem hid_eq
        have hupd : upd s r c0 = advance s c0 r.time := upd_adv s r c0 hc0id
        have hca : c = advance s c0 r.time := by rw [← hxeq, x_eq, hupd]
        have hc : c.count = windowCount s c0 r.time + 1 := by simp [hca, advance]
        omega
      · have hupd : upd s r x = x := upd_self s r x hxr
        have hceq : c = x := by rw [← hxeq, hupd]
        rw [hceq]
        exact hxle
  · have hEq := step_eq_rej s r h
    have hclientsN : (step s r).2.clients = s.clients := by rw [hEq]
    have hlimitN : (step s r).2.limit = s.limit := by rw [hEq]
    rw [hlimitN]
    rw [hclientsN] at hmem
    exact hbound c hmem

end FixedWindow
