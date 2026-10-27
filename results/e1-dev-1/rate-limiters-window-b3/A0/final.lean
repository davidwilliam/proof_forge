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

def step : Impl := fun s r =>
  if _h : Admissible s r then
    (.ok, { s with clients := s.clients.map (upd s r) })
  else (.rejected, s)

theorem upd_id (s : State) (r : Request) (x : Client) : (upd s r x).id = x.id := by
  unfold upd
  by_cases h : x.id = r.client
  · simp [h, advance]
  · simp [h]

theorem map_upd_ids (s : State) (r : Request) (l : List Client) :
    (l.map (upd s r)).map Client.id = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, upd_id s r x, ih]

theorem lookup_map_upd (s : State) (r : Request) (l : List Client) (i : ClientId) :
    lookup (l.map (upd s r)) i = (lookup l i).map (upd s r) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, lookup_cons]
    have h_id : (upd s r x).id = x.id := upd_id s r x
    by_cases hx : x.id = i
    · have hx' : (upd s r x).id = i := h_id.trans hx
      simp [hx, hx']
    · have hx' : ¬ ((upd s r x).id = i) := by rw [h_id]; exact hx
      simp [hx, hx', ih]

theorem option_map_upd_ne (s : State) (r : Request) (l : List Client) (i : ClientId)
    (hne : i ≠ r.client) :
    (lookup l i).map (upd s r) = lookup l i := by
  cases hEq : lookup l i with
  | none => rfl
  | some c =>
    have hc : c.id = i := lookup_id hEq
    have hcond : ¬ (c.id = r.client) := by rw [hc]; exact hne
    have hupd : upd s r c = c := by unfold upd; simp [hcond]
    simp [hupd]

theorem option_map_upd_eq (s : State) (r : Request) (l : List Client) (i : ClientId)
    (heq : i = r.client) :
    (lookup l i).map (upd s r) = (lookup l i).map (fun c => advance s c r.time) := by
  cases hEq : lookup l i with
  | none => rfl
  | some c =>
    have hc : c.id = i := lookup_id hEq
    have hcond : c.id = r.client := by rw [hc, heq]
    have hupd : upd s r c = advance s c r.time := by unfold upd; simp [hcond]
    simp [hupd]

theorem step_ok_of_adm (s : State) (r : Request) (h : Admissible s r) :
    (step s r).1 = .ok := by
  unfold step
  simp [h]

theorem step_eq_of_adm (s : State) (r : Request) (h : Admissible s r) :
    step s r = (.ok, { s with clients := s.clients.map (upd s r) }) := by
  unfold step
  simp [h]

theorem step_eq_of_not_adm (s : State) (r : Request) (h : ¬ Admissible s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem adm_of_step_ok (s : State) (r : Request) (h : (step s r).1 = .ok) :
    Admissible s r := by
  by_cases ha : Admissible s r
  · exact ha
  · have heq := step_eq_of_not_adm s r ha
    have h1 : (step s r).1 = .rejected := by rw [heq]
    rw [h] at h1
    cases h1

theorem mem_eq_of_lookup : ∀ (l : List Client) {i : ClientId} {c x : Client},
    (l.map Client.id).Nodup → lookup l i = some c → x ∈ l → x.id = i → x = c := by
  intro l
  induction l with
  | nil =>
    intro i c x _ hlook _ _
    rw [lookup_nil] at hlook
    cases hlook
  | cons y ys ih =>
    intro i c x hN hlook hmem hxid
    rw [lookup_cons] at hlook
    have hNmem : y.id ∉ (ys.map Client.id) ∧ (ys.map Client.id).Nodup :=
      List.nodup_cons.mp (by simpa using hN)
    have hNot : y.id ∉ (ys.map Client.id) := hNmem.1
    have hTail : (ys.map Client.id).Nodup := hNmem.2
    by_cases hy : y.id = i
    · simp only [hy, ↓reduceIte] at hlook
      have hyc : y = c := by cases hlook; rfl
      have hmem' : x = y ∨ x ∈ ys := List.mem_cons.mp hmem
      cases hmem' with
      | inl heq => rw [heq, hyc]
      | inr hmem2 =>
        have hIn : x.id ∈ (ys.map Client.id) :=
          List.mem_map.mpr ⟨x, hmem2, rfl⟩
        rw [hxid, ← hy] at hIn
        exact absurd hIn hNot
    · simp only [hy, ↓reduceIte] at hlook
      have hmem' : x = y ∨ x ∈ ys := List.mem_cons.mp hmem
      cases hmem' with
      | inl heq =>
        rw [heq] at hxid
        exact absurd hxid hy
      | inr hmem2 =>
        exact ih hTail hlook hmem2 hxid

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  exact step_ok_of_adm s r h

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  exact step_eq_of_not_adm s r h

theorem req_isolation : Isolation step := by
  intro s r i hne
  by_cases ha : Admissible s r
  · have heq := step_eq_of_adm s r ha
    have h2 : (step s r).2.clients = s.clients.map (upd s r) := by rw [heq]
    rw [h2, lookup_map_upd, option_map_upd_ne s r s.clients i hne]
  · have heq := step_eq_of_not_adm s r ha
    have h2 : (step s r).2 = s := by rw [heq]
    rw [h2]

theorem req_reset : ResetRule step := by
  intro s r hok c hlook
  have ha := adm_of_step_ok s r hok
  have heq := step_eq_of_adm s r ha
  have h2 : (step s r).2.clients = s.clients.map (upd s r) := by rw [heq]
  have hlookup : lookup (step s r).2.clients r.client = some (upd s r c) := by
    rw [h2, lookup_map_upd, hlook, Option.map_some]
  refine ⟨upd s r c, hlookup, ?_, ?_⟩
  · intro hexp
    have hcond : c.id = r.client := lookup_id hlook
    have hupd_eq : upd s r c = advance s c r.time := by
      unfold upd
      simp [hcond]
    rw [hupd_eq]
    unfold advance windowStart windowCount
    simp [hexp]
  · intro hlt
    have hcond : c.id = r.client := lookup_id hlook
    have hupd_eq : upd s r c = advance s c r.time := by
      unfold upd
      simp [hcond]
    rw [hupd_eq]
    have hle : ¬ (c.start + s.window ≤ r.time) := by omega
    unfold advance windowStart windowCount
    simp [hle]

theorem req_effects : Effects step := by
  intro s r hok
  have ha := adm_of_step_ok s r hok
  have heq := step_eq_of_adm s r ha
  have h2st : (step s r).2 = { s with clients := s.clients.map (upd s r) } := by rw [heq]
  have h2w : (step s r).2.window = s.window := by rw [h2st]
  have h2l : (step s r).2.limit = s.limit := by rw [h2st]
  have h2c : (step s r).2.clients = s.clients.map (upd s r) := by rw [h2st]
  refine ⟨h2w, h2l, ?_, ?_⟩
  · rw [h2c, map_upd_ids]
  · intro i
    rw [h2c, lookup_map_upd]
    have hExp : expectedLookup s r i =
      if i = r.client then (lookup s.clients i).map (fun c => advance s c r.time)
      else lookup s.clients i := by unfold expectedLookup; rfl
    rw [hExp]
    by_cases heq2 : i = r.client
    · simp only [heq2, ↓reduceIte]
      subst heq2
      exact option_map_upd_eq s r s.clients r.client rfl
    · simp only [heq2, ↓reduceIte]
      exact option_map_upd_ne s r s.clients i heq2

theorem req_window_bound : WindowBound step := by
  intro s r hall c hmem
  by_cases ha : Admissible s r
  · have heq := step_eq_of_adm s r ha
    have h2st : (step s r).2 = { s with clients := s.clients.map (upd s r) } := by rw [heq]
    have h2l : (step s r).2.limit = s.limit := by rw [h2st]
    have h2c : (step s r).2.clients = s.clients.map (upd s r) := by rw [h2st]
    rw [h2l]
    rw [h2c] at hmem
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hmem
    have hNodup : (s.clients.map Client.id).Nodup := ha.1
    have hAdm : Admits s r.time (lookup s.clients r.client) := ha.2
    by_cases hx : x.id = r.client
    · have hupd : upd s r x = advance s x r.time := by unfold upd; simp [hx]
      rw [hupd]
      cases hlook : lookup s.clients r.client with
      | none =>
        rw [hlook] at hAdm
        cases hAdm
      | some cc =>
        rw [hlook] at hAdm
        have hxc : x = cc := mem_eq_of_lookup s.clients hNodup hlook hxm hx
        subst hxc
        have hlt_cnt : windowCount s x r.time < s.limit := hAdm.2
        by_cases hexp : x.start + s.window ≤ r.time
        · have hwc : windowCount s x r.time = 0 := by unfold windowCount; simp [hexp]
          rw [hwc] at hlt_cnt
          have hAdv : (advance s x r.time).count = 1 := by
            unfold advance windowCount; simp [hexp]
          rw [hAdv]
          omega
        · have hwc : windowCount s x r.time = x.count := by
            unfold windowCount; simp [hexp]
          rw [hwc] at hlt_cnt
          have hAdv : (advance s x r.time).count = x.count + 1 := by
            unfold advance windowCount; simp [hexp]
          rw [hAdv]
          omega
    · have hupd : upd s r x = x := by unfold upd; simp [hx]
      rw [hupd]
      exact hall x hxm
  · have heq := step_eq_of_not_adm s r ha
    have h2 : (step s r).2 = s := by rw [heq]
    rw [h2] at hmem ⊢
    exact hall c hmem

end FixedWindow
