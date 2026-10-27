import FixedWindow.Spec
import FixedWindow.Lemmas

namespace FixedWindow

instance instDecidableAdmits (s : State) (t : Nat) : (o : Option Client) → Decidable (Admits s t o)
  | some c => inferInstanceAs (Decidable (c.start ≤ t ∧ windowCount s c t < s.limit))
  | none => isFalse (fun h => h)

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible
  infer_instance

def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with clients := s.clients.map fun c =>
      if c.id = r.client then advance s c r.time else c })
  else (.rejected, s)

theorem adv_id (s : State) (c : Client) (t : Nat) : (advance s c t).id = c.id := rfl

theorem f_id (s : State) (t : Nat) (target : ClientId) (c : Client) :
    (if c.id = target then advance s c t else c).id = c.id := by
  by_cases h : c.id = target
  · simp only [if_pos h, adv_id]
  · simp only [if_neg h]

theorem map_ids_preserve (l : List Client) (s : State) (t : Nat) (target : ClientId) :
    ((l.map fun c => if c.id = target then advance s c t else c).map Client.id) = l.map Client.id := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    have hid : (if c.id = target then advance s c t else c).id = c.id := f_id s t target c
    rw [hid, ih]

theorem lookup_map_other (l : List Client) (s : State) (t : Nat) (target i : ClientId) (hne : i ≠ target) :
    lookup (l.map fun c => if c.id = target then advance s c t else c) i = lookup l i := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    have h_left : lookup ((if c.id = target then advance s c t else c) :: List.map (fun c => if c.id = target then advance s c t else c) cs) i
      = if (if c.id = target then advance s c t else c).id = i then some (if c.id = target then advance s c t else c) else lookup (List.map (fun c => if c.id = target then advance s c t else c) cs) i := rfl
    have h_right : lookup (c :: cs) i = if c.id = i then some c else lookup cs i := rfl
    rw [h_left, h_right, ih]
    have hid : (if c.id = target then advance s c t else c).id = c.id := f_id s t target c
    rw [hid]
    by_cases hc : c.id = i
    · rw [if_pos hc, if_pos hc]
      have hnt : ¬ (c.id = target) := by
        intro hcon
        apply hne
        rw [← hc, hcon]
      rw [if_neg hnt]
    · rw [if_neg hc, if_neg hc]

theorem lookup_map_at_target (l : List Client) (s : State) (t : Nat) (target : ClientId) :
    lookup (l.map fun c => if c.id = target then advance s c t else c) target
      = (lookup l target).map fun c => if c.id = target then advance s c t else c := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    have h_left : lookup ((if c.id = target then advance s c t else c) :: List.map (fun c => if c.id = target then advance s c t else c) cs) target
      = if (if c.id = target then advance s c t else c).id = target then some (if c.id = target then advance s c t else c) else lookup (List.map (fun c => if c.id = target then advance s c t else c) cs) target := rfl
    have h_right : lookup (c :: cs) target = if c.id = target then some c else lookup cs target := rfl
    rw [h_left]
    have hid : (if c.id = target then advance s c t else c).id = c.id := f_id s t target c
    rw [hid, h_right, ih]
    by_cases hc : c.id = target
    · simp only [if_pos hc, Option.map_some]
    · simp only [if_neg hc]

theorem lookup_map_self (l : List Client) (s : State) (t : Nat) (target : ClientId) :
    lookup (l.map fun c => if c.id = target then advance s c t else c) target
      = (lookup l target).map fun c => advance s c t := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    have hid : (if c.id = target then advance s c t else c).id = c.id := f_id s t target c
    have eL : lookup ((if c.id = target then advance s c t else c) :: List.map (fun c => if c.id = target then advance s c t else c) cs) target
        = if c.id = target then some (if c.id = target then advance s c t else c) else lookup (List.map (fun c => if c.id = target then advance s c t else c) cs) target := by
      have h0 : lookup ((if c.id = target then advance s c t else c) :: List.map (fun c => if c.id = target then advance s c t else c) cs) target
        = if (if c.id = target then advance s c t else c).id = target then some (if c.id = target then advance s c t else c) else lookup (List.map (fun c => if c.id = target then advance s c t else c) cs) target := rfl
      rwa [hid] at h0
    have eR : (lookup (c :: cs) target).map (fun c => advance s c t)
        = if c.id = target then some (advance s c t) else (lookup cs target).map (fun c => advance s c t) := by
      have h0 : lookup (c :: cs) target = if c.id = target then some c else lookup cs target := rfl
      rw [h0]
      by_cases hc : c.id = target
      · simp [hc]
      · simp [hc]
    rw [eL, eR, ih]
    by_cases hc : c.id = target
    · simp [hc]
    · simp [hc]

theorem mem_ids {l : List Client} {c : Client} (h : c ∈ l) : c.id ∈ l.map Client.id := by
  induction l with
  | nil =>
    cases h
  | cons x xs ih =>
    simp only [List.map_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (ih hmem))

theorem mem_map_exists (l : List Client) (f : Client → Client) (c : Client)
    (hmem : c ∈ l.map f) : ∃ c0 ∈ l, c = f c0 := by
  induction l with
  | nil =>
    cases hmem
  | cons x xs ih =>
    simp only [List.map_cons] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨x, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨c0, hm, heq⟩ := ih hmem
      exact ⟨c0, List.mem_cons.mpr (Or.inr hm), heq⟩

theorem mem_unique_aux (l : List Client) (hNodup : (l.map Client.id).Nodup)
    {i : ClientId} {c0 : Client} (hlook : lookup l i = some c0)
    {c : Client} (hmem : c ∈ l) (hid : c.id = i) : c = c0 := by
  induction l generalizing c c0 with
  | nil =>
    simp [lookup] at hlook
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hNodup
    obtain ⟨hne, htail⟩ := hNodup
    have hlook2 : (if x.id = i then (some x : Option Client) else lookup xs i) = some c0 := hlook
    by_cases hx : x.id = i
    · rw [if_pos hx] at hlook2
      have he : x = c0 := by cases hlook2; rfl
      rcases List.mem_cons.mp hmem with rfl | hmem
      · rw [he]
      · exfalso
        apply hne
        have h1 : c.id ∈ xs.map Client.id := mem_ids hmem
        rw [hid, ← hx] at h1
        exact h1
    · rw [if_neg hx] at hlook2
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exfalso
        exact hx hid
      · exact ih htail hlook2 hmem hid

theorem step_ok_iff (s : State) (r : Request) : ((step s r).1 = .ok) ↔ Admissible s r := by
  unfold step
  by_cases h : Admissible s r <;> simp [h]

theorem step_ok_state (s : State) (r : Request) (h : Admissible s r) :
    (step s r).2 = { s with clients := s.clients.map fun c => if c.id = r.client then advance s c r.time else c } := by
  unfold step
  simp [h]

theorem step_noop_state (s : State) (r : Request) (h : ¬ Admissible s r) :
    (step s r).2 = s := by
  unfold step
  simp [h]

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
  by_cases h : Admissible s r
  · have h2 := step_ok_state s r h
    have hcl : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      rw [h2]
    rw [hcl]
    exact lookup_map_other s.clients s r.time r.client i hne
  · have h2 := step_noop_state s r h
    have hcl : (step s r).2.clients = s.clients := by
      rw [h2]
    rw [hcl]

theorem req_reset : ResetRule step := by
  intro s r hok c hlook
  have hAdm : Admissible s r := (step_ok_iff s r).mp hok
  have h2 := step_ok_state s r hAdm
  have hcl : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
    rw [h2]
  have hc : c.id = r.client := lookup_id hlook
  have hlk : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
    rw [hcl, lookup_map_at_target, hlook]
    simp [hc]
  refine ⟨advance s c r.time, hlk, ?_, ?_⟩
  · intro hexp
    unfold advance windowStart windowCount
    simp [hexp]
  · intro hnexp
    unfold advance windowStart windowCount
    have hle : ¬ (c.start + s.window ≤ r.time) := Nat.not_le_of_gt hnexp
    simp [hle]

theorem req_effects : Effects step := by
  intro s r hok
  have hAdm : Admissible s r := (step_ok_iff s r).mp hok
  have h2 := step_ok_state s r hAdm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [h2]
  · have hcl : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      rw [h2]
    rw [hcl]
    exact map_ids_preserve s.clients s r.time r.client
  · intro i
    have hcl : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      rw [h2]
    rw [hcl]
    by_cases heq : i = r.client
    · subst heq
      have hL := lookup_map_self s.clients s r.time r.client
      have hE : expectedLookup s r r.client = (lookup s.clients r.client).map (fun c => advance s c r.time) := by
        unfold expectedLookup
        rw [if_pos rfl]
      rw [hE]
      exact hL
    · have hL := lookup_map_other s.clients s r.time r.client i heq
      have hE : expectedLookup s r i = lookup s.clients i := by
        unfold expectedLookup
        rw [if_neg heq]
      rw [hE]
      exact hL

theorem req_window_bound : WindowBound step := by
  intro s r hbound c hmem
  by_cases h : Admissible s r
  · have h2 := step_ok_state s r h
    have hlim : (step s r).2.limit = s.limit := by
      rw [h2]
    rw [hlim]
    have hcl : (step s r).2.clients = s.clients.map fun c => if c.id = r.client then advance s c r.time else c := by
      rw [h2]
    rw [hcl] at hmem
    obtain ⟨c0, hm0, heq⟩ := mem_map_exists s.clients _ c hmem
    have hle0 : c0.count ≤ s.limit := hbound c0 hm0
    by_cases hcid : c0.id = r.client
    · have heqc : c = advance s c0 r.time := by
        rw [heq]
        simp [hcid]
      rw [heqc]
      obtain ⟨hNodup, hAdm⟩ := h
      cases hlk : lookup s.clients r.client with
      | none =>
        have hcon : Admits s r.time (lookup s.clients r.client) := hAdm
        rw [hlk] at hcon
        cases hcon
      | some cc =>
        have hcon : Admits s r.time (lookup s.clients r.client) := hAdm
        rw [hlk] at hcon
        obtain ⟨_, hlt⟩ := hcon
        have heqc0 : c0 = cc := mem_unique_aux s.clients hNodup hlk hm0 hcid
        have hlt2 : windowCount s c0 r.time < s.limit := heqc0 ▸ hlt
        have hc_eq : (advance s c0 r.time).count = windowCount s c0 r.time + 1 := rfl
        rw [hc_eq]
        have hW : windowCount s c0 r.time = if c0.start + s.window ≤ r.time then 0 else c0.count := rfl
        rw [hW] at hlt2 ⊢
        by_cases hexp : c0.start + s.window ≤ r.time
        · rw [if_pos hexp] at hlt2 ⊢
          omega
        · rw [if_neg hexp] at hlt2 ⊢
          omega
    · have heqc : c = c0 := by
        rw [heq]
        simp [hcid]
      rw [heqc]
      exact hle0
  · have h2 := step_noop_state s r h
    rw [h2] at hmem ⊢
    exact hbound c hmem

end FixedWindow
