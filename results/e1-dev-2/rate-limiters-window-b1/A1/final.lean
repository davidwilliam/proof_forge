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

theorem map_adv_id2 (s : State) (r : Request) (x : Client) :
    (if x.id = r.client then advance s x r.time else x).id = x.id := by
  by_cases he : x.id = r.client
  · simp only [he, ↓reduceIte, advance]
  · simp only [he, ↓reduceIte]

theorem lookup_map_adv_at3 (s : State) (r : Request) (L : List Client) (c : Client)
    (h : lookup L r.client = some c) :
    lookup (L.map fun x => if x.id = r.client then advance s x r.time else x) r.client =
      some (advance s c r.time) := by
  induction L with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    simp only [List.map_cons]
    have hmid : (if x.id = r.client then advance s x r.time else x).id = x.id := map_adv_id2 s r x
    simp only [lookup_cons, hmid]
    have hL : lookup (x :: xs) r.client = if x.id = r.client then some x else lookup xs r.client := rfl
    rw [hL] at h
    by_cases hx : x.id = r.client
    · simp only [hx, ↓reduceIte] at h ⊢
      obtain rfl := Option.some_inj.mp h
      simp [hx]
    · simp only [hx, ↓reduceIte] at h ⊢
      exact ih h

theorem eff_map_ids (s : State) (r : Request) (L : List Client) :
    ((L.map fun x => if x.id = r.client then advance s x r.time else x).map Client.id = L.map Client.id) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, map_adv_id2, ih]

theorem eff_lookup_gen (s : State) (r : Request) (L : List Client) (i : ClientId) :
    lookup (L.map fun x => if x.id = r.client then advance s x r.time else x) i =
      if i = r.client then (lookup L i).map (fun c => advance s c r.time) else lookup L i := by
  induction L with
  | nil =>
    show (none : Option Client) = _
    by_cases hi : i = r.client <;> simp [hi]
  | cons x xs ih =>
    have hmid : (if x.id = r.client then advance s x r.time else x).id = x.id := map_adv_id2 s r x
    have hM : lookup ((if x.id = r.client then advance s x r.time else x) :: List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) i =
      if x.id = i then some (if x.id = r.client then advance s x r.time else x) else lookup (List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) i := by
      have h := lookup_cons (if x.id = r.client then advance s x r.time else x) (List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) i
      rw [hmid] at h
      exact h
    have hOrig : lookup (x :: xs) i = if x.id = i then some x else lookup xs i := lookup_cons x xs i
    show lookup ((if x.id = r.client then advance s x r.time else x) :: List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) i = _
    rw [hM, ih, hOrig]
    by_cases hi : i = r.client
    · subst hi
      by_cases hx : x.id = r.client
      · simp [hx]
      · simp [hx]
    · by_cases hx : x.id = i
      · have hne : x.id ≠ r.client := by intro heq; rw [heq] at hx; exact hi hx.symm
        simp [hx, hi, hne]
      · simp [hx, hi]

theorem adv_count_le_aux2 (s : State) (c : Client) (t : Nat)
    (hlt : windowCount s c t < s.limit) :
    (advance s c t).count ≤ s.limit := by
  simp only [advance, windowCount] at hlt ⊢
  by_cases he : c.start + s.window ≤ t <;> simp only [he, ↓reduceIte] at hlt ⊢ <;> omega

theorem wb_test2 (s : State) (r : Request) (c : Client)
    (hNodup : (s.clients.map Client.id).Nodup)
    (hEq : lookup s.clients r.client = some c)
    (hAdm : c.start ≤ r.time ∧ windowCount s c r.time < s.limit) :
    (step s r).2.clients = s.clients.map (fun x => if x.id = r.client then advance s x r.time else x) := by
  have hS : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
    unfold step
    simp [hNodup, hEq, hAdm]
  rw [hS]

theorem nodup_get_mem2 (L : List Client) : ∀ (i : ClientId) (c x : Client),
    (L.map Client.id).Nodup →
    lookup L i = some c →
    x ∈ L → x.id = i → x = c := by
  induction L with
  | nil => intro i c x hN hL hm hid; simp at hm
  | cons y ys ih =>
    intro i c x hN hL hm hid
    simp only [List.map_cons, List.nodup_cons] at hN
    obtain ⟨hNotMem, hTail⟩ := hN
    have hL2 : lookup (y :: ys) i = if y.id = i then some y else lookup ys i := rfl
    rw [hL2] at hL
    simp only [List.mem_cons] at hm
    by_cases hy : y.id = i
    · simp only [hy, ↓reduceIte] at hL
      obtain rfl := Option.some_inj.mp hL
      rcases hm with rfl | hmem2
      · rfl
      · exfalso
        apply hNotMem
        rw [List.mem_map]
        exact ⟨x, hmem2, hid.trans hy.symm⟩
    · simp only [hy, ↓reduceIte] at hL
      rcases hm with rfl | hmem2
      · exfalso; exact hy hid
      · exact ih i c x hTail hL hmem2 hid

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨hNodup, hAdm⟩ := h
  unfold step
  simp only [hNodup, ↓reduceIte]
  cases hEq : lookup s.clients r.client with
  | none =>
    have hF : Admits s r.time (lookup s.clients r.client) := hAdm
    rw [hEq] at hF
    cases hF
  | some c =>
    have hF : Admits s r.time (lookup s.clients r.client) := hAdm
    rw [hEq] at hF
    simp only [Admits] at hF
    obtain ⟨hle, hlt⟩ := hF
    simp only [hle, hlt, and_self, ↓reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · simp only [hNodup, ↓reduceIte]
    have hAdm : ¬ Admits s r.time (lookup s.clients r.client) := fun ha => h ⟨hNodup, ha⟩
    cases hEq : lookup s.clients r.client with
    | none => rfl
    | some c =>
      have h2 : ¬ (c.start ≤ r.time ∧ windowCount s c r.time < s.limit) := by
        intro hc
        apply hAdm
        rw [hEq]
        exact hc
      simp only [h2, ↓reduceIte]
  · simp only [hNodup, ↓reduceIte]

theorem req_isolation : Isolation step := by
  intro s r i hi
  unfold step
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · simp only [hNodup, ↓reduceIte]
    cases hEq : lookup s.clients r.client with
    | none => rfl
    | some c =>
      by_cases hAdm : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
      · simp [hAdm]
        have hmap : lookup ((s.clients.map fun x => if x.id = r.client then advance s x r.time else x)) i = lookup s.clients i := by
          induction s.clients with
          | nil => rfl
          | cons x xs ih =>
            have hmid := map_adv_id2 s r x
            simp only [List.map_cons]
            rw [show lookup ((if x.id = r.client then advance s x r.time else x) :: List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) i
              = if (if x.id = r.client then advance s x r.time else x).id = i then some (if x.id = r.client then advance s x r.time else x)
                else lookup (List.map (fun x => if x.id = r.client then advance s x r.time else x) xs) i from rfl]
            rw [hmid, ih]
            rw [show (lookup (x :: xs) i = if x.id = i then some x else lookup xs i) from rfl]
            by_cases hx : x.id = i
            · have hne : x.id ≠ r.client := by intro heq; rw [heq] at hx; exact hi hx.symm
              have hmapped : (if x.id = r.client then advance s x r.time else x) = x := by
                simp [hne]
              rw [hmapped, hx]
            · simp [hx]
        simpa using hmap
      · simp [hAdm]
  · simp only [hNodup, ↓reduceIte]

theorem req_reset : ResetRule step := by
  intro s r hOk c hEq
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · by_cases hAdm : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
    · have hStep : step s r =
          (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
        unfold step
        simp only [hNodup, ↓reduceIte, hEq, hAdm, and_self]
      refine ⟨advance s c r.time, ?_, ?_, ?_⟩
      · have hlook : lookup (step s r).2.clients r.client = some (advance s c r.time) := by
          rw [hStep]
          simp only
          exact lookup_map_adv_at3 s r s.clients c hEq
        exact hlook
      · intro hexp
        have hs : windowStart s c r.time = r.time := by
          unfold windowStart
          simp [hexp]
        have hc : windowCount s c r.time = 0 := by
          unfold windowCount
          simp [hexp]
        have h1 : (advance s c r.time).start = r.time := by
          unfold advance
          simp [hs]
        have h2 : (advance s c r.time).count = 1 := by
          unfold advance
          simp [hc]
        exact ⟨h1, h2⟩
      · intro hlt
        have hexp_neg : ¬ (c.start + s.window ≤ r.time) := by omega
        have hs : windowStart s c r.time = c.start := by
          unfold windowStart
          simp [hexp_neg]
        have hc : windowCount s c r.time = c.count := by
          unfold windowCount
          simp [hexp_neg]
        have h1 : (advance s c r.time).start = c.start := by
          unfold advance
          simp [hs]
        have h2 : (advance s c r.time).count = c.count + 1 := by
          unfold advance
          simp [hc]
        exact ⟨h1, h2⟩
    · have hStep : step s r = (.rejected, s) := by
        unfold step
        simp only [hNodup, ↓reduceIte, hEq, hAdm, ↓reduceIte]
      rw [hStep] at hOk
      simp at hOk
  · have hStep : step s r = (.rejected, s) := by
      unfold step
      simp only [hNodup, ↓reduceIte]
    rw [hStep] at hOk
    simp at hOk

theorem req_effects : Effects step := by
  intro s r hOk
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · cases hEq : lookup s.clients r.client with
    | none =>
      have hStep : step s r = (.rejected, s) := by
        unfold step
        simp [hNodup, hEq]
      rw [hStep] at hOk
      simp at hOk
    | some c =>
      by_cases hAdm : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
      · have hStep : step s r =
            (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
          unfold step
          simp [hNodup, hEq, hAdm]
        rw [hStep]
        refine ⟨rfl, rfl, eff_map_ids s r s.clients, ?_⟩
        intro i
        show lookup (List.map (fun x => if x.id = r.client then advance s x r.time else x) s.clients) i = _
        rw [eff_lookup_gen]
        unfold expectedLookup
        by_cases hi : i = r.client <;> simp [hi]
      · have hStep : step s r = (.rejected, s) := by
          unfold step
          simp [hNodup, hEq, hAdm]
        rw [hStep] at hOk
        simp at hOk
  · have hStep : step s r = (.rejected, s) := by
      unfold step
      simp [hNodup]
    rw [hStep] at hOk
    simp at hOk

theorem req_window_bound : WindowBound step := by
  intro s r hBound c' hmem
  by_cases hNodup : (s.clients.map Client.id).Nodup
  · cases hEq : lookup s.clients r.client with
    | none =>
      have hS : step s r = (.rejected, s) := by
        unfold step; simp [hNodup, hEq]
      rw [hS] at hmem ⊢
      simp only at hmem ⊢
      exact hBound c' hmem
    | some c =>
      by_cases hAdm : c.start ≤ r.time ∧ windowCount s c r.time < s.limit
      · have hS : step s r = (.ok, { s with clients := s.clients.map fun x => if x.id = r.client then advance s x r.time else x }) := by
          unfold step; simp [hNodup, hEq, hAdm]
        rw [hS] at hmem ⊢
        simp only at hmem ⊢
        rw [List.mem_map] at hmem
        obtain ⟨x, hxmem, hxeq⟩ := hmem
        have himg : (if x.id = r.client then advance s x r.time else x) = c' := hxeq
        by_cases hx : x.id = r.client
        · have hxc : x = c := nodup_get_mem2 s.clients r.client c x hNodup hEq hxmem hx
          simp only [hx, ↓reduceIte] at himg
          rw [hxc] at himg
          rw [← himg]
          exact adv_count_le_aux2 s c r.time hAdm.2
        · simp only [hx, ↓reduceIte] at himg
          rw [← himg]
          exact hBound x hxmem
      · have hS : step s r = (.rejected, s) := by
          unfold step; simp [hNodup, hEq, hAdm]
        rw [hS] at hmem ⊢
        simp only at hmem ⊢
        exact hBound c' hmem
  · have hS : step s r = (.rejected, s) := by
      unfold step; simp [hNodup]
    rw [hS] at hmem ⊢
    simp only at hmem ⊢
    exact hBound c' hmem

end FixedWindow
