import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_idempotency_aux : Idempotent step := by
  intro s r h
  unfold step at h ⊢
  by_cases hv : ValidPayout s r
  · simp only [hv, ↓reduceIte] at h ⊢
    constructor
    · intro x
      simp
    · have hNotValid : ¬ ValidPayout { s with balance := expectedBalance s r, applied := r.txId :: s.applied } r := by
        intro hV
        unfold ValidPayout at hv hV
        obtain ⟨_, _, _, _, _, _, _, _, _, hNotMem⟩ := hV
        simp at hNotMem
      have hStep : (if ValidPayout { s with balance := expectedBalance s r, applied := r.txId :: s.applied } r then True else False) = False := by
        simp [hNotValid]
      simp [hNotValid]
  · simp [hv] at h

theorem fair_derive (s : State) (r : Request) (h : (step s r).1 = .ok) : ValidPayout s r := by
  unfold step at h
  by_cases hvv : ValidPayout s r
  · exact hvv
  · simp [hvv] at h

theorem fair_probe3 (s : State) (r : Request) (hv : ValidPayout s r) (i : Nat) (hi : i < r.recipients.length) :
    expectedBalance s r r.recipients[i] - s.balance r.recipients[i]
      = (fairShare r.amount r.recipients.length i : Int) := by
  obtain ⟨hnodup_acc, hpos, hne, hnodup_rec, hsrcNotIn, hsrcMem, hsub, hauth, hle, hnotMem⟩ := hv
  unfold expectedBalance
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne_src : r.recipients[i] ≠ r.source := fun heq => hsrcNotIn (heq ▸ hmem)
  have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by
    simp [hne_src]
  rw [hif]
  have hidx : indexOf? r.recipients r.recipients[i] = some i :=
    indexOf?_getElem hnodup_rec i hi
  have hshare : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
    unfold shareOf
    rw [hidx]
  rw [hshare]
  omega

theorem probe1 (k q : Nat) : (k + 1) * q = k * q + q := by
 exact Nat.succ_mul k q
#check @Nat.succ_mul
#check @Nat.add_mul
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @List.range_succ
#check @List.length_range

theorem probe_cast2 : ((1 : Nat) : Int) = 1 := by simp

theorem probe_cast3 (n : Nat) : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
#check @Int.ofNat_nonneg

theorem tmp_test_thm : True := trivial

theorem tmp_swap_test2 : True := trivial

theorem swap_sum_test : (1 : Int) = 1 := rfl

theorem sumOver_append_test (l1 l2 : List Nat) (f : Nat → Int) : sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem tmp_check_add_mul : True := trivial
#check @Int.add_mul
#check @Int.mul_add
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @List.range_succ
#check @List.getElem_mem





theorem plan0_share_sum_eq_range_aux (l : List AccountId) (hnd : l.Nodup)
    (amount n k : Nat) (hn : n = k + l.length) :
    sumOver l (fun a => ((match indexOf? l a with
      | some i => fairShare amount n (k + i)
      | none => 0 : Nat) : Int))
      = sumOver (List.range l.length) (fun i => (fairShare amount n (k + i) : Int)) := by
  have hAppend : ∀ (l1 l2 : List Nat) (f : Nat → Int), sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
    intro l1 l2 f
    induction l1 with
    | nil => simp
    | cons a t ih => simp [ih]; omega
  have hHead : ∀ (m : Nat) (f : Nat → Int), sumOver (List.range (m + 1)) f = f 0 + sumOver (List.range m) (fun i => f (i + 1)) := by
    intro m f
    induction m generalizing f with
    | zero => simp
    | succ m ih =>
      have h1 : List.range (m + 2) = List.range (m + 1) ++ [m + 1] := by simp [List.range_succ]
      have h2 : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      have e1 : sumOver ([m + 1] : List Nat) f = f (m + 1) := by simp
      have e2 : sumOver ([m] : List Nat) (fun i => f (i + 1)) = f (m + 1) := by simp
      rw [h1, hAppend, e1, ih]
      rw [h2, hAppend, e2]
      omega
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hx, hxs⟩ := hnd
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    have hhead : (match indexOf? (x :: xs) x with | some i => fairShare amount n (k + i) | none => 0) = fairShare amount n k := by
      have h0 : indexOf? (x :: xs) x = some 0 := by simp [indexOf?]
      rw [h0]; simp
    have hleft_cons : sumOver (x :: xs) (fun a => ((match indexOf? (x :: xs) a with | some i => fairShare amount n (k + i) | none => 0 : Nat) : Int))
      = ((fairShare amount n k : Nat) : Int) + sumOver xs (fun a => ((match indexOf? (x :: xs) a with | some i => fairShare amount n (k + i) | none => 0 : Nat) : Int)) := by
      simp only [sumOver_cons, hhead]
    rw [hleft_cons]
    have hshift : sumOver xs (fun a => ((match indexOf? (x :: xs) a with | some i => fairShare amount n (k + i) | none => 0 : Nat) : Int))
      = sumOver xs (fun a => ((match indexOf? xs a with | some i => fairShare amount n (k + 1 + i) | none => 0 : Nat) : Int)) := by
      apply sumOver_congr
      intro a ha
      have hne : a ≠ x := fun h => hx (h ▸ ha)
      have hxa : x ≠ a := Ne.symm hne
      have e : indexOf? (x :: xs) a = if x = a then some 0 else (indexOf? xs a).map (· + 1) := rfl
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by rw [e, if_neg hxa]
      cases h : indexOf? xs a with
      | none => rw [hidx, h]; rfl
      | some i => rw [hidx, h]; simp only [Option.map_some]; congr 1; congr 1; omega
    rw [hshift]
    have hn' : n = (k + 1) + xs.length := by omega
    have hih := ih hxs (k + 1) hn'
    rw [hih]
    have hright : sumOver (List.range (List.length (x :: xs))) (fun i => (fairShare amount n (k + i) : Int))
      = ((fairShare amount n k : Nat) : Int) + sumOver (List.range xs.length) (fun i => (fairShare amount n (k + 1 + i) : Int)) := by
      rw [hlen]
      have hhead2 := hHead xs.length (fun i => (fairShare amount n (k + i) : Int))
      simp only [Nat.add_zero] at hhead2
      rw [hhead2]
      congr 1
      apply sumOver_congr
      intro a ha
      have heq : k + (a + 1) = k + 1 + a := by omega
      rw [heq]
    rw [hright]




theorem plan0_sumOver_range_fairShare (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by sorry

theorem plan0_sumOver_eq_of_subset {l sub : List AccountId}
    (hl : l.Nodup) (hsubnd : sub.Nodup) (hsub : ∀ x ∈ sub, x ∈ l)
    (f : AccountId → Int) (hz : ∀ a, a ∉ sub → f a = 0) :
    sumOver l f = sumOver sub f := by sorry

theorem plan0_sumOver_append {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

theorem tmp_range_head_test2 (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by
      simp [List.range_succ]
    have h2 : List.range (n + 1) = List.range n ++ [n] := by
      simp [List.range_succ]
    have e1 : sumOver ([n + 1] : List Nat) f = f (n + 1) := by simp
    have e2 : sumOver ([n] : List Nat) (fun i => f (i + 1)) = f (n + 1) := by simp
    rw [h1, plan0_sumOver_append, e1, ih]
    rw [h2, plan0_sumOver_append, e2]
    omega

theorem plan0_sumOver_range_head (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f
      = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by
      simp [List.range_succ]
    have h2 : List.range (n + 1) = List.range n ++ [n] := by
      simp [List.range_succ]
    have e1 : sumOver ([n + 1] : List Nat) f = f (n + 1) := by simp
    have e2 : sumOver ([n] : List Nat) (fun i => f (i + 1)) = f (n + 1) := by simp
    rw [h1, plan0_sumOver_append, e1, ih]
    rw [h2, plan0_sumOver_append, e2]
    omega

theorem myProbeA (k : Nat) (l : List AccountId) : True := by
  induction l generalizing k with
  | nil => trivial
  | cons x xs ih => exact ih k











theorem tmp_indexOf_cons_ne_test2 (x : AccountId) (xs : List AccountId) (a : AccountId)
    (h : a ≠ x) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  have hxa : x ≠ a := Ne.symm h
  have e : indexOf? (x :: xs) a = if x = a then some 0 else (indexOf? xs a).map (· + 1) := rfl
  rw [e, if_neg hxa]

theorem plan1_indexOf_cons_ne (x : AccountId) (xs : List AccountId) (a : AccountId)
    (h : a ≠ x) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by
  have hxa : x ≠ a := Ne.symm h
  have e : indexOf? (x :: xs) a = if x = a then some 0 else (indexOf? xs a).map (· + 1) := rfl
  rw [e, if_neg hxa]

theorem plan1_fairShare_shift (amount n k i : Nat) :
    fairShare amount n (k + (i + 1)) = fairShare amount n (k + 1 + i) := by
  have h : k + (i + 1) = k + 1 + i := by omega
  rw [h]

theorem plan1_sumOver_range_succ (m : Nat) (f : Nat → Int) :
    sumOver (List.range (m + 1)) f
      = f 0 + sumOver (List.range m) (fun i => f (i + 1)) :=
  plan0_sumOver_range_head m f

theorem plan1_indexOf_cons_self (x : AccountId) (xs : List AccountId) :
    indexOf? (x :: xs) x = some 0 := by simp [indexOf?]

theorem plan1_sumOver_shift_cons (x : AccountId) (xs : List AccountId) (hx : x ∉ xs)
    (amount n k : Nat) :
    sumOver xs (fun a => ((match indexOf? (x :: xs) a with
      | some i => fairShare amount n (k + i)
      | none => 0 : Nat) : Int))
      = sumOver xs (fun a => ((match indexOf? xs a with
      | some i => fairShare amount n (k + 1 + i)
      | none => 0 : Nat) : Int)) := by
  apply sumOver_congr
  intro a ha
  have hne : a ≠ x := fun h => hx (h ▸ ha)
  have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) :=
    plan1_indexOf_cons_ne x xs a hne
  cases h : indexOf? xs a with
  | none =>
    rw [hidx, h]
    rfl
  | some i =>
    rw [hidx, h]
    simp only [Option.map_some]
    congr 1
    congr 1
    omega

theorem tmp_aux_proof2 (l : List AccountId) (hnd : l.Nodup)
    (amount n k : Nat) (hn : n = k + l.length) :
    sumOver l (fun a => ((match indexOf? l a with
      | some i => fairShare amount n (k + i)
      | none => 0 : Nat) : Int))
      = sumOver (List.range l.length) (fun i => (fairShare amount n (k + i) : Int)) := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hx, hxs⟩ := hnd
    have hn_simple : n = k + (xs.length + 1) := by simpa using hn
    have hhead : (match indexOf? (x :: xs) x with | some i => fairShare amount n (k + i) | none => 0) = fairShare amount n k := by
      have h0 : indexOf? (x :: xs) x = some 0 := plan1_indexOf_cons_self x xs
      rw [h0]
      simp
    have hleft_cons : sumOver (x :: xs) (fun a => ((match indexOf? (x :: xs) a with | some i => fairShare amount n (k + i) | none => 0 : Nat) : Int))
      = ((fairShare amount n k : Nat) : Int) + sumOver xs (fun a => ((match indexOf? (x :: xs) a with | some i => fairShare amount n (k + i) | none => 0 : Nat) : Int)) := by
      simp only [sumOver_cons, hhead]
    rw [hleft_cons]
    have hshift := plan1_sumOver_shift_cons x xs hx amount n k
    rw [hshift]
    have hn' : n = (k + 1) + xs.length := by omega
    have hih := ih hxs (k + 1) hn'
    rw [hih]
    have hrange : List.length (x :: xs) = xs.length + 1 := rfl
    have hright : sumOver (List.range (List.length (x :: xs))) (fun i => (fairShare amount n (k + i) : Int))
      = ((fairShare amount n k : Nat) : Int) + sumOver (List.range xs.length) (fun i => (fairShare amount n (k + 1 + i) : Int)) := by
      rw [hrange]
      have hhead2 := plan0_sumOver_range_head xs.length (fun i => (fairShare amount n (k + i) : Int))
      simp only [Nat.add_zero] at hhead2
      rw [hhead2]
      congr 1
      apply sumOver_congr
      intro a ha
      have heq : k + (a + 1) = k + 1 + a := by omega
      rw [heq]
    rw [hright]

theorem tmp_selfcontained2 (l : List AccountId) (hnd : l.Nodup)
    (amount n k : Nat) (hn : n = k + l.length) :
    sumOver l (fun a => ((match indexOf? l a with
      | some i => fairShare amount n (k + i)
      | none => 0 : Nat) : Int))
      = sumOver (List.range l.length) (fun i => (fairShare amount n (k + i) : Int)) := by
  have hAppend : ∀ (l1 l2 : List Nat) (f : Nat → Int), sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
    intro l1 l2 f
    induction l1 with
    | nil => simp
    | cons a t ih => simp [ih]; omega
  have hHead : ∀ (m : Nat) (f : Nat → Int), sumOver (List.range (m + 1)) f = f 0 + sumOver (List.range m) (fun i => f (i + 1)) := by
    intro m f
    induction m generalizing f with
    | zero => simp
    | succ m ih =>
      have h1 : List.range (m + 2) = List.range (m + 1) ++ [m + 1] := by simp [List.range_succ]
      have h2 : List.range (m + 1) = List.range m ++ [m] := by simp [List.range_succ]
      have e1 : sumOver ([m + 1] : List Nat) f = f (m + 1) := by simp
      have e2 : sumOver ([m] : List Nat) (fun i => f (i + 1)) = f (m + 1) := by simp
      rw [h1, hAppend, e1, ih]
      rw [h2, hAppend, e2]
      omega
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hx, hxs⟩ := hnd
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    have hhead : (match indexOf? (x :: xs) x with | some i => fairShare amount n (k + i) | none => 0) = fairShare amount n k := by
      have h0 : indexOf? (x :: xs) x = some 0 := by simp [indexOf?]
      rw [h0]; simp
    have hleft_cons : sumOver (x :: xs) (fun a => ((match indexOf? (x :: xs) a with | some i => fairShare amount n (k + i) | none => 0 : Nat) : Int))
      = ((fairShare amount n k : Nat) : Int) + sumOver xs (fun a => ((match indexOf? (x :: xs) a with | some i => fairShare amount n (k + i) | none => 0 : Nat) : Int)) := by
      simp only [sumOver_cons, hhead]
    rw [hleft_cons]
    have hshift : sumOver xs (fun a => ((match indexOf? (x :: xs) a with | some i => fairShare amount n (k + i) | none => 0 : Nat) : Int))
      = sumOver xs (fun a => ((match indexOf? xs a with | some i => fairShare amount n (k + 1 + i) | none => 0 : Nat) : Int)) := by
      apply sumOver_congr
      intro a ha
      have hne : a ≠ x := fun h => hx (h ▸ ha)
      have hxa : x ≠ a := Ne.symm hne
      have e : indexOf? (x :: xs) a = if x = a then some 0 else (indexOf? xs a).map (· + 1) := rfl
      have hidx : indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by rw [e, if_neg hxa]
      cases h : indexOf? xs a with
      | none => rw [hidx, h]; rfl
      | some i => rw [hidx, h]; simp only [Option.map_some]; congr 1; congr 1; omega
    rw [hshift]
    have hn' : n = (k + 1) + xs.length := by omega
    have hih := ih hxs (k + 1) hn'
    rw [hih]
    have hright : sumOver (List.range (List.length (x :: xs))) (fun i => (fairShare amount n (k + i) : Int))
      = ((fairShare amount n k : Nat) : Int) + sumOver (List.range xs.length) (fun i => (fairShare amount n (k + 1 + i) : Int)) := by
      rw [hlen]
      have hhead2 := hHead xs.length (fun i => (fairShare amount n (k + i) : Int))
      simp only [Nat.add_zero] at hhead2
      rw [hhead2]
      congr 1
      apply sumOver_congr
      intro a ha
      have heq : k + (a + 1) = k + 1 + a := by omega
      rw [heq]
    rw [hright]

theorem plan0b_const (n : Nat) (q : Int) : sumOver (List.range n) (fun _ => q) = (n : Int) * q := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : List.range (n + 1) = List.range n ++ [n] := by simp [List.range_succ]
    rw [h1, plan0_sumOver_append]
    have e1 : sumOver ([n] : List Nat) (fun _ => q) = q := by simp
    rw [e1, ih]
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast, Int.add_mul, Int.one_mul]

theorem plan0b_ite_step (m i : Nat) :
    (if i < m + 1 then (1 : Int) else 0) = (if i < m then (1 : Int) else 0) + (if i = m then (1 : Int) else 0) := by
  by_cases h1 : i < m <;> by_cases h2 : i = m <;> by_cases h3 : i < m + 1 <;> simp [h1, h2, h3] <;> omega

theorem plan0b_indicator_single (n m : Nat) (hm : m < n) :
    sumOver (List.range n) (fun i => (if i = m then (1 : Int) else 0)) = 1 := by
  have hnod : (List.range n).Nodup := List.nodup_range
  have h := sumOver_ite_eq hnod m (1 : Int)
  rw [h]
  have hmem : m ∈ List.range n := by simp [hm]
  simp [hmem]

theorem plan0b_ite_le (n m : Nat) (hm : m ≤ n) :
    sumOver (List.range n) (fun i => (if i < m then (1 : Int) else 0)) = (m : Int) := by
  induction m generalizing n with
  | zero =>
    have hz : ∀ a ∈ List.range n, (if a < 0 then (1 : Int) else 0) = 0 := by
      intro a _
      simp
    have h1 := sumOver_congr (List.range n) (fun i => (if i < 0 then (1 : Int) else 0)) (fun _ => (0 : Int)) hz
    have h2 := plan0b_const n (0 : Int)
    simp only [h1] at *
    simp only [h2] at *
    simp
  | succ m ih =>
    have hmle : m ≤ n := by omega
    have hmlt : m < n := by omega
    have ih' := ih n hmle
    have hcongr : ∀ a ∈ List.range n, (if a < m + 1 then (1 : Int) else 0) = ((if a < m then (1 : Int) else 0) + (if a = m then (1 : Int) else 0)) := by
      intro a _
      exact plan0b_ite_step m a
    have hsplit : sumOver (List.range n) (fun i => (if i < m + 1 then (1 : Int) else 0)) = sumOver (List.range n) (fun i => (if i < m then (1 : Int) else 0)) + sumOver (List.range n) (fun i => (if i = m then (1 : Int) else 0)) := by
      have h1 : sumOver (List.range n) (fun i => (if i < m then (1 : Int) else 0) + (if i = m then (1 : Int) else 0)) = sumOver (List.range n) (fun i => (if i < m then (1 : Int) else 0)) + sumOver (List.range n) (fun i => (if i = m then (1 : Int) else 0)) := sumOver_add _ _ _
      rw [← h1]
      apply sumOver_congr
      exact hcongr
    rw [hsplit, ih', plan0b_indicator_single n m hmlt]
    have hcast : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by simp
    rw [hcast]

theorem plan0_sumOver_range_add_ite (n q m : Nat) (hm : m ≤ n) :
    sumOver (List.range n) (fun i => (q : Int) + (if i < m then (1 : Int) else 0))
      = (n : Int) * (q : Int) + (m : Int) := by
  have h1 : sumOver (List.range n) (fun i => (q : Int) + (if i < m then (1 : Int) else 0))
    = sumOver (List.range n) (fun _ => (q : Int)) + sumOver (List.range n) (fun i => (if i < m then (1 : Int) else 0)) := sumOver_add _ _ _
  rw [h1, plan0b_const n (q : Int), plan0b_ite_le n m hm]

theorem tmp_cast_probe (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by simp

theorem tmp_cast_probe2 (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization  : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  by_cases hv : ValidPayout s r
  · simp [hv]
  · simp [hv] at h

theorem req_idempotency    : Idempotent step := req_idempotency_aux

theorem req_nonnegative    : NonNegative step := by
  intro s r hnn a ha
  unfold step at ha ⊢
  by_cases hv : ValidPayout s r
  · simp only [hv, ↓reduceIte] at ha ⊢
    unfold expectedBalance shareOf
    by_cases heq : a = r.source
    · subst heq
      obtain ⟨_, _, _, _, hsrcNotIn, _, _, _, hle, _⟩ := hv
      have hnone : indexOf? r.recipients r.source = none :=
        indexOf?_eq_none (by simpa using hsrcNotIn)
      simp [hnone]
      omega
    · simp [heq]
      have hbal : 0 ≤ s.balance a := hnn a ha
      have hshare : 0 ≤ ((match indexOf? r.recipients a with | some i => fairShare r.amount r.recipients.length i | none => 0 : Nat) : Int) :=
        Int.ofNat_nonneg _
      omega
  · simp only [hv, ↓reduceIte] at ha ⊢
    exact hnn a ha

theorem req_fair_shares : FairShares step := by
  intro s r h i hi
  have hv : ValidPayout s r := fair_derive s r h
  have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
    unfold step
    simp [hv]
  rw [hbal]
  exact fair_probe3 s r hv i hi

theorem req_conservation   : Conserves step := sorry

end Payout
