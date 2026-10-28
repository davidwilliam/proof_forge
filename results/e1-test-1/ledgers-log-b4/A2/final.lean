import EntryLog.Spec
import EntryLog.Lemmas
namespace EntryLog
instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance
/-- Acceptance check for an entry with a new ID. -/
def accepts (s : State) (e : Entry) : Bool :=
  s.accounts.contains e.account && e.amount != 0 && decide (0 ≤ s.balance e.account + e.amount)
def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if accepts s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem accepts_of_valid (s : State) (e : Entry) (h : ValidEntry s e) : accepts s e = true := by
  unfold accepts ValidEntry at *
  obtain ⟨hmem, hne, hle⟩ := h
  simp [*]

theorem req_valid_succeeds_aux : ValidSucceeds step := by
  intro s e hnew hvalid
  have hacc : accepts s e = true := accepts_of_valid s e hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  unfold step
  simp [hr, hacc]

theorem tmp_inv2 : ∀ (s : State) (e : Entry), accepts s e = false → ¬ ValidEntry s e := by
  intro s e h hc
  have ht := accepts_of_valid s e hc
  rw [ht] at h
  exact Bool.noConfusion h

theorem req_effects_test1 : Effects step := by
  intro s e hnew hvalid
  have hacc : accepts s e = true := accepts_of_valid s e hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  have hstep : step s e = (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    simp [hr, hacc]
  rw [hstep]
  exact ⟨rfl, rfl, fun a => by by_cases h : a = e.account <;> simp [h]⟩

theorem req_append_only2 : AppendOnly step := by
  intro s e
  unfold step
  cases h : receiptOf s.log e.id with
  | none =>
    by_cases ha : accepts s e = true
    · simp [ha]
    · simp [ha]
  | some n =>
    simp

theorem my_test_foo : True := trivial

theorem my_test_bar : List.Nodup [1,2] := by decide

theorem aux_notmem_test (log : List Entry) (i : EntryId)
    (h : receiptOf log i = none) : i ∉ ids log := by
  intro hmem
  obtain ⟨n, hn⟩ := receiptOf_isSome hmem
  rw [h] at hn
  simp at hn

theorem aux_probe_b : List.Nodup ([] : List Nat) := by simp

theorem aux_probe_c : List.Nodup ([3] : List Nat) := by simp

theorem aux_probe_d : True := trivial
#check List.Nodup
#check List.nodup_cons

theorem aux_probe_e (l : List Nat) (h : l.Nodup) : True := by
  cases h with
  | nil => trivial
  | cons h1 h2 => trivial

theorem probe1b (s : State) (e : Entry) (h : accepts s e = true) : e.account ∈ s.accounts := by
  unfold accepts at h
  simp at h
  exact h.1.1

theorem probe2b (s : State) (e : Entry) (h : accepts s e = true) : 0 ≤ s.balance e.account + e.amount := by
  unfold accepts at h
  simp at h
  exact h.2

theorem probe_step_acc (s : State) (e : Entry) (hacc : accepts s e = true) (hr : receiptOf s.log e.id = none) (a : AccountId) (ha : a ∈ (step s e).2.accounts) : a ∈ s.accounts := by
  unfold step at ha
  simp [hr, hacc] at ha
  exact ha

theorem probe_nn_simp (s : State) (e : Entry) (a : AccountId) (hr : receiptOf s.log e.id = none) (hacc : accepts s e = true) (ha : a ∈ (step s e).2.accounts) : a ∈ s.accounts := by
  simp only [step, hr, hacc, ↓reduceIte] at ha
  exact ha

theorem probe_nn_goal (s : State) (e : Entry) (a : AccountId) (hr : receiptOf s.log e.id = none) (hacc : accepts s e = true) : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by
  simp only [step, hr, hacc, ↓reduceIte]

theorem probe_inv1 (s : State) (e : Entry) (h : accepts s e = true) : s.accounts.contains e.account = true := by
  unfold accepts at h
  have h2 : (s.accounts.contains e.account && e.amount != 0) = true := by
    have : ((s.accounts.contains e.account && e.amount != 0) && decide (0 ≤ s.balance e.account + e.amount)) = true := h
    exact (Bool.and_eq_true_iff.mp this).1
  exact (Bool.and_eq_true_iff.mp h2).1

#check Bool.and_eq_true_iff
#check Bool.eq_true_of_ne_false
#check Bool.ne_false_of_eq_true

theorem probe_neb (s : State) (e : Entry) (h : accepts s e = true) : e.amount ≠ 0 := by
  unfold accepts at h
  simp at h
  exact h.1.2

theorem accepts_valid2 (s : State) (e : Entry) (h : accepts s e = true) : ValidEntry s e := by
  exact ⟨probe1b s e h, probe_neb s e h, probe2b s e h⟩

theorem helper_nodup_single2 (x : Nat) : ([x] : List Nat).Nodup := by
  simp

theorem helper_nodup_app2 (l : List Nat) (x : Nat) (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨h1, helper_nodup_single2 x, ?_⟩
  intro a ha b hb
  simp at hb
  subst hb
  intro hc
  subst hc
  exact h2 ha

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnew hvalid
  have hacc : accepts s e = true := accepts_of_valid s e hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  unfold step
  simp [hr, hacc]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnew hnvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  have haccF : accepts s e = false := by
    cases h : accepts s e
    · rfl
    · exact absurd (accepts_valid2 s e h) hnvalid
  show step s e = _
  unfold step
  simp [hr, haccF]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hn
  unfold step
  simp [hn]

theorem req_effects : Effects step := by
  intro s e hnew hvalid
  have hacc : accepts s e = true := accepts_of_valid s e hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  have hstep : step s e = (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    unfold step
    simp [hr, hacc]
  rw [hstep]
  exact ⟨rfl, rfl, fun a => by by_cases h : a = e.account <;> simp [h]⟩

theorem req_append_only : AppendOnly step := by
  intro s e
  unfold step
  cases h : receiptOf s.log e.id with
  | none =>
    by_cases ha : accepts s e = true
    · simp [ha]
    · simp [Bool.eq_false_of_ne_true ha]
  | some n =>
    simp

theorem req_unique_ids     : UniqueIds step := by
  intro s e hnod
  cases hrc : receiptOf s.log e.id with
  | some n =>
    have h2 : (step s e).2 = s := by simp only [step, hrc]
    rw [h2]
    exact hnod
  | none =>
    have hnotmem : e.id ∉ ids s.log := aux_notmem_test s.log e.id hrc
    by_cases hacc : accepts s e = true
    · have h2log : (step s e).2.log = s.log ++ [e] := by simp only [step, hrc, hacc, ↓reduceIte]
      rw [h2log, ids_append]
      simp only [ids]
      exact helper_nodup_app2 _ _ hnod hnotmem
    · have haccF : accepts s e = false := Bool.eq_false_of_ne_true hacc
      have h2 : (step s e).2 = s := by simp [step, hrc, haccF]
      rw [h2]
      exact hnod

theorem req_nonnegative : NonNegative step := by
  intro s e hnn a ha
  cases hrc : receiptOf s.log e.id with
  | some n =>
    have hacc_eq : (step s e).2.accounts = s.accounts := by simp only [step, hrc]
    have hb : (step s e).2.balance a = s.balance a := by simp only [step, hrc]
    rw [hacc_eq] at ha
    rw [hb]
    exact hnn a ha
  | none =>
    by_cases hacc : accepts s e = true
    · have hacc_eq : (step s e).2.accounts = s.accounts := by simp only [step, hrc, hacc, ↓reduceIte]
      have hb : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := probe_nn_goal s e a hrc hacc
      rw [hacc_eq] at ha
      rw [hb]
      by_cases heq : a = e.account
      · simp only [heq, ↓reduceIte]
        have hle : (0 : Int) ≤ s.balance e.account + e.amount := probe2b s e hacc
        subst heq
        exact hle
      · simp only [heq, ↓reduceIte]
        exact hnn a ha
    · have haccF : accepts s e = false := Bool.eq_false_of_ne_true hacc
      have hacc_eq : (step s e).2.accounts = s.accounts := by simp [step, hrc, haccF]
      have hb : (step s e).2.balance a = s.balance a := by simp [step, hrc, haccF]
      rw [hacc_eq] at ha
      rw [hb]
      exact hnn a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  cases hrc : receiptOf s.log e.id with
  | some n =>
    have h2 : (step s e).2 = s := by simp only [step, hrc]
    rw [h2]
    exact hcons a
  | none =>
    by_cases hacc : accepts s e = true
    · have h2log : (step s e).2.log = s.log ++ [e] := by simp only [step, hrc, hacc, ↓reduceIte]
      have h2bal : (step s e).2.balance a = (if a = e.account then s.balance a + e.amount else s.balance a) := by simp only [step, hrc, hacc, ↓reduceIte]
      rw [h2log, h2bal, hcons a]
      have happ : logSum (s.log ++ [e]) a = logSum s.log a + logSum [e] a := sumOver_append s.log [e] _
      rw [happ]
      have hsing : logSum [e] a = (if e.account = a then e.amount else 0) := by simp [logSum, sumOver]
      rw [hsing]
      by_cases heq : a = e.account
      · subst heq
        simp
      · have heq2 : ¬ (e.account = a) := fun h => heq h.symm
        simp [heq, heq2]
    · have haccF : accepts s e = false := Bool.eq_false_of_ne_true hacc
      have h2 : (step s e).2 = s := by simp [step, hrc, haccF]
      rw [h2]
      exact hcons a

end EntryLog
