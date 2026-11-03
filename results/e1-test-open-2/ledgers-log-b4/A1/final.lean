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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hfresh hvalid
  unfold step
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hfresh
  have hacc : accepts s e = true := by
    unfold ValidEntry at hvalid
    obtain ⟨hmem, hne, hbal⟩ := hvalid
    unfold accepts
    have hc : s.accounts.contains e.account = true := by simp [hmem]
    have h2 : (e.amount != 0) = true := by simp [hne]
    have h3 : decide (0 ≤ s.balance e.account + e.amount) = true := by simp [hbal]
    -- show accepts true
    simp only [hc, h2, h3, Bool.true_and]
  simp [hrec, hacc]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s e hfresh hinvalid
  unfold step
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hfresh
  rw [hrec]
  have hacc_false : accepts s e = false := by
    cases hac : accepts s e
    · rfl
    · exfalso
      apply hinvalid
      unfold accepts at hac
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hac
      obtain ⟨⟨hmem_c, hne_b⟩, hbal⟩ := hac
      have hmem : e.account ∈ s.accounts := by
        -- contains true implies mem
        simp at hmem_c
        exact hmem_c
      have hne : e.amount ≠ 0 := by
        intro heq
        simp [heq] at hne_b
      exact ⟨hmem, hne, hbal⟩
  simp only [hrec, hacc_false]
  simp

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  simp [h]

theorem req_effects : Effects step := by
  intro s e hfresh hvalid
  unfold step
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hfresh
  have hacc : accepts s e = true := by
    unfold ValidEntry at hvalid
    obtain ⟨hmem, hne, hbal⟩ := hvalid
    unfold accepts
    have hc : s.accounts.contains e.account = true := by simp [hmem]
    have h2 : (e.amount != 0) = true := by simp [hne]
    have h3 : decide (0 ≤ s.balance e.account + e.amount) = true := by simp [hbal]
    simp only [hc, h2, h3, Bool.true_and]
  simp only [hrec, hacc]
  refine ⟨rfl, rfl, ?_⟩
  intro a
  by_cases h : a = e.account
  · simp [h]
  · simp [h]

theorem req_append_only    : AppendOnly step := by
  intro s e
  unfold step
  cases hr : receiptOf s.log e.id
  case some n =>
    refine ⟨[], ?_⟩
    simp [hr]
  case none =>
    by_cases ha : accepts s e = true
    · refine ⟨[e], ?_⟩
      simp [hr, ha]
    · have ha' : accepts s e = false := by
        cases h : accepts s e <;> simp_all
      refine ⟨[], ?_⟩
      simp [hr, ha']

theorem req_unique_ids : UniqueIds step := by
  intro s e hnd
  unfold step
  cases hrec : receiptOf s.log e.id with
  | some n =>
    simp [hrec, hnd]
  | none =>
    simp only [hrec]
    by_cases hac : accepts s e = true
    · simp only [hac, ite_true]
      have hfresh : e.id ∉ ids s.log := by
        intro hmem
        have : receiptOf s.log e.id ≠ none := by
          obtain ⟨n, hn⟩ := receiptOf_isSome hmem
          simp [hn]
        simp [hrec] at this
      have h_eq : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by
        simp [ids]
      rw [h_eq]
      rw [List.nodup_append]
      refine ⟨hnd, ?_, ?_⟩
      · simp
      · intro a ha b hb
        simp at hb
        subst hb
        intro heq
        subst heq
        exact hfresh ha
    · have hacF : accepts s e = false := by cases h : accepts s e <;> simp_all
      simp [hacF]
      exact hnd

theorem req_nonnegative : NonNegative step := by
  intro s e hnonneg a ha
  simp only [step] at ha ⊢
  cases hrec : receiptOf s.log e.id with
  | some n =>
    simp [hrec] at ha ⊢
    exact hnonneg a ha
  | none =>
    simp only [hrec] at ha ⊢
    by_cases hac : accepts s e = true
    · simp only [hac, ite_true] at ha ⊢
      have hmem : a ∈ s.accounts := ha
      have h0 : 0 ≤ s.balance a := hnonneg a hmem
      by_cases heq : a = e.account
      · simp only [heq] at ⊢
        have hbal : 0 ≤ s.balance e.account + e.amount := by
          unfold accepts at hac
          simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hac
          exact hac.2
        -- after simp, goal is 0 ≤ s.balance e.account + e.amount
        exact hbal
      · simp only [heq] at ⊢
        exact h0
    · have hacF : accepts s e = false := by cases h : accepts s e <;> simp_all
      simp only [hacF, ite_false] at ha ⊢
      exact hnonneg a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  unfold step
  cases hrec : receiptOf s.log e.id with
  | some n =>
    exact hcons a
  | none =>
    by_cases hac : accepts s e = true
    · simp only [hrec, hac, ite_true]
      have hlog : logSum (s.log ++ [e]) a = logSum s.log a + (if e.account = a then e.amount else 0) := by
        unfold logSum
        have h2 := sumOver_append s.log [e] (fun e2 => if e2.account = a then e2.amount else (0 : Int))
        simp [sumOver_cons, sumOver_nil] at h2
        exact h2
      rw [hlog, hcons a]
      by_cases heq : a = e.account
      · rw [if_pos heq]
        have h2 : e.account = a := heq.symm
        rw [if_pos h2]
      · rw [if_neg heq]
        have hne : ¬ e.account = a := fun h => heq h.symm
        rw [if_neg hne]
        rw [Int.add_zero]
    · have hacF : accepts s e = false := by cases h : accepts s e <;> simp_all
      simp only [hrec, hacF, ite_false]
      exact hcons a

end EntryLog
