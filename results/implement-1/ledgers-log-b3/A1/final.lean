import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

def step : Impl := fun s e =>
  match h : receiptOf s.log e.id with
  | some n => (Outcome.ok n, s)
  | none =>
    if h1 : e.account ∈ s.accounts then
      if h2 : e.amount ≠ 0 then
        if h3 : 0 ≤ s.balance e.account + e.amount then
          (Outcome.ok s.log.length,
            { accounts := s.accounts,
              log := s.log ++ [e],
              balance := fun a => s.balance a + (if a = e.account then e.amount else 0) })
        else (Outcome.rejected, s)
      else (Outcome.rejected, s)
    else (Outcome.rejected, s)

theorem foo_test2 (s : State) (e : Entry) (hrec : receiptOf s.log e.id = none) (hmem : e.account ∈ s.accounts) (hne : e.amount ≠ 0) (hbal : 0 ≤ s.balance e.account + e.amount) : (step s e).1 = Outcome.ok s.log.length := by
  have hstep : step s e = (Outcome.ok s.log.length,
            { accounts := s.accounts,
              log := s.log ++ [e],
              balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
    unfold step
    rw [hrec]
    simp [hmem, hne, hbal]
  rw [hstep]

theorem req_effects_aux : Effects step := by
  intro s e hfresh hvalid
  obtain ⟨hmem, hne, hbal⟩ := hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hfresh
  have hstep : step s e = (Outcome.ok s.log.length,
            { accounts := s.accounts,
              log := s.log ++ [e],
              balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
    unfold step
    rw [hrec]
    simp [hmem, hne, hbal]
  constructor
  · rw [hstep]
  · constructor
    · rw [hstep]
    · intro a
      rw [hstep]

theorem req_append_only_aux2 : AppendOnly step := by
  intro s e
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (Outcome.ok n, s) := by unfold step; rw [hrec]
    rw [hstep]
    exact ⟨[], by simp⟩
  | none =>
    by_cases h1 : e.account ∈ s.accounts <;> by_cases h2 : e.amount ≠ 0 <;> by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
    · have hstep : step s e = (Outcome.ok s.log.length,
              { accounts := s.accounts,
                log := s.log ++ [e],
                balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
        unfold step; rw [hrec]; simp [h1, h2, h3]
      rw [hstep]
      exact ⟨[[e][0]], by simp⟩
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2, h3]
      rw [hstep]
      exact ⟨[], by simp⟩
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2]
      rw [hstep]
      exact ⟨[], by simp⟩
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2]
      rw [hstep]
      exact ⟨[], by simp⟩
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      rw [hstep]
      exact ⟨[], by simp⟩
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      rw [hstep]
      exact ⟨[], by simp⟩
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      rw [hstep]
      exact ⟨[], by simp⟩
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      rw [hstep]
      exact ⟨[], by simp⟩

theorem helper_nodup_append_single (l : List Nat) (x : Nat) (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have hcons : a ∉ as ∧ as.Nodup := List.nodup_cons.mp h1
    have hx1 : x ≠ a := by
      intro heq
      apply h2
      simp [heq]
    have hx2 : x ∉ as := by
      intro hmem
      apply h2
      simp [hmem]
    have ih' := ih hcons.2 hx2
    have ha_not : a ∉ (as ++ [x]) := by
      intro hmem
      rw [List.mem_append] at hmem
      rcases hmem with h | h
      · exact hcons.1 h
      · simp at h
        exact hx1 h.symm
    exact List.nodup_cons.mpr ⟨ha_not, ih'⟩

theorem logSum_append_single (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hfresh hvalid
  obtain ⟨hmem, hne, hbal⟩ := hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hfresh
  exact foo_test2 s e hrec hmem hne hbal

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hfresh hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hfresh
  unfold ValidEntry at hinvalid
  unfold step
  rw [hrec]
  by_cases h1 : e.account ∈ s.accounts
  · by_cases h2 : e.amount ≠ 0
    · by_cases h3 : 0 ≤ s.balance e.account + e.amount
      · exfalso; apply hinvalid; exact ⟨h1, h2, h3⟩
      · simp [h1, h2, h3]
    · simp [h1, h2]
  · simp [h1]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  rw [h]

theorem req_effects : Effects step := req_effects_aux

theorem req_append_only : AppendOnly step := req_append_only_aux2

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (Outcome.ok n, s) := by unfold step; rw [hrec]
    have hlog : (step s e).2.log = s.log := by rw [hstep]
    rw [hlog]
    exact hnodup
  | none =>
    have hfresh : e.id ∉ ids s.log := by
      intro hmem
      obtain ⟨m, hm⟩ := receiptOf_isSome hmem
      rw [hrec] at hm
      cases hm
    by_cases h1 : e.account ∈ s.accounts <;> by_cases h2 : e.amount ≠ 0 <;> by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
    · have hstep : step s e = (Outcome.ok s.log.length,
                { accounts := s.accounts,
                  log := s.log ++ [e],
                  balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
          unfold step; rw [hrec]; simp [h1, h2, h3]
      have hlog : (step s e).2.log = s.log ++ [e] := by rw [hstep]
      rw [hlog]
      have heq : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [heq]
      exact helper_nodup_append_single (ids s.log) e.id hnodup hfresh
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2, h3]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      rw [hlog]; exact hnodup
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      rw [hlog]; exact hnodup
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      rw [hlog]; exact hnodup
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      rw [hlog]; exact hnodup
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      rw [hlog]; exact hnodup
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      rw [hlog]; exact hnodup
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      rw [hlog]; exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hnonneg a ha
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (Outcome.ok n, s) := by unfold step; rw [hrec]
    have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
    have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
    rw [hacc] at ha
    rw [hbal]
    exact hnonneg a ha
  | none =>
    by_cases h1 : e.account ∈ s.accounts <;> by_cases h2 : e.amount ≠ 0 <;> by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
    · have hstep : step s e = (Outcome.ok s.log.length,
                { accounts := s.accounts,
                  log := s.log ++ [e],
                  balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
          unfold step; rw [hrec]; simp [h1, h2, h3]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by rw [hstep]
      rw [hacc] at ha
      rw [hbal]
      by_cases heq : a = e.account
      · subst heq
        simp only [↓reduceIte] at hbal ⊢
        exact h3
      · simp [heq]
        exact hnonneg a ha
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2, h3]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hacc] at ha
      rw [hbal]
      exact hnonneg a ha
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hacc] at ha
      rw [hbal]
      exact hnonneg a ha
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hacc] at ha
      rw [hbal]
      exact hnonneg a ha
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hacc] at ha
      rw [hbal]
      exact hnonneg a ha
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hacc] at ha
      rw [hbal]
      exact hnonneg a ha
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hacc] at ha
      rw [hbal]
      exact hnonneg a ha
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hacc : (step s e).2.accounts = s.accounts := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hacc] at ha
      rw [hbal]
      exact hnonneg a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  cases hrec : receiptOf s.log e.id with
  | some n =>
    have hstep : step s e = (Outcome.ok n, s) := by unfold step; rw [hrec]
    have hlog : (step s e).2.log = s.log := by rw [hstep]
    have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
    rw [hlog, hbal]
    exact hcons a
  | none =>
    by_cases h1 : e.account ∈ s.accounts <;> by_cases h2 : e.amount ≠ 0 <;> by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
    · have hstep : step s e = (Outcome.ok s.log.length,
                { accounts := s.accounts,
                  log := s.log ++ [e],
                  balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
          unfold step; rw [hrec]; simp [h1, h2, h3]
      have hlog : (step s e).2.log = s.log ++ [e] := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by rw [hstep]
      rw [hlog, hbal]
      rw [hcons a]
      rw [logSum_append_single]
      by_cases heq : a = e.account
      · subst heq
        simp
      · have h1' : ¬ (e.account = a) := fun h => heq h.symm
        simp [heq, h1']
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2, h3]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hlog, hbal]; exact hcons a
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hlog, hbal]; exact hcons a
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1, h2]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hlog, hbal]; exact hcons a
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hlog, hbal]; exact hcons a
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hlog, hbal]; exact hcons a
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hlog, hbal]; exact hcons a
    · have hstep : step s e = (Outcome.rejected, s) := by unfold step; rw [hrec]; simp [h1]
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hstep]
      rw [hlog, hbal]; exact hcons a

end EntryLog
