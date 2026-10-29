import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (Outcome.ok n, s)
  | none =>
    if _hv : e.account ∈ s.accounts ∧ e.amount ≠ 0 ∧ 0 ≤ s.balance e.account + e.amount then
      (Outcome.ok s.log.length,
        { accounts := s.accounts,
          log := s.log ++ [e],
          balance := fun a => s.balance a + (if a = e.account then e.amount else 0) })
    else (Outcome.rejected, s)

theorem myNodupSingle (x : Nat) : List.Nodup [x] := by
  simp

theorem myTest1 (x : Nat) : List.Nodup [x] := List.Pairwise.cons (by simp) List.Pairwise.nil

theorem logSum_append_single (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  simp

theorem probe1 : True := by trivial
#check @List.Nodup
#check @List.Pairwise

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnew hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  have hP : e.account ∈ s.accounts ∧ e.amount ≠ 0 ∧ 0 ≤ s.balance e.account + e.amount := hvalid
  unfold step
  simp only [hr]
  rw [dif_pos hP]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnew hinvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  have hP : ¬ (e.account ∈ s.accounts ∧ e.amount ≠ 0 ∧ 0 ≤ s.balance e.account + e.amount) := by
    intro h
    apply hinvalid
    exact h
  unfold step
  simp only [hr]
  rw [dif_neg hP]

theorem req_duplicate      : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  simp only [h]

theorem req_effects : Effects step := by
  intro s e hnew hvalid
  have hr : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  have hP : e.account ∈ s.accounts ∧ e.amount ≠ 0 ∧ 0 ≤ s.balance e.account + e.amount := hvalid
  have hstep : step s e = (Outcome.ok s.log.length,
        { accounts := s.accounts,
          log := s.log ++ [e],
          balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }) := by
    unfold step
    simp only [hr]
    rw [dif_pos hP]
  rw [hstep]
  exact ⟨rfl, rfl, fun a => rfl⟩

theorem req_append_only : AppendOnly step := by
  intro s e
  by_cases hm : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hm
    have hd := req_duplicate s e n hn
    exact ⟨[], by rw [hd]; simp⟩
  · have hm' : e.id ∉ ids s.log := hm
    by_cases hv : ValidEntry s e
    · obtain ⟨_, hlog, _⟩ := req_effects s e hm' hv
      exact ⟨[e], hlog⟩
    · have hi := req_invalid_noop s e hm' hv
      exact ⟨[], by rw [hi]; simp⟩

theorem req_unique_ids     : UniqueIds step := by
  intro s e hnodup
  by_cases hm : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hm
    have hd := req_duplicate s e n hn
    have hlog : (step s e).2.log = s.log := by rw [hd]
    rw [hlog]
    exact hnodup
  · have hm' : e.id ∉ ids s.log := hm
    by_cases hv : ValidEntry s e
    · obtain ⟨_, hlog, _⟩ := req_effects s e hm' hv
      rw [hlog, ids_append]
      simp only [ids, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hnodup, ?_, ?_⟩
      · simp
      · intro a ha b hb
        simp at hb
        subst hb
        intro hcon
        exact hm' (hcon ▸ ha)
    · have hi := req_invalid_noop s e hm' hv
      have hlog : (step s e).2.log = s.log := by rw [hi]
      rw [hlog]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hnn a ha
  by_cases hm : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hm
    have hd := req_duplicate s e n hn
    have hacc : (step s e).2.accounts = s.accounts := by rw [hd]
    have hbal : (step s e).2.balance a = s.balance a := by rw [hd]
    have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
    rw [hbal]
    exact hnn a ha'
  · have hm' : e.id ∉ ids s.log := hm
    by_cases hv : ValidEntry s e
    · obtain ⟨hacc, hlog, hbalfn⟩ := req_effects s e hm' hv
      have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
      have hbal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := hbalfn a
      rw [hbal]
      by_cases heq : a = e.account
      · have hif : (if a = e.account then e.amount else (0 : Int)) = e.amount := by simp [heq]
        rw [hif, heq]
        obtain ⟨_, _, hle⟩ := hv
        exact hle
      · have hif : (if a = e.account then e.amount else (0 : Int)) = 0 := by simp [heq]
        rw [hif, Int.add_zero]
        exact hnn a ha'
    · have hi := req_invalid_noop s e hm' hv
      have hacc : (step s e).2.accounts = s.accounts := by rw [hi]
      have hbal : (step s e).2.balance a = s.balance a := by rw [hi]
      have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
      rw [hbal]
      exact hnn a ha'

theorem req_consistent : StaysConsistent step := by
  intro s e hc a
  by_cases hm : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hm
    have hd := req_duplicate s e n hn
    have h2 : (step s e).2 = s := by rw [hd]
    rw [h2]
    exact hc a
  · have hm' : e.id ∉ ids s.log := hm
    by_cases hv : ValidEntry s e
    · obtain ⟨hacc, hlog, hbalfn⟩ := req_effects s e hm' hv
      have hbal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := hbalfn a
      have hlg : (step s e).2.log = s.log ++ [e] := hlog
      rw [hbal, hlg, hc a]
      rw [logSum_append_single]
      have hif : (if a = e.account then e.amount else (0 : Int)) = (if e.account = a then e.amount else 0) := by
        by_cases h : a = e.account
        · subst h; rfl
        · have h2 : e.account ≠ a := fun he => h he.symm
          simp [h, h2]
      rw [hif, Int.add_comm]
    · have hi := req_invalid_noop s e hm' hv
      have h2 : (step s e).2 = s := by rw [hi]
      rw [h2]
      exact hc a

end EntryLog
