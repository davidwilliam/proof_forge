import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if ValidEntry s e then
      (.ok s.log.length,
       { accounts := s.accounts, log := s.log ++ [e],
         balance := fun a => s.balance a + if a = e.account then e.amount else 0 })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  show (step s e).1 = Outcome.ok s.log.length
  simp only [step, hrec, hvalid, ite_true]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnotin hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  show step s e = (Outcome.rejected, s)
  simp only [step, hrec, hinvalid, ite_false]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n hrec
  show step s e = (Outcome.ok n, s)
  simp only [step, hrec]

theorem req_effects : Effects step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have hstep : step s e = (Outcome.ok s.log.length, { accounts := s.accounts, log := s.log ++ [e], balance := fun a => s.balance a + if a = e.account then e.amount else 0 }) := by
    simp only [step, hrec, hvalid, ite_true]
  refine ⟨?_, ?_, ?_⟩
  · show (step s e).2.accounts = s.accounts
    rw [hstep]
  · show (step s e).2.log = s.log ++ [e]
    rw [hstep]
  · intro a
    show (step s e).2.balance a = s.balance a + if a = e.account then e.amount else 0
    rw [hstep]

theorem req_append_only : AppendOnly step := by
  intro s e
  show ∃ t, (step s e).2.log = s.log ++ t
  by_cases h : receiptOf s.log e.id = none
  · by_cases hv : ValidEntry s e
    · exact ⟨[e], by simp only [step, h, hv, ite_true]⟩
    · exact ⟨[], by simp only [step, h, hv, ite_false, List.append_nil]⟩
  · have hm : ∃ n, receiptOf s.log e.id = some n := by
      match hm : receiptOf s.log e.id with
      | some n => exact ⟨n, rfl⟩
      | none => exact absurd hm h
    obtain ⟨n, hn⟩ := hm
    exact ⟨[], by simp only [step, hn, List.append_nil]⟩

private theorem nodup_append_singleton_aux {α : Type} [DecidableEq α] (l : List α) (x : α) (hl : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    have h1 : y ∉ ys := (List.nodup_cons.mp hl).1
    have h2 : ys.Nodup := (List.nodup_cons.mp hl).2
    have hx_ys : x ∉ ys := fun hm => hx (List.mem_cons.mpr (Or.inr hm))
    have hx_ne_y : x ≠ y := fun heq => hx (heq ▸ List.mem_cons.mpr (Or.inl rfl))
    have ih' := ih h2 hx_ys
    have heq : (y :: ys) ++ [x] = y :: (ys ++ [x]) := rfl
    rw [heq]
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rw [List.mem_append] at hm
      cases hm with
      | inl h => exact h1 h
      | inr h =>
        simp at h
        exact hx_ne_y h.symm
    · exact ih'

theorem req_unique_ids : UniqueIds step := by
  intro s e hnodup
  show List.Nodup (ids (step s e).2.log)
  by_cases h : receiptOf s.log e.id = none
  · by_cases hv : ValidEntry s e
    · have hstep : (step s e).2.log = s.log ++ [e] := by simp only [step, h, hv, ite_true]
      rw [hstep]
      have hnotin : e.id ∉ ids s.log := by
        intro hmem
        obtain ⟨n, hn⟩ := receiptOf_isSome hmem
        rw [hn] at h
        cases h
      have heq : ids (s.log ++ [e]) = ids s.log ++ [e.id] := ids_append s.log [e]
      rw [heq]
      exact nodup_append_singleton_aux (ids s.log) e.id hnodup hnotin
    · have hstep : (step s e).2.log = s.log := by simp only [step, h, hv, ite_false]
      rw [hstep]
      exact hnodup
  · have hm : ∃ n, receiptOf s.log e.id = some n := by
      match hm : receiptOf s.log e.id with
      | some n => exact ⟨n, rfl⟩
      | none => exact absurd hm h
    obtain ⟨n, hn⟩ := hm
    have hstep : (step s e).2.log = s.log := by simp only [step, hn]
    rw [hstep]
    exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hpos a ha
  show 0 ≤ (step s e).2.balance a
  by_cases h : receiptOf s.log e.id = none
  · by_cases hv : ValidEntry s e
    · have hstep_accounts : (step s e).2.accounts = s.accounts := by simp only [step, h, hv, ite_true]
      have hstep_balance : (step s e).2.balance a = s.balance a + if a = e.account then e.amount else 0 := by
        simp only [step, h, hv, ite_true]
      rw [hstep_accounts] at ha
      rw [hstep_balance]
      have hpos_a := hpos a ha
      have hbal2 : 0 ≤ s.balance e.account + e.amount := hv.2.2
      by_cases heq : a = e.account
      · rw [if_pos heq, heq]
        exact hbal2
      · rw [if_neg heq]
        simp
        exact hpos_a
    · have hstep_accounts : (step s e).2.accounts = s.accounts := by simp only [step, h, hv, ite_false]
      have hstep_balance : (step s e).2.balance a = s.balance a := by simp only [step, h, hv, ite_false]
      rw [hstep_accounts] at ha
      rw [hstep_balance]
      exact hpos a ha
  · have hm : ∃ n, receiptOf s.log e.id = some n := by
      match hm : receiptOf s.log e.id with
      | some n => exact ⟨n, rfl⟩
      | none => exact absurd hm h
    obtain ⟨n, hn⟩ := hm
    have hstep_accounts : (step s e).2.accounts = s.accounts := by simp only [step, hn]
    have hstep_balance : (step s e).2.balance a = s.balance a := by simp only [step, hn]
    rw [hstep_accounts] at ha
    rw [hstep_balance]
    exact hpos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons
  show Consistent (step s e).2
  by_cases h : receiptOf s.log e.id = none
  · by_cases hv : ValidEntry s e
    · have hstep : (step s e).2 = ({ accounts := s.accounts, log := s.log ++ [e], balance := fun a => s.balance a + if a = e.account then e.amount else 0 } : State) := by
        simp only [step, h, hv, ite_true]
      rw [hstep]
      intro a
      have h1 : s.balance a = logSum s.log a := hcons a
      have hsum : logSum (s.log ++ [e]) a = logSum s.log a + if e.account = a then e.amount else 0 := by
        unfold logSum
        rw [sumOver_append]
        have hsingle : sumOver [e] (fun e' => if e'.account = a then e'.amount else 0) = if e.account = a then e.amount else 0 := by
          simp only [sumOver_cons, sumOver_nil]
          omega
        rw [hsingle]
      have hif : (if a = e.account then e.amount else (0 : Int)) = (if e.account = a then e.amount else 0) := by
        by_cases heq : a = e.account
        · rw [if_pos heq, if_pos heq.symm]
        · have heq2 : ¬ e.account = a := fun hh => heq hh.symm
          rw [if_neg heq, if_neg heq2]
      show s.balance a + (if a = e.account then e.amount else (0 : Int)) = logSum (s.log ++ [e]) a
      rw [hsum, h1, hif]
    · have hstep : (step s e).2 = s := by simp only [step, h, hv, ite_false]
      rw [hstep]
      exact hcons
  · have hm : ∃ n, receiptOf s.log e.id = some n := by
      match hm : receiptOf s.log e.id with
      | some n => exact ⟨n, rfl⟩
      | none => exact absurd hm h
    obtain ⟨n, hn⟩ := hm
    have hstep : (step s e).2 = s := by simp only [step, hn]
    rw [hstep]
    exact hcons

end EntryLog
