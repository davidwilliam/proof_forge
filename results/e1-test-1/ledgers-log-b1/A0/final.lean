import EntryLog.Spec
import EntryLog.Lemmas
import Init.Data.List.Lemmas

namespace EntryLog

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry
  infer_instance

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none =>
    if ValidEntry s e then
      (.ok s.log.length,
       { s with log := s.log ++ [e],
                balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a })
    else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s e hnew hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  simp [step, hrec, hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s e hnew hnot
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  simp [step, hrec, hnot]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  unfold DuplicateReturnsOriginal
  intro s e n hn
  simp [step, hn]

theorem req_effects : Effects step := by
  unfold Effects
  intro s e hnew hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  have heq : step s e = (.ok s.log.length,
      { s with log := s.log ++ [e],
               balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
    simp [step, hrec, hvalid]
  rw [heq]
  refine ⟨rfl, rfl, fun a => ?_⟩
  by_cases h : a = e.account
  · simp [h]
  · simp [h]

theorem req_append_only : AppendOnly step := by
  unfold AppendOnly
  intro s e
  cases h : receiptOf s.log e.id with
  | some n => exact ⟨[], by simp [step, h]⟩
  | none =>
    by_cases hvalid : ValidEntry s e
    · exact ⟨[e], by simp [step, h, hvalid]⟩
    · exact ⟨[], by simp [step, h, hvalid]⟩

theorem req_unique_ids : UniqueIds step := by
  unfold UniqueIds
  intro s e hnodup
  have aux : ∀ (l : List EntryId) (x : EntryId), List.Nodup l → x ∉ l → List.Nodup (l ++ [x]) := by
    intro l
    induction l with
    | nil =>
      intro x _ _
      show List.Nodup [x]
      exact List.Pairwise.cons (fun y hy => by simp at hy) List.Pairwise.nil
    | cons a t ih =>
      intro x hn hx
      cases hn with
      | cons hhead htail =>
        have hxa : x ≠ a := by
          intro heq
          apply hx
          simp [heq]
        have hxt : x ∉ t := by
          intro hmem
          apply hx
          exact List.mem_cons.mpr (Or.inr hmem)
        have ih' := ih x htail hxt
        have hmem : ∀ y ∈ t ++ [x], a ≠ y := by
          intro y hy
          rw [List.mem_append] at hy
          rcases hy with hyt | hx1
          · exact hhead y hyt
          · have heq : y = x := by simpa using hx1
            rw [heq]
            exact Ne.symm hxa
        show List.Nodup ((a :: t) ++ [x])
        have hrewrite : ((a :: t) ++ [x]) = (a :: (t ++ [x])) := rfl
        rw [hrewrite]
        exact List.Pairwise.cons hmem ih'
  cases h : receiptOf s.log e.id with
  | some n =>
    have heq : (step s e).2.log = s.log := by simp [step, h]
    rw [heq]
    exact hnodup
  | none =>
    by_cases hvalid : ValidEntry s e
    · have heq : (step s e).2.log = s.log ++ [e] := by simp [step, h, hvalid]
      have hnotmem : e.id ∉ ids s.log := by
        intro hmem
        obtain ⟨n', hn'⟩ := receiptOf_isSome hmem
        rw [h] at hn'
        cases hn'
      rw [heq, ids_append]
      have h4 : ids [e] = [e.id] := rfl
      rw [h4]
      exact aux _ _ hnodup hnotmem
    · have heq : (step s e).2.log = s.log := by simp [step, h, hvalid]
      rw [heq]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  unfold NonNegative
  intro s e hnonneg a ha
  cases h : receiptOf s.log e.id with
  | some n =>
    have h2 : (step s e).2 = s := by simp [step, h]
    rw [h2] at ha
    rw [h2]
    exact hnonneg a ha
  | none =>
    by_cases hvalid : ValidEntry s e
    · have heq : step s e = (.ok s.log.length,
        { s with log := s.log ++ [e],
                 balance := fun a => if a = e.account then s.balance a + e.amount else s.balance a }) := by
        simp [step, h, hvalid]
      have hacc : (step s e).2.accounts = s.accounts := by rw [heq]
      have hbal : ∀ b, (step s e).2.balance b = s.balance b + (if b = e.account then e.amount else 0) := by
        intro b
        rw [heq]
        by_cases hb : b = e.account
        · simp [hb]
        · simp [hb]
      unfold ValidEntry at hvalid
      obtain ⟨_, _, hle⟩ := hvalid
      rw [hacc] at ha
      rw [hbal a]
      by_cases hb : a = e.account
      · subst hb
        simpa using hle
      · have hnn := hnonneg a ha
        simp [hb]; omega
    · have h2 : (step s e).2 = s := by simp [step, h, hvalid]
      rw [h2] at ha
      rw [h2]
      exact hnonneg a ha

theorem req_consistent : StaysConsistent step := by
  unfold StaysConsistent
  intro s e hcons
  unfold Consistent at hcons ⊢
  intro a
  cases h : receiptOf s.log e.id with
  | some n =>
    have h2 : (step s e).2 = s := by simp [step, h]
    rw [h2]
    exact hcons a
  | none =>
    by_cases hvalid : ValidEntry s e
    · have heqlog : (step s e).2.log = s.log ++ [e] := by simp [step, h, hvalid]
      have heqbal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by
        have heq : step s e = (.ok s.log.length,
            { s with log := s.log ++ [e],
                     balance := fun b => if b = e.account then s.balance b + e.amount else s.balance b }) := by
          simp [step, h, hvalid]
        rw [heq]
        by_cases hb : a = e.account
        · simp [hb]
        · simp [hb]
      rw [heqbal, heqlog]
      have hcons_a : s.balance a = logSum s.log a := hcons a
      have hsum : logSum (s.log ++ [e]) a = logSum s.log a + (if e.account = a then e.amount else 0) := by
        unfold logSum
        rw [sumOver_append]
        have hsingle : sumOver [e] (fun e' : Entry => if e'.account = a then e'.amount else 0)
            = (if e.account = a then e.amount else 0) := by
          show ((if e.account = a then e.amount else 0) + sumOver [] _) = _
          simp only [sumOver_nil]
          omega
        rw [hsingle]
      have hif : (if a = e.account then e.amount else (0 : Int)) = (if e.account = a then e.amount else 0) := by
        by_cases hb : a = e.account
        · subst hb
          rfl
        · have hb2 : e.account ≠ a := fun heq => hb heq.symm
          simp [hb, hb2]
      rw [hsum, ← hcons_a, hif]
    · have h2 : (step s e).2 = s := by simp [step, h, hvalid]
      rw [h2]
      exact hcons a

end EntryLog
