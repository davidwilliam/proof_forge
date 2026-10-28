import EntryLog.Spec
import EntryLog.Lemmas
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

theorem logSum_append_single2 (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  simp [sumOver]

theorem req_consistent_arith2 (s : State) (e : Entry) (a : AccountId)
    (hb : s.balance a = logSum s.log a) :
    (if a = e.account then s.balance a + e.amount else s.balance a)
      = logSum (s.log ++ [e]) a := by
  have h1 : logSum (s.log ++ [e]) a = logSum s.log a + (if e.account = a then e.amount else 0) :=
    logSum_append_single2 s.log e a
  rw [h1]
  rw [← hb]
  by_cases heq : a = e.account
  · have heq2 : e.account = a := Eq.symm heq
    rw [if_pos heq, if_pos heq2]
  · have heq2 : ¬ e.account = a := fun h => heq (Eq.symm h)
    rw [if_neg heq, if_neg heq2]
    omega

theorem req_consistent_final_probe (s : State) (e : Entry) (a : AccountId) (hcons : Consistent s) :
    ((step s e).2.balance a = logSum (step s e).2.log a) := by
  have hb : s.balance a = logSum s.log a := hcons a
  unfold step
  cases hrec : receiptOf s.log e.id with
  | some n =>
    simp only at *
    exact hb
  | none =>
    simp only at *
    by_cases hvalid : ValidEntry s e
    · simp only [hvalid, ↓reduceIte] at *
      exact req_consistent_arith2 s e a hb
    · simp only [hvalid, ↓reduceIte] at *
      exact hb

theorem nodup_append_singleton (l : List Nat) (x : Nat) (hnd : l.Nodup) (hmem : x ∉ l) :
    (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    match hnd with
    | List.Pairwise.cons h1 h2 =>
      have hx_ne_y : x ≠ y := by
        intro heq
        apply hmem
        rw [heq]
        simp
      have hx_not : x ∉ ys := by
        intro hmem2
        apply hmem
        simp [hmem2]
      have ih' : (ys ++ [x]).Nodup := ih h2 hx_not
      have hy_not : y ∉ ys ++ [x] := by
        intro hc
        rw [List.mem_append] at hc
        rcases hc with h | h
        · exact (h1 y h) rfl
        · simp at h
          exact hx_ne_y h.symm
      have hy_forall : ∀ a' ∈ ys ++ [x], y ≠ a' := by
        intro a' ha' heq2
        have hmem_y : y ∈ ys ++ [x] := by rw [heq2]; exact ha'
        exact hy_not hmem_y
      exact List.Pairwise.cons hy_forall ih'

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnew hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  unfold step
  simp [hrec, hvalid]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hnew hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  unfold step
  simp [hrec, hinvalid]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  intro s e n h
  unfold step
  simp [h]

theorem req_effects : Effects step := by
  intro s e hnew hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnew
  unfold step
  simp only [hrec, hvalid, ↓reduceIte]
  refine ⟨trivial, trivial, fun a => ?_⟩
  by_cases h : a = e.account <;> simp [h]

theorem req_append_only : AppendOnly step := by
  intro s e
  unfold step
  cases hrec : receiptOf s.log e.id with
  | some n =>
    simp only
    exact ⟨[], by simp⟩
  | none =>
    simp only
    by_cases hvalid : ValidEntry s e
    · simp only [hvalid, ↓reduceIte]
      exact ⟨[e], rfl⟩
    · simp only [hvalid, ↓reduceIte]
      exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  intro s e hnd
  unfold step
  cases hrec : receiptOf s.log e.id with
  | some n =>
    simp only
    exact hnd
  | none =>
    have hnew : e.id ∉ ids s.log := by
      intro hmem
      obtain ⟨n, hn⟩ := receiptOf_isSome hmem
      rw [hrec] at hn
      cases hn
    by_cases hvalid : ValidEntry s e
    · simp only [hvalid, ↓reduceIte]
      rw [ids_append]
      exact nodup_append_singleton (ids s.log) e.id hnd hnew
    · simp only [hvalid, ↓reduceIte]
      exact hnd

theorem req_nonnegative : NonNegative step := by
  intro s e hpos a ha
  unfold step at ha ⊢
  cases hrec : receiptOf s.log e.id with
  | some n =>
    simp [hrec] at ha ⊢
    exact hpos a ha
  | none =>
    simp [hrec] at ha ⊢
    by_cases hvalid : ValidEntry s e
    · simp [hvalid] at ha ⊢
      unfold ValidEntry at hvalid
      obtain ⟨hmem, _, hbal⟩ := hvalid
      by_cases heq : a = e.account
      · simp [heq]
        exact hbal
      · simp [heq]
        exact hpos a ha
    · simp [hvalid] at ha ⊢
      exact hpos a ha

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  exact req_consistent_final_probe s e a hcons

end EntryLog
