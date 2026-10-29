import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

def validBool (s : State) (e : Entry) : Bool :=
  decide (e.account ∈ s.accounts) && decide (e.amount ≠ 0) && decide (0 ≤ s.balance e.account + e.amount)

def step : Impl := fun s e =>
  match h : receiptOf s.log e.id with
  | some n => (Outcome.ok n, s)
  | none =>
    if validBool s e then
      (Outcome.ok s.log.length,
        { accounts := s.accounts
          log := s.log ++ [e]
          balance := fun a => s.balance a + (if a = e.account then e.amount else 0) })
    else (Outcome.rejected, s)

theorem req_effects_test : Effects step := by
  unfold Effects
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  obtain ⟨hmem, hne, hle⟩ := hvalid
  have hvb : validBool s e = true := by
    unfold validBool
    simp [hmem, hne, hle]
  refine ⟨?_, ?_, ?_⟩
  · show (step s e).2.accounts = _
    unfold step
    rw [hrec]
    simp [hvb]
  · show (step s e).2.log = _
    unfold step
    rw [hrec]
    simp [hvb]
  · intro a
    show (step s e).2.balance _ = _
    unfold step
    rw [hrec]
    simp [hvb]

theorem req_append_only_aux : AppendOnly step := by
  unfold AppendOnly
  intro s e
  unfold step
  split
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨[_], rfl⟩
    · exact ⟨[], by simp⟩

theorem mem_of_receipt_some {log : List Entry} {i : EntryId} {n : Nat}
    (h : receiptOf log i = some n) : i ∈ ids log := by
  induction log generalizing n with
  | nil => simp [receiptOf] at h
  | cons e es ih =>
    have hmap : ids (e :: es) = e.id :: ids es := rfl
    simp only [receiptOf] at h
    by_cases he : e.id = i
    · rw [hmap, List.mem_cons]
      exact Or.inl he.symm
    · simp [he] at h
      cases hm : receiptOf es i with
      | none => simp [hm] at h
      | some m =>
        simp [hm] at h
        have ihm := ih hm
        rw [hmap, List.mem_cons]
        exact Or.inr ihm

theorem not_mem_of_receipt_none {log : List Entry} {i : EntryId}
    (h : receiptOf log i = none) : i ∉ ids log := by
  intro hmem
  obtain ⟨n, hn⟩ := receiptOf_isSome hmem
  rw [hn] at h
  contradiction

theorem nodup_probe (a : Nat) (l : List Nat) : (a :: l).Nodup → a ∉ l := by
  intro h
  exact (List.nodup_cons.mp h).1

theorem req_nonnegative_aux_test : True := trivial

theorem step_some_eq (s : State) (e : Entry) (n : Nat) (hrec : receiptOf s.log e.id = some n) :
    step s e = (Outcome.ok n, s) := by
  unfold step
  rw [hrec]

theorem logSum_append_single3 (l : List Entry) (e : Entry) (a : AccountId) :
    logSum (l ++ [e]) a = logSum l a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  simp

theorem nodup_append_singleton_aux (l : List Nat) (a : Nat) (h1 : l.Nodup) (h2 : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx_not : x ∉ xs := (List.nodup_cons.mp h1).1
    have hx_nodup : xs.Nodup := (List.nodup_cons.mp h1).2
    have ha_xs : a ∉ xs := fun hm => h2 (List.mem_cons_of_mem x hm)
    have ha_ne : a ≠ x := fun heq => h2 (by simp [heq])
    have ih' := ih hx_nodup ha_xs
    have hx_not' : x ∉ xs ++ [a] := by simp [hx_not, Ne.symm ha_ne]
    exact List.nodup_cons.mpr ⟨hx_not', ih'⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  unfold ValidEntry at hvalid
  obtain ⟨hmem, hne, hle⟩ := hvalid
  have hvb : validBool s e = true := by
    unfold validBool
    simp [hmem, hne, hle]
  show (step s e).1 = _
  unfold step
  rw [hrec]
  simp [hvb]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s e hnotin hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have hvb : validBool s e = false := by
    unfold validBool
    by_cases h1 : e.account ∈ s.accounts
    · by_cases h2 : e.amount ≠ 0
      · by_cases h3 : 0 ≤ s.balance e.account + e.amount
        · exfalso; exact hinvalid ⟨h1, h2, h3⟩
        · simp [h1, h2, h3]
      · simp [h1, h2]
    · simp [h1]
  show step s e = _
  unfold step
  rw [hrec]
  simp [hvb]

theorem req_duplicate : DuplicateReturnsOriginal step := by
  unfold DuplicateReturnsOriginal
  intro s e n hn
  show step s e = _
  unfold step
  rw [hn]

theorem req_effects : Effects step := by
  unfold Effects
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  obtain ⟨hmem, hne, hle⟩ := hvalid
  have hvb : validBool s e = true := by
    unfold validBool
    simp [hmem, hne, hle]
  refine ⟨?_, ?_, ?_⟩
  · show (step s e).2.accounts = _
    unfold step
    rw [hrec]
    simp [hvb]
  · show (step s e).2.log = _
    unfold step
    rw [hrec]
    simp [hvb]
  · intro a
    show (step s e).2.balance _ = _
    unfold step
    rw [hrec]
    simp [hvb]

theorem req_append_only : AppendOnly step := by
  unfold AppendOnly
  intro s e
  unfold step
  split
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨[_], rfl⟩
    · exact ⟨[], by simp⟩

theorem req_unique_ids : UniqueIds step := by
  unfold UniqueIds
  intro s e hnodup
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (Outcome.ok n, s) := req_duplicate s e n hn
    have hlog : (step s e).2.log = s.log := by rw [hstep]
    rw [hlog]
    exact hnodup
  · by_cases hvalid : ValidEntry s e
    · obtain ⟨hacc, hlog, hbal⟩ := req_effects s e hmem hvalid
      rw [hlog]
      have hids : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
      rw [hids]
      exact nodup_append_singleton_aux (ids s.log) e.id hnodup hmem
    · have hstep : step s e = (Outcome.rejected, s) := req_invalid_noop s e hmem hvalid
      have hlog : (step s e).2.log = s.log := by rw [hstep]
      rw [hlog]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  unfold NonNegative
  intro s e hnn a ha
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (Outcome.ok n, s) := req_duplicate s e n hn
    have h2 : (step s e).2 = s := by rw [hstep]
    have ha' : a ∈ s.accounts := by
      have hmem2 : a ∈ (step s e).2.accounts := ha
      rw [h2] at hmem2
      exact hmem2
    have hbal : (step s e).2.balance a = s.balance a := by rw [h2]
    rw [hbal]
    exact hnn a ha'
  · by_cases hvalid : ValidEntry s e
    · obtain ⟨hacc, hlog, hbal⟩ := req_effects s e hmem hvalid
      have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
      have hgoal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := hbal a
      rw [hgoal]
      by_cases heq : a = e.account
      · subst heq
        obtain ⟨_, _, hle⟩ := hvalid
        simpa using hle
      · simp [heq]
        exact hnn a ha'
    · have hstep : step s e = (Outcome.rejected, s) := req_invalid_noop s e hmem hvalid
      have h2 : (step s e).2 = s := by rw [hstep]
      have ha' : a ∈ s.accounts := by
        have hmem2 : a ∈ (step s e).2.accounts := ha
        rw [h2] at hmem2
        exact hmem2
      have hbal : (step s e).2.balance a = s.balance a := by rw [h2]
      rw [hbal]
      exact hnn a ha'

theorem req_consistent : StaysConsistent step := by
  unfold StaysConsistent Consistent
  intro s e hcons a
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (Outcome.ok n, s) := req_duplicate s e n hn
    have h2 : (step s e).2 = s := by rw [hstep]
    rw [h2]
    exact hcons a
  · by_cases hvalid : ValidEntry s e
    · obtain ⟨hacc, hlog, hbal⟩ := req_effects s e hmem hvalid
      have h1 : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := hbal a
      have h2 : (step s e).2.log = s.log ++ [e] := hlog
      rw [h1, h2, hcons a]
      have h3 := logSum_append_single3 s.log e a
      have hif : (if a = e.account then e.amount else (0 : Int)) = (if e.account = a then e.amount else 0) := by
        by_cases h : a = e.account
        · subst h; rfl
        · have hne : ¬ (e.account = a) := fun hh => h hh.symm
          simp [h, hne]
      rw [hif]
      exact h3.symm
    · have hstep : step s e = (Outcome.rejected, s) := req_invalid_noop s e hmem hvalid
      have h2 : (step s e).2 = s := by rw [hstep]
      rw [h2]
      exact hcons a

end EntryLog
