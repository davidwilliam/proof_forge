import EntryLog.Spec
import EntryLog.Lemmas

namespace EntryLog

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (Outcome.ok n, s)
  | none =>
    if _h1 : e.account ∈ s.accounts then
      if _h2 : e.amount ≠ 0 then
        if _h3 : (0 : Int) ≤ s.balance e.account + e.amount then
          (Outcome.ok s.log.length,
            { accounts := s.accounts,
              log := s.log ++ [e],
              balance := fun a => s.balance a + (if a = e.account then e.amount else 0) })
        else (Outcome.rejected, s)
      else (Outcome.rejected, s)
    else (Outcome.rejected, s)

theorem req_append_only_aux_test : AppendOnly step := by
  intro s e
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    exact ⟨[], by simp [step, hn]⟩
  · have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases h1 : e.account ∈ s.accounts
    · by_cases h2 : e.amount ≠ 0
      · by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
        · exact ⟨[e], by simp [step, hrec, h1, h2, h3]⟩
        · exact ⟨[], by simp [step, hrec, h1, h2, h3]⟩
      · exact ⟨[], by simp [step, hrec, h1, h2]⟩
    · exact ⟨[], by simp [step, hrec, h1]⟩

theorem probe_nonneg_accounts (s : State) (e : Entry)
  (hrec : receiptOf s.log e.id = none)
  (h1 : e.account ∈ s.accounts) (h2 : e.amount ≠ 0)
  (h3 : (0:Int) ≤ s.balance e.account + e.amount) :
  (step s e).2.accounts = s.accounts := by
  simp [step, hrec, h1, h2, h3]

theorem probe_nonneg_balance (s : State) (e : Entry)
  (hrec : receiptOf s.log e.id = none)
  (h1 : e.account ∈ s.accounts) (h2 : e.amount ≠ 0)
  (h3 : (0:Int) ≤ s.balance e.account + e.amount) (b : AccountId) :
  (step s e).2.balance b = s.balance b + (if b = e.account then e.amount else 0) := by
  simp [step, hrec, h1, h2, h3]

theorem logSum_append_single (log : List Entry) (e : Entry) (a : AccountId) :
    logSum (log ++ [e]) a = logSum log a + (if e.account = a then e.amount else 0) := by
  unfold logSum
  rw [sumOver_append]
  have h1 : sumOver ([e] : List Entry) (fun e' => if e'.account = a then e'.amount else 0)
      = (if e.account = a then e.amount else 0) := by
    have : sumOver ([e] : List Entry) (fun e' => if e'.account = a then e'.amount else 0)
      = (if e.account = a then e.amount else 0) + sumOver ([] : List Entry) (fun e' => if e'.account = a then e'.amount else 0) := rfl
    rw [this, sumOver_nil, Int.add_zero]
  rw [h1]

theorem nodup_append_singleton (l : List EntryId) (x : EntryId)
    (h : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil =>
    exact (List.Pairwise.cons (by simp) List.Pairwise.nil : List.Nodup [x])
  | cons hd tl ih =>
    cases h with
    | cons hforall htail =>
      have hx_tl : x ∉ tl := by
        intro hm
        apply hx
        simp [hm]
      have hx_ne : x ≠ hd := by
        intro heq
        apply hx
        simp [heq]
      have ih' : (tl ++ [x]).Nodup := ih htail hx_tl
      have hmem : hd ∉ tl ++ [x] := by
        intro hm
        simp at hm
        rcases hm with hm | hm
        · exact (hforall _ hm) rfl
        · apply hx
          simp [hm]
      have hmem' : ∀ a' ∈ tl ++ [x], hd ≠ a' := by
        intro a' ha heq
        subst heq
        exact hmem ha
      have heq : (hd :: tl) ++ [x] = hd :: (tl ++ [x]) := rfl
      rw [heq]
      exact List.Pairwise.cons hmem' ih'

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have h1 : e.account ∈ s.accounts := hvalid.1
  have h2 : e.amount ≠ 0 := hvalid.2.1
  have h3 : (0 : Int) ≤ s.balance e.account + e.amount := hvalid.2.2
  simp [step, hrec, h1, h2, h3]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s e hnotin hinvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  by_cases h1 : e.account ∈ s.accounts
  · by_cases h2 : e.amount ≠ 0
    · by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
      · exfalso; apply hinvalid; exact ⟨h1, h2, h3⟩
      · simp [step, hrec, h1, h2, h3]
    · simp [step, hrec, h1, h2]
  · simp [step, hrec, h1]

theorem req_duplicate      : DuplicateReturnsOriginal step := by
  intro s e n h
  simp [step, h]

theorem req_effects : Effects step := by
  intro s e hnotin hvalid
  have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hnotin
  have h1 : e.account ∈ s.accounts := hvalid.1
  have h2 : e.amount ≠ 0 := hvalid.2.1
  have h3 : (0 : Int) ≤ s.balance e.account + e.amount := hvalid.2.2
  simp [step, hrec, h1, h2, h3]

theorem req_append_only    : AppendOnly step := by
  intro s e
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    exact ⟨[], by simp [step, hn]⟩
  · have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases h1 : e.account ∈ s.accounts
    · by_cases h2 : e.amount ≠ 0
      · by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
        · exact ⟨[e], by simp [step, hrec, h1, h2, h3]⟩
        · exact ⟨[], by simp [step, hrec, h1, h2, h3]⟩
      · exact ⟨[], by simp [step, hrec, h1, h2]⟩
    · exact ⟨[], by simp [step, hrec, h1]⟩

theorem req_unique_ids     : UniqueIds step := by
  intro s e hnodup
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hlog : (step s e).2.log = s.log := by simp [step, hn]
    rw [hlog]
    exact hnodup
  · have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases h1 : e.account ∈ s.accounts
    · by_cases h2 : e.amount ≠ 0
      · by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
        · have hlog : (step s e).2.log = s.log ++ [e] := by simp [step, hrec, h1, h2, h3]
          rw [hlog]
          have hids : ids (s.log ++ [e]) = ids s.log ++ [e.id] := by simp [ids]
          rw [hids]
          exact nodup_append_singleton (ids s.log) e.id hnodup hmem
        · have hlog : (step s e).2.log = s.log := by simp [step, hrec, h1, h2, h3]
          rw [hlog]
          exact hnodup
      · have hlog : (step s e).2.log = s.log := by simp [step, hrec, h1, h2]
        rw [hlog]
        exact hnodup
    · have hlog : (step s e).2.log = s.log := by simp [step, hrec, h1]
      rw [hlog]
      exact hnodup

theorem req_nonnegative : NonNegative step := by
  intro s e hnn a ha
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : step s e = (Outcome.ok n, s) := by simp [step, hn]
    have ha' : a ∈ s.accounts := by
      have h2 : (step s e).2 = s := by rw [hstep]
      rw [h2] at ha
      exact ha
    have hgoal : (step s e).2.balance a = s.balance a := by
      have h2 : (step s e).2 = s := by rw [hstep]
      rw [h2]
    rw [hgoal]
    exact hnn a ha'
  · have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases h1 : e.account ∈ s.accounts
    · by_cases h2 : e.amount ≠ 0
      · by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
        · have hacc := probe_nonneg_accounts s e hrec h1 h2 h3
          have hbal := probe_nonneg_balance s e hrec h1 h2 h3 a
          have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
          rw [hbal]
          by_cases heq : a = e.account
          · subst heq
            simp only [↓reduceIte]
            exact h3
          · simp only [heq, ↓reduceIte, Int.add_zero]
            exact hnn a ha'
        · have hstep : step s e = (Outcome.rejected, s) := by simp [step, hrec, h1, h2, h3]
          have ha' : a ∈ s.accounts := by
            have h2 : (step s e).2 = s := by rw [hstep]
            rw [h2] at ha
            exact ha
          have hgoal : (step s e).2.balance a = s.balance a := by
            have h2 : (step s e).2 = s := by rw [hstep]
            rw [h2]
          rw [hgoal]
          exact hnn a ha'
      · have hstep : step s e = (Outcome.rejected, s) := by simp [step, hrec, h1, h2]
        have ha' : a ∈ s.accounts := by
          have h2 : (step s e).2 = s := by rw [hstep]
          rw [h2] at ha
          exact ha
        have hgoal : (step s e).2.balance a = s.balance a := by
          have h2 : (step s e).2 = s := by rw [hstep]
          rw [h2]
        rw [hgoal]
        exact hnn a ha'
    · have hstep : step s e = (Outcome.rejected, s) := by simp [step, hrec, h1]
      have ha' : a ∈ s.accounts := by
        have h2 : (step s e).2 = s := by rw [hstep]
        rw [h2] at ha
        exact ha
      have hgoal : (step s e).2.balance a = s.balance a := by
        have h2 : (step s e).2 = s := by rw [hstep]
        rw [h2]
      rw [hgoal]
      exact hnn a ha'

theorem req_consistent : StaysConsistent step := by
  intro s e hcons a
  by_cases hmem : e.id ∈ ids s.log
  · obtain ⟨n, hn⟩ := receiptOf_isSome hmem
    have hstep : (step s e).2 = s := by simp [step, hn]
    rw [hstep]
    exact hcons a
  · have hrec : receiptOf s.log e.id = none := receiptOf_eq_none hmem
    by_cases h1 : e.account ∈ s.accounts
    · by_cases h2 : e.amount ≠ 0
      · by_cases h3 : (0 : Int) ≤ s.balance e.account + e.amount
        · have hbal : (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0) := by
            simp [step, hrec, h1, h2, h3]
          have hlog : (step s e).2.log = s.log ++ [e] := by
            simp [step, hrec, h1, h2, h3]
          rw [hbal, hlog, logSum_append_single, ← hcons a]
          by_cases heq : a = e.account
          · subst heq; simp
          · have heq2 : ¬ (e.account = a) := fun h => heq h.symm
            simp [heq, heq2]
        · have hstep : (step s e).2 = s := by simp [step, hrec, h1, h2, h3]
          rw [hstep]
          exact hcons a
      · have hstep : (step s e).2 = s := by simp [step, hrec, h1, h2]
        rw [hstep]
        exact hcons a
    · have hstep : (step s e).2 = s := by simp [step, hrec, h1]
      rw [hstep]
      exact hcons a

end EntryLog
