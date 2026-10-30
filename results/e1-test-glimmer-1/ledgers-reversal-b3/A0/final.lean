import Reversal.Spec
import Reversal.Lemmas

namespace Reversal

instance decValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) :=
  by unfold ValidPost; infer_instance

instance decValidReverse (s : State) (i : EntryId) : Decidable (ValidReverse s i) :=
  by unfold ValidReverse; infer_instance

def step : Impl
  | s, Command.post e =>
      if ValidPost s e then
        (Outcome.ok, { s with
          balance := fun a => s.balance a + netOf e.lines a,
          journal := s.journal ++ [e] })
      else (Outcome.rejected, s)
  | s, Command.reverse i =>
      if ValidReverse s i then
        let e := (findEntry s.journal i).get!
        (Outcome.ok, { s with
          balance := fun a => s.balance a - netOf e.lines a,
          reversed := s.reversed ++ [i] })
      else (Outcome.rejected, s)

private lemma findEntry_some_of_ids (j : List Entry) (i : EntryId)
    (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons e es ih =>
    simp [ids] at h
    rcases List.mem_cons.mp h with r | r
    · exact ⟨e, by simp [findEntry, r]⟩
    · rcases ih r with ⟨e', he'⟩
      exact ⟨e', by
        simp [findEntry]
        by_cases h0 : e.id = i
        · subst h0; simp
        · simp [h0, he']⟩

private lemma sumNet_eq_lineSum {acc : List AccountId} {ls : List Line}
    (hNodup : acc.Nodup) (hacc : ∀ l ∈ ls, l.1 ∈ acc) :
    sumOver acc (fun a => netOf ls a) = lineSum ls := by
  induction ls generalizing acc with
  | nil => simp [netOf, lineSum]
  | cons l0 ls ih =>
    have h0 : l0.1 ∈ acc := hacc l0 (by simp)
    have hacc' : ∀ l ∈ ls, l.1 ∈ acc := fun l hl => hacc l (by simp [List.mem_cons] at hl ⊢; exact hl)
    simp [netOf, lineSum, sumOver_add]
    rw [sumOver_ite_eq hNodup l0.1 l0.2, ih hNodup hacc']
    simp [h0]

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h; simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h; simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e => simp [step]; by_cases hv : ValidPost s e <;> simp [hv, hv at h]
  | reverse i => simp [step]; by_cases hv : ValidReverse s i <;> simp [hv, hv at h]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  simp [step] at hok
  by_cases hv : ValidPost s e
  · simp [hv] at hok; simp [hv]
  · simp [hv] at hok

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hfind
  simp [step] at hok
  have hv : ValidReverse s i := by
    constructor
    · have : i ∈ ids s.journal := by
        induction s.journal with
        | nil => simp [findEntry] at hfind
        | cons e' es ih =>
          simp [findEntry] at hfind
          by_cases h0 : e'.id = i
          · subst h0; simp [ids, List.mem_cons]
          · simp [h0] at hfind; exact List.mem_cons_of_mem _ (ih hfind)
    · by_contra h; simp [h] at hok
  simp [hv] at hok
  have hget : (findEntry s.journal i).get! = e := by
    cases findEntry s.journal i with
    | some e' => simp [hfind] at *; subst hfind; rfl
    | none => simp [hfind]
  simp [hget]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro x; simp [List.mem_append]
  · rfl

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  simp [step] at hok
  by_cases hv : ValidReverse s i
  · simp [hv] at hok
    simp [step]
    have : i ∈ s.reversed ++ [i] := List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    simp [ValidReverse, this, hv.1]
  · simp [hv] at hok

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  simp [step] at hok
  by_cases hv : ValidPost s e
  · simp [hv] at hok
    have hv' : ValidReverse { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } e.id := by
      constructor
      · simp [ids, List.mem_append, hv.2.2.1, List.mem_cons]
      · exact hv.2.2.2.2
    simp [step, hv']
    have hfind : findEntry (s.journal ++ [e]) e.id = some e := by
      induction s.journal with
      | nil => rfl
      | cons e' es ih =>
        simp [findEntry]
        by_cases h0 : e'.id = e.id
        · exfalso; have : e.id ∈ ids s.journal := by simp [ids, List.mem_cons, h0]; exact hv.2.2.2.1 this
        · simp [h0, ih]
    simp [hfind]
    constructor; rfl; funext a; rfl
  · simp [hv] at hok

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  cases c with
  | post e =>
    simp [step] at hok
    by_cases hv : ValidPost s e
    · rcases hv with ⟨_, hacc, _, hls, _, _⟩
      have hsum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
        sumNet_eq_lineSum hwf.1 hacc
      simp [total, sumOver_add, hsum, hls]
    · simp [hv] at hok
  | reverse i =>
    simp [step] at hok
    by_cases hv : ValidReverse s i
    · rcases findEntry_some_of_ids s.journal i hv.1 with ⟨e, he⟩
      have hacc : ∀ l ∈ e.lines, l.1 ∈ s.accounts := (hwf.2.2.2 e (by
        induction s.journal with
        | nil => simp [ids] at hv.1
        | cons e' es ih =>
          simp [findEntry] at he
          by_cases h0 : e'.id = i
          · subst h0; simp
          · simp [h0] at he; exact ih he)).1
      have hls : lineSum e.lines = 0 := (hwf.2.2.2 e (by
        induction s.journal with
        | nil => simp [ids] at hv.1
        | cons e' es ih =>
          simp [findEntry] at he
          by_cases h0 : e'.id = i
          · subst h0; simp
          · simp [h0] at he; exact ih he)).2
      have hsum : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
        rw [sumNet_eq_lineSum hwf.1 hacc, hls]
      simp [total, sumOver_sub, hsum]
    · simp [hv] at hok

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  cases c with
  | post e =>
    simp [step]
    split_ifs with hv
    · rcases hv with ⟨_, hacc, _, hls, hnid, hrev⟩
      constructor
      · exact hwf.1
      · constructor
        · simp [ids, List.nodup_append, hwf.2.1]
          intro h; rw [List.mem_append] at h; rcases h with h | h <;> [exact hwf.2.1.elim h | exact hnid h]
        · constructor
          · intro i hi; simp [List.mem_append] at hi; rcases hi with h | h <;> [exact hwf.2.2.1 i h | exact hacc _ (by simp)]
          · intro e' he'; simp [List.mem_append] at he'; rcases he' with h | h
            · exact hwf.2.2.2 e' h
            · subst h; constructor; intro l hl; exact hacc l hl; exact hls
      · rfl
    · exact hwf
  | reverse i =>
    simp [step]
    split_ifs with hv
    · constructor
      · exact hwf.1
      · constructor
        · exact hwf.2.1
        · constructor
          · intro j hj; exact hwf.2.2.1 j hj
          · intro e' he'; exact hwf.2.2.2 e' he'
    · exact hwf

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  cases c with
  | post e =>
    simp [step]
    split_ifs with hv
    · rcases hv with ⟨_, hacc, _, hls, _, _⟩
      intro a
      rw [hcons a]
      simp [activeNet, sumOver_append, sumOver_add]
      rw [sumNet_eq_lineSum hwf.1 hacc, hls]
    · intro a; simp [hcons a]
  | reverse i =>
    simp [step]
    split_ifs with hv
    · rcases findEntry_some_of_ids s.journal i hv.1 with ⟨e, he⟩
      have hacc : ∀ l ∈ e.lines, l.1 ∈ s.accounts := (hwf.2.2.2 e (by
        induction s.journal with
        | nil => simp [ids] at hv.1
        | cons e' es ih =>
          simp [findEntry] at he
          by_cases h0 : e'.id = i
          · subst h0; simp
          · simp [h0] at he; exact ih he)).1
      have hsum : sumOver s.accounts (fun a' => netOf e.lines a') = 0 := by
        rw [sumNet_eq_lineSum hwf.1 hacc, (hwf.2.2.2 e (by
          induction s.journal with
          | nil => simp [ids] at hv.1
          | cons e' es ih =>
            simp [findEntry] at he
            by_cases h0 : e'.id = i
            · subst h0; simp
            · simp [h0] at he; exact ih he)).2]
      intro a
      rw [hcons a]
      simp [activeNet, hsum]
    · intro a; simp [hcons a]

end Reversal
