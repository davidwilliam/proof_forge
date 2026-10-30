import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

def step : Impl :=
  fun s c =>
    match c with
    | .post e =>
      if ValidPost s e then
        (.ok, { s with
          balance := fun a => s.balance a + netOf e.lines a,
          journal := s.journal ++ [e] })
      else (.rejected, s)
    | .reverse i =>
      if ValidReverse s i then
        match findEntry s.journal i with
        | some e =>
          (.ok, { s with
            balance := fun a => s.balance a - netOf e.lines a,
            reversed := i :: s.reversed })
        | none => (.rejected, s)
      else (.rejected, s)

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h; simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  simp [step, h.1]
  have : i ∈ ids s.journal := h.1
  induction s.journal with
  | nil => simp [ids] at this
  | cons e' es ih =>
    simp [ids, findEntry]
    by_cases h' : e'.id = i
    · simp [h']
    · have : i ∈ ids es := by
        rw [List.mem_cons] at this
        cases this with
        | inl h0 => rw [← h0] at h'; simp [h'] at h'
        | inr h0 => exact h0
      exact ih this

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c with
  | post e =>
    simp [step, Valid] at *
    split_ifs with hv
    · exact absurd hv h
    · rfl
  | reverse i =>
    simp [step, Valid] at *
    split_ifs with hv
    · exact absurd hv h
    · rfl

theorem req_post_effects : PostEffects step := by
  intro s e hok
  simp [step] at hok
  by_cases hv : ValidPost s e
  · simp [hv] at hok; subst hok
    exact ⟨rfl, rfl, rfl, rfl, fun a => rfl⟩
  · simp [hv] at hok

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hfind
  simp [step] at hok
  by_cases hv : ValidReverse s i
  · simp [hv, hfind] at hok; subst hok
    refine ⟨rfl, rfl, rfl, ?_, fun a => rfl⟩
    intro x
    simp [List.mem_cons]
    constructor
    · intro hx; cases hx with | inl h => left; rfl | inr h => right; exact h
    · intro hx; cases hx with | inl h => subst h; left; rfl | inr h => right; exact h
  · simp [hv] at hok

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  simp [step] at hok
  by_cases hv : ValidReverse s i
  · have : i ∈ ids s.journal := hv.1
    induction s.journal with
    | nil => simp [ids] at this
    | cons e' es ih =>
      simp [ids, findEntry] at hok ⊢
      by_cases h' : e'.id = i
      · simp [h'] at hok; subst hok
        have : i ∈ ({ s with balance := fun a => s.balance a - netOf e'.lines a,
                      reversed := i :: s.reversed }).reversed := by simp
        simp [step, ValidReverse, this]
      · have : i ∈ ids es := by
          rw [List.mem_cons] at this
          cases this with
          | inl h0 => have : e'.id = i := by rw [← h0]; exact h'
          | inr h0 => exact h0
        have ⟨e, he⟩ := ih this
        simp [h'] at hok; subst hok
        have : i ∈ ({ s with balance := fun a => s.balance a - netOf e.lines a,
                      reversed := i :: s.reversed }).reversed := by simp
        simp [step, ValidReverse, this]
  · simp [hv] at hok

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  simp [step] at hok
  by_cases hv : ValidPost s e
  · simp [hv] at hok
    let s' : State := { s with balance := fun a => s.balance a + netOf e.lines a,
                         journal := s.journal ++ [e] }
    have hrev : ValidReverse s' e.id := by
      constructor
      · simp [ids, List.map_append]; right; rfl
      · intro h; rcases hv with ⟨_,_,_,_,h5,_⟩; exact h5 h
    have hfind : findEntry s'.journal e.id = some e := by
      simp [s', findEntry]; simp [List.mem_append]; right; rfl
    simp [step, hrev, hfind]
    exact ⟨rfl, fun a => by simp [s']⟩
  · simp [hv] at hok

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  rcases hwf with ⟨hn,_,_,hent⟩
  cases c with
  | post e =>
    simp [step] at hok
    by_cases hv : ValidPost s e
    · simp [hv] at hok
      rcases hv with ⟨_,hacc,_,hls,_,_⟩
      have hnet : sumOver s.accounts (netOf e.lines) = lineSum e.lines := by
        simp [netOf]; apply sumOver_congr; intro l hl; have hin := hacc l hl
        rw [sumOver_ite_eq hn l.1 l.2]; simp [hin]
      simp [total, sumOver_add, hnet, hls]
    · simp [hv] at hok
  | reverse i =>
    simp [step] at hok
    by_cases hv : ValidReverse s i
    · have : i ∈ ids s.journal := hv.1
      induction s.journal with
      | nil => simp [ids] at this
      | cons e' es ih =>
        simp [ids, findEntry] at hok ⊢
        by_cases h' : e'.id = i
        · simp [h'] at hok; subst hok
          have hmem : e' ∈ s.journal := List.mem_cons_self _
          have hacc := (hent e' hmem).1
          have hls  := (hent e' hmem).2
          have hnet : sumOver s.accounts (netOf e'.lines) = lineSum e'.lines := by
            simp [netOf]; apply sumOver_congr; intro l hl; have hin := hacc l hl
            rw [sumOver_ite_eq hn l.1 l.2]; simp [hin]
          simp [total, sumOver_sub, hnet, hls]
        · have : i ∈ ids es := by
            rw [List.mem_cons] at this
            cases this with
            | inl h0 => have : e'.id = i := by rw [← h0]; exact h'
            | inr h0 => exact h0
          have ⟨e, he⟩ := ih this
          simp [h'] at hok; subst hok
          have hmem : e ∈ s.journal := by
            induction s.journal with
            | nil => cases he
            | cons e'' es' ih2 =>
              simp [findEntry] at he
              split_ifs at he with h
              · subst h; exact List.mem_cons_self _
              · exact List.mem_cons_of_mem _ (ih2 he)
          have hacc := (hent e hmem).1
          have hls  := (hent e hmem).2
          have hnet : sumOver s.accounts (netOf e.lines) = lineSum e.lines := by
            simp [netOf]; apply sumOver_congr; intro l hl; have hin := hacc l hl
            rw [sumOver_ite_eq hn l.1 l.2]; simp [hin]
          simp [total, sumOver_sub, hnet, hls]
    · simp [hv] at hok

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  rcases hwf with ⟨hn,hid,hrev,hent⟩
  cases c with
  | post e =>
    simp [step]
    split_ifs with hv
    · rcases hv with ⟨_,hacc,_,hls,h5,_⟩
      refine ⟨hn,?_,hrev,?⟩
      · simp [ids, List.map_append]; apply List.Nodup_append_of_increasing hid; intro y hy; exact h5 hy
      · intro e' he'; rcases List.mem_append.mp he' with h1 | h2 <;> [exact hent e' h1; subst h2; exact ⟨fun l hl => hacc l hl, hls⟩]
    · simp [WellFormed, hn, hid, hrev, hent]
  | reverse i =>
    simp [step]
    split_ifs with hv
    · have : i ∈ ids s.journal := hv.1
      induction s.journal with
      | nil => simp [ids] at this
      | cons e' es ih =>
        simp [ids, findEntry]
        by_cases h' : e'.id = i
        · simp [h']
          refine ⟨hn,hid,?_,fun e' he' => hent e' he'⟩
          intro j hj; simp [List.mem_cons] at hj; rcases hj with rfl | hj <;> [exact hv.1; exact hrev j hj]
        · have : i ∈ ids es := by
            rw [List.mem_cons] at this
            cases this with
            | inl h0 => have : e'.id = i := by rw [← h0]; exact h'
            | inr h0 => exact h0
          have ⟨e, he⟩ := ih this
          simp [h']
          refine ⟨hn,hid,?_,fun e' he' => hent e' he'⟩
          intro j hj; simp [List.mem_cons] at hj; rcases hj with rfl | hj <;> [exact hv.1; exact hrev j hj]
    · simp [WellFormed, hn, hid, hrev, hent]

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  cases c with
  | post e =>
    simp [step]
    split_ifs with hv
    · intro a
      have ha := hcons a
      rcases hv with ⟨_,_,_,_,h5,_⟩
      have h1 : netOf e.lines a = sumOver [e] (fun e' => if e'.id ∈ s.reversed then 0 else netOf e'.lines a) := by
        simp [List.singleton, h5]
      simp [activeNet, sumOver_append, sumOver_add] at ha ⊢
      rw [ha, h1]; simp [activeNet, sumOver_append, sumOver_add]
    · intro a; exact hcons a
  | reverse i =>
    simp [step]
    split_ifs with hv
    · have : i ∈ ids s.journal := hv.1
      induction s.journal with
      | nil => simp [ids] at this
      | cons e' es ih =>
        simp [ids, findEntry]
        by_cases h' : e'.id = i
        · simp [h']
          intro a
          have ha := hcons a
          have hrev : i ∉ s.reversed := hv.2
          have hsum : sumOver s.journal (fun e' => if e'.id ∈ i :: s.reversed then 0 else netOf e'.lines a) =
              sumOver s.journal (fun e' => if e'.id ∈ s.reversed then 0 else netOf e'.lines a) - netOf e'.lines a := by
            apply sumOver_congr; intro e'' he''; by_cases heq : e''.id = i <;> [subst heq; simp [hrev]; simp [heq, hrev]]
          simp [activeNet]
          rw [ha, hsum]; ring
        · have : i ∈ ids es := by
            rw [List.mem_cons] at this
            cases this with
            | inl h0 => have : e'.id = i := by rw [← h0]; exact h'
            | inr h0 => exact h0
          have ⟨e, he⟩ := ih this
          simp [h']
          intro a
          have ha := hcons a
          have hrev : i ∉ s.reversed := hv.2
          have hsum : sumOver s.journal (fun e' => if e'.id ∈ i :: s.reversed then 0 else netOf e'.lines a) =
              sumOver s.journal (fun e' => if e'.id ∈ s.reversed then 0 else netOf e'.lines a) - netOf e.lines a := by
            apply sumOver_congr; intro e'' he''; by_cases heq : e''.id = i <;> [subst heq; simp [hrev]; simp [heq, hrev]]
          simp [activeNet]
          rw [ha, hsum]; ring
    · intro a; exact hcons a

end Reversal
