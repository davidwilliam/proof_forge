import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

/-- Post every line, first to last. -/
def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)

/-- Apply lines with negated amounts (used for reversal). -/
def reverseLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => reverseLines ls (adjust bal l.1 (-l.2))

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | some e =>
      if i ∈ s.reversed then (.rejected, s)
      else (.ok, { s with balance := reverseLines e.lines s.balance,
                          reversed := i :: s.reversed })
    | none => (.rejected, s)

theorem test_sum : (0 : Int) + 0 = 0 := rfl

theorem findEntry_mem (j : List Entry) (i : EntryId) (e : Entry) (h : findEntry j i = some e) : i ∈ j.map (·.id) := by
  induction j with
  | nil => cases h
  | cons e' es ih =>
    simp [findEntry] at h
    by_cases h_eq : e'.id = i
    · simp [h_eq] at h
      subst h
      simp [List.mem_cons, h_eq]
    · simp [h_eq] at h
      have hmem := ih h
      exact List.mem_cons_of_mem _ hmem

theorem netOf_cons (l : Line) (ls : List Line) (a : AccountId) :
    netOf (l :: ls) a = (if l.1 = a then l.2 else 0) + netOf ls a := by
  simp [netOf, sumOver_cons]

theorem sum_nil (l : List AccountId) : sumOver l (fun _ : AccountId => 0) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [sumOver_cons, ih]

def ValidPost_unfold (s : State) (e : Entry) : Prop :=
  e.lines ≠ [] ∧ (∀ l ∈ e.lines, l.1 ∈ s.accounts) ∧ (∀ l ∈ e.lines, l.2 ≠ 0) ∧ lineSum e.lines = 0 ∧ e.id ∉ ids s.journal ∧ e.id ∉ s.reversed

theorem req_post_succeeds : PostSucceeds step := by
  unfold PostSucceeds
  intro s e h
  simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := sorry

theorem req_invalid_noop     : InvalidNoop step := sorry

theorem req_post_effects     : PostEffects step := sorry

theorem req_reverse_effects  : ReverseEffects step := sorry

theorem req_reverse_once     : ReverseOnce step := sorry

theorem req_roundtrip        : RoundTrip step := sorry

theorem req_trial_balance    : TrialBalance step := sorry

theorem req_well_formed      : StaysWellFormed step := sorry

theorem req_consistent       : StaysConsistent step := sorry

end Reversal
