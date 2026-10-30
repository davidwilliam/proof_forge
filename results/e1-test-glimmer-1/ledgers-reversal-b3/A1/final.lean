import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

/-- Post every line, first to last. -/
def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

instance instDecidableValidReverse (s : State) (i : EntryId) : Decidable (ValidReverse s i) := by
  unfold ValidReverse; infer_instance

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with balance := postLines e.lines s.balance, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    if ValidReverse s i then
      match findEntry s.journal i with
      | some e =>
        let newBal : AccountId → Int := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance
        let newRev := s.reversed ++ [i]
        (.ok, { s with balance := newBal, reversed := newRev })
      | none => (.rejected, s)
    else (.rejected, s)

def foo : Nat := 0

def bar : Nat := 1

theorem test_thm : True := by trivial

theorem findEntry_exists (j i) (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons e es ih =>
    simp [ids] at h
    cases h with
    | inl h =>
      exact ⟨e, by simp [findEntry, h]⟩
    | inr h =>
      rcases h with ⟨a, ha, haid⟩
      have h' : i ∈ ids es := by
        rw [ids]
        exact List.mem_map.mpr ⟨a, ha, haid⟩
      have ⟨e', he'⟩ := ih h'
      by_cases heq : e.id = i
      · exact ⟨e, by simp [findEntry, heq]⟩
      · exact ⟨e', by simp [findEntry, heq, he']⟩

theorem test_simple : 1 = 1 := rfl

theorem sumOver_accounts_adjust' (accounts : List AccountId) (bal : AccountId → Int) (a : AccountId) (amt : Int)
    (hacc : a ∈ accounts) (hnodup : accounts.Nodup) :
    sumOver accounts (fun b => if b = a then bal b + amt else bal b) =
    sumOver accounts bal + amt := by
  have h_congr : ∀ b ∈ accounts, (if b = a then bal b + amt else bal b) = bal b + if b = a then amt else 0 := by
    intro b hb
    by_cases h : b = a
    · simp [h]
    · simp [h]
  rw [sumOver_congr accounts _ _ h_congr]
  rw [sumOver_add]
  have h2 : sumOver accounts (fun b => if b = a then amt else 0) = amt := by
    rw [sumOver_ite_eq hnodup a amt]
    simp [hacc]
  rw [h2]

theorem test_ok : True := by trivial

theorem foo_test : 1 = 1 := rfl

def tmp : Nat := 0

theorem adjust_cancel (bal : AccountId → Int) (a : AccountId) (amt : Int) :
    adjust (adjust bal a amt) a (-amt) = bal := by
  funext b
  by_cases h : b = a
  · subst h
    simp [adjust]
    omega
  · simp [adjust, h]

theorem req_post_succeeds : PostSucceeds step := by
  intro s e hvp
  unfold step
  simp [hvp]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i hvr
  unfold step
  simp [hvr]
  have hmem := hvr.1
  obtain ⟨e, he⟩ := findEntry_exists s.journal i hmem
  simp [he]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c hnv
  unfold step
  cases c with
  | post e =>
    by_cases h : ValidPost s e
    · have : Valid s (Command.post e) := by simp [Valid, h]
      contradiction
    · simp [h]
  | reverse i =>
    by_cases h : ValidReverse s i
    · have : Valid s (Command.reverse i) := by simp [Valid, h]
      contradiction
    · simp [h]

theorem req_post_effects     : PostEffects step := sorry

theorem req_reverse_effects  : ReverseEffects step := sorry

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  have hvr : ValidReverse s i := by
    by_cases hv : ValidReverse s i
    · exact hv
    · unfold step at hok; simp [hv] at hok
  have hmem : i ∈ ids s.journal := hvr.1
  obtain ⟨e, he⟩ := findEntry_exists s.journal i hmem
  unfold step at hok ⊢
  simp [hvr, he] at hok ⊢
  -- now hok is trivial, goal is about state with reversed appended
  have hmem_rev : i ∈ (s.reversed ++ [i]) := by
    simp
  have hvr2 : ¬ ValidReverse { s with balance := postLines (e.lines.map (fun l => (l.1, -l.2))) s.balance, reversed := s.reversed ++ [i] } i := by
    intro h
    exact h.2 hmem_rev
  simp [hvr2]

theorem req_roundtrip        : RoundTrip step := sorry

theorem req_trial_balance    : TrialBalance step := sorry

theorem req_well_formed      : StaysWellFormed step := sorry

theorem req_consistent       : StaysConsistent step := sorry

end Reversal
