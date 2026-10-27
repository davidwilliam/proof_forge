import Transfer.Spec
import Transfer.Lemmas
namespace Transfer

def admissible (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.source ≠ r.target ∧
  r.source ∈ s.accounts ∧
  r.target ∈ s.accounts ∧
  s.auth r.requester r.source = true ∧
  -(s.limit r.source : Int) ≤ s.balance r.source - r.amount ∧
  r.txId ∉ s.applied

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (admissible s r) := by
  unfold admissible; infer_instance

def step : Impl := fun s r =>
  if admissible s r then
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have ha : admissible s r := h
  unfold step
  simp [ha]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hn : ¬ admissible s r := h
  unfold step
  simp [hn]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  by_cases ha : admissible s r
  · have h := ha
    unfold admissible at h
    obtain ⟨_, _, _, _, _, hauth, _, _⟩ := h
    exact hauth
  · have hre : (step s r).1 = .rejected := by unfold step; simp [ha]
    rw [hre] at hok
    exact absurd hok (by decide)

theorem req_debit_credit : DebitCredit step := by
  intro s r hok
  have ha : admissible s r := by
    by_cases h : admissible s r
    · exact h
    · have hre : (step s r).1 = .rejected := by unfold step; simp [h]
      rw [hre] at hok
      exact absurd hok (by decide)
  have hne : r.source ≠ r.target := by
    have h := ha
    unfold admissible at h
    obtain ⟨_, _, hne, _, _, _, _, _⟩ := h
    exact hne
  have hns : r.target ≠ r.source := fun heq => hne heq.symm
  constructor
  · unfold step
    simp [ha, hne]
  · unfold step
    simp [ha, hns]

theorem req_effects : Effects step := by
  intro s r hok
  have ha : admissible s r := by
    by_cases h : admissible s r
    · exact h
    · have hre : (step s r).1 = .rejected := by unfold step; simp [h]
      rw [hre] at hok
      exact absurd hok (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold step
    simp [ha]
  · unfold step
    simp [ha]
  · unfold step
    simp [ha]
  · intro a
    unfold step expectedBalance
    simp [ha]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have ha : admissible s r := by
    by_cases h : admissible s r
    · exact h
    · have hre : (step s r).1 = .rejected := by unfold step; simp [h]
      rw [hre] at hok
      exact absurd hok (by decide)
  have happ : (step s r).2.applied = r.txId :: s.applied := by unfold step; simp [ha]
  have hmem : r.txId ∈ (step s r).2.applied := by rw [happ]; simp
  have hn : ¬ admissible ((step s r).2) r := by
    intro h
    unfold admissible at h
    obtain ⟨_, _, _, _, _, _, _, hnotin⟩ := h
    exact hnotin hmem
  constructor
  · intro x
    rw [happ]
    simp
  · revert hn
    generalize (step s r).2 = t
    intro hn
    unfold step
    simp [hn]

theorem req_limit : LimitRespected step := by
  intro s r hw a hm
  by_cases ha : admissible s r
  · have hacc : (step s r).2.accounts = s.accounts := by unfold step; simp [ha]
    have hlim_eq : (step s r).2.limit = s.limit := by unfold step; simp [ha]
    have hbal : ∀ b, (step s r).2.balance b = expectedBalance s r b := by
      intro b
      unfold step expectedBalance
      simp [ha]
    rw [hacc] at hm
    rw [hlim_eq, hbal a]
    unfold expectedBalance
    have hwa : -(s.limit a : Int) ≤ s.balance a := hw a hm
    have hlim : -(s.limit r.source : Int) ≤ s.balance r.source - (r.amount : Int) := by
      have h := ha
      unfold admissible at h
      obtain ⟨_, _, _, _, _, _, hlim, _⟩ := h
      exact hlim
    have hpos : (0 : Int) < (r.amount : Int) := by
      have h := ha
      unfold admissible at h
      obtain ⟨_, hpos, _, _, _, _, _, _⟩ := h
      omega
    have hne : r.source ≠ r.target := by
      have h := ha
      unfold admissible at h
      obtain ⟨_, _, hne, _, _, _, _, _⟩ := h
      exact hne
    by_cases h1 : a = r.source
    · subst h1
      by_cases h2 : r.source = r.target
      · exfalso
        exact hne h2
      · simp [h2]
        exact hlim
    · by_cases h2 : a = r.target
      · subst h2
        simp [h1]
        omega
      · simp [h1, h2]
        exact hwa
  · have heq : (step s r).2 = s := by unfold step; simp [ha]
    rw [heq] at hm
    rw [heq]
    exact hw a hm

theorem req_conservation : Conserves step := by
  intro s r hok
  have ha : admissible s r := by
    by_cases h : admissible s r
    · exact h
    · have hre : (step s r).1 = .rejected := by unfold step; simp [h]
      rw [hre] at hok
      exact absurd hok (by decide)
  have ha_copy := ha
  unfold admissible at ha_copy
  obtain ⟨hnodup, _, _, hsrc, htgt, _, _, _⟩ := ha_copy
  have hacc : (step s r).2.accounts = s.accounts := by unfold step; simp [ha]
  have hbal : ∀ b, (step s r).2.balance b = expectedBalance s r b := by
    intro b
    unfold step expectedBalance
    simp [ha]
  have htot : total ((step s r).2) = sumOver s.accounts (fun a => expectedBalance s r a) := by
    unfold total
    rw [hacc]
    exact sumOver_congr s.accounts ((step s r).2.balance) (fun a => expectedBalance s r a) (fun a _ => hbal a)
  rw [htot]
  unfold total
  have hsplit : sumOver s.accounts (fun a => expectedBalance s r a) = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) := by
    have h1 := sumOver_add s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)) (fun a => if a = r.target then (r.amount : Int) else 0)
    have h2 := sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
    have heq : (fun a => expectedBalance s r a) = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))) := rfl
    rw [heq, h1, h2]
  rw [hsplit]
  have hs : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.source (r.amount : Int)
    simp [hsrc] at h
    exact h
  have ht : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by
    have h := sumOver_ite_eq hnodup r.target (r.amount : Int)
    simp [htgt] at h
    exact h
  rw [hs, ht]
  omega

end Transfer
