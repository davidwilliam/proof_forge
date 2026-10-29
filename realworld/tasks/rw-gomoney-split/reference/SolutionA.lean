import EqualSplit.Spec
/-!
# Reference solution (build team; hidden from agents)

Floor division plus one extra unit for the first `amount % n` parties (Euclidean remainder,
so it lies in `[0, n)` for negative amounts too).
-/

namespace EqualSplit

def shares (amount : Int) (n : Nat) : List Int :=
  (List.range n).map (fun i => amount / (n : Int) + if i < (amount % (n : Int)).toNat then 1 else 0)

def split : Impl := fun amount n =>
  if 0 < n then some (shares amount n) else none

theorem sum_shares (q : Int) (m : Nat) : ∀ n,
    ((List.range n).map (fun i => q + if i < m then (1 : Int) else 0)).sum = (n : Int) * q + (min m n : Nat) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases h : n < m
    · simp [h, Nat.min_def]; split <;> split <;> push_cast [Int.add_mul] <;> omega
    · simp [h, Nat.min_def]; split <;> split <;> push_cast [Int.add_mul] <;> omega

theorem split_some {amount : Int} {n : Nat} {out : List Int} (h : split amount n = some out) :
    0 < n ∧ out = shares amount n := by
  unfold split at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · contradiction

theorem mem_shares {amount : Int} {n : Nat} {x : Int} (h : x ∈ shares amount n) :
    x = amount / (n : Int) ∧ (amount % (n : Int)).toNat ≤ 0 ∨
    x = amount / (n : Int) ∨ (x = amount / (n : Int) + 1 ∧ 0 < amount % (n : Int)) := by
  unfold shares at h
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
  by_cases hi : i < (amount % (n : Int)).toNat
  · right; right; simp [hi]; omega
  · right; left; simp [hi]

theorem req_valid_succeeds : ValidSucceeds split := by
  intro amount n hn; simp [split, hn]

theorem req_invalid_fails : InvalidFails split := by
  intro amount; simp [split]

theorem req_one_share_each : OneShareEach split := by
  intro amount n out h
  obtain ⟨_, rfl⟩ := split_some h
  simp [OneShareEachOn, shares]

theorem req_conservation : Conserves split := by
  intro amount n out h
  obtain ⟨hn, rfl⟩ := split_some h
  unfold ConservesOn shares
  rw [sum_shares]
  have hn' : (0 : Int) < (n : Int) := by omega
  have h1 : (n : Int) * (amount / (n : Int)) + amount % (n : Int) = amount := by
    rw [Int.emod_def]; omega
  have h2 := Int.emod_nonneg amount (Int.ne_of_gt hn')
  have h3 := Int.emod_lt_of_pos amount hn'
  have : min (amount % (n : Int)).toNat n = (amount % (n : Int)).toNat := by omega
  rw [this, Int.toNat_of_nonneg h2]
  omega

theorem req_within_one_unit : WithinOneUnit split := by
  intro amount n out h
  obtain ⟨hn, rfl⟩ := split_some h
  intro x hx
  have hn' : (0 : Int) < (n : Int) := by omega
  have h1 : (n : Int) * (amount / (n : Int)) + amount % (n : Int) = amount := by
    rw [Int.emod_def]; omega
  have h2 := Int.emod_nonneg amount (Int.ne_of_gt hn')
  have h3 := Int.emod_lt_of_pos amount hn'
  rw [Int.mul_comm] at h1
  rcases mem_shares hx with ⟨rfl, _⟩ | rfl | ⟨rfl, hp⟩
  · omega
  · omega
  · rw [Int.add_mul]; omega

theorem req_sign : Sign split := by
  intro amount n out h
  obtain ⟨hn, rfl⟩ := split_some h
  intro x hx
  have hn' : (0 : Int) < (n : Int) := by omega
  have h1 : (n : Int) * (amount / (n : Int)) + amount % (n : Int) = amount := by
    rw [Int.emod_def]; omega
  have h2 := Int.emod_nonneg amount (Int.ne_of_gt hn')
  have h3 := Int.emod_lt_of_pos amount hn'
  have hq : 0 ≤ amount → 0 ≤ amount / (n : Int) := fun ha => Int.ediv_nonneg ha (by omega)
  have hq2 : amount ≤ 0 → amount / (n : Int) ≤ 0 := by
    intro ha
    rcases Int.lt_or_le 0 (amount / (n : Int)) with hp | hp
    · have : (n : Int) * 1 ≤ (n : Int) * (amount / (n : Int)) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    · exact hp
  have hq3 : amount ≤ 0 → 0 < amount % (n : Int) → amount / (n : Int) < 0 := by
    intro ha hp
    rcases Int.lt_or_le (amount / (n : Int)) 0 with hneg | hnn
    · exact hneg
    · have : 0 ≤ (n : Int) * (amount / (n : Int)) := Int.mul_nonneg (by omega) hnn
      omega
  rcases mem_shares hx with ⟨rfl, _⟩ | rfl | ⟨rfl, hp⟩
  · exact ⟨hq, hq2⟩
  · exact ⟨hq, hq2⟩
  · constructor
    · intro ha; have := hq ha; omega
    · intro ha; have := hq3 ha hp; omega

end EqualSplit
