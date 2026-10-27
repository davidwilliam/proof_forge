import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := fun a => expectedBalance s r a,
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_nonnegative_aux : NonNegative step := by
  intro s r hpos a ha
  by_cases hv : ValidPayout s r
  · simp [step, hv] at ha ⊢
    have hnn : 0 ≤ s.balance a := hpos a ha
    unfold expectedBalance shareOf
    by_cases has : a = r.source
    · subst has
      have hmem : r.source ∉ r.recipients := hv.2.2.2.2.1
      have hidx : indexOf? r.recipients r.source = none := indexOf?_eq_none hmem
      simp [hidx]
      obtain ⟨_, _, _, _, _, _, _, _, hle, _⟩ := hv
      omega
    · simp [has]
      omega
  · simp [step, hv] at ha ⊢
    exact hpos a ha

def foo : Nat := 1
#check List.range
#check List.nodup_range
#check Nat.div_add_mod
#check Nat.mod_lt

def bar : Nat := 2
#check @List.range_succ
#check @List.range_zero
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @List.getElem_mem

theorem sumOver_append_test (l1 l2 : List Nat) (f : Nat → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sumOver_range_ite (n m : Nat) :
    sumOver (List.range n) (fun i => (if i < m then (1 : Int) else 0)) = ((min n m : Nat) : Int) := by
  induction n generalizing m with
  | zero => simp
  | succ k ih =>
    have hrange : List.range (k + 1) = List.range k ++ [k] := by simp [List.range_succ]
    rw [hrange, sumOver_append_test]
    simp only [sumOver_cons, sumOver_nil]
    rw [ih]
    by_cases hk : k < m
    · have hmin1 : min (k+1) m = min k m + 1 := by omega
      have hmin2 : (k : Int) < (m : Int) := by exact_mod_cast hk
      simp [hk]
      rw [hmin1]
      push_cast
      omega
    · have hmin1 : min (k+1) m = min k m := by omega
      simp [hk]
      rw [hmin1]

def probeB : Nat := 4
#check Int.add_mul

theorem probe_add_mul_test : ∀ (a b c : Int), (a + b) * c = a * c + b * c := fun a b c => Int.add_mul a b c

theorem probe_mul_add_test : ∀ (a b c : Int), a * (b + c) = a * b + a * c := fun a b c => Int.mul_add a b c
#check Int.add_mul
#check Int.mul_add
#check Int.mul_comm

theorem consv_range_const (n : Nat) (c : Int) : sumOver (List.range n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hrange : List.range (k + 1) = List.range k ++ [k] := by simp [List.range_succ]
    rw [hrange, sumOver_append_test]
    simp only [sumOver_cons, sumOver_nil]
    rw [ih]
    have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by simp
    rw [hcast]
    rw [Int.add_mul]
    simp

theorem consv_zero_test (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp only [step, h, ↓reduceIte]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · unfold step at h
    simp [hv] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hv : ValidPayout s r
  · have e : step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
      simp [step, hv]
    rw [e]
    exact ⟨rfl, rfl, fun a => rfl⟩
  · simp [step, hv] at h

theorem req_idempotency    : Idempotent step := by
  intro s r h
  have hv : ValidPayout s r := by
    by_cases hnv : ValidPayout s r
    · exact hnv
    · have he : (step s r).1 = .rejected := by simp [step, hnv]
      rw [he] at h
      simp at h
  have h2 : (step s r).2 = { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } := by
    simp [step, hv]
  have hnv : ¬ ValidPayout (step s r).2 r := by
    rw [h2]
    intro hcon
    obtain ⟨_, _, _, _, _, _, _, _, _, hmem⟩ := hcon
    exact hmem (List.mem_cons.mpr (Or.inl rfl))
  exact ⟨fun x => by rw [h2]; simp, req_invalid_noop _ _ hnv⟩

theorem req_nonnegative : NonNegative step := req_nonnegative_aux

theorem req_fair_shares    : FairShares step := by
  intro s r h i hi
  by_cases hv : ValidPayout s r
  · have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
      simp [step, hv]
    rw [hbal]
    unfold expectedBalance shareOf
    obtain ⟨hnodup_acc, hpos, hne, hnodup_rec, hnsrc, hsrc_mem, hrec_mem, hauth, hle, htx⟩ := hv
    have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_src : r.recipients[i] ≠ r.source := fun heq => hnsrc (heq ▸ hmem)
    have hidx : indexOf? r.recipients r.recipients[i] = some i := indexOf?_getElem hnodup_rec i hi
    simp [hidx, hne_src]
    omega
  · simp [step, hv] at h

theorem req_conservation   : Conserves step := sorry

end Payout
