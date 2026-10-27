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

theorem aux_step_ok (s : State) (r : Request) (hv : ValidPayout s r) : step s r = (Outcome.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
  unfold step
  simp [hv]

theorem tmpA (n : Nat) : (0 : Int) ≤ (n : Int) := by
  simp
#check @Int.natCast_nonneg

theorem check_erase_lemmas : True := trivial
#check @List.erase
#check @List.Nodup

theorem t_range_append : List.range 3 = List.range 2 ++ [2] := by native_decide

theorem myTestThm : True := trivial

theorem myTestLem2 : 1 + 1 = (2 : Nat) := rfl

theorem mySumAppend (l1 l2 : List Nat) (f : Nat → Int) : sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem mySumRangeSucc (n : Nat) (f : Nat → Int) : sumOver (List.range (n+1)) f = sumOver (List.range n) f + f n := by
  have h1 : List.range (n+1) = List.range n ++ [n] := by simp [List.range_succ]
  rw [h1, mySumAppend]
  simp

theorem myProbeErase : True := trivial

theorem mySumZero (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · unfold step at hok
    simp [hv] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · unfold step
    simp [hv]
  · unfold step at hok
    simp [hv] at hok

theorem req_idempotency    : Idempotent step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hEq := aux_step_ok s r hv
    have hnot : ¬ ValidPayout ({ s with balance := (fun a => expectedBalance s r a), applied := r.txId :: s.applied } : State) r := by
      intro hc
      obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := hc
      exact h10 (List.mem_cons.mpr (Or.inl rfl))
    have hRej := req_invalid_noop ({ s with balance := (fun a => expectedBalance s r a), applied := r.txId :: s.applied } : State) r hnot
    have h2 : (step s r).2 = ({ s with balance := (fun a => expectedBalance s r a), applied := r.txId :: s.applied } : State) := by
      rw [hEq]
    rw [h2]
    constructor
    · intro x
      simp
    · exact hRej
  · have hEq2 : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [hv]
    rw [hEq2] at hok
    simp at hok

theorem req_nonnegative : NonNegative step := by
  intro s r hnn a ha
  by_cases hv : ValidPayout s r
  · have hEq := aux_step_ok s r hv
    have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := congrArg Prod.snd hEq
    have hacc : (step s r).2.accounts = s.accounts := by rw [h2]
    rw [hacc] at ha
    have hbal : (step s r).2.balance a = expectedBalance s r a := by rw [h2]
    rw [hbal]
    have hnn_a : 0 ≤ s.balance a := hnn a ha
    have hle : (r.amount : Int) ≤ s.balance r.source := hv.2.2.2.2.2.2.2.2.1
    have hmem : r.source ∉ r.recipients := hv.2.2.2.2.1
    unfold expectedBalance
    by_cases hsrc : a = r.source
    · subst hsrc
      have hsh0 : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hmem]
      rw [hsh0]
      simp
      omega
    · simp only [hsrc, ↓reduceIte]
      omega
  · have hEq2 : step s r = (Outcome.rejected, s) := by unfold step; simp [hv]
    have h2b : (step s r).2 = s := congrArg Prod.snd hEq2
    rw [h2b] at ha ⊢
    exact hnn a ha

theorem req_fair_shares : FairShares step := by
  intro s r hok i hi
  by_cases hv : ValidPayout s r
  · have hEq := aux_step_ok s r hv
    obtain ⟨h_nodup_acc, h_pos, h_ne, h_nodup_rec, h_src_notin, h_src_mem, h_sub, h_auth, h_bal, h_fresh⟩ := hv
    have h2 : (step s r).2 = ({ s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied } : State) := congrArg Prod.snd hEq
    have hbal_eq : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by rw [h2]
    rw [hbal_eq]
    have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
    have hne_src : r.recipients[i] ≠ r.source := fun h => h_src_notin (h ▸ hmem)
    have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by simp [hne_src]
    have hidx : indexOf? r.recipients r.recipients[i] = some i := indexOf?_getElem h_nodup_rec i hi
    have hshare : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
      unfold shareOf
      rw [hidx]
    unfold expectedBalance
    rw [hif, hshare]
    omega
  · have hEq2 : step s r = (Outcome.rejected, s) := by unfold step; simp [hv]
    rw [hEq2] at hok
    simp at hok

theorem req_conservation   : Conserves step := sorry

end Payout
