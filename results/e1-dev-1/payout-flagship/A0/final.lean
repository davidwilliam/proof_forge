import Payout.Spec
import Payout.Lemmas
namespace Payout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

def step : Impl := fun s r =>
  if ValidPayout s r then
    (.ok, { s with
      balance := expectedBalance s r,
      applied := r.txId :: s.applied })
  else (.rejected, s)

private theorem ok_imp_valid (s : State) (r : Request) (h : (step s r).1 = .ok) :
    ValidPayout s r := by
  have hem : ValidPayout s r ∨ ¬ ValidPayout s r := Decidable.em _
  cases hem with
  | inl hV => exact hV
  | inr hV =>
    have hstep : (step s r).1 = .rejected := by
      unfold step
      simp [if_neg hV]
    rw [hstep] at h
    simp at h

private theorem step_ok_eq (s : State) (r : Request) (hV : ValidPayout s r) :
    step s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  unfold step
  simp [if_pos hV]

private theorem step_noop_eq (s : State) (r : Request) (hV : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [if_neg hV]

private theorem state_ok_eq (s : State) (r : Request) (hV : ValidPayout s r) :
    (step s r).2 = { s with balance := expectedBalance s r, applied := r.txId :: s.applied } := by
  rw [step_ok_eq s r hV]

private theorem fst_ok_of_valid (s : State) (r : Request) (hV : ValidPayout s r) :
    (step s r).1 = .ok := by
  rw [step_ok_eq s r hV]

private def shareOff (q rmd : Nat) (R : List Nat) (off : Nat) (a : Nat) : Int :=
  match indexOf? R a with
  | some i => (q : Int) + (if off + i < rmd then 1 else 0)
  | none => 0

private def extraRec : List Nat → Nat → Nat → Int
  | [], _, _ => 0
  | _ :: ys, off, rmd => (if off < rmd then (1 : Int) else 0) + extraRec ys (off + 1) rmd

private theorem shareOff_nil (q rmd off a : Nat) : shareOff q rmd [] off a = 0 := by
  unfold shareOff
  simp [indexOf?]

private theorem shareOff_cons (y : Nat) (ys : List Nat) (hy : y ∉ ys)
    (q rmd off a : Nat) :
    shareOff q rmd (y :: ys) off a =
      (if a = y then (q : Int) + (if off < rmd then 1 else 0) else 0) +
      shareOff q rmd ys (off + 1) a := by
  have hem : a = y ∨ ¬ a = y := Decidable.em _
  cases hem with
  | inl heq =>
    rw [heq]
    have hnone : indexOf? ys y = none := indexOf?_eq_none hy
    have h1 : indexOf? (y :: ys) y = some 0 := by simp [indexOf?]
    unfold shareOff
    rw [h1]
    simp [hnone]
  | inr hne =>
    have hne' : y ≠ a := fun e => hne e.symm
    have hIdx : indexOf? (y :: ys) a = (indexOf? ys a).map (· + 1) := by
      simp [indexOf?, hne']
    have hif : (if a = y then (q : Int) + (if off < rmd then 1 else 0) else 0) = 0 := by
      simp [hne]
    have hall : ∀ i : Nat, off + (i + 1) = off + 1 + i := fun i => by omega
    unfold shareOff
    rw [hIdx, hif]
    cases hys : indexOf? ys a with
    | none =>
      simp [hys]
    | some i =>
      simp [hys, hall i]

private theorem sumOver_zero (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [sumOver_cons, ih]

private theorem extraRec_ge (R : List Nat) (off rmd : Nat) (h : rmd ≤ off) :
    extraRec R off rmd = 0 := by
  induction R generalizing off with
  | nil => simp [extraRec]
  | cons hd ys ih =>
    have hif : (if off < rmd then (1 : Int) else 0) = 0 := by
      have hnn : ¬ off < rmd := by omega
      simp [hnn]
    have h2 : rmd ≤ off + 1 := by omega
    have hz := ih (off + 1) h2
    simp [extraRec, hif, hz]

private theorem extraRec_eq (R : List Nat) (off rmd : Nat)
    (hle : off ≤ rmd) (hge : rmd ≤ off + R.length) :
    extraRec R off rmd = ((rmd : Int) - (off : Int)) := by
  induction R generalizing off with
  | nil =>
    have hge' : rmd ≤ off := by simpa using hge
    have heq : off = rmd := by omega
    subst heq
    simp [extraRec]
  | cons hd ys ih =>
    have hlen : (hd :: ys).length = ys.length + 1 := rfl
    rw [hlen] at hge
    have hem : off < rmd ∨ ¬ off < rmd := Decidable.em _
    cases hem with
    | inl hlt =>
      have hle' : off + 1 ≤ rmd := by omega
      have hge' : rmd ≤ off + 1 + ys.length := by omega
      have iht := ih (off + 1) hle' hge'
      have hif : (if off < rmd then (1 : Int) else 0) = 1 := by simp [hlt]
      simp only [extraRec, hif] at ⊢
      rw [iht]
      omega
    | inr hnlt =>
      have heq : off = rmd := by omega
      rw [heq] at hle hge ⊢
      have hif : (if rmd < rmd then (1 : Int) else 0) = 0 := by simp
      have hz : extraRec ys (rmd + 1) rmd = 0 := extraRec_ge ys (rmd + 1) rmd (by omega)
      simp only [extraRec, hif] at ⊢
      rw [hz]
      omega

private theorem sum_F (A R : List Nat) (hA : A.Nodup) (q rmd off : Nat)
    (hR : R.Nodup) (hSub : ∀ x ∈ R, x ∈ A) :
    sumOver A (shareOff q rmd R off) = ((R.length * q : Nat) : Int) + extraRec R off rmd := by
  induction R generalizing off with
  | nil =>
    have hz : ∀ a ∈ A, shareOff q rmd [] off a = 0 := fun a _ => shareOff_nil q rmd off a
    have h1 := sumOver_congr A (shareOff q rmd [] off) (fun _ => (0 : Int)) hz
    have h0 : sumOver A (fun _ => (0 : Int)) = 0 := sumOver_zero A
    rw [h1, h0]
    simp [extraRec]
  | cons y ys ih =>
    have hRcons := hR
    rw [List.nodup_cons] at hRcons
    obtain ⟨hynot, hRys⟩ := hRcons
    have hSubYs : ∀ x ∈ ys, x ∈ A := fun x hx => hSub x (by simp [hx])
    have hyA : y ∈ A := hSub y (by simp)
    have hSubTail := ih (off + 1) hRys hSubYs
    have hpoint : ∀ a ∈ A, shareOff q rmd (y :: ys) off a =
        (if a = y then (q : Int) + (if off < rmd then 1 else 0) else 0) +
        (shareOff q rmd ys (off + 1)) a := by
      intro a _
      rw [shareOff_cons y ys hynot q rmd off a]
    have hsum := sumOver_congr A (shareOff q rmd (y :: ys) off)
      (fun a => (if a = y then (q : Int) + (if off < rmd then 1 else 0) else 0) + shareOff q rmd ys (off + 1) a) hpoint
    rw [hsum, sumOver_add]
    have hsingle : sumOver A (fun a => (if a = y then (q : Int) + (if off < rmd then 1 else 0) else 0))
        = (q : Int) + (if off < rmd then 1 else 0) := by
      have h2 := sumOver_ite_eq hA y ((q : Int) + (if off < rmd then 1 else 0))
      rw [h2]
      simp [hyA]
    rw [hsingle, hSubTail]
    have hNat : (ys.length + 1) * q = ys.length * q + q := by
      rw [Nat.add_mul, Nat.one_mul]
    have hcast : (((ys.length + 1) * q : Nat) : Int) = ((ys.length * q : Nat) : Int) + (q : Int) := by
      rw [hNat]
      omega
    have hlen : (y :: ys).length = ys.length + 1 := rfl
    rw [hlen, hcast]
    simp only [extraRec]
    omega

private theorem shareOf_eq_shareOff (r : Request) (a : Nat) :
    (shareOf r a : Int) = shareOff (r.amount / r.recipients.length) (r.amount % r.recipients.length) r.recipients 0 a := by
  unfold shareOf shareOff fairShare
  cases h : indexOf? r.recipients a with
  | none => rfl
  | some i =>
    simp only [h]
    rw [Nat.zero_add]
    by_cases hP : i < r.amount % r.recipients.length
    · simp only [if_pos hP]
      omega
    · simp only [if_neg hP]
      omega

private theorem sum_shareOf_eq_amount (s : State) (r : Request) (hV : ValidPayout s r) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = (r.amount : Int) := by
  unfold ValidPayout at hV
  obtain ⟨hNodupA, hPos, hNeNil, hNodupR, hSrcNot, hSrcMem, hSub, hAuth, hBal, hFresh⟩ := hV
  have hdivmod : r.recipients.length * (r.amount / r.recipients.length) + r.amount % r.recipients.length = r.amount :=
    Nat.div_add_mod _ _
  have hlenPos : 0 < r.recipients.length := by
    match hR : r.recipients with
    | [] => simp [hR] at hNeNil
    | _ :: _ => simp
  have hmodLt : r.amount % r.recipients.length < r.recipients.length := Nat.mod_lt _ hlenPos
  have heach : ∀ a ∈ s.accounts, ((shareOf r a : Nat) : Int) =
      shareOff (r.amount / r.recipients.length) (r.amount % r.recipients.length) r.recipients 0 a := by
    intro a _
    exact shareOf_eq_shareOff r a
  have hcongr : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))
      = sumOver s.accounts (shareOff (r.amount / r.recipients.length) (r.amount % r.recipients.length) r.recipients 0) :=
    sumOver_congr s.accounts _ _ heach
  rw [hcongr]
  have hsum := sum_F s.accounts r.recipients hNodupA
    (r.amount / r.recipients.length) (r.amount % r.recipients.length) 0 hNodupR hSub
  rw [hsum]
  have hlen_ge : r.amount % r.recipients.length ≤ 0 + r.recipients.length := by omega
  have hex := extraRec_eq r.recipients 0 (r.amount % r.recipients.length) (Nat.zero_le _) hlen_ge
  rw [hex]
  omega

private theorem shareOf_of_mem (r : Request) (hNodup : r.recipients.Nodup)
    (i : Nat) (hi : i < r.recipients.length) :
    shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
  unfold shareOf
  rw [indexOf?_getElem hNodup i hi]

private theorem shareOf_of_notmem (r : Request) (a : Nat) (h : a ∉ r.recipients) :
    shareOf r a = 0 := by
  unfold shareOf
  rw [indexOf?_eq_none h]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hV
  exact fst_ok_of_valid s r hV

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hV
  have hN : ¬ ValidPayout s r := hV
  exact step_noop_eq s r hN

theorem req_fair_shares : FairShares step := by
  intro s r hOk i hi
  have hV := ok_imp_valid s r hOk
  unfold ValidPayout at hV
  obtain ⟨hNodupA, hPos, hNeNil, hNodupR, hSrcNot, hSrcMem, hSub, hAuth, hBal, hFresh⟩ := hV
  have hstate := state_ok_eq s r ⟨hNodupA, hPos, hNeNil, hNodupR, hSrcNot, hSrcMem, hSub, hAuth, hBal, hFresh⟩
  have hmem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hne : r.recipients[i] ≠ r.source := by
    intro heq
    apply hSrcNot
    rw [heq] at hmem
    exact hmem
  have hshare := shareOf_of_mem r hNodupR i hi
  have hbal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] := by
    rw [hstate]
  have hbal2 : expectedBalance s r r.recipients[i]
      = s.balance r.recipients[i] + ((shareOf r r.recipients[i] : Nat) : Int) := by
    unfold expectedBalance
    have hif : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by simp [hne]
    rw [hif]
    omega
  rw [hbal, hbal2, hshare]
  omega

theorem req_effects : Effects step := by
  intro s r hOk
  have hV := ok_imp_valid s r hOk
  have hstate := state_ok_eq s r hV
  refine ⟨?_, ?_, ?_⟩
  · rw [hstate]
  · rw [hstate]
  · intro a
    rw [hstate]

theorem req_conservation : Conserves step := by
  intro s r hOk
  have hV := ok_imp_valid s r hOk
  have hVcopy := hV
  unfold ValidPayout at hVcopy
  obtain ⟨hNodupA, hPos, hNeNil, hNodupR, hSrcNot, hSrcMem, hSub, hAuth, hBal, hFresh⟩ := hVcopy
  have hstate := state_ok_eq s r hV
  unfold total
  rw [hstate]
  simp only
  have hexp : ∀ a ∈ s.accounts, expectedBalance s r a =
      s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int) := by
    intro a _
    rfl
  have hcongr := sumOver_congr s.accounts (fun a => expectedBalance s r a)
    (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)) hexp
  rw [hcongr]
  have hsplit : ∀ a : Nat, s.balance a - (if a = r.source then (r.amount : Int) else 0) + ((shareOf r a : Nat) : Int)
      = (s.balance a + ((shareOf r a : Nat) : Int)) - (if a = r.source then (r.amount : Int) else 0) := by
    intro a; omega
  rw [sumOver_congr s.accounts _ _ (fun a _ => hsplit a)]
  rw [sumOver_sub]
  rw [sumOver_add]
  have hsrc : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
      = (r.amount : Int) := by
    have h2 := sumOver_ite_eq hNodupA r.source (r.amount : Int)
    rw [h2]
    simp [hSrcMem]
  have hshare := sum_shareOf_eq_amount s r hV
  rw [hsrc, hshare]
  omega

theorem req_nonnegative : NonNegative step := by
  intro s r hNonneg a ha
  have hem : ValidPayout s r ∨ ¬ ValidPayout s r := Decidable.em _
  cases hem with
  | inl hV =>
    have hstate := state_ok_eq s r hV
    have ha' : a ∈ s.accounts := by
      rw [hstate] at ha
      simpa using ha
    have h0 := hNonneg a ha'
    unfold ValidPayout at hV
    obtain ⟨hNodupA, hPos, hNeNil, hNodupR, hSrcNot, hSrcMem, hSub, hAuth, hBal, hFresh⟩ := hV
    have hbal : (step s r).2.balance a = expectedBalance s r a := by
      rw [hstate]
    rw [hbal]
    unfold expectedBalance
    have hem2 : a = r.source ∨ ¬ a = r.source := Decidable.em _
    cases hem2 with
    | inl heq =>
      rw [heq]
      have hshare0 : shareOf r r.source = 0 := shareOf_of_notmem r r.source hSrcNot
      rw [hshare0]
      simp
      omega
    | inr hne =>
      simp [hne]
      omega
  | inr hV =>
    have hstep : step s r = (.rejected, s) := step_noop_eq s r hV
    have hbal : (step s r).2.balance a = s.balance a := by rw [hstep]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
    rw [hbal]
    exact hNonneg a ha'

theorem req_authorization : AuthorizedOnly step := by
  intro s r hOk
  have hV := ok_imp_valid s r hOk
  unfold ValidPayout at hV
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := hV
  exact h8

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  have hV := ok_imp_valid s r hOk
  have hstate := state_ok_eq s r hV
  constructor
  · intro x
    rw [hstate]
    simp
  · have hmem : r.txId ∈ (step s r).2.applied := by
      rw [hstate]; simp
    have hV2 : ¬ ValidPayout (step s r).2 r := by
      intro hC
      unfold ValidPayout at hC
      obtain ⟨c1,c2,c3,c4,c5,c6,c7,c8,c9,c10⟩ := hC
      exact c10 hmem
    rw [step_noop_eq _ _ hV2]

end Payout
