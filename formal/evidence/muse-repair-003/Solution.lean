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

private theorem step_valid_eq (s : State) (r : Request) (h : ValidPayout s r) :
    step s r = (.ok, { s with balance := fun a => expectedBalance s r a, applied := r.txId :: s.applied }) := by
  unfold step
  rw [if_pos h]

private theorem step_invalid_eq (s : State) (r : Request) (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  unfold step
  rw [if_neg h]

private theorem ok_implies_valid (s : State) (r : Request) (hOk : (step s r).1 = .ok) :
    ValidPayout s r := by
  cases Decidable.em (ValidPayout s r) with
  | inl h => exact h
  | inr h =>
    have hneg := step_invalid_eq s r h
    have hFst : (step s r).1 = .rejected := by rw [hneg]
    have hEq : (Outcome.ok = Outcome.rejected) := by rw [← hOk, hFst]
    exact absurd hEq (by decide)

private theorem step_balance_eq (s : State) (r : Request) (hV : ValidPayout s r) (a : AccountId) :
    (step s r).2.balance a = expectedBalance s r a := by
  have hEq := step_valid_eq s r hV
  rw [hEq]

private theorem step_accounts_eq (s : State) (r : Request) (hV : ValidPayout s r) :
    (step s r).2.accounts = s.accounts := by
  have hEq := step_valid_eq s r hV
  rw [hEq]

private theorem step_auth_eq (s : State) (r : Request) (hV : ValidPayout s r) :
    (step s r).2.auth = s.auth := by
  have hEq := step_valid_eq s r hV
  rw [hEq]

private theorem step_applied_eq (s : State) (r : Request) (hV : ValidPayout s r) :
    (step s r).2.applied = r.txId :: s.applied := by
  have hEq := step_valid_eq s r hV
  rw [hEq]

private theorem sumOver_zero (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver_cons, ih, Int.add_zero]

private theorem sumIf (accs : List Nat) (hNodup : accs.Nodup) (y0 : Nat) (c : Int) (G : Nat → Int) :
    sumOver accs (fun a => if a = y0 then c else G a)
      = sumOver accs G + (if y0 ∈ accs then c - G y0 else 0) := by
  have hPoint : ∀ a, (if a = y0 then c else G a) = G a + (if a = y0 then c - G y0 else 0) := by
    intro a
    by_cases h : a = y0
    · subst h
      rw [if_pos rfl, if_pos rfl]
      omega
    · rw [if_neg h, if_neg h]
      omega
  have hCong : sumOver accs (fun a => if a = y0 then c else G a)
      = sumOver accs (fun a => G a + (if a = y0 then c - G y0 else 0)) :=
    sumOver_congr accs _ _ (fun a _ => hPoint a)
  rw [hCong, sumOver_add]
  have hIte := sumOver_ite_eq (l := accs) hNodup y0 (c - G y0)
  rw [hIte]

private theorem sumAccAux (amount n : Nat) (accs : List Nat) (hn : 0 < n) (hAcc : accs.Nodup) :
    ∀ (rec : List Nat) (k : Nat),
    rec.Nodup → (∀ x ∈ rec, x ∈ accs) → k + rec.length = n →
    sumOver accs (fun a => match indexOf? rec a with
      | some i => ((fairShare amount n (k + i) : Nat) : Int)
      | none => 0)
    = ((((rec.length * (amount / n) + (if k < amount % n then amount % n - k else 0) : Nat)) : Int)) := by
  intro rec
  induction rec with
  | nil =>
    intro k hRec hSub heq
    have hFzero : ∀ a ∈ accs, (match indexOf? ([] : List Nat) a with
        | some i => ((fairShare amount n (k + i) : Nat) : Int)
        | none => (0 : Int)) = 0 := by
      intro a _
      rfl
    have hEq := sumOver_congr accs _ _ hFzero
    rw [hEq, sumOver_zero]
    have hkn : k = n := by simpa using heq
    have hlt : amount % n < n := Nat.mod_lt amount hn
    have hNot : ¬ (k < amount % n) := by omega
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
    rw [if_neg hNot]
    simp
  | cons hd0 tl0 ih =>
    intro k hRec hSub heq
    have hxnotin : hd0 ∉ tl0 := (List.nodup_cons.mp hRec).1
    have htail : tl0.Nodup := (List.nodup_cons.mp hRec).2
    have hxmem : hd0 ∈ accs := hSub hd0 (by simp only [List.mem_cons, true_or])
    have heq_tail : (k + 1) + tl0.length = n := by
      simp only [List.length_cons] at heq
      omega
    have hSub_tail : ∀ y ∈ tl0, y ∈ accs := fun y hy => hSub y (List.mem_cons_of_mem hd0 hy)
    have ihTail := ih (k + 1) htail hSub_tail heq_tail
    have hDecomp : ∀ a, (match indexOf? (hd0 :: tl0) a with
        | some i => ((fairShare amount n (k + i) : Nat) : Int)
        | none => (0 : Int))
        = (if a = hd0 then (((fairShare amount n k : Nat)) : Int)
            else (match indexOf? tl0 a with
              | some i => ((fairShare amount n ((k + 1) + i) : Nat) : Int)
              | none => 0)) := by
      intro a
      by_cases ha : hd0 = a
      · have ha2 : a = hd0 := ha.symm
        have hIdx_a : indexOf? (hd0 :: tl0) a = some 0 := by simp [indexOf?, ha]
        rw [hIdx_a, if_pos ha2]
        show (((fairShare amount n (k + 0) : Nat)) : Int) = (((fairShare amount n k : Nat)) : Int)
        rw [Nat.add_zero]
      · have ha2 : ¬ (a = hd0) := fun h => ha h.symm
        have hIdx : indexOf? (hd0 :: tl0) a = (indexOf? tl0 a).map (· + 1) := by
          simp [indexOf?, ha]
        rw [hIdx, if_neg ha2]
        cases htl0 : indexOf? tl0 a with
        | none => simp [htl0]
        | some i =>
          simp only [htl0, Option.map_some]
          have hkk : k + (i + 1) = (k + 1) + i := by omega
          rw [hkk]
    have hCongF : sumOver accs (fun a => match indexOf? (hd0 :: tl0) a with
        | some i => ((fairShare amount n (k + i) : Nat) : Int)
        | none => (0 : Int))
        = sumOver accs (fun a => if a = hd0 then (((fairShare amount n k : Nat)) : Int)
            else (match indexOf? tl0 a with
              | some i => ((fairShare amount n ((k + 1) + i) : Nat) : Int)
              | none => 0)) := by
      apply sumOver_congr
      intro a ha
      exact hDecomp a
    have hS := sumIf accs hAcc hd0 (((fairShare amount n k : Nat)) : Int)
      (fun a => match indexOf? tl0 a with
        | some i => ((fairShare amount n ((k + 1) + i) : Nat) : Int)
        | none => 0)
    have hGx : (match indexOf? tl0 hd0 with
        | some i => ((fairShare amount n ((k + 1) + i) : Nat) : Int)
        | none => (0 : Int)) = 0 := by
      have hNone : indexOf? tl0 hd0 = none :=
        indexOf?_eq_none (a := hd0) (l := tl0) (by simpa using hxnotin)
      rw [hNone]
    have hFair : fairShare amount n k = amount / n + (if k < amount % n then 1 else 0) := rfl
    have hNatEq : tl0.length * (amount / n)
        + (if k + 1 < amount % n then amount % n - (k + 1) else 0)
        + fairShare amount n k
        = (tl0.length + 1) * (amount / n)
          + (if k < amount % n then amount % n - k else 0) := by
      rw [hFair]
      have hMul : (tl0.length + 1) * (amount / n)
          = tl0.length * (amount / n) + amount / n := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [hMul]
      by_cases hk : k < amount % n
      · by_cases hk2 : k + 1 < amount % n
        · simp only [hk, hk2, if_true]; omega
        · simp only [hk, hk2, if_true, if_false]; omega
      · have hk2 : ¬ (k + 1 < amount % n) := by omega
        simp only [hk, hk2, if_false]; omega
    have hLen : (hd0 :: tl0).length = tl0.length + 1 := rfl
    rw [hLen, hCongF, hS, hGx, ihTail]
    simp only [hxmem, if_true]
    omega

private theorem sumShares_accounts (s : State) (r : Request) (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) = ((r.amount : Nat) : Int) := by
  have hNodupAcc : s.accounts.Nodup := hv.1
  have hNeNil : r.recipients ≠ [] := hv.2.2.1
  have hNodupRec : r.recipients.Nodup := hv.2.2.2.1
  have hRecMem : ∀ x ∈ r.recipients, x ∈ s.accounts := hv.2.2.2.2.2.2.1
  have hn : 0 < r.recipients.length := by
    cases hr : r.recipients with
    | nil => exact False.elim (hNeNil hr)
    | cons hd tl => exact Nat.succ_pos _
  have h0 := sumAccAux r.amount r.recipients.length s.accounts hn hNodupAcc r.recipients 0 hNodupRec hRecMem (by simp only [Nat.zero_add])
  simp only [Nat.zero_add] at h0
  have hCongAcc : sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int))
      = sumOver s.accounts (fun a => match indexOf? r.recipients a with
        | some i => ((fairShare r.amount r.recipients.length i : Nat) : Int)
        | none => 0) := by
    apply sumOver_congr
    intro a ha
    unfold shareOf
    cases hmo : indexOf? r.recipients a with
    | none => rfl
    | some i => rfl
  rw [hCongAcc, h0]
  have hdiv : r.recipients.length * (r.amount / r.recipients.length) + r.amount % r.recipients.length = r.amount :=
    Nat.div_add_mod _ _
  by_cases hrem0 : 0 < r.amount % r.recipients.length
  · have e : (if (0 : Nat) < r.amount % r.recipients.length then r.amount % r.recipients.length - 0 else 0)
        = r.amount % r.recipients.length := by simp [hrem0]
    rw [e, hdiv]
  · have hNot : ¬ (0 : Nat) < r.amount % r.recipients.length := by omega
    have e : (if (0 : Nat) < r.amount % r.recipients.length then r.amount % r.recipients.length - 0 else 0) = 0 := by
      simp [hNot]
    rw [e]
    have hNat : r.recipients.length * (r.amount / r.recipients.length) + 0 = r.amount := by omega
    rw [hNat]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hV
  have hEq := step_valid_eq s r hV
  simpa using congrArg Prod.fst hEq

theorem req_invalid_noop : InvalidNoop step := by
  intro s r hN
  exact step_invalid_eq s r hN

theorem req_fair_shares : FairShares step := by
  intro s r hOk i hi
  have hVd : ValidPayout s r := ok_implies_valid s r hOk
  have hNodupRec : r.recipients.Nodup := hVd.2.2.2.1
  have hSrcNotRec : r.source ∉ r.recipients := hVd.2.2.2.2.1
  have hBal : (step s r).2.balance r.recipients[i] = expectedBalance s r r.recipients[i] :=
    step_balance_eq s r hVd r.recipients[i]
  have hMem : r.recipients[i] ∈ r.recipients := List.getElem_mem hi
  have hNe : r.recipients[i] ≠ r.source := by
    intro heq
    apply hSrcNotRec
    rw [← heq]
    exact hMem
  have hIdx : indexOf? r.recipients r.recipients[i] = some i :=
    indexOf?_getElem hNodupRec i hi
  have hShare : shareOf r r.recipients[i] = fairShare r.amount r.recipients.length i := by
    unfold shareOf
    rw [hIdx]
  have hExp : expectedBalance s r r.recipients[i]
      = s.balance r.recipients[i] + ((fairShare r.amount r.recipients.length i : Nat) : Int) := by
    unfold expectedBalance
    rw [hShare]
    have hIf : (if r.recipients[i] = r.source then (r.amount : Int) else 0) = 0 := by simp [hNe]
    rw [hIf]
    simp only [Int.sub_zero]
  rw [hBal, hExp]
  omega

theorem req_effects : Effects step := by
  intro s r hOk
  have hVd : ValidPayout s r := ok_implies_valid s r hOk
  have hAcc : (step s r).2.accounts = s.accounts := step_accounts_eq s r hVd
  have hAuth : (step s r).2.auth = s.auth := step_auth_eq s r hVd
  exact ⟨hAcc, hAuth, fun a => step_balance_eq s r hVd a⟩

theorem req_conservation : Conserves step := by
  intro s r hOk
  have hVd : ValidPayout s r := ok_implies_valid s r hOk
  have hNodupAcc : s.accounts.Nodup := hVd.1
  have hSrcMem : r.source ∈ s.accounts := hVd.2.2.2.2.2.1
  have hAccEq : (step s r).2.accounts = s.accounts := step_accounts_eq s r hVd
  have hBalEq : ∀ a, (step s r).2.balance a = expectedBalance s r a :=
    fun a => step_balance_eq s r hVd a
  have hCong : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (fun a => expectedBalance s r a) := by
    apply sumOver_congr
    intro a ha
    exact hBalEq a
  have hSplit : sumOver s.accounts (fun a => expectedBalance s r a)
      = sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0))
        + sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by
    rw [← sumOver_add]
    apply sumOver_congr
    intro a ha
    rfl
  have hSub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then ((r.amount : Nat) : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then ((r.amount : Nat) : Int) else 0)) :=
    sumOver_sub _ _ _
  have hInd : sumOver s.accounts (fun a => (if a = r.source then ((r.amount : Nat) : Int) else 0))
      = ((r.amount : Nat) : Int) := by
    have h := sumOver_ite_eq (l := s.accounts) hNodupAcc r.source ((r.amount : Nat) : Int)
    simp only [hSrcMem, if_true] at h
    exact h
  have hShares := sumShares_accounts s r hVd
  unfold total
  rw [hAccEq, hCong, hSplit, hSub, hInd, hShares, Int.sub_add_cancel]

theorem req_nonnegative : NonNegative step := by
  intro s r hNonneg a ha
  by_cases hVc : ValidPayout s r
  · have hSrcNotRec : r.source ∉ r.recipients := hVc.2.2.2.2.1
    have hBalLe : (r.amount : Int) ≤ s.balance r.source := hVc.2.2.2.2.2.2.2.2.1
    have hAcc : (step s r).2.accounts = s.accounts := step_accounts_eq s r hVc
    have hBal : (step s r).2.balance a = expectedBalance s r a := step_balance_eq s r hVc a
    rw [hAcc] at ha
    rw [hBal]
    unfold expectedBalance
    have hOld : 0 ≤ s.balance a := hNonneg a ha
    by_cases heq : a = r.source
    · subst heq
      have hShareZero : shareOf r r.source = 0 := by
        unfold shareOf
        rw [indexOf?_eq_none hSrcNotRec]
      rw [hShareZero]
      simp only [Int.ofNat_zero, Int.add_zero]
      omega
    · have hIf : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [heq]
      rw [hIf]
      simp only [Int.sub_zero]
      have hShareNonneg : (0 : Int) ≤ ((shareOf r a : Nat) : Int) := by omega
      omega
  · have hEq := step_invalid_eq s r hVc
    have hAcc : (step s r).2.accounts = s.accounts := by rw [hEq]
    have hBal : (step s r).2.balance a = s.balance a := by rw [hEq]
    rw [hAcc] at ha
    rw [hBal]
    exact hNonneg a ha

theorem req_authorization : AuthorizedOnly step := by
  intro s r hOk
  have hVd : ValidPayout s r := ok_implies_valid s r hOk
  have hAuth : s.auth r.requester r.source = true := hVd.2.2.2.2.2.2.2.1
  exact hAuth

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  have hVd : ValidPayout s r := ok_implies_valid s r hOk
  have hAppl := step_applied_eq s r hVd
  constructor
  · intro x
    rw [hAppl]
    simp only [List.mem_cons]
  · have hMem : r.txId ∈ (step s r).2.applied := by
      rw [hAppl]
      simp only [List.mem_cons, true_or]
    have hNotValid : ¬ ValidPayout (step s r).2 r := by
      intro hV2
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hFresh2⟩ := hV2
      exact hFresh2 hMem
    have hStep2 := step_invalid_eq (step s r).2 r hNotValid
    rw [hStep2]

end Payout
