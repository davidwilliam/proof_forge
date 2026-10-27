import FeePayout.Spec
import FeePayout.Lemmas
namespace FeePayout

instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout
  infer_instance

private def nextState (s : State) (r : Request) : State :=
  { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
                          + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0),
      applied := r.txId :: s.applied }

def step : Impl := fun s r =>
  if ValidPayout s r then (.ok, nextState s r)
  else (.rejected, s)

private theorem step_ok (s : State) (r : Request) (h : ValidPayout s r) :
    step s r = (.ok, nextState s r) := by
  unfold step
  simp [h]

private theorem step_rej (s : State) (r : Request) (h : ¬ ValidPayout s r) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

private theorem sumOver_zero (l : List Nat) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumOver_cons, ih]

private theorem sumOver_mem_eq (accts : List Nat) (rs : List Nat) (c : Int) :
    accts.Nodup → rs.Nodup → (∀ x ∈ rs, x ∈ accts) →
    sumOver accts (fun a => if a ∈ rs then c else 0) = (rs.length : Int) * c := by
  intro hNodAccts
  induction rs with
  | nil =>
    intro _ _
    have h0 : ∀ a ∈ accts, (if a ∈ ([] : List Nat) then c else 0) = 0 := by
      intro a _
      simp
    have hCong := sumOver_congr accts _ _ h0
    rw [hCong, sumOver_zero]
    simp
  | cons x xs ih =>
    intro hNodRs hSub
    rw [List.nodup_cons] at hNodRs
    obtain ⟨hx_not, hNodXs⟩ := hNodRs
    have hx_mem : x ∈ accts := hSub x (by simp)
    have hSubXs : ∀ y ∈ xs, y ∈ accts := fun y hy => hSub y (List.mem_cons_of_mem x hy)
    have ih' : sumOver accts (fun a => if a ∈ xs then c else 0) = (xs.length : Int) * c :=
      ih hNodXs hSubXs
    have hPoint : ∀ a ∈ accts, (if a ∈ x :: xs then c else 0)
        = ((if a = x then c else 0) + (if a ∈ xs then c else 0)) := by
      intro a _
      by_cases hax : a = x
      · subst hax
        simp [hx_not]
      · have hmem : (a ∈ x :: xs) = (a ∈ xs) := by simp [List.mem_cons, hax]
        simp [hmem, hax]
    have hCong : sumOver accts (fun a => if a ∈ x :: xs then c else 0)
        = sumOver accts (fun a => (if a = x then c else 0) + (if a ∈ xs then c else 0)) :=
      sumOver_congr accts _ _ hPoint
    rw [hCong, sumOver_add, sumOver_ite_eq hNodAccts x c, if_pos hx_mem, ih']
    have hLen : ((((x :: xs).length : Nat) : Int)) = (xs.length : Int) + 1 := by simp
    rw [hLen, Int.add_mul, Int.one_mul, Int.add_comm]

private theorem fee_le_amount (bps amount : Nat) (hBps : bps ≤ 10000) :
    feeOf bps amount ≤ amount := by
  unfold feeOf
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hBps
  have hEq : amount * 10000 = amount * bps + amount * d := by
    rw [hd, Nat.mul_add]
  have hMul : amount * bps ≤ amount * 10000 := by
    rw [hEq]
    exact Nat.le_add_right _ _
  have h1 : 10000 * (amount * bps / 10000) ≤ amount * bps := by
    have hle : 10000 * (amount * bps / 10000)
        ≤ 10000 * (amount * bps / 10000) + amount * bps % 10000 :=
      Nat.le_add_right _ _
    rw [Nat.div_add_mod] at hle
    exact hle
  have hDivLe : (amount * bps / 10000) * 10000 ≤ amount * bps := by
    rw [Nat.mul_comm]
    exact h1
  have hLeMul : (amount * bps / 10000) * 10000 ≤ amount * 10000 :=
    Nat.le_trans hDivLe hMul
  omega

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hE := step_ok s r h
  rw [hE]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hE := step_rej s r h
  rw [hE]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hauth, _, _⟩ := hv
    exact hauth
  · have hstep := step_rej s r hv
    rw [hstep] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hE := step_ok s r hv
    rw [hE]
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro a
    rfl
  · have hstep := step_rej s r hv
    rw [hstep] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hE := step_ok s r hv
    have hSnd : (step s r).2 = nextState s r := by rw [hE]
    have hApp : (step s r).2.applied = r.txId :: s.applied := by rw [hSnd]; rfl
    refine ⟨?_, ?_⟩
    · intro x
      rw [hApp]
      simp
    · have hMem : r.txId ∈ (step s r).2.applied := by rw [hApp]; exact List.mem_cons_self
      have hInvalid : ¬ ValidPayout (step s r).2 r := by
        intro h2
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hFresh2⟩ := h2
        exact hFresh2 hMem
      have hStep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
        have := step_rej (step s r).2 r hInvalid
        rw [this]
      exact hStep2
  · have hstep := step_rej s r hv
    rw [hstep] at hok
    simp at hok

theorem req_nonnegative : NonNegative step := by
  intro s r hNonneg a ha
  by_cases hv : ValidPayout s r
  · have hE := step_ok s r hv
    obtain ⟨hNodup, hBps, hPos, hNe, hNodupR, hSrcNot, hFeeNot, hFeeNe, hSrcMem, hFeeMem, hSub, hAuth, hBalLe, hFresh⟩ := hv
    have hSnd : (step s r).2 = nextState s r := by rw [hE]
    have hAccEq : (step s r).2.accounts = s.accounts := by rw [hSnd]; rfl
    have ha' : a ∈ s.accounts := by rw [← hAccEq]; exact ha
    have hOld : 0 ≤ s.balance a := hNonneg a ha'
    have hBal : (step s r).2.balance a = s.balance a
        - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
        + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by
      rw [hSnd]; rfl
    rw [hBal]
    by_cases hSrc : a = r.source
    · have hNotRec : a ∉ r.recipients := by rw [hSrc]; exact hSrcNot
      have hNotFee : ¬ (a = s.feeAccount) := by
        intro heq
        rw [hSrc] at heq
        exact hFeeNe heq.symm
      have e1 : (if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := if_pos hSrc
      have e2 : (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
        if_neg hNotRec
      have e3 : (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
        if_neg hNotFee
      rw [e1, e2, e3]
      have hLe : (r.amount : Int) ≤ s.balance a := by rw [hSrc]; exact hBalLe
      omega
    · by_cases hRec : a ∈ r.recipients
      · have hNotFee : ¬ (a = s.feeAccount) := by
          intro heq
          rw [heq] at hRec
          exact hFeeNot hRec
        have e1 : (if a = r.source then (r.amount : Int) else 0) = 0 := if_neg hSrc
        have e2 : (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
            = (recipientShare s.feeBps r.amount r.recipients.length : Int) := if_pos hRec
        have e3 : (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
          if_neg hNotFee
        rw [e1, e2, e3]
        omega
      · by_cases hFee : a = s.feeAccount
        · have e1 : (if a = r.source then (r.amount : Int) else 0) = 0 := if_neg hSrc
          have e2 : (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
            if_neg hRec
          have e3 : (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
              = (feeCredit s.feeBps r.amount r.recipients.length : Int) := if_pos hFee
          rw [e1, e2, e3]
          omega
        · have e1 : (if a = r.source then (r.amount : Int) else 0) = 0 := if_neg hSrc
          have e2 : (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
            if_neg hRec
          have e3 : (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
            if_neg hFee
          rw [e1, e2, e3]
          simpa using hOld
  · have hstep := step_rej s r hv
    have hSndEq : (step s r).2 = s := by rw [hstep]
    have ha' : a ∈ s.accounts := by
      have : a ∈ (step s r).2.accounts := ha
      rw [hSndEq] at this
      exact this
    rw [hSndEq]
    exact hNonneg a ha'

theorem req_equal_shares : EqualShares step := by
  intro s r hok x hx
  by_cases hv : ValidPayout s r
  · have hE := step_ok s r hv
    obtain ⟨_, _, _, _, _, hSrcNot, hFeeNot, _, _, _, _, _, _, _⟩ := hv
    have hSnd : (step s r).2 = nextState s r := by rw [hE]
    have hSrcNe : ¬ (x = r.source) := fun heq => hSrcNot (heq ▸ hx)
    have hFeeNe' : ¬ (x = s.feeAccount) := fun heq => hFeeNot (heq ▸ hx)
    have hBal : (step s r).2.balance x = s.balance x
        - (if x = r.source then (r.amount : Int) else 0)
        + (if x ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
        + (if x = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by
      rw [hSnd]; rfl
    rw [hBal]
    have e1 : (if x = r.source then (r.amount : Int) else 0) = 0 := if_neg hSrcNe
    have e2 : (if x ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
        = (recipientShare s.feeBps r.amount r.recipients.length : Int) := if_pos hx
    have e3 : (if x = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
      if_neg hFeeNe'
    rw [e1, e2, e3]
    omega
  · have hstep := step_rej s r hv
    rw [hstep] at hok
    simp at hok

theorem req_fee_collected : FeeCollected step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hE := step_ok s r hv
    obtain ⟨_, _, _, _, hNodupR, hSrcNot, hFeeNot, hFeeNe, _, _, _, _, _, _⟩ := hv
    have hSnd : (step s r).2 = nextState s r := by rw [hE]
    have hSrcNe : ¬ (s.feeAccount = r.source) := fun heq => hFeeNe heq
    have hNotRec : s.feeAccount ∉ r.recipients := hFeeNot
    have hBal : (step s r).2.balance s.feeAccount = s.balance s.feeAccount
        - (if s.feeAccount = r.source then (r.amount : Int) else 0)
        + (if s.feeAccount ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
        + (if s.feeAccount = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by
      rw [hSnd]; rfl
    rw [hBal]
    have e1 : (if s.feeAccount = r.source then (r.amount : Int) else 0) = 0 := if_neg hSrcNe
    have e2 : (if s.feeAccount ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0) = 0 :=
      if_neg hNotRec
    have e3 : (if s.feeAccount = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)
        = (feeCredit s.feeBps r.amount r.recipients.length : Int) := if_pos rfl
    rw [e1, e2, e3]
    omega
  · have hstep := step_rej s r hv
    rw [hstep] at hok
    simp at hok

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hv : ValidPayout s r
  · have hE := step_ok s r hv
    obtain ⟨hNodup, hBps, hPos, hNe, hNodupR, hSrcNot, hFeeNot, hFeeNe, hSrcMem, hFeeMem, hSub, hAuth, hBalLe, hFresh⟩ := hv
    have hSnd : (step s r).2 = nextState s r := by rw [hE]
    have hAccEq : (step s r).2.accounts = s.accounts := by rw [hSnd]; rfl
    have hBalEq : ∀ a, (step s r).2.balance a = s.balance a
        - (if a = r.source then (r.amount : Int) else 0)
        + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
        + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0) := by
      intro a
      rw [hSnd]; rfl
    have hFeeLe : feeOf s.feeBps r.amount ≤ r.amount := fee_le_amount s.feeBps r.amount hBps
    have hAddCancel : feeOf s.feeBps r.amount + (r.amount - feeOf s.feeBps r.amount) = r.amount :=
      Nat.add_sub_cancel' hFeeLe
    have hKeyNat : r.recipients.length * recipientShare s.feeBps r.amount r.recipients.length
        + feeCredit s.feeBps r.amount r.recipients.length = r.amount := by
      unfold recipientShare feeCredit netOf
      have hDivMod := Nat.div_add_mod (r.amount - feeOf s.feeBps r.amount) r.recipients.length
      omega
    have hKeyInt : (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int)
        + (feeCredit s.feeBps r.amount r.recipients.length : Int) = (r.amount : Int) := by
      have hNatCast := congrArg (fun n : Nat => (n : Int)) hKeyNat
      simp at hNatCast
      exact hNatCast
    have hSumSrc : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0))
        = (r.amount : Int) := by
      have h := sumOver_ite_eq hNodup r.source (r.amount : Int)
      simp [hSrcMem] at h
      exact h
    have hSumFee : sumOver s.accounts (fun a => (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0))
        = (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
      have h := sumOver_ite_eq hNodup s.feeAccount (feeCredit s.feeBps r.amount r.recipients.length : Int)
      simp [hFeeMem] at h
      exact h
    have hSumRec : sumOver s.accounts (fun a => (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0))
        = (r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int) :=
      sumOver_mem_eq s.accounts r.recipients _ hNodup hNodupR hSub
    have hTotalEq : total (step s r).2
        = sumOver s.accounts (fun a => s.balance a
          - (if a = r.source then (r.amount : Int) else 0)
          + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
          + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) := by
      unfold total
      rw [hAccEq]
      apply sumOver_congr
      intro a _
      exact hBalEq a
    rw [hTotalEq]
    have hDecomp : sumOver s.accounts (fun a => s.balance a
          - (if a = r.source then (r.amount : Int) else 0)
          + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
          + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0))
        = total s - (r.amount : Int)
          + ((r.recipients.length : Int) * (recipientShare s.feeBps r.amount r.recipients.length : Int))
          + (feeCredit s.feeBps r.amount r.recipients.length : Int) := by
      have e1 : (fun a => s.balance a
            - (if a = r.source then (r.amount : Int) else 0)
            + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
            + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0))
          = (fun a => ((s.balance a - (if a = r.source then (r.amount : Int) else 0))
            + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0))
            + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)) := by
        funext a
        omega
      rw [e1]
      have e2 := sumOver_add s.accounts
        (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0))
        (fun a => (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0))
      have e3 := sumOver_add s.accounts
        (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        (fun a => (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0))
      have e4 := sumOver_sub s.accounts s.balance (fun a => (if a = r.source then (r.amount : Int) else 0))
      rw [e2, e3, e4, hSumSrc, hSumRec, hSumFee]
      unfold total
      omega
    rw [hDecomp]
    omega
  · have hstep := step_rej s r hv
    rw [hstep] at hok
    simp at hok

end FeePayout
