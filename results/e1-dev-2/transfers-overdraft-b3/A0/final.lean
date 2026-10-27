import Transfer.Spec
import Transfer.Lemmas
namespace Transfer

/-- Admission check for a transfer request. -/
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
  have hpos : admissible s r := h
  have hstep : step s r = (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) := by
    unfold step
    rw [if_pos hpos]
  rw [hstep]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hn : ¬ admissible s r := fun ha => h ha
  show step s r = (.rejected, s)
  unfold step
  rw [if_neg hn]

theorem req_authorization : AuthorizedOnly step := by
  intro s r hok
  have hem := Decidable.em (admissible s r)
  cases hem with
  | inl hpos =>
    exact hpos.2.2.2.2.2.1
  | inr hneg =>
    have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hneg]
    have hre : (step s r).1 = .rejected := by
      rw [hstep]
    rw [hre] at hok
    cases hok

theorem req_debit_credit : DebitCredit step := by
  intro s r hok
  have hem := Decidable.em (admissible s r)
  cases hem with
  | inl hpos =>
    have hne : r.source ≠ r.target := hpos.2.2.1
    have hne' : r.target ≠ r.source := fun hh => hne hh.symm
    have hstep : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by
      unfold step
      rw [if_pos hpos]
    constructor
    · have e : (step s r).2.balance r.source =
        s.balance r.source - (if r.source = r.source then (r.amount : Int) else 0)
        + (if r.source = r.target then (r.amount : Int) else 0) := by
        rw [hstep]
      rw [e]
      simp [hne]
    · have e : (step s r).2.balance r.target =
        s.balance r.target - (if r.target = r.source then (r.amount : Int) else 0)
        + (if r.target = r.target then (r.amount : Int) else 0) := by
        rw [hstep]
      rw [e]
      simp [hne']
  | inr hneg =>
    have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hneg]
    have hre : (step s r).1 = .rejected := by
      rw [hstep]
    rw [hre] at hok
    cases hok

theorem req_effects : Effects step := by
  intro s r hok
  have hem := Decidable.em (admissible s r)
  cases hem with
  | inl hpos =>
    have hstep : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by
      unfold step
      rw [if_pos hpos]
    have h2 : (step s r).2 = { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } := by
      rw [hstep]
    constructor
    · rw [h2]
    · constructor
      · rw [h2]
      · constructor
        · rw [h2]
        · intro a
          have e : (step s r).2.balance a =
              s.balance a - (if a = r.source then (r.amount : Int) else 0)
              + (if a = r.target then (r.amount : Int) else 0) := by
            rw [h2]
          rw [e]
          rfl
  | inr hneg =>
    have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hneg]
    have hre : (step s r).1 = .rejected := by
      rw [hstep]
    rw [hre] at hok
    cases hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hem := Decidable.em (admissible s r)
  cases hem with
  | inl hpos =>
    have hstep : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by
      unfold step
      rw [if_pos hpos]
    have h2 : (step s r).2 =
        { s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } := by
      rw [hstep]
    constructor
    · intro x
      rw [h2]
      exact List.mem_cons
    · have hmem2 : r.txId ∈ (({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State).applied) := by
        simp
      have hn2 : ¬ admissible ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) r := by
        intro hc
        exact hc.2.2.2.2.2.2.2 hmem2
      have hstep2 : step ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State) r =
          (.rejected, ({ s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } : State)) := by
        unfold step
        rw [if_neg hn2]
      rw [h2]
      exact hstep2
  | inr hneg =>
    have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hneg]
    have hre : (step s r).1 = .rejected := by
      rw [hstep]
    rw [hre] at hok
    cases hok

theorem req_limit : LimitRespected step := by
  intro s r hlim a ha
  have hem := Decidable.em (admissible s r)
  cases hem with
  | inl hpos =>
    have hne : r.source ≠ r.target := hpos.2.2.1
    have hne' : r.target ≠ r.source := fun hh => hne hh.symm
    have hamnt : 0 < r.amount := hpos.2.1
    have hamtI : (0 : Int) < (r.amount : Int) := by
      exact_mod_cast hamnt
    have hbound : -(s.limit r.source : Int) ≤ s.balance r.source - r.amount :=
      hpos.2.2.2.2.2.2.1
    have hstep : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by
      unfold step
      rw [if_pos hpos]
    have h2 : (step s r).2 =
        { s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied } := by
      rw [hstep]
    have hacc : (step s r).2.accounts = s.accounts := by
      rw [h2]
    have hlim_eq : (step s r).2.limit = s.limit := by
      rw [h2]
    have hbal_a : (step s r).2.balance a = expectedBalance s r a := by
      have e : (step s r).2.balance a =
          s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0) := by
        rw [h2]
      rw [e]
      rfl
    have ha' : a ∈ s.accounts := hacc ▸ ha
    have hlima : -(s.limit a : Int) ≤ s.balance a := hlim a ha'
    rw [hlim_eq, hbal_a]
    unfold expectedBalance
    have hem2 := Decidable.em (a = r.source)
    cases hem2 with
    | inl hasEq =>
      subst hasEq
      have h1 : (if r.source = r.source then (r.amount : Int) else 0) = (r.amount : Int) :=
        if_pos rfl
      have h2t : (if r.source = r.target then (r.amount : Int) else 0) = 0 :=
        if_neg hne
      rw [h1, h2t]
      omega
    | inr hasNe =>
      have hem3 := Decidable.em (a = r.target)
      cases hem3 with
      | inl hatEq =>
        subst hatEq
        have h1 : (if r.target = r.source then (r.amount : Int) else 0) = 0 :=
          if_neg hne'
        have h2t : (if r.target = r.target then (r.amount : Int) else 0) = (r.amount : Int) :=
          if_pos rfl
        rw [h1, h2t]
        omega
      | inr hatNe =>
        have h1 : (if a = r.source then (r.amount : Int) else 0) = 0 :=
          if_neg hasNe
        have h2t : (if a = r.target then (r.amount : Int) else 0) = 0 :=
          if_neg hatNe
        rw [h1, h2t]
        omega
  | inr hneg =>
    have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hneg]
    have h2 : (step s r).2 = s := by
      rw [hstep]
    have hacc : (step s r).2.accounts = s.accounts := by
      rw [h2]
    rw [hacc] at ha
    have hlima : -(s.limit a : Int) ≤ s.balance a := hlim a ha
    have hlim_eq : (step s r).2.limit = s.limit := by
      rw [h2]
    have hbal_a : (step s r).2.balance a = s.balance a := by
      rw [h2]
    rw [hlim_eq, hbal_a]
    exact hlima

theorem req_conservation : Conserves step := by
  intro s r hok
  have hem := Decidable.em (admissible s r)
  cases hem with
  | inl hpos =>
    have hnodup : s.accounts.Nodup := hpos.1
    have hsrcmem : r.source ∈ s.accounts := hpos.2.2.2.1
    have htgtmem : r.target ∈ s.accounts := hpos.2.2.2.2.1
    have hstep : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by
      unfold step
      rw [if_pos hpos]
    have hacc : (step s r).2.accounts = s.accounts := by
      rw [hstep]
    have hbal : ∀ b, (step s r).2.balance b = expectedBalance s r b := by
      intro b
      have h2 : (step s r).2 =
          { s with
            balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                                + (if a = r.target then (r.amount : Int) else 0),
            applied := r.txId :: s.applied } := by
        rw [hstep]
      have e : (step s r).2.balance b =
          s.balance b - (if b = r.source then (r.amount : Int) else 0)
          + (if b = r.target then (r.amount : Int) else 0) := by
        rw [h2]
      rw [e]
      rfl
    have hsrc_sum : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        = (r.amount : Int) := by
      rw [sumOver_ite_eq hnodup _ _]
      simp [hsrcmem]
    have htgt_sum : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0)
        = (r.amount : Int) := by
      rw [sumOver_ite_eq hnodup _ _]
      simp [htgtmem]
    have hsum : sumOver s.accounts (fun a => expectedBalance s r a)
        = sumOver s.accounts s.balance := by
      unfold expectedBalance
      have hadd : sumOver s.accounts
          (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
            + (if a = r.target then (r.amount : Int) else 0))
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) :=
        sumOver_add _ _ _
      rw [hadd, sumOver_sub _ _ _, hsrc_sum, htgt_sum]
      omega
    have hcongr : sumOver s.accounts ((step s r).2.balance)
        = sumOver s.accounts (fun a => expectedBalance s r a) := by
      apply sumOver_congr
      intro b _
      exact hbal b
    unfold total
    rw [hacc, hcongr, hsum]
  | inr hneg =>
    have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hneg]
    have hre : (step s r).1 = .rejected := by
      rw [hstep]
    rw [hre] at hok
    cases hok

end Transfer
