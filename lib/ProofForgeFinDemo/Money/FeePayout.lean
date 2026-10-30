import ProofForgeFin
/-!
# Demonstration: the fee arithmetic of `payouts-fee-b1` with the library

The definitions `feeOf`, `netOf`, `recipientShare` and `feeCredit` are copied without change
from `tasks/payouts-fee-b1/spec/FeePayout/Spec.lean`. The task files are not imported or
modified.

The reference solution (`reference/SolutionA.lean`) proves `fee_le` (a fee at no more than
10000 basis points is at most the amount) and `split_sum` (the recipients' equal shares and the
fee account's credit add up to the amount, the arithmetic of REQ-CONSERVATION) from
`Nat.div_le_of_le_mul` and `Nat.div_add_mod` (13 lines). Here `feeOf` is the library's
`bpsFee` by definition, `fee_le` is `Money.feeDown_le`, and `split_sum` combines
`Money.feeDown_add_net` with `Nat.div_add_mod`. The library adds what the reference does not
state: the net amount is itself a rounded percentage (`net_eq`), monotone in the gross
(`net_mono`), and the fee changes by at most one cent when a payment is split (`fee_split`).
-/

namespace ProofForgeFinDemo.Money.FeePayout

/-! ## Copied from `spec/FeePayout/Spec.lean` -/

/-- Platform fee on `amount` at `bps` basis points, rounded down. -/
def feeOf (bps amount : Nat) : Nat := amount * bps / 10000

/-- The part of `amount` left for the recipients after the fee. -/
def netOf (bps amount : Nat) : Nat := amount - feeOf bps amount

/-- Each of `n` recipients receives the net amount divided by `n`, rounded down. -/
def recipientShare (bps amount n : Nat) : Nat := netOf bps amount / n

/-- The fee account receives the fee plus the cents left over from the equal split. -/
def feeCredit (bps amount n : Nat) : Nat := feeOf bps amount + netOf bps amount % n

/-! ## The task's fee is the library's -/

/-- The task's fee is the library's basis-point fee rounded down. -/
theorem feeOf_eq (bps amount : Nat) : feeOf bps amount = ProofForgeFin.Money.bpsFee bps amount := rfl

/-! ## The two arithmetic facts of the reference solution -/

/-- `fee_le` of the reference: `Money.feeDown_le`. -/
theorem fee_le (bps amount : Nat) (h : bps ≤ 10000) : feeOf bps amount ≤ amount :=
  ProofForgeFin.Money.feeDown_le 10000 amount h

/-- `split_sum` of the reference: the equal shares and the fee credit add up to the amount. -/
theorem split_sum (bps amount n : Nat) (h : bps ≤ 10000) :
    n * recipientShare bps amount n + feeCredit bps amount n = amount := by
  have h1 := Nat.div_add_mod (netOf bps amount) n
  have h2 : feeOf bps amount + (amount - feeOf bps amount) = amount :=
    ProofForgeFin.Money.feeDown_add_net 10000 amount h
  unfold recipientShare feeCredit netOf at *
  omega

/-! ## Facts the reference does not state -/

/-- The net is the remaining percentage rounded up. -/
theorem net_eq (bps amount : Nat) (h : bps ≤ 10000) :
    netOf bps amount = ProofForgeFin.ceilDiv (amount * (10000 - bps)) 10000 :=
  ProofForgeFin.Money.net_feeDown amount (by decide) h

/-- A larger payment never nets less. -/
theorem net_mono (bps : Nat) {a a' : Nat} (h : bps ≤ 10000) (ha : a ≤ a') : netOf bps a ≤ netOf bps a' :=
  ProofForgeFin.Money.net_feeDown_mono (by decide) h ha

/-- Splitting a payment in two lowers the fee by at most one cent and never raises it. -/
theorem fee_split (bps a b : Nat) :
    feeOf bps a + feeOf bps b ≤ feeOf bps (a + b) ∧ feeOf bps (a + b) ≤ feeOf bps a + feeOf bps b + 1 :=
  ⟨ProofForgeFin.Money.feeDown_add_le 10000 bps a b, ProofForgeFin.Money.le_feeDown_add 10000 bps a b⟩

end ProofForgeFinDemo.Money.FeePayout
