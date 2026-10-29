import CompRewards.Spec
/-!
# The requirements are not vacuous (protected, proved)

An implementation that refuses every call, or credits nothing, would meet every bound. The
success and effects requirements rule that out: `honest_rewards` shows that every
implementation meeting REQ-CALLS-SUCCEED, REQ-CLAIM and REQ-SET-SPEEDS runs this sequence with
exactly these results.

A market that never had COMP rewards (both indices 0, speed 0, as cSUSHI, cTUSD, cMKR, cAAVE,
cYFI and cSAI before Proposal 62) holds two positions from before the upgrade: account 0 has
50 cTokens and account 1 has 20 borrow units, neither with a recorded index. After the
upgrade, governance sets a supply speed of 3 and a borrow speed of 2 COMP per block, 10 blocks
pass (50 COMP emitted), and both accounts claim. Account 0 receives 30, all of the supply
emission, and account 1 receives 20, all of the borrow emission: the COMP emitted, all of it,
and nothing for the blocks before rewards were switched on. The Comptroller's COMP falls from
1000 to 950.

`upgrade_credits_nobody` states that the upgrade itself changes no account.
-/

namespace CompRewards

instance (s : St) : Decidable (Consistent s) := by unfold Consistent; infer_instance

/-- The market before the upgrade. -/
def neverRewarded : Legacy :=
  { blockNumber := 100, compSpeed := 0, supplyIndex := 0, supplyBlock := 90, borrowIndex := 0,
    borrowBlock := 90, supplyStart := 0, borrowStart := 0, reserve := 1000,
    accts := [⟨50, 0, 0, 0, 0, 0⟩, ⟨0, 20, 0, 0, 0, 0⟩] }

/-- The upgrade changes no account: balances, recorded indices, accrued COMP and wallets are
those of the pre-upgrade state. -/
theorem upgrade_credits_nobody (L : Legacy) : (upgrade L).accts = L.accts := rfl

section
variable {impl : Impl}

theorem call_some (h1 : CallsSucceed impl) (s : St) (c : Call) (hc : Consistent s) :
    ∃ s', impl s c = some s' :=
  Option.isSome_iff_exists.mp (h1 s c hc)

theorem honest_rewards (h1 : CallsSucceed impl) (h4 : ClaimEffects impl) (h5 : SetSpeedsEffects impl) :
    let s := run impl (upgrade neverRewarded) [.setSpeeds 3 2, .advance 10, .claim 0, .claim 1]
    (s.acct 0).wallet = 30 ∧ (s.acct 1).wallet = 20 ∧ (s.acct 0).accrued = 0 ∧
      (s.acct 1).accrued = 0 ∧ s.reserve = 950 ∧ s.blockNumber = 110 := by
  intro s
  -- 1. `setSpeeds 3 2`
  obtain ⟨t1, e1⟩ := call_some h1 (upgrade neverRewarded) (.setSpeeds 3 2) (by decide)
  obtain ⟨-, -, q1⟩ := h5 _ _ _ _ e1
  have r1 : exec impl (upgrade neverRewarded) (.setSpeeds 3 2) = t1 := by
    simp only [exec, e1, Option.getD_some]
  -- 2. `advance 10`
  have r2 : exec impl t1 (.advance 10) = { t1 with blockNumber := t1.blockNumber + 10 } := rfl
  -- 3. `claim 0`
  obtain ⟨t3, e3⟩ := call_some h1 { t1 with blockNumber := t1.blockNumber + 10 } (.claim 0)
    (by rw [q1]; decide)
  obtain ⟨m1, m2, ⟨-, -, q31⟩, ⟨-, -, q32⟩, q33⟩ := h4 _ _ _ e3
  have r3 : exec impl { t1 with blockNumber := t1.blockNumber + 10 } (.claim 0) = t3 := by
    simp only [exec, e3, Option.getD_some]
  -- 4. `claim 1`
  obtain ⟨t4, e4⟩ := call_some h1 t3 (.claim 1)
    (by rw [q33, q32, q31, q1]; decide)
  obtain ⟨n1, n2, ⟨-, -, q41⟩, ⟨-, -, q42⟩, q43⟩ := h4 _ _ _ e4
  have r4 : exec impl t3 (.claim 1) = t4 := by
    simp only [exec, e4, Option.getD_some]
  have hs : s = t4 := by
    show run impl (upgrade neverRewarded) _ = t4
    simp only [run, r1, r2, r3, r4]
  rw [hs, q43, q42, q41, q33, q32, q31, q1]
  decide

end

end CompRewards
