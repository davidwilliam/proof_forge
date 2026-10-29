import Solution
/-!
Kernel-checked refutation of the Proposal 62 port (`candidate/Solution.lean`, also
`attacks/p62_port.lean`) on a claim made on mainnet 139 blocks after the upgrade: transaction
0xc9244e5349f49f3b74a54a882e71f1ca11ba14ed74f73bf2cd091ed8be2b0001 (block 13322937,
2021-09-29), `claimComp(0xf3f5C252e8ACd60671f92c7F72cf33661221Ef42, [cSUSHI, cETH])`.

Values read from mainnet at block 13322797 (the last block before the upgrade) and checked
again at block 13322936:
* cSUSHI (0x4B0181102A0112A2ef11AbEE5563bb4a3176c9d7): `compBorrowState` index 0 and block
  13322577, `compSupplyState` index 0 and block 13320900, `compSpeeds` 0. After the upgrade
  both indices are 1e36 and both speeds are 0.
* The account: `compBorrowerIndex` 0, `compAccrued` 0, `borrowBalanceStored`
  19192199818109949449525 at a cToken `borrowIndex` of 1011323718759163337, so its borrow
  units are 19192199818109949449525 * 1e18 / 1011323718759163337 = 18977306140567618322762.
* The Comptroller held 300514463598935139440340 COMP-wei (300,514.46 COMP) before the upgrade.

On chain the transaction emitted `DistributedBorrowerComp(cSUSHI, account,
18977306140567618322762, 1e36)` and transferred the account 18,977.35 COMP, of which
18977306140567618322762 came from cSUSHI (the rest is its cETH supply rewards). The cETH market
is not modelled; this file models cSUSHI only.
-/
open CompRewards

instance (s : St) (who : Account) (s' : St) : Decidable (BorrowDistributed s who s') := by
  unfold BorrowDistributed; infer_instance

instance (s : St) (who : Account) (s' : St) : Decidable (SupplyDistributed s who s') := by
  unfold SupplyDistributed; infer_instance

def holder : Acct :=
  { supply := 0, borrow := 18977306140567618322762, supplierIndex := 0, borrowerIndex := 0,
    accrued := 0, wallet := 0 }

def cSUSHI : Legacy :=
  { blockNumber := 13322798, compSpeed := 0, supplyIndex := 0, supplyBlock := 13320900,
    borrowIndex := 0, borrowBlock := 13322577, supplyStart := 0, borrowStart := 0,
    reserve := 300514463598935139440340, accts := [holder] }

/-- 139 blocks pass, then the account claims. -/
def claimTx : List Op := [.advance 139, .claim 0]

theorem wf : cSUSHI.WellFormed := by decide

/-- Nothing was owed at the upgrade and nothing was emitted since. -/
theorem nothing_owed_or_emitted :
    cSUSHI.owed = 0 ∧ cSUSHI.owedTo 0 = 0 ∧ emitted (0, 0) claimTx = 0 := by decide

/-- The port pays the account 18977306140567618322762 COMP-wei, out of the Comptroller's COMP. -/
theorem port_pays :
    ((run comptroller (upgrade cSUSHI) claimTx).acct 0).wallet = 18977306140567618322762 ∧
    (run comptroller (upgrade cSUSHI) claimTx).reserve =
      300514463598935139440340 - 18977306140567618322762 := by decide

theorem port_refuted_rewards_bounded : ¬ RewardsBounded comptroller := by
  intro h
  have := h cSUSHI claimTx wf
  revert this
  decide

theorem port_refuted_account_bounded : ¬ AccountBounded comptroller := by
  intro h
  have := h cSUSHI claimTx 0 wf
  revert this
  decide

/-- The state just before the claim. -/
def beforeClaim : St := run comptroller (upgrade cSUSHI) [.advance 139]

theorem borrow_hook_some : (comptroller beforeClaim (.borrowHook 0)).isSome := by decide

/-- The borrow hook (`borrowAllowed` or `repayBorrowAllowed`) credits the account
18977306140567618322762, where REQ-BORROW-HOOK requires 0: its start is `compInitialIndex`
because the market index has reached it, and the index has not moved. -/
theorem port_refuted_borrow_hook : ¬ BorrowHookEffects comptroller := by
  intro h
  have hs : comptroller beforeClaim (.borrowHook 0) =
      some ((comptroller beforeClaim (.borrowHook 0)).get borrow_hook_some) :=
    (Option.some_get borrow_hook_some).symm
  have := h _ _ _ hs
  revert this
  decide

theorem claim_some : (comptroller beforeClaim (.claim 0)).isSome := by decide

theorem port_refuted_claim : ¬ ClaimEffects comptroller := by
  intro h
  have hs : comptroller beforeClaim (.claim 0) =
      some ((comptroller beforeClaim (.claim 0)).get claim_some) :=
    (Option.some_get claim_some).symm
  obtain ⟨m₁, m₂, h1, h2, h3⟩ := h _ _ _ hs
  obtain ⟨-, -, e1⟩ := h1
  obtain ⟨-, -, e2⟩ := h2
  subst e1; subst e2
  revert h3
  decide
