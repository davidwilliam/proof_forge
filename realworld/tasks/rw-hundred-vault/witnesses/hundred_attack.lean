import Solution
/-!
Kernel-checked refutation of the Hundred Finance hToken port (`candidate/Solution.lean`, also
`attacks/hundred_port.lean`) on the first round of the attack transaction
0x6e9ebcdebbabda04fa9f2e3bc21ea8b2e4fb4bf4f4670cb8483e2f0b2604f451 (Optimism block 90761918),
with the amounts of its Mint, Redeem and Transfer events on hWBTC. Amounts are in satoshi
(1e-8 WBTC) and 1e-8 hWBTC.

1. The market holds no shares. The attacker deposits 4 WBTC and receives 200 hWBTC.
2. It redeems all but 2 of its 20,000,000,000 share units (0.00000002 hWBTC stay
   outstanding) and gets 3.99999999 WBTC back; 1 satoshi stays in the vault.
3. It sends 500.30063816 WBTC straight to the market (a donation). One share unit is now
   worth 25,015,031,908.5 satoshi, about 250 WBTC.
4. It withdraws 500.30063815 WBTC with `redeemUnderlying`. The shares this is worth are
   50030063815 * 2 / 50030063817 = 1.99999999992; the port truncates and burns 1.

The remaining share unit is then backed by 2 satoshi instead of about 250 WBTC. On chain the
attacker had borrowed about 1,021.9 ETH from hETH against that share between steps 3 and 4.
-/
open ShareVault

def attacker : Actor := 1

/-- Steps 1 to 3. -/
def history : List Op :=
  [.call (.deposit attacker 400000000), .call (.redeem attacker 19999999998), .donate 50030063816]

/-- Step 4. -/
def attack : List Op := [.call (.withdraw attacker 50030063815)]

def before : Vault := run vault empty history
def after : Vault := run vault before attack

theorem minted_200_hwbtc :
    (run vault empty [.call (.deposit attacker 400000000)]).supply = 20000000000 := by decide

theorem before_attack :
    before.assets = 50030063817 ∧ before.supply = 2 ∧ before.balance attacker = 2 := by decide

theorem after_attack :
    after.assets = 2 ∧ after.supply = 1 ∧ after.balance attacker = 1 := by decide

/-- The withdrawal succeeds and burns one share unit for 50030063815 satoshi. -/
theorem withdraw_burns_one :
    (vault before (.withdraw attacker 50030063815)).map (·.supply) = some 1 := by decide

/-- REQ-SHARE-VALUE fails: a share was worth 50030063817 / 2 satoshi before step 4 and is
worth 2 / 1 after it, with shares outstanding throughout. -/
theorem port_refuted_share_value : ¬ ShareValueNeverFalls vault := by
  intro h
  have hv := h history attack (by decide)
  revert hv
  decide

/-- Other balances are untouched by `redeemFresh` (generic fact about the port). -/
theorem redeemFresh_frame {s s' : Vault} {r ti ai b : Nat} (h : redeemFresh s r ti ai = some s')
    (hb : b ≠ r) : s'.balance b = s.balance b := by
  unfold redeemFresh at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · cases h; simp [hb]

/-- REQ-WITHDRAW-ROUNDS-UP fails on step 4: one share unit is burned for an amount worth
1.99999999992 share units. -/
theorem withdraw_succeeds : (vault before (.withdraw attacker 50030063815)).isSome := by decide

/-- The state the withdrawal returns. -/
def withdrawn : Vault := (vault before (.withdraw attacker 50030063815)).get withdraw_succeeds

theorem port_refuted_withdraw_rounds_up : ¬ WithdrawRoundsUp vault := by
  intro h
  have hs : vault before (.withdraw attacker 50030063815) = some withdrawn :=
    (Option.some_get withdraw_succeeds).symm
  have hb : Burned before attacker 1 50030063815 withdrawn :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
     fun b hb => redeemFresh_frame (r := attacker) (ti := 0) (ai := 50030063815) hs hb⟩
  have := (h before withdrawn attacker 50030063815 1 hs hb).2.1
  revert this
  decide
