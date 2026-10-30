import ProofForgeFin.Ledger
import ProofForgeFin.Trading.Basic
/-!
# Multilateral settlement netting

A clearing house or a central securities depository does not settle each obligation of a trading
day separately. It computes, for every party, the net amount the party receives (positive) or
pays (negative) over all its obligations, and settles one amount per party. The net settlement
must move exactly what gross settlement moves: every party ends with the same balance, the net
amounts add up to zero (money is neither created nor destroyed by netting), and less money
moves than under gross settlement.

* `netOf ms k`: the net amount party `k` receives over the obligations `ms` (`Ledger.Move`:
  payer `src`, payee `dst`, amount).
* `settleNet bal ms`: balances after crediting every party with its net amount.
* `ccpMoves ccp parties ms`: the settlement instructions of a central counterparty `ccp` that
  pays every party its net amount (a negative amount is a payment to the counterparty).
* `Trade`: a trade of `qty` units at price `px` between a buyer and a seller; `cashMove` and
  `secMove` are its two legs (delivery versus payment), `netCash` and `netSec` the nets.

The theorems:

* `applyMoves_eq_add_netOf`, `applyMoves_eq_settleNet`: gross settlement in any order equals net
  settlement, account by account, with no hypothesis on the parties.
* `sumOver_netOf`: over a duplicate-free list of parties that contains the payer and payee of
  every obligation, the net amounts sum to zero.
* `sumOver_pos_netOf_le`: with nonnegative amounts, the net amounts received add up to at most
  the gross amount of the obligations; `sumOver_pos_eq_sumOver_neg`: what the net receivers get is
  what the net payers pay.
* `applyMoves_ccpMoves`, `applyMoves_ccpMoves_ccp`: settling through a central counterparty with
  one instruction per party gives every party its gross-settlement balance and leaves the
  counterparty flat.
* The same three facts for the cash and securities legs of a list of trades.

Amounts are `Int`, as in `ProofForgeFin.Ledger`; balances may be negative (overdrafts, short
positions in a securities account).
-/

namespace ProofForgeFin.Trading.Netting

open ProofForgeFin.Ledger

universe u v

variable {κ : Type u} [DecidableEq κ]

/-! ## Net amounts -/

/-- The amount party `k` receives from one obligation: the amount if `k` is the payee, minus the
amount if `k` is the payer (zero for an obligation of a party to itself). -/
def moveNet (m : Move κ) (k : κ) : Int :=
  (if k = m.dst then m.amount else 0) - (if k = m.src then m.amount else 0)

/-- The net amount party `k` receives over the obligations `ms`. -/
def netOf (ms : List (Move κ)) (k : κ) : Int := sumOver ms (fun m => moveNet m k)

/-- No obligations, no net amount. -/
@[simp] theorem netOf_nil (k : κ) : netOf ([] : List (Move κ)) k = 0 := rfl

/-- The net amount over `m :: ms` is the amount from `m` plus the net amount over `ms`. -/
@[simp] theorem netOf_cons (m : Move κ) (ms : List (Move κ)) (k : κ) :
    netOf (m :: ms) k = moveNet m k + netOf ms k := rfl

/-- The net amount over a concatenation is the sum of the net amounts. -/
theorem netOf_append (ms ms' : List (Move κ)) (k : κ) :
    netOf (ms ++ ms') k = netOf ms k + netOf ms' k := by
  unfold netOf; rw [sumOver_append]

/-- The sum over a mapped list is the sum of the composed function. -/
theorem sumOver_map {α : Type v} {β : Type v} (l : List α) (g : α → β) (f : β → Int) :
    sumOver (l.map g) f = sumOver l (fun a => f (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- A transfer changes the balance of `k` by the amount `k` receives from the obligation. -/
theorem transfer_eq_add_moveNet (bal : κ → Int) (m : Move κ) (k : κ) :
    transfer bal m.src m.dst m.amount k = bal k + moveNet m k := by
  unfold transfer moveNet; omega

/-! ## Gross settlement equals net settlement -/

/-- Gross settlement of the obligations in order changes the balance of every party by exactly
its net amount. -/
theorem applyMoves_eq_add_netOf (bal : κ → Int) (ms : List (Move κ)) (k : κ) :
    applyMoves bal ms k = bal k + netOf ms k := by
  induction ms generalizing bal with
  | nil => simp [applyMoves, Seq.run]
  | cons m ms ih =>
    show applyMoves (transfer bal m.src m.dst m.amount) ms k = _
    rw [ih, transfer_eq_add_moveNet, netOf_cons]; omega

/-- Balances after crediting every party with its net amount. -/
def settleNet (bal : κ → Int) (ms : List (Move κ)) : κ → Int := fun k => bal k + netOf ms k

/-- Net settlement leaves every party with the balance gross settlement leaves it. -/
theorem applyMoves_eq_settleNet (bal : κ → Int) (ms : List (Move κ)) :
    applyMoves bal ms = settleNet bal ms := by
  funext k; exact applyMoves_eq_add_netOf bal ms k

/-- Gross settlement in two different orders gives the same balances when the two lists have the
same net amounts; in particular the order of the obligations does not matter. -/
theorem applyMoves_eq_of_netOf_eq (bal : κ → Int) {ms ms' : List (Move κ)}
    (h : ∀ k, netOf ms k = netOf ms' k) : applyMoves bal ms = applyMoves bal ms' := by
  funext k; rw [applyMoves_eq_add_netOf, applyMoves_eq_add_netOf, h]

/-- Net amounts do not depend on the order of the obligations. -/
theorem netOf_perm {ms ms' : List (Move κ)} (h : ms.Perm ms') (k : κ) :
    netOf ms k = netOf ms' k := by
  induction h with
  | nil => rfl
  | cons m _ ih => simp [ih]
  | swap a b l => simp; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Net amounts sum to zero -/

/-- Over a duplicate-free list of parties containing the payer and payee of every obligation,
the net amounts sum to zero. -/
theorem sumOver_netOf {l : List κ} (hl : l.Nodup) {ms : List (Move κ)}
    (h : ∀ m ∈ ms, m.src ∈ l ∧ m.dst ∈ l) : sumOver l (netOf ms) = 0 := by
  have e : netOf ms = applyMoves (fun _ => 0) ms := by
    funext k; rw [applyMoves_eq_add_netOf]; omega
  rw [e, sumOver_applyMoves hl _ h, sumOver_zero]

/-! ## Netting reduces what moves -/

/-- The positive part of an integer. -/
def pos (a : Int) : Int := max a 0

/-- The negative part of an integer, as a nonnegative number. -/
def neg (a : Int) : Int := max (-a) 0

/-- An integer is its positive part minus its negative part. -/
theorem pos_sub_neg (a : Int) : pos a - neg a = a := by unfold pos neg; omega

/-- The positive part of a sum is at most the sum of the positive parts. -/
theorem pos_add_le (a b : Int) : pos (a + b) ≤ pos a + pos b := by unfold pos; omega

/-- What the net receivers receive is what the net payers pay: over a duplicate-free list of
parties containing every payer and payee, the positive net amounts and the negative net amounts
have the same total. -/
theorem sumOver_pos_eq_sumOver_neg {l : List κ} (hl : l.Nodup) {ms : List (Move κ)}
    (h : ∀ m ∈ ms, m.src ∈ l ∧ m.dst ∈ l) :
    sumOver l (fun k => pos (netOf ms k)) = sumOver l (fun k => neg (netOf ms k)) := by
  have h0 := sumOver_netOf hl h
  have e : sumOver l (netOf ms) =
      sumOver l (fun k => pos (netOf ms k)) - sumOver l (fun k => neg (netOf ms k)) := by
    rw [← sumOver_sub]; exact sumOver_congr l (fun k _ => (pos_sub_neg _).symm)
  omega

/-- The gross amount of a list of obligations. -/
def gross (ms : List (Move κ)) : Int := sumOver ms (fun m => m.amount)

/-- With nonnegative amounts, the net amounts received by the parties of a duplicate-free list add
up to at most the gross amount: netting never moves more money than gross settlement. -/
theorem sumOver_pos_netOf_le {l : List κ} (hl : l.Nodup) {ms : List (Move κ)}
    (h : ∀ m ∈ ms, 0 ≤ m.amount) : sumOver l (fun k => pos (netOf ms k)) ≤ gross ms := by
  induction ms with
  | nil => simp [gross, pos]
  | cons m ms ih =>
    have ih' := ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))
    have hm := h m (by simp)
    have h1 : sumOver l (fun k => pos (netOf (m :: ms) k)) ≤
        sumOver l (fun k => pos (moveNet m k)) + sumOver l (fun k => pos (netOf ms k)) := by
      rw [← sumOver_add]
      exact sumOver_le_sumOver l (fun k _ => by rw [netOf_cons]; exact pos_add_le _ _)
    have h2 : sumOver l (fun k => pos (moveNet m k)) ≤
        sumOver l (fun k => if k = m.dst then m.amount else 0) := by
      apply sumOver_le_sumOver l
      intro k _
      unfold pos moveNet
      split <;> split <;> omega
    have h3 := sumOver_ite_eq hl m.dst m.amount
    have h4 : (if m.dst ∈ l then m.amount else 0) ≤ m.amount := by split <;> omega
    simp only [gross, sumOver_cons] at ih' ⊢
    omega

/-! ## Settlement through a central counterparty -/

/-- The instructions of a central counterparty `ccp` that settles the net amounts of `ms`: one
transfer per party of `parties`, from `ccp` to the party, of the party's net amount (a negative
amount is a payment from the party to `ccp`). -/
def ccpMoves (ccp : κ) (parties : List κ) (ms : List (Move κ)) : List (Move κ) :=
  parties.map (fun k => ⟨ccp, k, netOf ms k⟩)

/-- The net amount of a party under the counterparty's instructions. -/
theorem netOf_ccpMoves (ccp : κ) {parties : List κ} (hl : parties.Nodup) (ms : List (Move κ))
    (k : κ) :
    netOf (ccpMoves ccp parties ms) k =
      (if k ∈ parties then netOf ms k else 0) -
        (if k = ccp then sumOver parties (netOf ms) else 0) := by
  show sumOver (parties.map _) (fun m => moveNet m k) = _
  rw [sumOver_map]
  have e : ∀ p, moveNet (⟨ccp, p, netOf ms p⟩ : Move κ) k =
      (if p = k then netOf ms k else 0) - (if k = ccp then netOf ms p else 0) := by
    intro p
    unfold moveNet
    by_cases hp : p = k
    · subst hp; simp
    · simp [hp, Ne.symm hp]
  have e2 : sumOver parties (fun p => if k = ccp then netOf ms p else 0) =
      if k = ccp then sumOver parties (netOf ms) else 0 := by
    by_cases hk : k = ccp
    · simp [hk]
    · simp [hk]
  rw [sumOver_congr parties (fun p _ => e p), sumOver_sub, sumOver_ite_eq hl, e2]

/-- Settling through a central counterparty that is not one of the parties gives every party
the balance gross settlement gives it. -/
theorem applyMoves_ccpMoves (bal : κ → Int) {ccp : κ} {parties : List κ} (hl : parties.Nodup)
    (hccp : ccp ∉ parties) (ms : List (Move κ)) {k : κ} (hk : k ∈ parties) :
    applyMoves bal (ccpMoves ccp parties ms) k = applyMoves bal ms k := by
  have hne : k ≠ ccp := fun e => hccp (e ▸ hk)
  rw [applyMoves_eq_add_netOf, applyMoves_eq_add_netOf, netOf_ccpMoves ccp hl]
  simp [hk, hne]

/-- When the parties include every payer and payee, the central counterparty ends with the
balance it started with: it pays out exactly what it collects. -/
theorem applyMoves_ccpMoves_ccp (bal : κ → Int) {ccp : κ} {parties : List κ}
    (hl : parties.Nodup) (hccp : ccp ∉ parties) {ms : List (Move κ)}
    (h : ∀ m ∈ ms, m.src ∈ parties ∧ m.dst ∈ parties) :
    applyMoves bal (ccpMoves ccp parties ms) ccp = bal ccp := by
  rw [applyMoves_eq_add_netOf, netOf_ccpMoves ccp hl, sumOver_netOf hl h]
  simp [hccp]

/-- The counterparty's instructions settle one amount per party. -/
theorem length_ccpMoves (ccp : κ) (parties : List κ) (ms : List (Move κ)) :
    (ccpMoves ccp parties ms).length = parties.length := by
  simp [ccpMoves]

/-! ## Delivery versus payment -/

/-- A trade of `qty` units at price `px` per unit between a buyer and a seller. -/
structure Trade (κ : Type u) where
  /-- The party that receives the securities and pays cash. -/
  buyer : κ
  /-- The party that delivers the securities and receives cash. -/
  seller : κ
  /-- The number of units traded. -/
  qty : Nat
  /-- The price per unit. -/
  px : Nat

/-- The cash leg of a trade: the buyer pays `qty * px` to the seller. -/
def cashMove (t : Trade κ) : Move κ := ⟨t.buyer, t.seller, (t.qty * t.px : Nat)⟩

/-- The securities leg of a trade: the seller delivers `qty` units to the buyer. -/
def secMove (t : Trade κ) : Move κ := ⟨t.seller, t.buyer, (t.qty : Nat)⟩

/-- The net cash party `k` receives over the trades `ts`. -/
def netCash (ts : List (Trade κ)) (k : κ) : Int := netOf (ts.map cashMove) k

/-- The net units party `k` receives over the trades `ts`. -/
def netSec (ts : List (Trade κ)) (k : κ) : Int := netOf (ts.map secMove) k

/-- The net cash of a party: the proceeds of its sales minus the cost of its purchases. -/
theorem netCash_eq (ts : List (Trade κ)) (k : κ) :
    netCash ts k = sumOver ts (fun t =>
      (if k = t.seller then ((t.qty * t.px : Nat) : Int) else 0) -
        (if k = t.buyer then ((t.qty * t.px : Nat) : Int) else 0)) := by
  unfold netCash netOf; rw [sumOver_map]; rfl

/-- The net units of a party: the units it bought minus the units it sold. -/
theorem netSec_eq (ts : List (Trade κ)) (k : κ) :
    netSec ts k = sumOver ts (fun t =>
      (if k = t.buyer then (t.qty : Int) else 0) - (if k = t.seller then (t.qty : Int) else 0)) := by
  unfold netSec netOf; rw [sumOver_map]; rfl

/-- The parties of every trade are in the list `l`. -/
def TradesIn (l : List κ) (ts : List (Trade κ)) : Prop := ∀ t ∈ ts, t.buyer ∈ l ∧ t.seller ∈ l

/-- Net cash sums to zero over the parties. -/
theorem sumOver_netCash {l : List κ} (hl : l.Nodup) {ts : List (Trade κ)} (h : TradesIn l ts) :
    sumOver l (netCash ts) = 0 := by
  apply sumOver_netOf hl
  intro m hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  exact ⟨(h t ht).1, (h t ht).2⟩

/-- Net units sum to zero over the parties. -/
theorem sumOver_netSec {l : List κ} (hl : l.Nodup) {ts : List (Trade κ)} (h : TradesIn l ts) :
    sumOver l (netSec ts) = 0 := by
  apply sumOver_netOf hl
  intro m hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  exact ⟨(h t ht).2, (h t ht).1⟩

/-- Settling the cash legs gross leaves every party with its balance plus its net cash. -/
theorem applyMoves_cash (bal : κ → Int) (ts : List (Trade κ)) (k : κ) :
    applyMoves bal (ts.map cashMove) k = bal k + netCash ts k :=
  applyMoves_eq_add_netOf bal _ k

/-- Settling the securities legs gross leaves every party with its holding plus its net units. -/
theorem applyMoves_sec (hold : κ → Int) (ts : List (Trade κ)) (k : κ) :
    applyMoves hold (ts.map secMove) k = hold k + netSec ts k :=
  applyMoves_eq_add_netOf hold _ k

/-- The total cash over the parties is the same after settlement. -/
theorem sumOver_applyMoves_cash {l : List κ} (hl : l.Nodup) (bal : κ → Int)
    {ts : List (Trade κ)} (h : TradesIn l ts) :
    sumOver l (applyMoves bal (ts.map cashMove)) = sumOver l bal := by
  apply sumOver_applyMoves hl
  intro m hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  exact ⟨(h t ht).1, (h t ht).2⟩

/-- The total units over the parties is the same after settlement. -/
theorem sumOver_applyMoves_sec {l : List κ} (hl : l.Nodup) (hold : κ → Int)
    {ts : List (Trade κ)} (h : TradesIn l ts) :
    sumOver l (applyMoves hold (ts.map secMove)) = sumOver l hold := by
  apply sumOver_applyMoves hl
  intro m hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  exact ⟨(h t ht).2, (h t ht).1⟩

end ProofForgeFin.Trading.Netting
