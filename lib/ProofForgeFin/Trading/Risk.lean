import ProofForgeFin.Seq
import ProofForgeFin.Trading.Basic
/-!
# Pre-trade risk controls

SEC Rule 15c3-5 (the Market Access Rule) requires a broker-dealer with market access to apply
pre-trade controls that "prevent the entry of orders that exceed appropriate pre-set credit or
capital thresholds in the aggregate for each customer" and "prevent the entry of erroneous
orders, by rejecting orders that exceed appropriate price or size parameters, on an
order-by-order basis or over a short period of time, or that indicate duplicative orders". Exchange
and broker gateways implement them as a chain of checks in front of the order entry port, plus a
kill switch that cancels open orders and blocks new ones.

This module models such a gateway and proves the properties a supervisor asks of it:

* the per-order checks: quantity (`QtyOk`), notional (`NotionalOk`), a price collar around a
  reference price in basis points (`CollarOk`, cross-multiplied, so no division and no rounding),
  a duplicate client order id check, and the aggregate credit check (`CreditOk`);
* `check`: the checks in order, returning the first failing one as a `Reject` reason;
  `check_eq_none_iff` states exactly when an order passes and `check_eq_some` that every reason
  names a failed check;
* `exposure`: the notional already executed plus the open notional (`leaves * px`) of every open
  order. `run_exposure_le`: from a state within the credit limit, every sequence of new orders,
  fills, cancels, kills and resets keeps exposure within the limit. A fill moves notional from open
  to executed (`exposure_fill`), a cancel lowers it (`exposure_cancel_le`);
* `run_sent_of_killed`: after the kill switch, in any sequence of events without a reset, no
  order is forwarded and no order is open;
* `run_sent_checked`: every forwarded order passed the per-order checks and no
  two forwarded orders share a client order id.

The generic shape of the credit argument is `run_le_of_gate`: a quantity stays within a bound
over every run when the operations that may raise it are admitted only when the result is
within the bound and every other operation does not raise it.
-/

namespace ProofForgeFin.Trading.Risk

open ProofForgeFin.Seq

universe u v

/-! ## Gates over runs -/

/-- A gate keeps a bound over every run: operations that `admits` accepts lead to states within
the bound, and every other operation does not raise the quantity. -/
theorem run_le_of_gate {σ : Type u} {α : Type v} {step : σ → α → σ} (P : σ → Nat) (B : Nat)
    (admits : σ → α → Prop) (hadmit : ∀ s a, P s ≤ B → admits s a → P (step s a) ≤ B)
    (hother : ∀ s a, ¬ admits s a → P (step s a) ≤ P s) {s : σ} (h0 : P s ≤ B) (as : List α) :
    P (run step s as) ≤ B := by
  apply run_invariant (I := fun t => P t ≤ B) _ h0
  intro t a ht
  by_cases h : admits t a
  · exact hadmit t a ht h
  · exact Nat.le_trans (hother t a h) ht

/-- The gate for partial steps whose refusals leave the state unchanged: when every successful
operation from a state within the bound leads to a state within the bound, the bound holds after
every run. -/
theorem run_skip_le_of_gate {σ : Type u} {α : Type v} {step : σ → α → Option σ} (P : σ → Nat)
    (B : Nat) (h : ∀ s a s', P s ≤ B → step s a = some s' → P s' ≤ B) {s : σ} (h0 : P s ≤ B)
    (as : List α) : P (run (skip step) s as) ≤ B :=
  run_invariant (skip_preserves (I := fun t => P t ≤ B) h) h0 as

/-! ## Limits, orders and checks -/

/-- The pre-set limits of one customer account. -/
structure Limits where
  /-- The largest quantity of a single order. -/
  maxQty : Nat
  /-- The largest notional (`qty * px`) of a single order. -/
  maxNotional : Nat
  /-- The aggregate credit threshold: executed notional plus open notional. -/
  credit : Nat
  /-- The half-width of the price collar around the reference price, in basis points. -/
  collarBps : Nat

/-- A new order presented to the gateway. -/
structure NewOrder where
  /-- The client order id (FIX `ClOrdID`). -/
  id : Nat
  /-- The limit price. -/
  px : Nat
  /-- The quantity. -/
  qty : Nat
  /-- The reference price the collar is centred on (last sale, or the midpoint of the best bid
  and offer). -/
  ref : Nat
  deriving DecidableEq, Repr

/-- An open order as the gateway tracks it: its id, price and unexecuted quantity. -/
structure Open where
  /-- The client order id. -/
  id : Nat
  /-- The limit price. -/
  px : Nat
  /-- The quantity not yet executed. -/
  leaves : Nat
  deriving DecidableEq, Repr

/-- The gateway's state for one account. -/
structure State where
  /-- The kill switch is engaged. -/
  killed : Bool
  /-- The open orders. -/
  orders : List Open
  /-- The notional executed so far. -/
  executed : Nat
  /-- Every client order id accepted so far. -/
  seen : List Nat
  /-- The orders forwarded to the market, in order. -/
  sent : List NewOrder

/-- The state of a new account: no orders, nothing executed, kill switch off. -/
def State.empty : State := ⟨false, [], 0, [], []⟩

/-- The open notional of a list of open orders: the sum of `leaves * px`. -/
def openNotional (os : List Open) : Nat := (os.map (fun o => o.leaves * o.px)).sum

/-- The aggregate exposure: notional executed plus open notional. -/
def exposure (s : State) : Nat := s.executed + openNotional s.orders

/-- The order's quantity is within the per-order limit. -/
def QtyOk (L : Limits) (o : NewOrder) : Prop := o.qty ≤ L.maxQty

/-- The order's notional is within the per-order limit. -/
def NotionalOk (L : Limits) (o : NewOrder) : Prop := o.qty * o.px ≤ L.maxNotional

/-- The order's price is within `collarBps` basis points of the reference price:
`ref * (1 - b) ≤ px ≤ ref * (1 + b)` with `b = collarBps / 10000`, cross-multiplied. -/
def CollarOk (L : Limits) (o : NewOrder) : Prop :=
  o.ref * (10000 - L.collarBps) ≤ o.px * 10000 ∧ o.px * 10000 ≤ o.ref * (10000 + L.collarBps)

/-- Accepting the order keeps the aggregate exposure within the credit threshold. -/
def CreditOk (L : Limits) (s : State) (o : NewOrder) : Prop := exposure s + o.qty * o.px ≤ L.credit

/-- The checks that depend on the order alone. -/
def PerOrderOk (L : Limits) (o : NewOrder) : Prop := QtyOk L o ∧ NotionalOk L o ∧ CollarOk L o

/-- The quantity check is decidable. -/
instance (L : Limits) (o : NewOrder) : Decidable (QtyOk L o) := by unfold QtyOk; infer_instance
/-- The notional check is decidable. -/
instance (L : Limits) (o : NewOrder) : Decidable (NotionalOk L o) := by
  unfold NotionalOk; infer_instance
/-- The price collar check is decidable. -/
instance (L : Limits) (o : NewOrder) : Decidable (CollarOk L o) := by unfold CollarOk; infer_instance
/-- The credit check is decidable. -/
instance (L : Limits) (s : State) (o : NewOrder) : Decidable (CreditOk L s o) := by
  unfold CreditOk; infer_instance

/-- Why the gateway rejects an order. -/
inductive Reject where
  /-- The kill switch is engaged. -/
  | killed
  /-- The client order id was already used. -/
  | duplicate
  /-- The quantity exceeds the per-order limit. -/
  | qty
  /-- The notional exceeds the per-order limit. -/
  | notional
  /-- The price is outside the collar. -/
  | collar
  /-- The order would take the aggregate exposure over the credit threshold. -/
  | credit
  deriving DecidableEq, Repr

/-- The checks in the order a gateway applies them; `none` when the order passes all of them,
otherwise the first failing check. -/
def check (L : Limits) (s : State) (o : NewOrder) : Option Reject :=
  if s.killed then some .killed
  else if o.id ∈ s.seen then some .duplicate
  else if ¬ QtyOk L o then some .qty
  else if ¬ NotionalOk L o then some .notional
  else if ¬ CollarOk L o then some .collar
  else if ¬ CreditOk L s o then some .credit
  else none

/-- An order passes exactly when the kill switch is off, its id is new, and the quantity,
notional, collar and credit checks hold. -/
theorem check_eq_none_iff (L : Limits) (s : State) (o : NewOrder) :
    check L s o = none ↔ s.killed = false ∧ o.id ∉ s.seen ∧ QtyOk L o ∧ NotionalOk L o ∧
      CollarOk L o ∧ CreditOk L s o := by
  unfold check
  cases s.killed <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;>
    by_cases h1 : o.id ∈ s.seen <;> by_cases h2 : QtyOk L o <;> by_cases h3 : NotionalOk L o <;>
    by_cases h4 : CollarOk L o <;> by_cases h5 : CreditOk L s o <;> simp [h1, h2, h3, h4, h5]

/-- The condition a rejection reason reports. -/
def Reject.Fails (L : Limits) (s : State) (o : NewOrder) : Reject → Prop
  | .killed => s.killed = true
  | .duplicate => o.id ∈ s.seen
  | .qty => ¬ QtyOk L o
  | .notional => ¬ NotionalOk L o
  | .collar => ¬ CollarOk L o
  | .credit => ¬ CreditOk L s o

/-- Every rejection names a check the order fails. -/
theorem check_eq_some {L : Limits} {s : State} {o : NewOrder} {r : Reject}
    (h : check L s o = some r) : r.Fails L s o := by
  unfold check at h
  split at h
  · cases h; assumption
  split at h
  · cases h; assumption
  split at h
  · cases h; assumption
  split at h
  · cases h; assumption
  split at h
  · cases h; assumption
  split at h
  · cases h; assumption
  · cases h

/-- With the kill switch engaged every order is rejected. -/
theorem check_of_killed (L : Limits) {s : State} (h : s.killed = true) (o : NewOrder) :
    check L s o = some .killed := by simp [check, h]

/-- A reused client order id is rejected (unless the kill switch already rejects the order). -/
theorem check_of_seen (L : Limits) {s : State} (hk : s.killed = false) {o : NewOrder}
    (h : o.id ∈ s.seen) : check L s o = some .duplicate := by simp [check, hk, h]

/-- An order that passes satisfies every per-order check. -/
theorem perOrderOk_of_check {L : Limits} {s : State} {o : NewOrder} (h : check L s o = none) :
    PerOrderOk L o := by
  have := (check_eq_none_iff L s o).1 h
  exact ⟨this.2.2.1, this.2.2.2.1, this.2.2.2.2.1⟩

/-! ## Events and the gateway -/

/-- Inputs to the gateway. -/
inductive Event where
  /-- A new order from the customer. -/
  | submit (o : NewOrder)
  /-- An execution report: `q` units of order `id` were executed. -/
  | fill (id q : Nat)
  /-- A cancel request (or an unsolicited cancel from the venue) for order `id`. -/
  | cancel (id : Nat)
  /-- The kill switch: cancel every open order and block new ones. -/
  | kill
  /-- Re-enable the account after a kill. -/
  | reset
  deriving DecidableEq, Repr

/-- Apply an execution report to the open orders: the first order with the id executes at most
its leaves quantity. Returns the new list and the notional executed. An unknown id executes
nothing. -/
def fillOrders (id q : Nat) : List Open → List Open × Nat
  | [] => ([], 0)
  | o :: os =>
    if o.id = id then ({ o with leaves := o.leaves - min q o.leaves } :: os, min q o.leaves * o.px)
    else ((o :: (fillOrders id q os).1), (fillOrders id q os).2)

/-- A fill moves notional from open to executed: the open notional left plus the notional
executed is the open notional before. -/
theorem openNotional_fillOrders (id q : Nat) (os : List Open) :
    openNotional (fillOrders id q os).1 + (fillOrders id q os).2 = openNotional os := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    unfold fillOrders
    split
    · simp only [openNotional, List.map_cons, List.sum_cons]
      have : (o.leaves - min q o.leaves) * o.px + min q o.leaves * o.px = o.leaves * o.px := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.min_le_right _ _)]
      omega
    · simp only [openNotional, List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- Removing the orders with a given id does not raise the open notional. -/
theorem openNotional_filter_le (p : Open → Bool) (os : List Open) :
    openNotional (os.filter p) ≤ openNotional os := by
  induction os with
  | nil => exact Nat.le_refl _
  | cons o os ih =>
    simp only [List.filter_cons]
    split <;> simp only [openNotional, List.map_cons, List.sum_cons] at ih ⊢ <;> omega

/-- The state after accepting an order: it is opened with its full quantity, its id is
recorded, and it is forwarded to the market. -/
def accept (s : State) (o : NewOrder) : State :=
  { s with orders := s.orders ++ [⟨o.id, o.px, o.qty⟩], seen := o.id :: s.seen,
           sent := s.sent ++ [o] }

/-- The gateway's response to one event. -/
def step (L : Limits) (s : State) : Event → State
  | .submit o =>
    match check L s o with
    | none => accept s o
    | some _ => s
  | .fill id q =>
    { s with orders := (fillOrders id q s.orders).1,
             executed := s.executed + (fillOrders id q s.orders).2 }
  | .cancel id => { s with orders := s.orders.filter (fun o => o.id != id) }
  | .kill => { s with killed := true, orders := [] }
  | .reset => { s with killed := false }

/-- An accepted order is forwarded and opened. -/
theorem step_submit_of_check {L : Limits} {s : State} {o : NewOrder} (h : check L s o = none) :
    step L s (.submit o) = accept s o := by
  simp [step, h]

/-- A rejected order leaves the state unchanged. -/
theorem step_submit_of_reject {L : Limits} {s : State} {o : NewOrder} {r : Reject}
    (h : check L s o = some r) : step L s (.submit o) = s := by
  simp [step, h]

/-! ## Exposure -/

/-- An accepted order raises the exposure by its notional. -/
theorem exposure_submit_of_check {L : Limits} {s : State} {o : NewOrder} (h : check L s o = none) :
    exposure (step L s (.submit o)) = exposure s + o.qty * o.px := by
  rw [step_submit_of_check h]
  simp [accept, exposure, openNotional, Nat.add_assoc]

/-- A fill leaves the exposure unchanged: the executed notional rises by what the open notional
falls. -/
theorem exposure_fill (L : Limits) (s : State) (id q : Nat) :
    exposure (step L s (.fill id q)) = exposure s := by
  have := openNotional_fillOrders id q s.orders
  simp only [exposure, step]
  omega

/-- A cancel does not raise the exposure. -/
theorem exposure_cancel_le (L : Limits) (s : State) (id : Nat) :
    exposure (step L s (.cancel id)) ≤ exposure s := by
  have := openNotional_filter_le (fun o => o.id != id) s.orders
  simp only [exposure, step]
  omega

/-- After the kill switch the exposure is the executed notional alone. -/
theorem exposure_kill (L : Limits) (s : State) :
    exposure (step L s .kill) = s.executed := by
  simp [exposure, step, openNotional]

/-- Every event from a state within the credit threshold leads to a state within it. -/
theorem exposure_step_le {L : Limits} {s : State} (h : exposure s ≤ L.credit) (e : Event) :
    exposure (step L s e) ≤ L.credit := by
  cases e with
  | submit o =>
    cases hc : check L s o with
    | none =>
      rw [exposure_submit_of_check hc]
      exact ((check_eq_none_iff L s o).1 hc).2.2.2.2.2
    | some r => rw [step_submit_of_reject hc]; exact h
  | fill id q => rw [exposure_fill]; exact h
  | cancel id => exact Nat.le_trans (exposure_cancel_le L s id) h
  | kill => rw [exposure_kill]; simp only [exposure] at h; omega
  | reset => simpa [exposure, step] using h

/-- REQ-CREDIT: from a state within the credit threshold, the aggregate exposure stays within it
after every sequence of new orders, fills, cancels, kills and resets. -/
theorem run_exposure_le {L : Limits} {s : State} (h : exposure s ≤ L.credit) (evs : List Event) :
    exposure (run (step L) s evs) ≤ L.credit :=
  run_le_of_gate exposure L.credit (fun t e => ∃ o, e = .submit o ∧ check L t o = none)
    (fun t e ht _ => exposure_step_le ht e)
    (fun t e hne => by
      cases e with
      | submit o =>
        cases hc : check L t o with
        | none => exact absurd ⟨o, rfl, hc⟩ hne
        | some r => rw [step_submit_of_reject hc]; exact Nat.le_refl _
      | fill id q => rw [exposure_fill]; exact Nat.le_refl _
      | cancel id => exact exposure_cancel_le L t id
      | kill => rw [exposure_kill]; simp [exposure]
      | reset => simp [exposure, step])
    h evs

/-- A new account is within every credit threshold. -/
theorem exposure_empty : exposure State.empty = 0 := rfl

/-- The credit bound for a new account. -/
theorem run_exposure_le_empty (L : Limits) (evs : List Event) :
    exposure (run (step L) State.empty evs) ≤ L.credit :=
  run_exposure_le (by simp [exposure_empty]) evs

/-! ## Kill switch -/

/-- With the kill switch engaged, every event other than a reset keeps it engaged, forwards no
order and leaves no order open. -/
theorem step_of_killed (L : Limits) {s : State} (hk : s.killed = true) (ho : s.orders = [])
    {e : Event} (he : e ≠ .reset) :
    (step L s e).killed = true ∧ (step L s e).orders = [] ∧ (step L s e).sent = s.sent := by
  cases e with
  | submit o => rw [step_submit_of_reject (check_of_killed L hk o)]; exact ⟨hk, ho, rfl⟩
  | fill id q => simp [step, hk, ho, fillOrders]
  | cancel id => simp [step, hk, ho]
  | kill => simp [step]
  | reset => exact absurd rfl he

/-- REQ-KILL-SWITCH: after the kill switch, in every sequence of events without a reset, no order
is forwarded (the list of forwarded orders is unchanged) and no order is open. -/
theorem run_sent_of_killed (L : Limits) (s : State) {evs : List Event}
    (h : ∀ e ∈ evs, e ≠ .reset) :
    (run (step L) (step L s .kill) evs).sent = s.sent ∧
      (run (step L) (step L s .kill) evs).orders = [] ∧
      (run (step L) (step L s .kill) evs).killed = true := by
  have := run_invariant_of_mem (step := step L)
    (I := fun t => t.killed = true ∧ t.orders = [] ∧ t.sent = s.sent) (as := evs)
    (fun t e he ht => by
      obtain ⟨h1, h2, h3⟩ := step_of_killed L ht.1 ht.2.1 (h e he)
      exact ⟨h1, h2, h3.trans ht.2.2⟩)
    (s := step L s .kill) ⟨rfl, rfl, rfl⟩
  exact ⟨this.2.2, this.2.1, this.1⟩

/-! ## Forwarded orders -/

/-- The orders an event forwards: those added to `sent`. -/
theorem step_sent (L : Limits) (s : State) (e : Event) :
    (step L s e).sent = s.sent ∨ ∃ o, e = .submit o ∧ check L s o = none ∧
      (step L s e).sent = s.sent ++ [o] := by
  cases e with
  | submit o =>
    cases hc : check L s o with
    | none => exact Or.inr ⟨o, rfl, hc, by rw [step_submit_of_check hc]; rfl⟩
    | some r => rw [step_submit_of_reject hc]; exact Or.inl rfl
  | fill => exact Or.inl rfl
  | cancel => exact Or.inl rfl
  | kill => exact Or.inl rfl
  | reset => exact Or.inl rfl

/-- The accepted ids are recorded and every forwarded order passed the per-order checks. -/
def SentOk (L : Limits) (s : State) : Prop :=
  (∀ o ∈ s.sent, PerOrderOk L o ∧ o.id ∈ s.seen) ∧ (s.sent.map NewOrder.id).Nodup

/-- Every event preserves `SentOk`. -/
theorem sentOk_step {L : Limits} {s : State} (h : SentOk L s) (e : Event) : SentOk L (step L s e) := by
  cases e with
  | submit o =>
    cases hc : check L s o with
    | none =>
      rw [step_submit_of_check hc]
      have hn := (check_eq_none_iff L s o).1 hc
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [accept, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact ⟨(h.1 x hx).1, List.mem_cons_of_mem _ (h.1 x hx).2⟩
        · exact ⟨perOrderOk_of_check hc, List.mem_cons_self⟩
      · simp only [accept, List.map_append, List.map_cons, List.map_nil]
        rw [List.nodup_append]
        refine ⟨h.2, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        intro e
        exact hn.2.1 (e ▸ (h.1 x hx).2)
    | some r => rw [step_submit_of_reject hc]; exact h
  | fill => exact h
  | cancel => exact h
  | kill => exact h
  | reset => exact h

/-- REQ-PER-ORDER and REQ-DUPLICATE: after any sequence of events from a new account, every
forwarded order passed the quantity, notional and collar checks, and no two forwarded orders share
a client order id. -/
theorem run_sent_checked (L : Limits) (evs : List Event) :
    (∀ o ∈ (run (step L) State.empty evs).sent, PerOrderOk L o) ∧
      ((run (step L) State.empty evs).sent.map NewOrder.id).Nodup := by
  have := run_invariant (step := step L) (I := SentOk L) (fun t e ht => sentOk_step ht e)
    (s := State.empty) ⟨by simp [State.empty], by simp [State.empty]⟩ evs
  exact ⟨fun o ho => (this.1 o ho).1, this.2⟩

end ProofForgeFin.Trading.Risk
