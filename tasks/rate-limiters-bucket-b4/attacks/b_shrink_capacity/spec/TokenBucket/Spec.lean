/-!
# Token bucket specification (protected)

Definitions and requirement predicates for a single token bucket rate limiter.
Candidates may not edit this file. Every requirement is a predicate over an
implementation `step : Impl`; the locked challenge (`TokenBucket/Challenge.lean`)
applies each one to the definition hole `TokenBucket.step`.
-/

namespace TokenBucket

/-- Bucket state: maximum level, tokens added per elapsed tick, the stored level, and
the time of the last accepted request. -/
structure State where
  capacity : Nat
  rate     : Nat
  tokens   : Nat
  last     : Nat
  deriving DecidableEq, Repr

/-- A request arriving at `time` that consumes `cost` tokens. -/
structure Request where
  time : Nat
  cost : Nat
  deriving DecidableEq, Repr

inductive Outcome where
  | ok
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Request → Outcome × State

/-- The level available at time `t`: the stored level plus `rate` tokens per tick
elapsed since `last`, capped at `capacity`. Only meaningful when `last ≤ t`. -/
def refilled (s : State) (t : Nat) : Nat :=
  min s.capacity (s.tokens + s.rate * (t - s.last))

/-- The conditions under which a request must be accepted: it is not earlier than the
last accepted request, it costs at least one token, and the refilled level covers it. -/
def Admissible (s : State) (r : Request) : Prop :=
  s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every admissible request is accepted. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s r, Admissible s r → (step s r).1 = .ok

/-- REQ-INVALID-NOOP: every inadmissible request is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s r, ¬ Admissible s r → step s r = (.rejected, s)

/-- REQ-ALLOW-IFF-SUFFICIENT: for a timely request of positive cost, acceptance holds
exactly when the refilled level covers the cost. -/
def AllowIffSufficient (step : Impl) : Prop :=
  ∀ s r, s.last ≤ r.time → 0 < r.cost →
    ((step s r).1 = .ok ↔ r.cost ≤ refilled s r.time)

/-- REQ-TIME-MONOTONE: the last-update time never decreases, and an accepted request
sets it to the request time. -/
def TimeMonotone (step : Impl) : Prop :=
  ∀ s r, s.last ≤ (step s r).2.last ∧
    ((step s r).1 = .ok → (step s r).2.last = r.time)

/-- REQ-REMAINING: on acceptance, the stored level plus the cost equals the refilled level. -/
def Remaining (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → (step s r).2.tokens + r.cost = refilled s r.time

/-- REQ-EFFECTS: on acceptance, the whole next state is determined: capacity and rate
are unchanged, the level is the refilled level minus the cost, and the time is the
request time. -/
def Effects (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.rate = s.rate ∧
    (step s r).2.tokens = refilled s r.time - r.cost ∧
    (step s r).2.last = r.time

/-- REQ-CAPACITY: a level within capacity stays within capacity. -/
def CapacityBound (step : Impl) : Prop :=
  ∀ s r, s.tokens ≤ s.capacity → (step s r).2.tokens ≤ (step s r).2.capacity

end TokenBucket
