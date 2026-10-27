/-!
# Fixed-window rate limiter specification (protected)

Definitions and requirement predicates for a per-client fixed-window counter.
Candidates may not edit this file. Every requirement is a predicate over an
implementation `step : Impl`; the locked challenge (`FixedWindow/Challenge.lean`)
applies each one to the definition hole `FixedWindow.step`.
-/

namespace FixedWindow

abbrev ClientId := Nat

/-- Per-client counter: the start of the client's current window and the number of
requests accepted in it. -/
structure Client where
  id    : ClientId
  start : Nat
  count : Nat
  deriving DecidableEq, Repr

/-- Limiter state: window length, the per-window limit, and the registered clients. -/
structure State where
  window  : Nat
  limit   : Nat
  clients : List Client
  deriving DecidableEq, Repr

/-- A request from `client` arriving at `time`. -/
structure Request where
  client : ClientId
  time   : Nat
  deriving DecidableEq, Repr

inductive Outcome where
  | ok
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Request → Outcome × State

/-- The first registered entry with id `i`, if any. -/
def lookup : List Client → ClientId → Option Client
  | [], _ => none
  | c :: cs, i => if c.id = i then some c else lookup cs i

/-- Start of the window that contains time `t`: the window of `c` has expired once `t`
reaches `start + window`, and a new one then starts at `t`. -/
def windowStart (s : State) (c : Client) (t : Nat) : Nat :=
  if c.start + s.window ≤ t then t else c.start

/-- Requests already accepted in the window that contains time `t`. -/
def windowCount (s : State) (c : Client) (t : Nat) : Nat :=
  if c.start + s.window ≤ t then 0 else c.count

/-- The entry of `c` after one more accepted request at time `t`. -/
def advance (s : State) (c : Client) (t : Nat) : Client :=
  { id := c.id, start := windowStart s c t, count := windowCount s c t + 1 }

/-- Whether the registered entry (if any) admits a request at time `t`: the request is
not earlier than the window start, and the current window is below the limit. -/
def Admits (s : State) (t : Nat) : Option Client → Prop
  | some c => c.start ≤ t ∧ windowCount s c t < s.limit
  | none => False

/-- The conditions under which a request must be accepted: client ids are distinct,
the client is registered, and its entry admits the request. -/
def Admissible (s : State) (r : Request) : Prop :=
  (s.clients.map Client.id).Nodup ∧ Admits s r.time (lookup s.clients r.client)

/-- The entry registered under id `i` after an accepted request `r`. -/
def expectedLookup (s : State) (r : Request) (i : ClientId) : Option Client :=
  if i = r.client then (lookup s.clients i).map (fun c => advance s c r.time)
  else lookup s.clients i

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every admissible request is accepted. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s r, Admissible s r → (step s r).1 = .ok

/-- REQ-INVALID-NOOP: every inadmissible request is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s r, ¬ Admissible s r → step s r = (.rejected, s)

/-- REQ-ISOLATION: a request never changes the entry of any other client. -/
def Isolation (step : Impl) : Prop :=
  ∀ s r i, i ≠ r.client → lookup (step s r).2.clients i = lookup s.clients i

/-- REQ-RESET: on acceptance, the requesting client's entry follows the window rule: an
expired window restarts at the request time with count 1; otherwise the start is kept
and the count grows by one. -/
def ResetRule (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → ∀ c, lookup s.clients r.client = some c →
    ∃ c', lookup (step s r).2.clients r.client = some c' ∧
      (c.start + s.window ≤ r.time → c'.start = r.time ∧ c'.count = 1) ∧
      (r.time < c.start + s.window → c'.start = c.start ∧ c'.count = c.count + 1)

/-- REQ-EFFECTS: on acceptance, the whole next state is determined: window and limit are
unchanged, the client ids keep their order, and every id's entry is `expectedLookup`. -/
def Effects (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.window = s.window ∧
    (step s r).2.limit = s.limit ∧
    (step s r).2.clients.map Client.id = s.clients.map Client.id ∧
    ∀ i, lookup (step s r).2.clients i = expectedLookup s r i

/-- REQ-WINDOW-BOUND: if no client has exceeded the limit, none does after the request. -/
def WindowBound (step : Impl) : Prop :=
  ∀ s r, (∀ c ∈ s.clients, c.count ≤ s.limit) →
    ∀ c ∈ (step s r).2.clients, c.count ≤ (step s r).2.limit

end FixedWindow
