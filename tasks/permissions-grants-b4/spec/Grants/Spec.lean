/-!
# Role grant specification (protected)

Owner-reviewed definitions for the role grant component. Candidates may not edit this file.
Users hold roles through a grant relation; admins issue grant and revoke commands.
Every requirement is a predicate over an implementation `step : Impl`; the locked
challenge (`Grants/Challenge.lean`) applies each one to the definition hole `Grants.step`.
-/

namespace Grants

abbrev UserId := Nat

inductive Role where
  | admin
  | editor
  | viewer
  deriving DecidableEq, Repr

inductive Op where
  | grant
  | revoke
  deriving DecidableEq, Repr

/-- State: a fixed user universe and the grant relation (`has user role`). -/
structure State where
  users : List UserId
  has   : UserId → Role → Bool

/-- `actor` asks to grant `role` to `target`, or to revoke it from `target`. -/
structure Request where
  op     : Op
  actor  : UserId
  target : UserId
  role   : Role

inductive Outcome where
  | ok
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Request → Outcome × State

/-- Some user of the universe other than `u` holds the admin role. -/
def OtherAdmin (s : State) (u : UserId) : Prop :=
  ∃ v ∈ s.users, v ≠ u ∧ s.has v .admin = true

/-- The conditions under which a command must succeed. Only admins issue commands. A grant
must add a role the target does not hold, and never to the actor itself. A revoke must
remove a role the target holds, and removing an admin role requires another admin. -/
def ValidCommand (s : State) (r : Request) : Prop :=
  r.actor ∈ s.users ∧
  r.target ∈ s.users ∧
  s.has r.actor .admin = true ∧
  (r.op = .grant → r.actor ≠ r.target ∧ s.has r.target r.role = false) ∧
  (r.op = .revoke → s.has r.target r.role = true ∧ (r.role = .admin → OtherAdmin s r.target))

/-- The grant relation after a successful command: only the pair `(target, role)` changes. -/
def expectedHas (s : State) (r : Request) (u : UserId) (q : Role) : Bool :=
  if u = r.target ∧ q = r.role then decide (r.op = .grant) else s.has u q

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every valid command succeeds. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s r, ValidCommand s r → (step s r).1 = .ok

/-- REQ-INVALID-NOOP: every invalid command is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s r, ¬ ValidCommand s r → step s r = (.rejected, s)

/-- REQ-AUTHORIZATION: a successful command was issued by an admin of the universe. -/
def AdminOnly (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → r.actor ∈ s.users ∧ s.has r.actor .admin = true

/-- REQ-NO-SELF-GRANT: a successful grant never targets the actor. -/
def NoSelfGrant (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → r.op = .grant → r.actor ≠ r.target

/-- REQ-LAST-ADMIN: if some user holds the admin role before a command, some user holds it after. -/
def KeepsAdmin (step : Impl) : Prop :=
  ∀ s r, (∃ u ∈ s.users, s.has u .admin = true) →
    ∃ u ∈ (step s r).2.users, (step s r).2.has u .admin = true

/-- REQ-OTHERS-UNCHANGED: a successful command changes no grant other than `(target, role)`. -/
def OthersUnchanged (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    ∀ u q, (u ≠ r.target ∨ q ≠ r.role) → (step s r).2.has u q = s.has u q

/-- REQ-EFFECTS: on success, the user universe is unchanged and the grant relation is
exactly `expectedHas`. -/
def Effects (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.users = s.users ∧
    ∀ u q, (step s r).2.has u q = expectedHas s r u q

/-- REQ-IDEMPOTENCY: resubmitting a successful command is rejected without changing the state. -/
def Idempotent (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → step (step s r).2 r = (.rejected, (step s r).2)

end Grants
