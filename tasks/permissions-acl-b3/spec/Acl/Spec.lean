/-!
# Access control list specification (protected)

Owner-reviewed definitions for the access check component. Candidates may not edit this
file. An access list holds allow and deny entries for users (subject 0 means every user) on
resource path prefixes. A matching entry on a longer prefix is more specific; the most
specific matching entries decide, and at equal specificity deny overrides allow. Every
check is recorded in a log. Every requirement is a predicate over an implementation
`step : Impl`; the locked challenge (`Acl/Challenge.lean`) applies each one to `Acl.step`.
-/

namespace Acl

abbrev UserId := Nat

/-- A resource path from the root, for example `[3, 1]` for resource 1 inside folder 3. -/
abbrev Path := List Nat

inductive Effect where
  | allow
  | deny
  deriving DecidableEq, Repr

/-- An access list entry: `effect` for `subject` (0 means every user) on every resource
whose path starts with `path`. -/
structure Entry where
  effect  : Effect
  subject : UserId
  path    : Path
  deriving DecidableEq, Repr

/-- One log record: the check of `user` on `path` and whether access was granted. -/
structure Record where
  user    : UserId
  path    : Path
  granted : Bool
  deriving DecidableEq, Repr

/-- State: the user universe, the access list and the check log (oldest record first). -/
structure State where
  users   : List UserId
  entries : List Entry
  log     : List Record

/-- `user` asks for access to the resource at `path`. -/
structure Request where
  user : UserId
  path : Path

inductive Outcome where
  | granted
  | denied
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Request → Outcome × State

/-- A check must be answered when the user belongs to the universe and is not the wildcard 0. -/
def ValidQuery (s : State) (r : Request) : Prop :=
  r.user ∈ s.users ∧ r.user ≠ 0

/-- Entry `e` applies to request `r`: its subject is the user or the wildcard, and its path is
a prefix of the requested path. -/
def Matches (e : Entry) (r : Request) : Prop :=
  (e.subject = 0 ∨ e.subject = r.user) ∧ e.path <+: r.path

/-- The specificity of an entry: the length of its path. -/
def depth (e : Entry) : Nat := e.path.length

/-- Some matching entry allows access. -/
def HasAllow (l : List Entry) (r : Request) : Prop :=
  ∃ a ∈ l, Matches a r ∧ a.effect = .allow

/-- Some matching deny entry is at least as specific as every matching allow entry. -/
def Overridden (l : List Entry) (r : Request) : Prop :=
  ∃ d ∈ l, Matches d r ∧ d.effect = .deny ∧
    ∀ a ∈ l, Matches a r → a.effect = .allow → depth a ≤ depth d

/-- Some matching allow entry is strictly more specific than every matching deny entry. -/
def Permitted (l : List Entry) (r : Request) : Prop :=
  ∃ a ∈ l, Matches a r ∧ a.effect = .allow ∧
    ∀ d ∈ l, Matches d r → d.effect = .deny → depth d < depth a

/-! ## Requirements -/

/-- REQ-VALID-ANSWERED: every valid check is answered with granted or denied. -/
def ValidAnswered (step : Impl) : Prop :=
  ∀ s r, ValidQuery s r → (step s r).1 ≠ .rejected

/-- REQ-INVALID-NOOP: every invalid check is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s r, ¬ ValidQuery s r → step s r = (.rejected, s)

/-- REQ-EFFECTS: an answered check leaves the users and the access list unchanged and appends
exactly one log record with its decision. -/
def Effects (step : Impl) : Prop :=
  ∀ s r, (step s r).1 ≠ .rejected →
    (step s r).2.users = s.users ∧
    (step s r).2.entries = s.entries ∧
    (step s r).2.log = s.log ++ [⟨r.user, r.path, decide ((step s r).1 = .granted)⟩]

/-- REQ-DEFAULT-DENY: without a matching allow entry, access is not granted. -/
def DefaultDeny (step : Impl) : Prop :=
  ∀ s r, ¬ HasAllow s.entries r → (step s r).1 ≠ .granted

/-- REQ-DENY-OVERRIDES: a matching deny entry at least as specific as every matching allow
entry prevents access. -/
def DenyOverrides (step : Impl) : Prop :=
  ∀ s r, Overridden s.entries r → (step s r).1 ≠ .granted

/-- REQ-SPECIFIC-ALLOW: a valid check is granted when a matching allow entry is strictly more
specific than every matching deny entry. -/
def SpecificAllow (step : Impl) : Prop :=
  ∀ s r, ValidQuery s r → Permitted s.entries r → (step s r).1 = .granted

/-- REQ-GRANT-JUSTIFIED: a granted check has a matching allow entry strictly more specific
than every matching deny entry. -/
def GrantJustified (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .granted → Permitted s.entries r

/-- REQ-ORDER-INDEPENDENT: reordering the access list does not change any outcome. -/
def OrderIndependent (step : Impl) : Prop :=
  ∀ s r (l : List Entry), l.Perm s.entries → (step { s with entries := l } r).1 = (step s r).1

/-- REQ-DENIAL-EXPLAINED: a denied check has no matching allow entry, or a matching deny entry
at least as specific as every matching allow entry. -/
def DenialExplained (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .denied → ¬ HasAllow s.entries r ∨ Overridden s.entries r

end Acl
