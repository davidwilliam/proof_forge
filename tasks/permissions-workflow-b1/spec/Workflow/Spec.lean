/-!
# Document workflow specification (protected)

Owner-reviewed definitions for the document workflow component. Candidates may not edit
this file. Documents move through draft, review, approved, published and archived along a
role-based transition table; authors edit drafts; an audit list records every accepted
transition in order. Every requirement is a predicate over an implementation `step : Impl`;
the locked challenge (`Workflow/Challenge.lean`) applies each one to the hole `Workflow.step`.
-/

namespace Workflow

abbrev DocId := Nat
abbrev UserId := Nat

inductive Status where
  | draft
  | review
  | approved
  | published
  | archived
  deriving DecidableEq, Repr

inductive Role where
  | guest
  | author
  | reviewer
  | publisher
  deriving DecidableEq, Repr

/-- The transition table: `allowed role src dst` holds when a user with `role` may move a
document from `src` to `dst`. Every pair not listed is forbidden. -/
def allowed : Role → Status → Status → Bool
  | .author,    .draft,     .review    => true
  | .author,    .draft,     .archived  => true
  | .author,    .review,    .draft     => true
  | .reviewer,  .review,    .approved  => true
  | .reviewer,  .review,    .draft     => true
  | .publisher, .approved,  .published => true
  | .publisher, .approved,  .draft     => true
  | .publisher, .published, .archived  => true
  | _,          _,          _          => false

/-- One audit record: `actor` moved `doc` from `src` to `dst`. -/
structure Entry where
  doc   : DocId
  actor : UserId
  src   : Status
  dst   : Status
  deriving DecidableEq, Repr

/-- State: fixed document and user universes, each document's status and content, each
user's role, and the audit list (oldest entry first). -/
structure State where
  docs    : List DocId
  users   : List UserId
  status  : DocId → Status
  content : DocId → Nat
  role    : UserId → Role
  audit   : List Entry

inductive Kind where
  | move
  | edit
  deriving DecidableEq, Repr

/-- `actor` asks to move `doc` to status `dst` (kind `move`, `body` ignored) or to replace its
content with `body` (kind `edit`, `dst` ignored). -/
structure Request where
  actor : UserId
  doc   : DocId
  kind  : Kind
  dst   : Status
  body  : Nat

inductive Outcome where
  | ok
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Request → Outcome × State

/-- The conditions under which a request must succeed: a move follows an edge of the table
for the actor's role; an edit is made by an author on a draft. -/
def ValidRequest (s : State) (r : Request) : Prop :=
  r.doc ∈ s.docs ∧
  r.actor ∈ s.users ∧
  (r.kind = .move → allowed (s.role r.actor) (s.status r.doc) r.dst = true) ∧
  (r.kind = .edit → s.role r.actor = .author ∧ s.status r.doc = .draft)

/-- The status of document `d` after a successful request. -/
def expectedStatus (s : State) (r : Request) (d : DocId) : Status :=
  if r.kind = .move ∧ d = r.doc then r.dst else s.status d

/-- The content of document `d` after a successful request. -/
def expectedContent (s : State) (r : Request) (d : DocId) : Nat :=
  if r.kind = .edit ∧ d = r.doc then r.body else s.content d

/-- The audit list after a successful request: a move appends one entry, an edit none. -/
def expectedAudit (s : State) (r : Request) : List Entry :=
  if r.kind = .move then s.audit ++ [⟨r.doc, r.actor, s.status r.doc, r.dst⟩] else s.audit

/-- Replay an audit list for document `d`, starting from status `st`: the destination of the
last entry for `d`, or `st` if there is none. -/
def replay : List Entry → DocId → Status → Status
  | [], _, st => st
  | e :: es, d, st => replay es d (if e.doc = d then e.dst else st)

/-- The audit agrees with the state: replaying it from `draft` gives every document's status. -/
def AuditConsistent (s : State) : Prop :=
  ∀ d ∈ s.docs, replay s.audit d .draft = s.status d

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every valid request succeeds. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s r, ValidRequest s r → (step s r).1 = .ok

/-- REQ-INVALID-NOOP: every invalid request is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s r, ¬ ValidRequest s r → step s r = (.rejected, s)

/-- REQ-AUTHORIZATION: a successful move follows the table for the actor's role, and a
successful edit is made by an author on a draft. -/
def Authorized (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (r.kind = .move → allowed (s.role r.actor) (s.status r.doc) r.dst = true) ∧
    (r.kind = .edit → s.role r.actor = .author ∧ s.status r.doc = .draft)

/-- REQ-SINGLE-DOC: a successful request changes no other document's status or content. -/
def SingleDoc (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → ∀ d, d ≠ r.doc →
    (step s r).2.status d = s.status d ∧ (step s r).2.content d = s.content d

/-- REQ-PUBLISHED-IMMUTABLE: the content of a published or archived document never changes. -/
def PublishedImmutable (step : Impl) : Prop :=
  ∀ s r d, (s.status d = .published ∨ s.status d = .archived) →
    (step s r).2.content d = s.content d

/-- REQ-NO-UNPUBLISH: a published document stays published or becomes archived, and an
archived document stays archived. -/
def NoUnpublish (step : Impl) : Prop :=
  ∀ s r d,
    (s.status d = .published →
      (step s r).2.status d = .published ∨ (step s r).2.status d = .archived) ∧
    (s.status d = .archived → (step s r).2.status d = .archived)

/-- REQ-EFFECTS: on success, the universes and roles are unchanged and statuses, contents and
the audit list are exactly `expectedStatus`, `expectedContent` and `expectedAudit`. -/
def Effects (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.docs = s.docs ∧
    (step s r).2.users = s.users ∧
    (step s r).2.role = s.role ∧
    (∀ d, (step s r).2.status d = expectedStatus s r d) ∧
    (∀ d, (step s r).2.content d = expectedContent s r d) ∧
    (step s r).2.audit = expectedAudit s r

/-- REQ-AUDIT-APPEND-ONLY: the old audit list is always a prefix of the new one. -/
def AuditAppendOnly (step : Impl) : Prop :=
  ∀ s r, s.audit <+: (step s r).2.audit

/-- REQ-AUDIT-CONSISTENT: a request never breaks agreement between the audit and the state. -/
def KeepsAuditConsistent (step : Impl) : Prop :=
  ∀ s r, AuditConsistent s → AuditConsistent (step s r).2

end Workflow
