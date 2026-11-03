import Workflow.Spec
namespace Workflow
instance instDecidableValidRequest (s : State) (r : Request) : Decidable (ValidRequest s r) := by
  unfold ValidRequest; infer_instance
def edges : List (Role × Status × Status) :=
  [(.author, .draft, .review), (.author, .draft, .archived), (.author, .review, .draft),
   (.reviewer, .review, .approved), (.reviewer, .review, .draft),
   (.publisher, .approved, .published), (.publisher, .approved, .draft),
   (.publisher, .published, .archived)]

def mayMove (s : State) (r : Request) : Bool :=
  edges.contains (s.role r.actor, s.status r.doc, r.dst)

def mayEdit (s : State) (r : Request) : Bool :=
  s.role r.actor == .author && s.status r.doc != .approved && s.status r.doc != .published &&
    s.status r.doc != .archived

def doMove (s : State) (r : Request) : State :=
  { s with status := fun d => if d == r.doc then r.dst else s.status d,
           audit := s.audit ++ [{ doc := r.doc, actor := r.actor, src := s.status r.doc, dst := r.dst }] }

def doEdit (s : State) (r : Request) : State :=
  { s with content := fun d => if d == r.doc then r.body else s.content d }

def step : Impl := fun s r =>
  if s.docs.contains r.doc && s.users.contains r.actor then
    match r.kind with
    | .move => if mayMove s r then (.ok, doMove s r) else (.rejected, s)
    | .edit => if mayEdit s r then (.ok, doEdit s r) else (.rejected, s)
  else (.rejected, s)
theorem req_valid_succeeds       : ValidSucceeds step := sorry
theorem req_invalid_noop         : InvalidNoop step := sorry
theorem req_authorization        : Authorized step := sorry
theorem req_single_doc           : SingleDoc step := sorry
theorem req_published_immutable  : PublishedImmutable step := sorry
theorem req_no_unpublish         : NoUnpublish step := sorry
theorem req_effects              : Effects step := sorry
theorem req_audit_append_only    : AuditAppendOnly step := sorry
theorem req_audit_consistent     : KeepsAuditConsistent step := sorry
end Workflow
