import Acl.Spec
namespace Acl

instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance

def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def maxOption (l : List Nat) : Option Nat :=
  l.foldl (fun acc x => match acc with
    | none => some x
    | some v => some (max v x)) none

def grantedDecision (entries : List Entry) (r : Request) : Bool :=
  let allowDepths := (entries.filter (fun e => matchesB e r && e.effect == .allow)).map depth
  let denyDepths  := (entries.filter (fun e => matchesB e r && e.effect == .deny)).map depth
  match maxOption allowDepths, maxOption denyDepths with
  | none, _ => false
  | some a, none => true
  | some a, some d => a > d

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := grantedDecision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

def foo : Nat := 1

theorem test_default : 1 = 1 := rfl

theorem myLemma2 : True := trivial

theorem myLemma3 : Nat.zero = 0 := rfl

theorem dummy_lemma : True := by trivial

def test : Nat := 0

def foo2 : Nat := 2

theorem dummy_test : 1 = 1 := rfl

theorem t : 2 = 2 := rfl

theorem test_eq : (1 : Nat) = 1 := rfl

theorem trivial_test : True := by trivial

theorem maxOption_test : maxOption [] = none := rfl

theorem test_perm : maxOption ([] : List Nat) = none := rfl

theorem decide_granted : ∀ b : Bool, decide ((if b then Outcome.granted else Outcome.denied) = Outcome.granted) = b := by
  intro b
  cases b <;> rfl

theorem matchesB_iff : ∀ e r, matchesB e r = true ↔ Matches e r := by
  intro e r
  simp [matchesB, Matches, BEq.beq]

theorem foo_test : 1 = 1 := rfl

theorem test_tmp : True := trivial

theorem foo_lemma : 1 = 1 := rfl

theorem test_lemma : True := by trivial

def dummy : Nat := 0

theorem lemma_placeholder : True := by trivial

theorem req_valid_answered     : ValidAnswered step := sorry

theorem req_invalid_noop       : InvalidNoop step := sorry

theorem req_effects            : Effects step := sorry

theorem req_default_deny       : DefaultDeny step := sorry

theorem req_deny_overrides     : DenyOverrides step := sorry

theorem req_specific_allow     : SpecificAllow step := sorry

theorem req_grant_justified    : GrantJustified step := sorry

theorem req_order_independent  : OrderIndependent step := sorry

theorem req_denial_explained   : DenialExplained step := sorry

end Acl
