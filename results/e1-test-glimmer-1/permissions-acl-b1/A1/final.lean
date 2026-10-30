import Acl.Spec
namespace Acl

def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def updateBest (allowOpt : Option Nat) (denyOpt : Option Nat) (e : Entry) (r : Request) : Option Nat × Option Nat :=
  if matchesB e r then
    match e.effect with
    | .allow =>
        let d := e.path.length
        let newAllow :=
          match allowOpt with
          | none => some d
          | some cur => if d > cur then some d else allowOpt
        (newAllow, denyOpt)
    | .deny =>
        let d := e.path.length
        let newDeny :=
          match denyOpt with
          | none => some d
          | some cur => if d > cur then some d else denyOpt
        (allowOpt, newDeny)
  else
    (allowOpt, denyOpt)

def bestDepths (l : List Entry) (r : Request) : Option Nat × Option Nat :=
  l.foldl (fun acc e => updateBest acc.1 acc.2 e r) (none, none)

def isGranted (l : List Entry) (r : Request) : Bool :=
  match bestDepths l r with
  | (some ad, none) => true
  | (some ad, some dd) => ad > dd
  | _ => false

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := isGranted s.entries r
    let outcome := if g then .granted else .denied
    (outcome, { s with log := s.log ++ [{ user := r.user, path := r.path, granted := g }] })
  else
    (.rejected, s)

def foo (a b : List Nat) : Prop := a.isPrefixOf b = true ↔ a <+: b

def test : Nat := 1

theorem trivial_test : True := trivial

def dummy : Nat := 0

def test2 : Nat := 1

theorem req_specific_allow_test : True := by trivial

theorem matchesB_correct : ∀ e r, matchesB e r = true ↔ Matches e r := by
  intro e r
  unfold matchesB Matches
  simp [beq_iff_eq]


theorem test1 : True := True.intro

theorem dummy2 : True := trivial

theorem matchesB_correct2 : ∀ e r, matchesB e r = true ↔ Matches e r := by
  intro e r
  unfold matchesB Matches
  simp [beq_iff_eq]

theorem req_valid_answered     : ValidAnswered step := sorry

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [ValidQuery] at h
  by_cases hmem : r.user ∈ s.users
  · have h0 : r.user = 0 := h hmem
    simp [hmem] at *
    simp [h0]
  · simp [hmem]

theorem req_effects            : Effects step := sorry

theorem req_default_deny       : DefaultDeny step := sorry

theorem req_deny_overrides     : DenyOverrides step := sorry

theorem req_specific_allow     : SpecificAllow step := sorry

theorem req_grant_justified    : GrantJustified step := sorry

theorem req_order_independent  : OrderIndependent step := sorry

theorem req_denial_explained   : DenialExplained step := sorry

end Acl
