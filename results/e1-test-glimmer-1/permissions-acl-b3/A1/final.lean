import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

/-- Depth of the most specific matching entry with effect `eff`. -/
def best (eff : Effect) (r : Request) (l : List Entry) : Option Nat :=
  (l.filter (fun e => matchesB e r && e.effect == eff)).foldl
    (fun m e => some (max (m.getD 0) (depth e))) none

def decision (l : List Entry) (r : Request) : Bool :=
  match best .allow r l, best .deny r l with
  | some a, none => true
  | some a, some d => a > d
  | none, _ => false

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

def test : Bool := true

def foo (x : Nat) : Nat := x+1

def baz := 0

theorem tmp : 1 = 1 := rfl

def dummy : Nat := 1

theorem dummy_test : 1+1 = 2 := rfl

theorem test_tmp : True := by trivial

def foo2 : Nat := 1

theorem tmp2 : 2 = 2 := rfl

theorem test_helper (n : Nat) : n = n := rfl

theorem req_valid_answered     : ValidAnswered step := sorry

theorem req_invalid_noop       : InvalidNoop step := sorry

theorem req_effects            : Effects step := sorry

theorem req_default_deny       : DefaultDeny step := sorry

theorem req_deny_overrides     : DenyOverrides step := sorry

theorem req_specific_allow : SpecificAllow step := by
  intro s r hvalid hperm
  have hmem : r.user ∈ s.users := hvalid.1
  have hne : r.user ≠ 0 := hvalid.2
  -- condition true
  have hcond : s.users.contains r.user && (r.user != 0 : Bool) = true := by
    simp [hmem, hne]
  simp [step, hcond]
  unfold decision
  rcases hperm with ⟨a, ha_mem, ha_match, ha_eff, hforall⟩
  -- show best allow is some and > best deny
  -- For now just admit
  sorry

theorem req_grant_justified    : GrantJustified step := sorry

theorem req_order_independent  : OrderIndependent step := sorry

theorem req_denial_explained   : DenialExplained step := sorry

end Acl
