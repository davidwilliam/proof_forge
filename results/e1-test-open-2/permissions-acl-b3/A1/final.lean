import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def best (eff : Effect) (r : Request) (l : List Entry) : Option Nat :=
  (l.filter (fun e => matchesB e r && e.effect == eff)).foldl
    (fun m e => some (max (m.getD 0) (depth e))) none



def decision (l : List Entry) (r : Request) : Bool :=
  match best .allow r l, best .deny r l with
  | some _, none => true
  | some a, some d => decide (d < a)
  | none, _ => false


def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

def foo : Nat := 1

def foo2 : Nat := 2

private def test_perm_filter : Bool := true

def helper_test2 : Nat := 1

def foldMax2 : Option Nat → List Entry → Option Nat
  | m, [] => m
  | m, e :: es => foldMax2 (some (Nat.max (m.getD 0) (depth e))) es

def myLemma1 : Nat := 1

theorem dummy_test : True := trivial

theorem myThmTest : True := trivial

theorem test_prefix_eq (a b : List Nat) : a.isPrefixOf b = decide (a <+: b) := by rfl

theorem req_valid_answered     : ValidAnswered step := sorry

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp only
  split
  next htrue =>
    rw [Bool.and_eq_true_iff] at htrue
    have hc : s.users.contains r.user = true := htrue.1
    have hz : (r.user != 0) = true := htrue.2
    have hmem : r.user ∈ s.users := by
      have hdec : decide (r.user ∈ s.users) = true := by
        have := hc
        rwa [List.contains_eq_mem] at this
      exact of_decide_eq_true hdec
    have hnz : r.user ≠ 0 := by
      intro heq; simp [heq] at hz
    exact absurd ⟨hmem, hnz⟩ h
  next => rfl

theorem req_effects            : Effects step := sorry

theorem req_default_deny       : DefaultDeny step := sorry

theorem req_deny_overrides     : DenyOverrides step := sorry

theorem req_specific_allow     : SpecificAllow step := sorry

theorem req_grant_justified    : GrantJustified step := sorry

theorem req_order_independent  : OrderIndependent step := by
  intro s r l hperm
  have hdec : decision l r = decision s.entries r := by
    unfold decision best
    have h_allow_perm : (l.filter (fun e => matchesB e r && e.effect == Effect.allow)).Perm (s.entries.filter (fun e => matchesB e r && e.effect == Effect.allow)) := hperm.filter _
    have h_deny_perm : (l.filter (fun e => matchesB e r && e.effect == Effect.deny)).Perm (s.entries.filter (fun e => matchesB e r && e.effect == Effect.deny)) := hperm.filter _
    have fold_perm : ∀ (m : Option Nat) (a b : List Entry), a.Perm b →
        a.foldl (fun m e => some (max (m.getD 0) (depth e))) m = b.foldl (fun m e => some (max (m.getD 0) (depth e))) m := by
      intro m a b hp
      induction hp generalizing m with
      | nil => rfl
      | cons x h ih => simp [ih]
      | swap x y ls => simp [Nat.max_comm, Nat.max_left_comm]
      | trans h1 h2 ih1 ih2 => rw [ih1, ih2]
    have ha := fold_perm none _ _ h_allow_perm
    have hd := fold_perm none _ _ h_deny_perm
    rw [ha, hd]
  show (step { s with entries := l } r).1 = (step s r).1
  unfold step
  simp only
  split
  · simp [hdec]
  · rfl

theorem req_denial_explained   : DenialExplained step := sorry

end Acl
