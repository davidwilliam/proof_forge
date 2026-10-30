import Acl.Spec
namespace Acl
instance instDecidableValidQuery (s : State) (r : Request) : Decidable (ValidQuery s r) := by
  unfold ValidQuery; infer_instance
def matchesB (e : Entry) (r : Request) : Bool :=
  (e.subject == 0 || e.subject == r.user) && e.path.isPrefixOf r.path

def maxAllowDepth (l : List Entry) (r : Request) : Option Nat :=
  (l.filter (fun e => matchesB e r && e.effect == .allow) |>.map depth).max?

def maxDenyDepth (l : List Entry) (r : Request) : Option Nat :=
  (l.filter (fun e => matchesB e r && e.effect == .deny) |>.map depth).max?

def decision (l : List Entry) (r : Request) : Bool :=
  match maxAllowDepth l r, maxDenyDepth l r with
  | none, _ => false
  | some a, none => true
  | some a, some d => decide (d < a)

def step : Impl := fun s r =>
  if s.users.contains r.user && r.user != 0 then
    let g := decision s.entries r
    (if g then .granted else .denied, { s with log := s.log ++ [⟨r.user, r.path, g⟩] })
  else (.rejected, s)

def testIsPrefix : Bool := [1,2].isPrefixOf [1,2,3]
#check testIsPrefix
#check List.IsPrefix
-- let's try to find lemma connecting isPrefixOf and IsPrefix
-- Search via try
example : [1,2].isPrefixOf [1,2,3] = true := rfl

def myMax? : List Nat → Option Nat
| [] => none
| x :: xs => match myMax? xs with
  | none => some x
  | some y => some (max x y)
-- Check if this matches List.max?
example : ([1,2] : List Nat).max? = some 2 := rfl
example : ([2,1] : List Nat).max? = some 2 := rfl
example : ([] : List Nat).max? = none := rfl

def foo : List Nat → Option Nat := List.max?
#check List.max?_eq_some_iff
#check List.le_max_of_mem
#check Option.isSome

def dummyX : Nat := 42

theorem test_lemma2 : 1 + 1 = (2:Nat) := rfl

theorem isPrefix_lemma_test : [1,2].isPrefixOf [1,2,3] = true := rfl
#check List.IsPrefix
#check List.isPrefixOf
#check decide
-- search names

def tmp1 : List Nat := [1,2]

def tmp2 : List Nat := [1,2,3]
#check (tmp1.isPrefixOf tmp2)
-- try to find lemmas about isPrefixOf
#check List.IsPrefix
#check List.take
#check List.drop

theorem isPrefixOf_true_of_prefix2 {l1 l2 : List Nat} (h : l1 <+: l2) : l1.isPrefixOf l2 = true := by
  induction l1 generalizing l2 with
  | nil => simp [List.isPrefixOf]
  | cons hd tl ih =>
    cases l2 with
    | nil => simp at h
    | cons hd2 tl2 =>
      simp only [List.isPrefixOf]
      have hp : hd = hd2 ∧ tl <+: tl2 := by
        obtain ⟨t, ht⟩ := h
        simp at ht
        exact ⟨ht.1, ⟨t, ht.2⟩⟩
      simp [hp.1, ih hp.2, Bool.and_self]

theorem req_valid_answered     : ValidAnswered step := by
  intro s r h
  simp [step, h.1, h.2]
  intro heq
  cases hc : decision s.entries r <;> simp_all

theorem req_invalid_noop       : InvalidNoop step := sorry

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  simp only at h ⊢
  split at h
  · simp_all
  · simp_all

theorem req_default_deny       : DefaultDeny step := sorry

theorem req_deny_overrides     : DenyOverrides step := sorry

theorem req_specific_allow     : SpecificAllow step := sorry

theorem req_grant_justified    : GrantJustified step := sorry

theorem req_order_independent  : OrderIndependent step := sorry

theorem req_denial_explained   : DenialExplained step := sorry

end Acl
