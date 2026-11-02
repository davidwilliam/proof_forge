import ProofForgeFin.Accumulator.Runs
import ProofForgeFin.Accumulator.Potential
/-!
# Two-sided index markets: a whole run bounded from one case analysis per action

A market with two reward sides (for example a supply side and a borrow side) keeps, for each
side, a reward index at scale `one`, the time it was last brought up to date and a rate per unit
of time; each account holds units on each side, records a checkpoint of each index (0 meaning
none) and has been credited an amount (accrued and paid together). The bounds "the amounts
credited to all accounts never exceed the start amount, plus what was owed at the start, plus
what was emitted since", the same for one account, and "an account that holds nothing gains at
most what is emitted from then on" all follow from a potential that no action raises except the
passage of time.

This module proves those bounds once for every state type `σ` and account type `α`. A `Market σ α`
says how to read a state: its `Clock` (the time and each side's index, last update and rate), its
account list, and each account's units, checkpoints and credited amount. A proof for a concrete
system then shows, for each of its actions, which primitive transition it is:

* `Settle₁` / `Settle₂`: one side brought up to date (`catchUp`) and one account credited its
  units times the index gained since its start (`firstStart`), rounded down, with its checkpoint
  moved to the index;
* `Adjust`: a change of one account that does not raise its credited amount (a payment moves an
  accrued amount to a wallet) and changes its units on a side only while it is settled there
  (`Settled₁`, `Settled₂`: the side is up to date and the account's checkpoint is the index);
* `Retune`: either side brought up to date with a new rate, or left as it is;
* `Advance`: time passes; nothing else changes.

`Step` collects the transitions that keep the rates; an action is an `Act`: a chain of steps
(`Reach`, whose intermediate states are views, so a proof never builds them), a retune that sets
the rates, or an advance, which emits `k * (rate₁ + rate₂)`.

* `Act.bound`: an action keeps the invariant `Inv` and raises the potential `pot` (all accounts)
  and `potOf w` (account `w`) by at most `one` times its emission.
* `run_bound`: the same over a run given by its defining equations.
* `rewards_bounded`, `account_rewards_bounded`: from a bound on the potential at the start to a
  bound on the credited amounts after any run; `rewards_after_no_position_bounded`: an account
  that holds no units after any history gains at most what is emitted from then on.
* `pot_le_of`, `potOf_le_of`: the potential at the start from bounds on what each account is owed
  and on the emission not yet indexed; `start_reinit`, `owed_reinit_le`, `unindexed_reinit_le`:
  an index still at 0 set to `init` (with its unindexed emission dropped) raises nothing owed.
* `Settle₁.then_adjust`, `Settle₂.then_adjust`, `Settle₁.transfer`, `Settle₂.transfer`: an
  account settled and then given new units on that side, and two accounts settled and then
  exchanging units, as chains of steps.

## Using the module

For a specification with a state `St`, accounts `Acct`, a step `exec : St → Op → St`, a run
`run`, rewards emitted `emitted : Nat × Nat → List Op → Nat` and rates after a run
`speedsAfter`, all defined by structural recursion:

1. `def M : Market St Acct` reads the state: `clock s := ⟨now, index₁, last₁, rate₁, index₂,
   last₂, rate₂⟩` from the state's fields, `accts`, `units₁`, `rec₁`, ..., `credited a :=
   a.accrued + a.wallet`, `dflt_units₁ := rfl`.
2. For each call that brings a side up to date and credits an account (a hook, a distribution),
   a lemma `M.Settle₁ who s s'` (or `Settle₂`): `obtain` the call's equation, then the clock
   equation by `simp` with the index update rewritten to `catchUp`, the account change by `rfl`
   and its credited amount by `omega` once the protocol's start is rewritten to `firstStart`.
3. `theorem exec_act ... : M.Act sp s (next sp op) (emittedBy sp op) (exec s op)` by cases on the
   operation: `.moves` with `Reach.refl` for a refused operation, `Settle₁.then_adjust` for a
   hook followed by a change of units, `Settle₁.transfer` for two hooks and a transfer,
   `Reach.single`, `Reach.tail`, `Reach.trans` and `Reach.of_getD` for other chains (a payment is
   `Step.adjust`, a change of nothing the market reads is `Step.same`); `.retune` for a rate
   change; `.advance k ⟨rfl, rfl⟩` for time passing.
4. The start: `M.Inv g₁ g₂ sp s₀` and a bound on `M.pot g₁ g₂ s₀` (`pot_le_of`) or on
   `M.potOf g₁ g₂ w s₀` (`potOf_le_of`).
5. `M.rewards_bounded run emitted speedsAfter exec_act hone h0 hs ops` bounds the credited total
   after any run, `account_rewards_bounded` one account, and `rewards_after_no_position_bounded`
   an account that holds nothing after a history; the equations of `run`, `emitted` and
   `speedsAfter` are proved by `rfl` automatically.
-/

namespace ProofForgeFin.Accumulator

open ProofForgeFin.DeFi.Rewards (effStart firstStart effStart_le_firstStart le_effStart_self
  forall_mem_modify sum_le_of_index_le₂)

universe u v w

/-! ## Clocks -/

/-- The time and the two reward sides of a market: for each side the index, the time it was last
brought up to date and the rate per unit of time. -/
structure Clock where
  /-- The current time (a block number or a timestamp). -/
  now : Nat
  /-- The index of side 1. -/
  index₁ : Nat
  /-- The time side 1 was last brought up to date. -/
  last₁ : Nat
  /-- The rate of side 1 per unit of time. -/
  rate₁ : Nat
  /-- The index of side 2. -/
  index₂ : Nat
  /-- The time side 2 was last brought up to date. -/
  last₂ : Nat
  /-- The rate of side 2 per unit of time. -/
  rate₂ : Nat
  deriving DecidableEq, Repr

namespace Clock

/-- The emission of side 1 not yet in its index. -/
def un₁ (c : Clock) : Nat := unindexed c.last₁ c.rate₁ c.now

/-- The emission of side 2 not yet in its index. -/
def un₂ (c : Clock) : Nat := unindexed c.last₂ c.rate₂ c.now

/-- Side 1 brought up to date over `total` units at scale `one`. -/
def catchUp₁ (one total : Nat) (c : Clock) : Clock :=
  { c with index₁ := catchUp one c.index₁ c.last₁ c.rate₁ c.now total, last₁ := c.now }

/-- Side 2 brought up to date over `total` units at scale `one`. -/
def catchUp₂ (one total : Nat) (c : Clock) : Clock :=
  { c with index₂ := catchUp one c.index₂ c.last₂ c.rate₂ c.now total, last₂ := c.now }

/-- `k` units of time later. -/
def advance (k : Nat) (c : Clock) : Clock := { c with now := c.now + k }

/-- The two sides exchanged. -/
def swap (c : Clock) : Clock := ⟨c.now, c.index₂, c.last₂, c.rate₂, c.index₁, c.last₁, c.rate₁⟩

/-- A field of the exchanged sides. -/
@[simp] theorem swap_now (c : Clock) : c.swap.now = c.now := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_index₁ (c : Clock) : c.swap.index₁ = c.index₂ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_index₂ (c : Clock) : c.swap.index₂ = c.index₁ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_last₁ (c : Clock) : c.swap.last₁ = c.last₂ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_last₂ (c : Clock) : c.swap.last₂ = c.last₁ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_rate₁ (c : Clock) : c.swap.rate₁ = c.rate₂ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_rate₂ (c : Clock) : c.swap.rate₂ = c.rate₁ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_un₁ (c : Clock) : c.swap.un₁ = c.un₂ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_un₂ (c : Clock) : c.swap.un₂ = c.un₁ := rfl

/-- Bringing side 2 up to date is bringing side 1 of the exchanged clock up to date. -/
theorem swap_catchUp₂ (one total : Nat) (c : Clock) :
    (c.catchUp₂ one total).swap = c.swap.catchUp₁ one total := rfl

/-- Right after side 1 is brought up to date nothing of it is left unindexed. -/
@[simp] theorem catchUp₁_un₁ (one total : Nat) (c : Clock) : (c.catchUp₁ one total).un₁ = 0 := by
  simp [catchUp₁, un₁]

/-- Bringing side 1 up to date never lowers its index. -/
theorem le_catchUp₁_index₁ (one total : Nat) (c : Clock) :
    c.index₁ ≤ (c.catchUp₁ one total).index₁ := le_catchUp _ _ _ _ _ _

end Clock

/-! ## Reading a state as a market -/

/-- How to read a state of type `σ` as a two-sided reward market (a supply side and a borrow side,
each with a reward index accrued at a rate) whose accounts have type `α`: the scale `one` of the
indices, the value `init` an index is set to when rewards start (an index may also
start from 0), the clock, the account list with the record `dflt` of an account beyond the list
(which holds no units), and each account's units, checkpoints (0 meaning none) and credited
amount. -/
structure Market (σ : Type u) (α : Type v) where
  /-- The scale of the indices. -/
  one : Nat
  /-- The value an index is set to when rewards start. -/
  init : Nat
  /-- The time and the two sides. -/
  clock : σ → Clock
  /-- The accounts, by position. -/
  accts : σ → List α
  /-- The record of an account beyond the list. -/
  dflt : α
  /-- Units held on side 1. -/
  units₁ : α → Nat
  /-- Units held on side 2. -/
  units₂ : α → Nat
  /-- The checkpoint of the index of side 1 (0 meaning none). -/
  rec₁ : α → Nat
  /-- The checkpoint of the index of side 2 (0 meaning none). -/
  rec₂ : α → Nat
  /-- The amount credited to the account (accrued and paid). -/
  credited : α → Nat
  /-- An account beyond the list holds no units on side 1. -/
  dflt_units₁ : units₁ dflt = 0
  /-- An account beyond the list holds no units on side 2. -/
  dflt_units₂ : units₂ dflt = 0

namespace Market

variable {σ : Type u} {α : Type v} (M : Market σ α)

/-- The same market with its two sides exchanged. -/
def swap : Market σ α where
  one := M.one
  init := M.init
  clock s := (M.clock s).swap
  accts := M.accts
  dflt := M.dflt
  units₁ := M.units₂
  units₂ := M.units₁
  rec₁ := M.rec₂
  rec₂ := M.rec₁
  credited := M.credited
  dflt_units₁ := M.dflt_units₂
  dflt_units₂ := M.dflt_units₁

/-- The record of account `w`. -/
def acct (s : σ) (w : Nat) : α := (M.accts s).getD w M.dflt

/-- Total units of side 1. -/
def total₁ (s : σ) : Nat := ((M.accts s).map M.units₁).sum

/-- Total units of side 2. -/
def total₂ (s : σ) : Nat := ((M.accts s).map M.units₂).sum

/-- The amount credited to all accounts. -/
def creditSum (s : σ) : Nat := ((M.accts s).map M.credited).sum

/-- What an account is owed on both sides, at the clock `c`, counted from the starts `g₁` and
`g₂` of the indices (`effStart`: its checkpoint, or the start of the index if it has none). -/
def owed (g₁ g₂ : Nat) (c : Clock) (a : α) : Nat :=
  M.units₁ a * (c.index₁ - effStart g₁ (M.rec₁ a)) + M.units₂ a * (c.index₂ - effStart g₂ (M.rec₂ a))

/-- An account's term of the potential: its credited amount at scale `one` plus what it is owed. -/
def term (g₁ g₂ : Nat) (c : Clock) (a : α) : Nat := M.credited a * M.one + M.owed g₁ g₂ c a

/-- The potential of all accounts: their terms plus `one` times the emission not yet indexed. -/
def pot (g₁ g₂ : Nat) (s : σ) : Nat :=
  ((M.accts s).map (M.term g₁ g₂ (M.clock s))).sum + M.one * ((M.clock s).un₁ + (M.clock s).un₂)

/-- The potential of account `w`: its term plus `one` times the emission not yet indexed on each
side where it holds units. -/
def potOf (g₁ g₂ w : Nat) (s : σ) : Nat :=
  M.term g₁ g₂ (M.clock s) (M.acct s w) +
    M.one * ((if 0 < M.units₁ (M.acct s w) then (M.clock s).un₁ else 0) +
      (if 0 < M.units₂ (M.acct s w) then (M.clock s).un₂ else 0))

/-! ## Transitions -/

/-- Account `w` is settled on side 1: the side is up to date and the account's checkpoint is the
index. -/
def Settled₁ (s : σ) (w : Nat) : Prop :=
  (M.clock s).last₁ = (M.clock s).now ∧
    (w < (M.accts s).length → M.rec₁ (M.acct s w) = (M.clock s).index₁)

/-- Account `w` is settled on side 2. -/
def Settled₂ (s : σ) (w : Nat) : Prop :=
  (M.clock s).last₂ = (M.clock s).now ∧
    (w < (M.accts s).length → M.rec₂ (M.acct s w) = (M.clock s).index₂)

/-- `f` settles an account on side 1 at index `i`: its units and its side-2 checkpoint are kept,
its side-1 checkpoint becomes `i`, and its credited amount grows by at most its units times the
index gained since `firstStart init (rec₁ a) i`, rounded down at scale `one` (a later start
credits less, so any start at or after `firstStart` qualifies). -/
def SettlesAt₁ (i : Nat) (f : α → α) : Prop :=
  ∀ a, M.units₁ (f a) = M.units₁ a ∧ M.units₂ (f a) = M.units₂ a ∧ M.rec₁ (f a) = i ∧
    M.rec₂ (f a) = M.rec₂ a ∧
    M.credited (f a) ≤ M.credited a + M.units₁ a * (i - firstStart M.init (M.rec₁ a) i) / M.one

/-- `f` settles an account on side 2 at index `i`. -/
def SettlesAt₂ (i : Nat) (f : α → α) : Prop :=
  ∀ a, M.units₂ (f a) = M.units₂ a ∧ M.units₁ (f a) = M.units₁ a ∧ M.rec₂ (f a) = i ∧
    M.rec₁ (f a) = M.rec₁ a ∧
    M.credited (f a) ≤ M.credited a + M.units₂ a * (i - firstStart M.init (M.rec₂ a) i) / M.one

/-- Side 1 brought up to date, then account `w` settled on side 1 at the new index. -/
structure Settle₁ (w : Nat) (s t : σ) : Prop where
  /-- The clock after: side 1 brought up to date over its total units. -/
  clock : M.clock t = (M.clock s).catchUp₁ M.one (M.total₁ s)
  /-- The accounts after: account `w` settled. -/
  accts : ∃ f, M.accts t = (M.accts s).modify w f ∧ M.SettlesAt₁ (M.clock t).index₁ f

/-- Side 2 brought up to date, then account `w` settled on side 2 at the new index. -/
structure Settle₂ (w : Nat) (s t : σ) : Prop where
  /-- The clock after: side 2 brought up to date over its total units. -/
  clock : M.clock t = (M.clock s).catchUp₂ M.one (M.total₂ s)
  /-- The accounts after: account `w` settled. -/
  accts : ∃ f, M.accts t = (M.accts s).modify w f ∧ M.SettlesAt₂ (M.clock t).index₂ f

/-- `f` adjusts an account: it does not raise its credited amount and keeps its checkpoints. -/
def AdjustsAt (f : α → α) : Prop :=
  ∀ a, M.credited (f a) ≤ M.credited a ∧ M.rec₁ (f a) = M.rec₁ a ∧ M.rec₂ (f a) = M.rec₂ a

/-- Account `w` adjusted with the clock unchanged: its credited amount does not grow (a payment,
which moves an accrued amount to a wallet), its checkpoints are kept, and its units on a side
change only while it is settled there. -/
structure Adjust (w : Nat) (s t : σ) : Prop where
  /-- The clock is unchanged. -/
  clock : M.clock t = M.clock s
  /-- The accounts after: account `w` adjusted. -/
  accts : ∃ f, M.accts t = (M.accts s).modify w f ∧ M.AdjustsAt f ∧
    ((∀ a, M.units₁ (f a) = M.units₁ a) ∨ M.Settled₁ s w) ∧
    ((∀ a, M.units₂ (f a) = M.units₂ a) ∨ M.Settled₂ s w)

/-- One side left as it is (index `i`, last update `l`, rate `r`), or brought up to date at `now`
over `total` units with any new rate. -/
def SideMove (one total now i l r i' l' r' : Nat) : Prop :=
  (i' = i ∧ l' = l ∧ r' = r) ∨ (i' = catchUp one i l r now total ∧ l' = now)

/-- Each side left as it is or brought up to date with a new rate; the accounts and the time are
unchanged. -/
structure Retune (s t : σ) : Prop where
  /-- The accounts are unchanged. -/
  accts : M.accts t = M.accts s
  /-- The time is unchanged. -/
  now : (M.clock t).now = (M.clock s).now
  /-- Side 1. -/
  side₁ : SideMove M.one (M.total₁ s) (M.clock s).now (M.clock s).index₁ (M.clock s).last₁
    (M.clock s).rate₁ (M.clock t).index₁ (M.clock t).last₁ (M.clock t).rate₁
  /-- Side 2. -/
  side₂ : SideMove M.one (M.total₂ s) (M.clock s).now (M.clock s).index₂ (M.clock s).last₂
    (M.clock s).rate₂ (M.clock t).index₂ (M.clock t).last₂ (M.clock t).rate₂

/-- `k` units of time pass; nothing else changes. -/
structure Advance (k : Nat) (s t : σ) : Prop where
  /-- The clock after. -/
  clock : M.clock t = (M.clock s).advance k
  /-- The accounts are unchanged. -/
  accts : M.accts t = M.accts s

/-- The transitions inside one action that keep the rates. -/
inductive Step : σ → σ → Prop
  /-- A settlement on side 1. -/
  | settle₁ {w : Nat} {s t : σ} : M.Settle₁ w s t → Step s t
  /-- A settlement on side 2. -/
  | settle₂ {w : Nat} {s t : σ} : M.Settle₂ w s t → Step s t
  /-- An adjustment of one account. -/
  | adjust {w : Nat} {s t : σ} : M.Adjust w s t → Step s t
  /-- Sides brought up to date at the same rates. -/
  | retune {s t : σ} : M.Retune s t → (M.clock t).rate₁ = (M.clock s).rate₁ →
      (M.clock t).rate₂ = (M.clock s).rate₂ → Step s t
  /-- Nothing the market reads changes. -/
  | same {s t : σ} : M.clock t = M.clock s → M.accts t = M.accts s → Step s t

/-- The part of a state the market reads: its clock and its accounts. -/
def view (s : σ) : Clock × List α := (M.clock s, M.accts s)

/-- The market of views, each read as itself. Chains of steps run over views, so that the states
between two steps of one action (after the first of two changes of units, say) need not be
states of `σ`. -/
def vm : Market (Clock × List α) α where
  one := M.one
  init := M.init
  clock := Prod.fst
  accts := Prod.snd
  dflt := M.dflt
  units₁ := M.units₁
  units₂ := M.units₂
  rec₁ := M.rec₁
  rec₂ := M.rec₂
  credited := M.credited
  dflt_units₁ := M.dflt_units₁
  dflt_units₂ := M.dflt_units₂

/-- `t` is reached from `s` by a chain of steps (through views). -/
def Reach (s t : σ) : Prop := Moves M.vm.Step (M.view s) (M.view t)

/-- One action from `s` at rates `sp`, to `t` at rates `sp'`, emitting `e`: a chain of steps, a
retune that sets the rates, or `k` units of time at the rates `sp`. -/
inductive Act (sp : Nat × Nat) (s : σ) : Nat × Nat → Nat → σ → Prop
  /-- A chain of steps: the rates are kept and nothing is emitted. -/
  | moves {t : σ} : M.Reach s t → Act sp s sp 0 t
  /-- A retune to the rates `(r₁, r₂)`. -/
  | retune {t : σ} {r₁ r₂ : Nat} : M.Retune s t → (M.clock t).rate₁ = r₁ →
      (M.clock t).rate₂ = r₂ → Act sp s (r₁, r₂) 0 t
  /-- `k` units of time at the rates `sp`. -/
  | advance {t : σ} (k : Nat) : M.Advance k s t → Act sp s sp (k * (sp.1 + sp.2)) t

/-- The invariant: no side was brought up to date in the future, no checkpoint is above its
index, each index started from 0 or `init` (`g₁`, `g₂`) and is at or above its start, and the
rates are `sp`. -/
structure Inv (g₁ g₂ : Nat) (sp : Nat × Nat) (s : σ) : Prop where
  /-- Side 1 was last brought up to date at or before now. -/
  last₁ : (M.clock s).last₁ ≤ (M.clock s).now
  /-- Side 2 was last brought up to date at or before now. -/
  last₂ : (M.clock s).last₂ ≤ (M.clock s).now
  /-- No checkpoint is above its index. -/
  recs : ∀ a ∈ M.accts s, M.rec₁ a ≤ (M.clock s).index₁ ∧ M.rec₂ a ≤ (M.clock s).index₂
  /-- Index 1 started from 0 or `init`, at or below it. -/
  start₁ : (g₁ = 0 ∨ g₁ = M.init) ∧ g₁ ≤ (M.clock s).index₁
  /-- Index 2 started from 0 or `init`, at or below it. -/
  start₂ : (g₂ = 0 ∨ g₂ = M.init) ∧ g₂ ≤ (M.clock s).index₂
  /-- The rate of side 1. -/
  rate₁ : (M.clock s).rate₁ = sp.1
  /-- The rate of side 2. -/
  rate₂ : (M.clock s).rate₂ = sp.2

/-! ## Lists -/

/-- A property of every account of a list and of the default holds of every account read by
position. -/
theorem forall_getD {P : α → Prop} {l : List α} (i : Nat) {d : α} (h : ∀ a ∈ l, P a) (hd : P d) :
    P (l.getD i d) := by
  rcases Ledger.getD_mem_or l i d with hm | hm
  · exact h _ hm
  · rw [hm]; exact hd

/-- Units of one account on side 1 are at most the total. -/
theorem units₁_acct_le (s : σ) (w : Nat) : M.units₁ (M.acct s w) ≤ M.total₁ s := by
  rcases Ledger.getD_mem_or (M.accts s) w M.dflt with hm | hm
  · exact Ledger.le_sum_map _ hm
  · unfold acct; rw [hm, M.dflt_units₁]; exact Nat.zero_le _

/-- Units of one account on side 2 are at most the total. -/
theorem units₂_acct_le (s : σ) (w : Nat) : M.units₂ (M.acct s w) ≤ M.total₂ s := by
  rcases Ledger.getD_mem_or (M.accts s) w M.dflt with hm | hm
  · exact Ledger.le_sum_map _ hm
  · unfold acct; rw [hm, M.dflt_units₂]; exact Nat.zero_le _

/-- An account read after a change of the account at position `w`. -/
theorem acct_modify {s t : σ} {w : Nat} {f : α → α} (h : M.accts t = (M.accts s).modify w f)
    (v : Nat) :
    M.acct t v = if w = v ∧ v < (M.accts s).length then f (M.acct s v) else M.acct s v := by
  unfold acct; rw [h, Ledger.getD_modify]

/-! ## The swapped market -/

/-- A field of the exchanged sides. -/
@[simp] theorem swap_accts : M.swap.accts = M.accts := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_clock (s : σ) : M.swap.clock s = (M.clock s).swap := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_one : M.swap.one = M.one := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_init : M.swap.init = M.init := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_units₁ : M.swap.units₁ = M.units₂ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_units₂ : M.swap.units₂ = M.units₁ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_rec₁ : M.swap.rec₁ = M.rec₂ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_rec₂ : M.swap.rec₂ = M.rec₁ := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_credited : M.swap.credited = M.credited := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_acct (s : σ) (w : Nat) : M.swap.acct s w = M.acct s w := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_total₁ (s : σ) : M.swap.total₁ s = M.total₂ s := rfl
/-- A field of the exchanged sides. -/
@[simp] theorem swap_total₂ (s : σ) : M.swap.total₂ s = M.total₁ s := rfl

/-- What an account is owed is the same read through the swapped market. -/
theorem swap_owed (g₁ g₂ : Nat) (c : Clock) (a : α) :
    M.swap.owed g₂ g₁ c.swap a = M.owed g₁ g₂ c a := by
  simp only [owed, swap_units₁, swap_units₂, swap_rec₁, swap_rec₂, Clock.swap_index₁,
    Clock.swap_index₂]
  omega

/-- An account's term is the same read through the swapped market. -/
theorem swap_term (g₁ g₂ : Nat) (c : Clock) (a : α) :
    M.swap.term g₂ g₁ c.swap a = M.term g₁ g₂ c a := by
  simp only [term, swap_owed, swap_credited, swap_one]

/-- The potential is the same read through the swapped market. -/
theorem swap_pot (g₁ g₂ : Nat) (s : σ) : M.swap.pot g₂ g₁ s = M.pot g₁ g₂ s := by
  unfold pot
  simp only [swap_accts, swap_clock, swap_one, Clock.swap_un₁, Clock.swap_un₂]
  have : M.swap.term g₂ g₁ (M.clock s).swap = M.term g₁ g₂ (M.clock s) :=
    funext fun a => M.swap_term g₁ g₂ _ a
  rw [this, Nat.add_comm (Clock.un₂ _)]

/-- An account's potential is the same read through the swapped market. -/
theorem swap_potOf (g₁ g₂ w : Nat) (s : σ) : M.swap.potOf g₂ g₁ w s = M.potOf g₁ g₂ w s := by
  unfold potOf
  rw [swap_acct, swap_clock, swap_term]
  simp only [swap_one, swap_units₁, swap_units₂, Clock.swap_un₁, Clock.swap_un₂]
  ac_rfl

/-- The invariant read through the swapped market. -/
theorem swap_inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : σ} (h : M.Inv g₁ g₂ sp s) :
    M.swap.Inv g₂ g₁ (sp.2, sp.1) s :=
  ⟨h.last₂, h.last₁, fun a ha => (h.recs a ha).symm, h.start₂, h.start₁, h.rate₂, h.rate₁⟩

/-- The invariant read back from the swapped market. -/
theorem inv_of_swap {g₁ g₂ : Nat} {sp : Nat × Nat} {s : σ} (h : M.swap.Inv g₂ g₁ (sp.2, sp.1) s) :
    M.Inv g₁ g₂ sp s :=
  ⟨h.last₂, h.last₁, fun a ha => (h.recs a ha).symm, h.start₂, h.start₁, h.rate₂, h.rate₁⟩

/-- Settled on side 1 of the swapped market is settled on side 2. -/
theorem swap_settled₁ {s : σ} {w : Nat} : M.swap.Settled₁ s w ↔ M.Settled₂ s w := Iff.rfl
/-- Settled on side 2 of the swapped market is settled on side 1. -/
theorem swap_settled₂ {s : σ} {w : Nat} : M.swap.Settled₂ s w ↔ M.Settled₁ s w := Iff.rfl

/-- A settlement on side 2 is a settlement on side 1 of the swapped market. -/
theorem Settle₂.swap {w : Nat} {s t : σ} (h : M.Settle₂ w s t) : M.swap.Settle₁ w s t := by
  obtain ⟨hc, f, ha, hf⟩ := h
  refine ⟨?_, f, ha, ?_⟩
  · simp only [swap_clock, swap_one, swap_total₁, hc]; rfl
  · intro a
    obtain ⟨h1, h2, h3, h4, h5⟩ := hf a
    exact ⟨h1, h2, h3, h4, h5⟩

/-- A settlement on side 1 is a settlement on side 2 of the swapped market. -/
theorem Settle₁.swap {w : Nat} {s t : σ} (h : M.Settle₁ w s t) : M.swap.Settle₂ w s t := by
  obtain ⟨hc, f, ha, hf⟩ := h
  refine ⟨?_, f, ha, ?_⟩
  · simp only [swap_clock, swap_one, swap_total₂, hc]; rfl
  · intro a
    obtain ⟨h1, h2, h3, h4, h5⟩ := hf a
    exact ⟨h1, h2, h3, h4, h5⟩

/-- An adjustment read through the swapped market. -/
theorem Adjust.swap {w : Nat} {s t : σ} (h : M.Adjust w s t) : M.swap.Adjust w s t := by
  obtain ⟨hc, f, ha, hf, hu₁, hu₂⟩ := h
  refine ⟨by simp [hc], f, ha, fun a => ?_, hu₂, hu₁⟩
  obtain ⟨h1, h2, h3⟩ := hf a
  exact ⟨h1, h3, h2⟩

/-- A retune read through the swapped market. -/
theorem Retune.swap {s t : σ} (h : M.Retune s t) : M.swap.Retune s t :=
  ⟨h.accts, h.now, h.side₂, h.side₁⟩

/-- The passage of time read through the swapped market. -/
theorem Advance.swap {k : Nat} {s t : σ} (h : M.Advance k s t) : M.swap.Advance k s t :=
  ⟨by simp only [swap_clock, h.clock]; rfl, h.accts⟩

/-! ## One account's term -/

/-- Moving both indices raises an account's term by at most its units times each increase. -/
theorem term_index_le (g₁ g₂ : Nat) (c c' : Clock) (a : α) :
    M.term g₁ g₂ c' a ≤
      M.term g₁ g₂ c a + M.units₁ a * (c'.index₁ - c.index₁) +
        M.units₂ a * (c'.index₂ - c.index₂) := by
  unfold term owed
  have e1 := owed_le_add (u := M.units₁ a) (i := c.index₁) (i' := c'.index₁)
    (s := effStart g₁ (M.rec₁ a)) (s' := effStart g₁ (M.rec₁ a)) (Nat.le_refl _)
  have e2 := owed_le_add (u := M.units₂ a) (i := c.index₂) (i' := c'.index₂)
    (s := effStart g₂ (M.rec₂ a)) (s' := effStart g₂ (M.rec₂ a)) (Nat.le_refl _)
  omega

/-- An account settled on side 1 at index `c.index₁` does not raise its term, when index 1
started from 0 or `init` and is at or above its start. -/
theorem term_settle₁_le {g₁ g₂ : Nat} {c : Clock} {f : α → α} (hf : M.SettlesAt₁ c.index₁ f)
    (hg : (g₁ = 0 ∨ g₁ = M.init) ∧ g₁ ≤ c.index₁) (a : α) :
    M.term g₁ g₂ c (f a) ≤ M.term g₁ g₂ c a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf a
  unfold term owed
  rw [h1, h2, h3, h4]
  have z : c.index₁ - effStart g₁ c.index₁ = 0 :=
    Nat.sub_eq_zero_of_le (le_effStart_self _ _)
  rw [z, Nat.mul_zero, Nat.zero_add]
  have hs := effStart_le_firstStart (M.rec₁ a) hg.1 hg.2
  have hX : M.units₁ a * (c.index₁ - firstStart M.init (M.rec₁ a) c.index₁) ≤
      M.units₁ a * (c.index₁ - effStart g₁ (M.rec₁ a)) := Nat.mul_le_mul_left _ (by omega)
  have hd := Nat.div_mul_le_self (M.units₁ a * (c.index₁ - firstStart M.init (M.rec₁ a) c.index₁))
    M.one
  have hm := Nat.mul_le_mul_right M.one h5
  rw [Nat.add_mul] at hm
  omega

/-- An adjusted account does not raise its term: on a side where its units change it is
settled, so it is owed nothing there before and after. -/
theorem term_adjust_le {g₁ g₂ : Nat} {c : Clock} {f : α → α} (hf : M.AdjustsAt f) {a : α}
    (hu₁ : M.units₁ (f a) = M.units₁ a ∨ M.rec₁ a = c.index₁)
    (hu₂ : M.units₂ (f a) = M.units₂ a ∨ M.rec₂ a = c.index₂) :
    M.term g₁ g₂ c (f a) ≤ M.term g₁ g₂ c a := by
  obtain ⟨h1, h2, h3⟩ := hf a
  unfold term owed
  rw [h2, h3]
  have hc := Nat.mul_le_mul_right M.one h1
  have k1 : M.units₁ (f a) * (c.index₁ - effStart g₁ (M.rec₁ a)) ≤
      M.units₁ a * (c.index₁ - effStart g₁ (M.rec₁ a)) := by
    rcases hu₁ with e | e
    · exact Nat.le_of_eq (by rw [e])
    · have : c.index₁ - effStart g₁ (M.rec₁ a) = 0 := by
        have := le_effStart_self g₁ (M.rec₁ a); omega
      rw [this]; simp
  have k2 : M.units₂ (f a) * (c.index₂ - effStart g₂ (M.rec₂ a)) ≤
      M.units₂ a * (c.index₂ - effStart g₂ (M.rec₂ a)) := by
    rcases hu₂ with e | e
    · exact Nat.le_of_eq (by rw [e])
    · have : c.index₂ - effStart g₂ (M.rec₂ a) = 0 := by
        have := le_effStart_self g₂ (M.rec₂ a); omega
      rw [this]; simp
  omega

/-- One side's share of an update covered by the emission: zero when the account holds no units
there. -/
theorem side_ite_le {u T d one U U' : Nat} (hu : u ≤ T) (h : T * d + one * U' ≤ one * U) :
    u * d + one * (if 0 < u then U' else 0) ≤ one * (if 0 < u then U else 0) := by
  have : u * d ≤ T * d := Nat.mul_le_mul_right _ hu
  split
  · omega
  · have : u = 0 := by omega
    subst this; simp

/-! ## Settlements -/

section Settle

variable {M}

/-- A settlement does not move the time. -/
theorem Settle₁.now {w : Nat} {s t : σ} (h : M.Settle₁ w s t) : (M.clock t).now = (M.clock s).now := by
  rw [h.clock]; rfl

/-- A settlement does not lower the index of its side. -/
theorem Settle₁.index₁_le {w : Nat} {s t : σ} (h : M.Settle₁ w s t) :
    (M.clock s).index₁ ≤ (M.clock t).index₁ := by
  rw [h.clock]; exact Clock.le_catchUp₁_index₁ _ _ _

/-- A settlement keeps the number of accounts. -/
theorem Settle₁.length {w : Nat} {s t : σ} (h : M.Settle₁ w s t) :
    (M.accts t).length = (M.accts s).length := by
  obtain ⟨f, ha, -⟩ := h.accts
  rw [ha, List.length_modify]

/-- A settlement keeps the invariant. -/
theorem Settle₁.inv {g₁ g₂ : Nat} {sp : Nat × Nat} {w : Nat} {s t : σ} (h : M.Settle₁ w s t)
    (hI : M.Inv g₁ g₂ sp s) : M.Inv g₁ g₂ sp t := by
  obtain ⟨hc, f, ha, hf⟩ := h
  have hi : (M.clock s).index₁ ≤ (M.clock t).index₁ := by
    rw [hc]; exact Clock.le_catchUp₁_index₁ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]; exact Nat.le_refl _
  · rw [hc]; exact hI.last₂
  · rw [ha]
    refine forall_mem_modify (P := fun a => M.rec₁ a ≤ (M.clock t).index₁ ∧
      M.rec₂ a ≤ (M.clock t).index₂) ?_ ?_
    · intro a hm
      have := hI.recs a hm
      rw [hc] at hi ⊢
      exact ⟨Nat.le_trans this.1 hi, this.2⟩
    · intro a hm
      obtain ⟨-, -, h3, h4, -⟩ := hf a
      have := hI.recs a hm
      rw [h3, h4]
      refine ⟨Nat.le_refl _, ?_⟩
      rw [hc]; exact this.2
  · exact ⟨hI.start₁.1, Nat.le_trans hI.start₁.2 hi⟩
  · rw [hc]; exact hI.start₂
  · rw [hc]; exact hI.rate₁
  · rw [hc]; exact hI.rate₂

/-- A settlement does not raise the potential. -/
theorem Settle₁.pot_le {g₁ g₂ : Nat} {sp : Nat × Nat} {w : Nat} {s t : σ} (h : M.Settle₁ w s t)
    (hI : M.Inv g₁ g₂ sp s) : M.pot g₁ g₂ t ≤ M.pot g₁ g₂ s := by
  have hI' := h.inv hI
  obtain ⟨hc, f, ha, hf⟩ := h
  have hcov := (covered_catchUp M.one (M.clock s).index₁ (M.clock s).last₁ (M.clock s).rate₁
    (M.clock s).now (M.total₁ s)).2
  have h1 : ((M.accts t).map (M.term g₁ g₂ (M.clock t))).sum ≤
      ((M.accts s).map (M.term g₁ g₂ (M.clock t))).sum := by
    rw [ha]
    exact Ledger.sum_map_modify_le _ _ _ _ M.dflt fun _ =>
      M.term_settle₁_le hf hI'.start₁ _
  have hi : (M.clock s).index₁ ≤ (M.clock t).index₁ := by
    rw [hc]; exact Clock.le_catchUp₁_index₁ _ _ _
  have h2 : ((M.accts s).map (M.term g₁ g₂ (M.clock t))).sum ≤
      ((M.accts s).map (M.term g₁ g₂ (M.clock s))).sum +
        (M.total₁ s * ((M.clock t).index₁ - (M.clock s).index₁) +
          M.total₂ s * ((M.clock t).index₂ - (M.clock s).index₂)) :=
    sum_le_of_index_le₂ _ _ _ _ _ (fun a _ => M.term_index_le g₁ g₂ _ _ a) (Nat.le_refl _)
  unfold pot
  have e2 : (M.clock t).index₂ - (M.clock s).index₂ = 0 := by rw [hc]; simp [Clock.catchUp₁]
  have u1 : (M.clock t).un₁ = 0 := by rw [hc]; simp
  have u2 : (M.clock t).un₂ = (M.clock s).un₂ := by rw [hc]; rfl
  have ci : (M.clock t).index₁ = catchUp M.one (M.clock s).index₁ (M.clock s).last₁
      (M.clock s).rate₁ (M.clock s).now (M.total₁ s) := by rw [hc]; rfl
  rw [e2, Nat.mul_zero, Nat.add_zero] at h2
  rw [u1, u2]
  rw [← ci] at hcov
  unfold Clock.un₁ at *
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- A settlement does not raise the potential of any account. -/
theorem Settle₁.potOf_le {g₁ g₂ : Nat} {sp : Nat × Nat} {w : Nat} {s t : σ} (h : M.Settle₁ w s t)
    (hI : M.Inv g₁ g₂ sp s) (v : Nat) : M.potOf g₁ g₂ v t ≤ M.potOf g₁ g₂ v s := by
  have hI' := h.inv hI
  obtain ⟨hc, f, ha, hf⟩ := h
  have hcov := covered_catchUp M.one (M.clock s).index₁ (M.clock s).last₁ (M.clock s).rate₁
    (M.clock s).now (M.total₁ s)
  have hi : (M.clock s).index₁ ≤ (M.clock t).index₁ := by
    rw [hc]; exact Clock.le_catchUp₁_index₁ _ _ _
  have ci : (M.clock t).index₁ = catchUp M.one (M.clock s).index₁ (M.clock s).last₁
      (M.clock s).rate₁ (M.clock s).now (M.total₁ s) := by rw [hc]; rfl
  rw [← ci] at hcov
  have e2 : (M.clock t).index₂ = (M.clock s).index₂ := by rw [hc]; rfl
  have u1 : (M.clock t).un₁ = 0 := by rw [hc]; simp
  have u2 : (M.clock t).un₂ = (M.clock s).un₂ := by rw [hc]; rfl
  -- the account after, with the same units, and a term no larger than before at the new clock
  have key : ∃ a', M.acct t v = a' ∧ M.units₁ a' = M.units₁ (M.acct s v) ∧ M.units₂ a' = M.units₂ (M.acct s v) ∧
      M.term g₁ g₂ (M.clock t) a' ≤ M.term g₁ g₂ (M.clock t) (M.acct s v) := by
    rw [M.acct_modify ha v]
    split
    · obtain ⟨h1, h2, -⟩ := hf (M.acct s v)
      exact ⟨_, rfl, h1, h2, M.term_settle₁_le hf hI'.start₁ (M.acct s v)⟩
    · exact ⟨_, rfl, rfl, rfl, Nat.le_refl _⟩
  obtain ⟨a', ha', hu1, hu2, ht⟩ := key
  have hti := M.term_index_le g₁ g₂ (M.clock s) (M.clock t) (M.acct s v)
  rw [e2, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hti
  have hs := side_ite_le (u := M.units₁ (M.acct s v)) (T := M.total₁ s) (one := M.one)
    (d := (M.clock t).index₁ - (M.clock s).index₁) (U' := (M.clock t).un₁) (U := (M.clock s).un₁) (M.units₁_acct_le s v)
    (by rw [u1, Nat.mul_zero, Nat.add_zero]; exact hcov.2)
  unfold potOf
  rw [ha', hu1, hu2, u2]
  rw [Nat.mul_add, Nat.mul_add] at *
  omega

/-- A settlement on side 2 keeps the invariant. -/
theorem Settle₂.inv {g₁ g₂ : Nat} {sp : Nat × Nat} {w : Nat} {s t : σ} (h : M.Settle₂ w s t)
    (hI : M.Inv g₁ g₂ sp s) : M.Inv g₁ g₂ sp t :=
  M.inv_of_swap ((h.swap).inv (M.swap_inv hI))

/-- A settlement on side 2 does not raise the potential. -/
theorem Settle₂.pot_le {g₁ g₂ : Nat} {sp : Nat × Nat} {w : Nat} {s t : σ} (h : M.Settle₂ w s t)
    (hI : M.Inv g₁ g₂ sp s) : M.pot g₁ g₂ t ≤ M.pot g₁ g₂ s := by
  rw [← M.swap_pot, ← M.swap_pot]; exact (h.swap).pot_le (M.swap_inv hI)

/-- A settlement on side 2 does not raise the potential of any account. -/
theorem Settle₂.potOf_le {g₁ g₂ : Nat} {sp : Nat × Nat} {w : Nat} {s t : σ} (h : M.Settle₂ w s t)
    (hI : M.Inv g₁ g₂ sp s) (v : Nat) : M.potOf g₁ g₂ v t ≤ M.potOf g₁ g₂ v s := by
  rw [← M.swap_potOf, ← M.swap_potOf]; exact (h.swap).potOf_le (M.swap_inv hI) v

/-- A settlement on side 1 leaves the settled account settled there. -/
theorem Settle₁.settled {w : Nat} {s t : σ} (h : M.Settle₁ w s t) : M.Settled₁ t w := by
  have hl := h.length
  obtain ⟨hc, f, ha, hf⟩ := h
  refine ⟨by rw [hc]; rfl, fun hw => ?_⟩
  rw [M.acct_modify ha w]
  split
  · exact (hf _).2.2.1
  · rename_i hn; exact absurd ⟨rfl, by omega⟩ hn

/-- A settlement on side 2 leaves the settled account settled there. -/
theorem Settle₂.settled {w : Nat} {s t : σ} (h : M.Settle₂ w s t) : M.Settled₂ t w :=
  (h.swap).settled

/-- A settlement on side 1 keeps every account settled there that was. -/
theorem Settled₁.settle₁ {v w : Nat} {s t : σ} (hv : M.Settled₁ s v) (h : M.Settle₁ w s t) :
    M.Settled₁ t v := by
  have hl := h.length
  obtain ⟨hc, f, ha, hf⟩ := h
  have hi : (M.clock t).index₁ = (M.clock s).index₁ := by
    rw [hc]; exact catchUp_of_le (Nat.le_of_eq hv.1.symm)
  refine ⟨by rw [hc]; rfl, fun hw => ?_⟩
  rw [M.acct_modify ha v, hi]
  split
  · rw [(hf _).2.2.1, hi]
  · exact hv.2 (by omega)

/-- A settlement on side 2 keeps every account settled on side 1 that was. -/
theorem Settled₁.settle₂ {v w : Nat} {s t : σ} (hv : M.Settled₁ s v) (h : M.Settle₂ w s t) :
    M.Settled₁ t v := by
  have hl : (M.accts t).length = (M.accts s).length := by
    obtain ⟨f, ha, -⟩ := h.accts; rw [ha, List.length_modify]
  obtain ⟨hc, f, ha, hf⟩ := h
  refine ⟨by rw [hc]; exact hv.1, fun hw => ?_⟩
  rw [M.acct_modify ha v]
  have e : (M.clock t).index₁ = (M.clock s).index₁ := by rw [hc]; rfl
  rw [e]
  split
  · rw [(hf _).2.2.2.1]; exact hv.2 (by omega)
  · exact hv.2 (by omega)

/-- A settlement on side 2 keeps every account settled there that was. -/
theorem Settled₂.settle₂ {v w : Nat} {s t : σ} (hv : M.Settled₂ s v) (h : M.Settle₂ w s t) :
    M.Settled₂ t v :=
  Settled₁.settle₁ (M := M.swap) hv h.swap

/-- A settlement on side 1 keeps every account settled on side 2 that was. -/
theorem Settled₂.settle₁ {v w : Nat} {s t : σ} (hv : M.Settled₂ s v) (h : M.Settle₁ w s t) :
    M.Settled₂ t v :=
  Settled₁.settle₂ (M := M.swap) hv h.swap

/-- An adjustment keeps every account settled on side 1 that was. -/
theorem Settled₁.adjust {v w : Nat} {s t : σ} (hv : M.Settled₁ s v) (h : M.Adjust w s t) :
    M.Settled₁ t v := by
  obtain ⟨hc, f, ha, hf, -, -⟩ := h
  have hl : (M.accts t).length = (M.accts s).length := by rw [ha, List.length_modify]
  refine ⟨by rw [hc]; exact hv.1, fun hw => ?_⟩
  rw [M.acct_modify ha v, hc]
  split
  · rw [(hf _).2.1]; exact hv.2 (by omega)
  · exact hv.2 (by omega)

/-- An adjustment keeps every account settled on side 2 that was. -/
theorem Settled₂.adjust {v w : Nat} {s t : σ} (hv : M.Settled₂ s v) (h : M.Adjust w s t) :
    M.Settled₂ t v :=
  Settled₁.adjust (M := M.swap) hv h.swap

end Settle

/-! ## Adjustments, retunes and the passage of time -/

section Others

variable {M}

/-- An adjustment keeps the invariant. -/
theorem Adjust.inv {g₁ g₂ : Nat} {sp : Nat × Nat} {w : Nat} {s t : σ} (h : M.Adjust w s t)
    (hI : M.Inv g₁ g₂ sp s) : M.Inv g₁ g₂ sp t := by
  obtain ⟨hc, f, ha, hf, -, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hc]
  · exact hI.last₁
  · exact hI.last₂
  · rw [ha]
    refine forall_mem_modify (P := fun a => M.rec₁ a ≤ (M.clock s).index₁ ∧
      M.rec₂ a ≤ (M.clock s).index₂) hI.recs ?_
    intro a hm
    obtain ⟨-, h2, h3⟩ := hf a
    rw [h2, h3]; exact hI.recs a hm
  · exact hI.start₁
  · exact hI.start₂
  · exact hI.rate₁
  · exact hI.rate₂

/-- The term of an adjusted account does not grow, in the form both potentials use. -/
theorem Adjust.term_le {g₁ g₂ : Nat} {w : Nat} {s : σ} {f : α → α}
    (hf : M.AdjustsAt f) (hu₁ : (∀ a, M.units₁ (f a) = M.units₁ a) ∨ M.Settled₁ s w)
    (hu₂ : (∀ a, M.units₂ (f a) = M.units₂ a) ∨ M.Settled₂ s w) (hw : w < (M.accts s).length) :
    M.term g₁ g₂ (M.clock s) (f (M.acct s w)) ≤ M.term g₁ g₂ (M.clock s) (M.acct s w) := by
  refine M.term_adjust_le hf ?_ ?_
  · rcases hu₁ with e | e
    · exact Or.inl (e _)
    · exact Or.inr (e.2 hw)
  · rcases hu₂ with e | e
    · exact Or.inl (e _)
    · exact Or.inr (e.2 hw)

/-- An adjustment does not raise the potential. -/
theorem Adjust.pot_le {g₁ g₂ : Nat} {w : Nat} {s t : σ} (h : M.Adjust w s t) :
    M.pot g₁ g₂ t ≤ M.pot g₁ g₂ s := by
  obtain ⟨hc, f, ha, hf, hu₁, hu₂⟩ := h
  unfold pot
  rw [hc, ha]
  have := Ledger.sum_map_modify_le (M.accts s) w f (M.term g₁ g₂ (M.clock s)) M.dflt
    fun hw => Adjust.term_le (g₁ := g₁) (g₂ := g₂) hf hu₁ hu₂ hw
  omega

/-- An adjustment does not raise the potential of any account. -/
theorem Adjust.potOf_le {g₁ g₂ : Nat} {w : Nat} {s t : σ} (h : M.Adjust w s t) (v : Nat) :
    M.potOf g₁ g₂ v t ≤ M.potOf g₁ g₂ v s := by
  obtain ⟨hc, f, ha, hf, hu₁, hu₂⟩ := h
  unfold potOf
  rw [hc, M.acct_modify ha v]
  split
  · rename_i hv
    obtain ⟨rfl, hw⟩ := hv
    have ht := Adjust.term_le (g₁ := g₁) (g₂ := g₂) hf hu₁ hu₂ hw
    have k1 : (if 0 < M.units₁ (f (M.acct s w)) then (M.clock s).un₁ else 0) ≤
        (if 0 < M.units₁ (M.acct s w) then (M.clock s).un₁ else 0) := by
      rcases hu₁ with e | e
      · exact Nat.le_of_eq (by rw [e])
      · have : (M.clock s).un₁ = 0 := by simp [Clock.un₁, unindexed, e.1]
        simp [this]
    have k2 : (if 0 < M.units₂ (f (M.acct s w)) then (M.clock s).un₂ else 0) ≤
        (if 0 < M.units₂ (M.acct s w) then (M.clock s).un₂ else 0) := by
      rcases hu₂ with e | e
      · exact Nat.le_of_eq (by rw [e])
      · have : (M.clock s).un₂ = 0 := by simp [Clock.un₂, unindexed, e.1]
        simp [this]
    have := Nat.mul_le_mul_left M.one (Nat.add_le_add k1 k2)
    omega
  · exact Nat.le_refl _

/-- A side left as it is or brought up to date: its index does not fall, and its total units
times the increase plus what it leaves unindexed is at most what was unindexed before. -/
theorem SideMove.bound {one T now i l r i' l' r' : Nat} (h : SideMove one T now i l r i' l' r')
    (hl : l ≤ now) :
    i ≤ i' ∧ l' ≤ now ∧ T * (i' - i) + one * unindexed l' r' now ≤ one * unindexed l r now := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨h1, h2⟩
  · simp [hl]
  · have := (covered_catchUp one i l r now T)
    rw [h1, h2]
    exact ⟨this.1, Nat.le_refl _, by simp [this.2]⟩

/-- A retune keeps the invariant at the rates it leaves. -/
theorem Retune.inv' {g₁ g₂ : Nat} {sp : Nat × Nat} {s t : σ} (h : M.Retune s t)
    (hI : M.Inv g₁ g₂ sp s) : M.Inv g₁ g₂ ((M.clock t).rate₁, (M.clock t).rate₂) t := by
  obtain ⟨ha, hn, h1, h2⟩ := h
  have b1 := h1.bound hI.last₁
  have b2 := h2.bound hI.last₂
  refine ⟨by rw [hn]; exact b1.2.1, by rw [hn]; exact b2.2.1, ?_, ?_, ?_, rfl, rfl⟩
  · rw [ha]; intro a hm
    have := hI.recs a hm
    exact ⟨Nat.le_trans this.1 b1.1, Nat.le_trans this.2 b2.1⟩
  · exact ⟨hI.start₁.1, Nat.le_trans hI.start₁.2 b1.1⟩
  · exact ⟨hI.start₂.1, Nat.le_trans hI.start₂.2 b2.1⟩

/-- A retune keeps the invariant at the new rates. -/
theorem Retune.inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s t : σ} {r₁ r₂ : Nat} (h : M.Retune s t)
    (hI : M.Inv g₁ g₂ sp s) (h₁ : (M.clock t).rate₁ = r₁) (h₂ : (M.clock t).rate₂ = r₂) :
    M.Inv g₁ g₂ (r₁, r₂) t := by
  subst h₁ h₂; exact h.inv' hI

/-- A retune does not raise the potential: what a side indexes was unindexed before. -/
theorem Retune.pot_le {g₁ g₂ : Nat} {sp : Nat × Nat} {s t : σ} (h : M.Retune s t)
    (hI : M.Inv g₁ g₂ sp s) : M.pot g₁ g₂ t ≤ M.pot g₁ g₂ s := by
  obtain ⟨ha, hn, h1, h2⟩ := h
  have b1 := h1.bound hI.last₁
  have b2 := h2.bound hI.last₂
  have hs := sum_le_of_index_le₂ (M.accts s) (M.term g₁ g₂ (M.clock s))
    (M.term g₁ g₂ (M.clock t)) M.units₁ M.units₂ (E := M.total₁ s *
      ((M.clock t).index₁ - (M.clock s).index₁) + M.total₂ s *
        ((M.clock t).index₂ - (M.clock s).index₂))
    (fun a _ => M.term_index_le g₁ g₂ _ _ a) (Nat.le_refl _)
  unfold pot Clock.un₁ Clock.un₂
  rw [ha, hn]
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- A retune does not raise the potential of any account. -/
theorem Retune.potOf_le {g₁ g₂ : Nat} {sp : Nat × Nat} {s t : σ} (h : M.Retune s t)
    (hI : M.Inv g₁ g₂ sp s) (v : Nat) : M.potOf g₁ g₂ v t ≤ M.potOf g₁ g₂ v s := by
  obtain ⟨ha, hn, h1, h2⟩ := h
  have b1 := h1.bound hI.last₁
  have b2 := h2.bound hI.last₂
  have hacct : M.acct t v = M.acct s v := by unfold acct; rw [ha]
  have ht := M.term_index_le g₁ g₂ (M.clock s) (M.clock t) (M.acct s v)
  have s1 := side_ite_le (one := M.one) (M.units₁_acct_le s v) b1.2.2
  have s2 := side_ite_le (one := M.one) (M.units₂_acct_le s v) b2.2.2
  unfold potOf Clock.un₁ Clock.un₂
  rw [hacct, hn]
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- The passage of time keeps the invariant. -/
theorem Advance.inv {g₁ g₂ : Nat} {sp : Nat × Nat} {k : Nat} {s t : σ} (h : M.Advance k s t)
    (hI : M.Inv g₁ g₂ sp s) : M.Inv g₁ g₂ sp t := by
  obtain ⟨hc, ha⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hc] <;> simp only [Clock.advance]
  · exact Nat.le_trans hI.last₁ (Nat.le_add_right _ _)
  · exact Nat.le_trans hI.last₂ (Nat.le_add_right _ _)
  · rw [ha]; exact hI.recs
  · exact hI.start₁
  · exact hI.start₂
  · exact hI.rate₁
  · exact hI.rate₂

/-- Time passing raises the potential by exactly `one` times the emission at the current rates. -/
theorem Advance.pot_eq {g₁ g₂ : Nat} {sp : Nat × Nat} {k : Nat} {s t : σ} (h : M.Advance k s t)
    (hI : M.Inv g₁ g₂ sp s) : M.pot g₁ g₂ t = M.pot g₁ g₂ s + M.one * (k * (sp.1 + sp.2)) := by
  obtain ⟨hc, ha⟩ := h
  unfold pot
  rw [hc, ha]
  have e1 := unindexed_add (M.clock s).rate₁ k hI.last₁
  have e2 := unindexed_add (M.clock s).rate₂ k hI.last₂
  have : M.term g₁ g₂ ((M.clock s).advance k) = M.term g₁ g₂ (M.clock s) := rfl
  rw [this]
  simp only [Clock.un₁, Clock.un₂, Clock.advance]
  rw [e1, e2, ← hI.rate₁, ← hI.rate₂]
  simp only [Nat.mul_add]
  omega

/-- Time passing raises the potential of one account by at most `one` times the emission. -/
theorem Advance.potOf_le {g₁ g₂ : Nat} {sp : Nat × Nat} {k : Nat} {s t : σ} (h : M.Advance k s t)
    (hI : M.Inv g₁ g₂ sp s) (v : Nat) :
    M.potOf g₁ g₂ v t ≤ M.potOf g₁ g₂ v s + M.one * (k * (sp.1 + sp.2)) := by
  obtain ⟨hc, ha⟩ := h
  have hacct : M.acct t v = M.acct s v := by unfold acct; rw [ha]
  unfold potOf
  rw [hacct, hc]
  have : M.term g₁ g₂ ((M.clock s).advance k) = M.term g₁ g₂ (M.clock s) := rfl
  rw [this]
  have e1 := unindexed_ite_add (0 < M.units₁ (M.acct s v)) (M.clock s).rate₁ k hI.last₁
  have e2 := unindexed_ite_add (0 < M.units₂ (M.acct s v)) (M.clock s).rate₂ k hI.last₂
  simp only [Clock.un₁, Clock.un₂, Clock.advance]
  rw [← hI.rate₁, ← hI.rate₂]
  have := Nat.mul_le_mul_left M.one (Nat.add_le_add e1 e2)
  simp only [Nat.mul_add] at this ⊢
  omega

end Others

/-! ## Steps, chains and actions -/

section Actions

variable {M}

/-- A step keeps the invariant and raises neither potential. -/
theorem Step.bound {g₁ g₂ : Nat} {sp : Nat × Nat} {s t : σ} (h : M.Step s t)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Inv g₁ g₂ sp t ∧ M.pot g₁ g₂ t ≤ M.pot g₁ g₂ s ∧
      ∀ v, M.potOf g₁ g₂ v t ≤ M.potOf g₁ g₂ v s := by
  obtain ⟨p₁, p₂⟩ := sp
  cases h with
  | settle₁ h => exact ⟨h.inv hI, h.pot_le hI, h.potOf_le hI⟩
  | settle₂ h => exact ⟨h.inv hI, h.pot_le hI, h.potOf_le hI⟩
  | adjust h => exact ⟨h.inv hI, h.pot_le, h.potOf_le⟩
  | retune h e1 e2 =>
    have := h.inv (r₁ := p₁) (r₂ := p₂) hI (e1.trans hI.rate₁) (e2.trans hI.rate₂)
    exact ⟨this, h.pot_le hI, h.potOf_le hI⟩
  | same hc ha =>
    have hacct : ∀ v, M.acct t v = M.acct s v := fun v => by unfold acct; rw [ha]
    refine ⟨?_, ?_, fun v => ?_⟩
    · obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
      exact ⟨hc ▸ i1, hc ▸ i2, by rw [ha, hc]; exact i3, hc ▸ i4, hc ▸ i5, hc ▸ i6, hc ▸ i7⟩
    · unfold pot; rw [hc, ha]; exact Nat.le_refl _
    · unfold potOf; rw [hc, hacct]; exact Nat.le_refl _

/-- A chain of steps keeps the invariant and raises neither potential. -/
theorem moves_bound {g₁ g₂ : Nat} {sp : Nat × Nat} {s t : σ} (h : Moves M.Step s t)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Inv g₁ g₂ sp t ∧ M.pot g₁ g₂ t ≤ M.pot g₁ g₂ s ∧
      ∀ v, M.potOf g₁ g₂ v t ≤ M.potOf g₁ g₂ v s := by
  refine ⟨(h.bound (P := M.pot g₁ g₂) (fun _ _ hs hi => ⟨(hs.bound hi).1, (hs.bound hi).2.1⟩)
    hI).1, (h.bound (P := M.pot g₁ g₂) (fun _ _ hs hi => ⟨(hs.bound hi).1, (hs.bound hi).2.1⟩)
    hI).2, fun v => ?_⟩
  exact (h.bound (P := M.potOf g₁ g₂ v)
    (fun _ _ hs hi => ⟨(hs.bound hi).1, (hs.bound hi).2.2 v⟩) hI).2

/-- A step read on views. -/
theorem Step.view {s t : σ} (h : M.Step s t) : M.vm.Step (M.view s) (M.view t) := by
  cases h with
  | settle₁ h => exact .settle₁ ⟨h.1, h.2⟩
  | settle₂ h => exact .settle₂ ⟨h.1, h.2⟩
  | adjust h => exact .adjust ⟨h.1, h.2⟩
  | retune h e1 e2 => exact .retune ⟨h.1, h.2, h.3, h.4⟩ e1 e2
  | same hc ha => exact .same hc ha

/-- No step: a state reaches itself. -/
theorem Reach.refl (s : σ) : M.Reach s s := Moves.refl _

/-- One step. -/
theorem Reach.single {s t : σ} (h : M.Step s t) : M.Reach s t := Moves.single h.view

/-- Chains compose. -/
theorem Reach.trans {s t u : σ} (h₁ : M.Reach s t) (h₂ : M.Reach t u) : M.Reach s u :=
  Moves.trans h₁ h₂

/-- A chain followed by one step. -/
theorem Reach.tail {s t u : σ} (h₁ : M.Reach s t) (h₂ : M.Step t u) : M.Reach s u :=
  Moves.tail h₁ h₂.view

/-- A call that returns a new state or fails, where a failed call leaves the state unchanged
(`o.getD s`), is a chain when every result is. -/
theorem Reach.of_getD {o : Option σ} {s : σ} (h : ∀ t, o = some t → M.Reach s t) :
    M.Reach s (o.getD s) := by
  cases o with
  | none => exact Reach.refl _
  | some t => exact h t rfl

/-- A chain of steps keeps the invariant and raises neither potential. -/
theorem Reach.bound {g₁ g₂ : Nat} {sp : Nat × Nat} {s t : σ} (h : M.Reach s t)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Inv g₁ g₂ sp t ∧ M.pot g₁ g₂ t ≤ M.pot g₁ g₂ s ∧
      ∀ v, M.potOf g₁ g₂ v t ≤ M.potOf g₁ g₂ v s := by
  have hI' : M.vm.Inv g₁ g₂ sp (M.view s) := ⟨hI.1, hI.2, hI.3, hI.4, hI.5, hI.6, hI.7⟩
  have r := moves_bound h hI'
  exact ⟨⟨r.1.1, r.1.2, r.1.3, r.1.4, r.1.5, r.1.6, r.1.7⟩, r.2.1, r.2.2⟩

/-- An action keeps the invariant (at its new rates) and raises each potential by at most `one`
times its emission. -/
theorem Act.bound {g₁ g₂ : Nat} {sp sp' : Nat × Nat} {e : Nat} {s t : σ} (h : M.Act sp s sp' e t)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Inv g₁ g₂ sp' t ∧ M.pot g₁ g₂ t ≤ M.pot g₁ g₂ s + M.one * e ∧
      ∀ v, M.potOf g₁ g₂ v t ≤ M.potOf g₁ g₂ v s + M.one * e := by
  cases h with
  | moves h =>
    have := h.bound hI
    exact ⟨this.1, by simpa using this.2.1, fun v => by simpa using this.2.2 v⟩
  | retune h e1 e2 =>
    exact ⟨h.inv hI e1 e2, by simpa using h.pot_le hI, fun v => by simpa using h.potOf_le hI v⟩
  | advance k h =>
    exact ⟨h.inv hI, Nat.le_of_eq (h.pot_eq hI), h.potOf_le hI⟩

end Actions

/-! ## Runs -/

section Runs

variable {β : Type w}

/-- The potential bound over a run (any sequence of operations), from one step bound per
operation. `run`, the emission `total` and the rates `ghost` after a run are given
by their defining equations (each holds by `rfl` for definitions by structural recursion, and is
proved by `rfl` when omitted). When every action from a state satisfying the invariant is an
`Act` whose rates and emission are those of `next` and `f`, a run keeps the invariant and raises
each potential by at most `one` times the emission. -/
theorem run_bound {step : σ → β → σ} {next : Nat × Nat → β → Nat × Nat}
    {f : Nat × Nat → β → Nat}
    (run : σ → List β → σ) (total : Nat × Nat → List β → Nat)
    (ghost : Nat × Nat → List β → Nat × Nat) {g₁ g₂ : Nat}
    (hact : ∀ sp s a, M.Inv g₁ g₂ sp s → M.Act sp s (next sp a) (f sp a) (step s a))
    {sp : Nat × Nat} {s : σ} (h0 : M.Inv g₁ g₂ sp s) (as : List β)
    (hr0 : ∀ s, run s [] = s := by intros; rfl)
    (hr1 : ∀ s a as, run s (a :: as) = run (step s a) as := by intros; rfl)
    (ht0 : ∀ g, total g [] = 0 := by intros; rfl)
    (ht1 : ∀ g a as, total g (a :: as) = f g a + total (next g a) as := by intros; rfl)
    (hg0 : ∀ g, ghost g [] = g := by intros; rfl)
    (hg1 : ∀ g a as, ghost g (a :: as) = ghost (next g a) as := by intros; rfl) :
    M.Inv g₁ g₂ (ghost sp as) (run s as) ∧
      M.pot g₁ g₂ (run s as) ≤ M.pot g₁ g₂ s + M.one * total sp as ∧
      ∀ v, M.potOf g₁ g₂ v (run s as) ≤ M.potOf g₁ g₂ v s + M.one * total sp as := by
  have hstep : ∀ (P : σ → Nat), (∀ sp s a, M.Inv g₁ g₂ sp s →
      P (step s a) ≤ P s + M.one * f sp a) → ∀ sp s a, M.Inv g₁ g₂ sp s →
      M.Inv g₁ g₂ (next sp a) (step s a) ∧ P (step s a) ≤ P s + M.one * f sp a :=
    fun P hP sp s a hI => ⟨((hact sp s a hI).bound hI).1, hP sp s a hI⟩
  have r := Accumulator.run_bound run total ghost hr0 hr1 ht0 ht1 hg0 hg1
    (fun sp s => M.Inv g₁ g₂ sp s) (M.pot g₁ g₂) M.one
    (hstep _ fun sp s a hI => ((hact sp s a hI).bound hI).2.1) h0 as
  refine ⟨r.2, r.1, fun v => ?_⟩
  exact (Accumulator.run_bound run total ghost hr0 hr1 ht0 ht1 hg0 hg1
    (fun sp s => M.Inv g₁ g₂ sp s) (M.potOf g₁ g₂ v) M.one
    (hstep _ fun sp s a hI => ((hact sp s a hI).bound hI).2.2 v) h0 as).1

end Runs

/-! ## From the potential to credited amounts -/

/-- The credited amount of all accounts at scale `one` is at most the potential. -/
theorem creditSum_mul_le_pot (g₁ g₂ : Nat) (s : σ) : M.creditSum s * M.one ≤ M.pot g₁ g₂ s := by
  unfold creditSum pot term
  have := sum_mul_le_sum_scaled (M.accts s) M.credited (M.owed g₁ g₂ (M.clock s)) M.one
  exact Nat.le_trans this (Nat.le_add_right _ _)

/-- The credited amount of one account at scale `one` is at most its potential. -/
theorem credited_mul_le_potOf (g₁ g₂ w : Nat) (s : σ) :
    M.credited (M.acct s w) * M.one ≤ M.potOf g₁ g₂ w s := by
  unfold potOf term; omega

/-- The potential at a state from bounds on what each account is owed (`q`) and on each side's
emission not yet indexed. -/
theorem pot_le_of {g₁ g₂ : Nat} {s : σ} {q : α → Nat} {U₁ U₂ : Nat}
    (hq : ∀ a ∈ M.accts s, M.owed g₁ g₂ (M.clock s) a ≤ q a) (h₁ : (M.clock s).un₁ ≤ U₁)
    (h₂ : (M.clock s).un₂ ≤ U₂) :
    M.pot g₁ g₂ s ≤ M.creditSum s * M.one + ((M.accts s).map q).sum + M.one * (U₁ + U₂) := by
  unfold pot term creditSum
  have := sum_scaled_le (M.accts s) M.credited (M.owed g₁ g₂ (M.clock s)) q M.one hq
  have := Nat.mul_le_mul_left M.one (Nat.add_le_add h₁ h₂)
  omega

/-- The potential of one account from a bound `R` on what it is owed and bounds on each side's
emission not yet indexed. -/
theorem potOf_le_of {g₁ g₂ w : Nat} {s : σ} {R U₁ U₂ : Nat}
    (hq : M.owed g₁ g₂ (M.clock s) (M.acct s w) ≤ R) (h₁ : (M.clock s).un₁ ≤ U₁)
    (h₂ : (M.clock s).un₂ ≤ U₂) :
    M.potOf g₁ g₂ w s ≤ M.credited (M.acct s w) * M.one + R +
      M.one * ((if 0 < M.units₁ (M.acct s w) then U₁ else 0) +
        (if 0 < M.units₂ (M.acct s w) then U₂ else 0)) := by
  unfold potOf term
  have k1 : (if 0 < M.units₁ (M.acct s w) then (M.clock s).un₁ else 0) ≤
      (if 0 < M.units₁ (M.acct s w) then U₁ else 0) := by split <;> omega
  have k2 : (if 0 < M.units₂ (M.acct s w) then (M.clock s).un₂ else 0) ≤
      (if 0 < M.units₂ (M.acct s w) then U₂ else 0) := by split <;> omega
  have := Nat.mul_le_mul_left M.one (Nat.add_le_add k1 k2)
  omega

/-- The potential of an account that holds no units is its credited amount at scale `one`. -/
theorem potOf_of_no_units {g₁ g₂ w : Nat} {s : σ} (h₁ : M.units₁ (M.acct s w) = 0)
    (h₂ : M.units₂ (M.acct s w) = 0) :
    M.potOf g₁ g₂ w s = M.credited (M.acct s w) * M.one := by
  unfold potOf term owed
  simp [h₁, h₂]

section Bounds

variable {β : Type w}

/-- Rewards bounded over any run of a supply and borrow reward index market: the rewards credited
to all accounts (accrued plus paid) after any sequence of operations are at most those at the
start `C`, plus what was owed at the start `R` (at the index scale `one`, rounded down once), plus
the emission not yet indexed `U₁ + U₂`, plus the rewards emitted over the run. `hact` is the case
analysis of the step (`Act`); `hs` is usually `pot_le_of`. -/
theorem rewards_bounded {step : σ → β → σ} {next : Nat × Nat → β → Nat × Nat}
    {f : Nat × Nat → β → Nat}
    (run : σ → List β → σ) (total : Nat × Nat → List β → Nat)
    (ghost : Nat × Nat → List β → Nat × Nat) {g₁ g₂ : Nat}
    (hact : ∀ sp s a, M.Inv g₁ g₂ sp s → M.Act sp s (next sp a) (f sp a) (step s a))
    (hone : 0 < M.one) {sp : Nat × Nat} {s : σ} (h0 : M.Inv g₁ g₂ sp s) {C R U₁ U₂ : Nat}
    (hs : M.pot g₁ g₂ s ≤ C * M.one + R + M.one * (U₁ + U₂)) (as : List β)
    (hr0 : ∀ s, run s [] = s := by intros; rfl)
    (hr1 : ∀ s a as, run s (a :: as) = run (step s a) as := by intros; rfl)
    (ht0 : ∀ g, total g [] = 0 := by intros; rfl)
    (ht1 : ∀ g a as, total g (a :: as) = f g a + total (next g a) as := by intros; rfl)
    (hg0 : ∀ g, ghost g [] = g := by intros; rfl)
    (hg1 : ∀ g a as, ghost g (a :: as) = ghost (next g a) as := by intros; rfl) :
    M.creditSum (run s as) ≤ C + (R / M.one + U₁ + U₂) + total sp as := by
  have := amount_le_of_scaled hone (M.creditSum_mul_le_pot g₁ g₂ _)
    (M.run_bound run total ghost hact h0 as hr0 hr1 ht0 ht1 hg0 hg1).2.1 hs
  omega

/-- Rewards of one account bounded over any run: the rewards credited to account `w` after any
sequence of operations are at most its amount `C` at the start, plus what it was owed `R` (at
scale `one`, rounded down once), plus the unindexed emission `U₁ + U₂` counted for it (on the
sides where it holds units), plus the rewards emitted over the run. `hs` is usually
`potOf_le_of`. -/
theorem account_rewards_bounded {step : σ → β → σ} {next : Nat × Nat → β → Nat × Nat}
    {f : Nat × Nat → β → Nat}
    (run : σ → List β → σ) (total : Nat × Nat → List β → Nat)
    (ghost : Nat × Nat → List β → Nat × Nat) {g₁ g₂ : Nat}
    (hact : ∀ sp s a, M.Inv g₁ g₂ sp s → M.Act sp s (next sp a) (f sp a) (step s a))
    (hone : 0 < M.one) {sp : Nat × Nat} {s : σ} (h0 : M.Inv g₁ g₂ sp s) (w : Nat)
    {C R U₁ U₂ : Nat} (hs : M.potOf g₁ g₂ w s ≤ C * M.one + R + M.one * (U₁ + U₂))
    (as : List β)
    (hr0 : ∀ s, run s [] = s := by intros; rfl)
    (hr1 : ∀ s a as, run s (a :: as) = run (step s a) as := by intros; rfl)
    (ht0 : ∀ g, total g [] = 0 := by intros; rfl)
    (ht1 : ∀ g a as, total g (a :: as) = f g a + total (next g a) as := by intros; rfl)
    (hg0 : ∀ g, ghost g [] = g := by intros; rfl)
    (hg1 : ∀ g a as, ghost g (a :: as) = ghost (next g a) as := by intros; rfl) :
    M.credited (M.acct (run s as) w) ≤ C + (R / M.one + U₁ + U₂) + total sp as := by
  have := amount_le_of_scaled hone (M.credited_mul_le_potOf g₁ g₂ w _)
    ((M.run_bound run total ghost hact h0 as hr0 hr1 ht0 ht1 hg0 hg1).2.2 w) hs
  omega

/-- No rewards backdated to before a position: an account that holds no units (no supply, no
borrow) after any history is credited at most the rewards emitted from then on, at the rates the
history left; it is never credited for time before it held a position. -/
theorem rewards_after_no_position_bounded {step : σ → β → σ} {next : Nat × Nat → β → Nat × Nat}
    {f : Nat × Nat → β → Nat}
    (run : σ → List β → σ) (total : Nat × Nat → List β → Nat)
    (ghost : Nat × Nat → List β → Nat × Nat) {g₁ g₂ : Nat}
    (hact : ∀ sp s a, M.Inv g₁ g₂ sp s → M.Act sp s (next sp a) (f sp a) (step s a))
    (hone : 0 < M.one) {sp : Nat × Nat} {s : σ} (h0 : M.Inv g₁ g₂ sp s) (history as : List β)
    (w : Nat) (h₁ : M.units₁ (M.acct (run s history) w) = 0)
    (h₂ : M.units₂ (M.acct (run s history) w) = 0)
    (hr0 : ∀ s, run s [] = s := by intros; rfl)
    (hr1 : ∀ s a as, run s (a :: as) = run (step s a) as := by intros; rfl)
    (ht0 : ∀ g, total g [] = 0 := by intros; rfl)
    (ht1 : ∀ g a as, total g (a :: as) = f g a + total (next g a) as := by intros; rfl)
    (hg0 : ∀ g, ghost g [] = g := by intros; rfl)
    (hg1 : ∀ g a as, ghost g (a :: as) = ghost (next g a) as := by intros; rfl) :
    M.credited (M.acct (run (run s history) as) w) ≤
      M.credited (M.acct (run s history) w) + total (ghost sp history) as := by
  have hI := (M.run_bound run total ghost hact h0 history hr0 hr1 ht0 ht1 hg0 hg1).1
  exact amount_le_of_scaled_exact hone (M.credited_mul_le_potOf g₁ g₂ w _)
    ((M.run_bound run total ghost hact hI as hr0 hr1 ht0 ht1 hg0 hg1).2.2 w)
    (Nat.le_of_eq (M.potOf_of_no_units h₁ h₂))

end Bounds

/-! ## Chains for common actions -/

section Chains

variable {M}

/-- An account settled on side 1 and then given new units there (with its credited amount not
raised and its other fields kept) is a chain of two steps. -/
theorem Settle₁.then_adjust {w : Nat} {s s' t : σ} {g : α → α} (h : M.Settle₁ w s s')
    (ha : M.accts t = (M.accts s').modify w g) (hc : M.clock t = M.clock s')
    (hg : M.AdjustsAt g) (hu : ∀ a, M.units₂ (g a) = M.units₂ a) : M.Reach s t :=
  (Reach.single (.settle₁ h)).tail (.adjust ⟨hc, g, ha, hg, .inr h.settled, .inl hu⟩)

/-- An account settled on side 2 and then given new units there is a chain of two steps. -/
theorem Settle₂.then_adjust {w : Nat} {s s' t : σ} {g : α → α} (h : M.Settle₂ w s s')
    (ha : M.accts t = (M.accts s').modify w g) (hc : M.clock t = M.clock s')
    (hg : M.AdjustsAt g) (hu : ∀ a, M.units₁ (g a) = M.units₁ a) : M.Reach s t :=
  (Reach.single (.settle₂ h)).tail (.adjust ⟨hc, g, ha, hg, .inl hu, .inr h.settled⟩)

/-- Two accounts settled on side 1, then both given new units there (a transfer between them),
is a chain of four steps. -/
theorem Settle₁.transfer {v w : Nat} {s s₁ s₂ t : σ} {g₁ g₂ : α → α} (h₁ : M.Settle₁ v s s₁)
    (h₂ : M.Settle₁ w s₁ s₂) (ha : M.accts t = ((M.accts s₂).modify v g₁).modify w g₂)
    (hc : M.clock t = M.clock s₂) (hg₁ : M.AdjustsAt g₁)
    (hg₂ : M.AdjustsAt g₂) (hu₁ : ∀ a, M.units₂ (g₁ a) = M.units₂ a)
    (hu₂ : ∀ a, M.units₂ (g₂ a) = M.units₂ a) : M.Reach s t := by
  have a₃ : M.vm.Adjust v (M.view s₂) (M.clock s₂, (M.accts s₂).modify v g₁) :=
    ⟨rfl, g₁, rfl, hg₁, .inr (h₁.settled.settle₁ h₂), .inl hu₁⟩
  have hs : M.vm.Settled₁ (M.view s₂) w := h₂.settled
  have a₄ : M.vm.Adjust w (M.clock s₂, (M.accts s₂).modify v g₁) (M.view t) :=
    ⟨hc, g₂, ha, hg₂, .inr (hs.adjust a₃), .inl hu₂⟩
  have r : M.Reach s s₂ := (Reach.single (.settle₁ h₁)).tail (.settle₁ h₂)
  exact Moves.tail (Moves.tail r (.adjust a₃)) (.adjust a₄)

/-- Two accounts settled on side 2, then both given new units there, is a chain of four steps. -/
theorem Settle₂.transfer {v w : Nat} {s s₁ s₂ t : σ} {g₁ g₂ : α → α} (h₁ : M.Settle₂ v s s₁)
    (h₂ : M.Settle₂ w s₁ s₂) (ha : M.accts t = ((M.accts s₂).modify v g₁).modify w g₂)
    (hc : M.clock t = M.clock s₂) (hg₁ : M.AdjustsAt g₁)
    (hg₂ : M.AdjustsAt g₂) (hu₁ : ∀ a, M.units₁ (g₁ a) = M.units₁ a)
    (hu₂ : ∀ a, M.units₁ (g₂ a) = M.units₁ a) : M.Reach s t := by
  have a₃ : M.vm.Adjust v (M.view s₂) (M.clock s₂, (M.accts s₂).modify v g₁) :=
    ⟨rfl, g₁, rfl, hg₁, .inl hu₁, .inr (h₁.settled.settle₂ h₂)⟩
  have hs : M.vm.Settled₂ (M.view s₂) w := h₂.settled
  have a₄ : M.vm.Adjust w (M.clock s₂, (M.accts s₂).modify v g₁) (M.view t) :=
    ⟨hc, g₂, ha, hg₂, .inl hu₂, .inr (hs.adjust a₃)⟩
  have r : M.Reach s s₂ := (Reach.single (.settle₂ h₁)).tail (.settle₂ h₂)
  exact Moves.tail (Moves.tail r (.adjust a₃)) (.adjust a₄)

end Chains

/-! ## An index still at 0 set to its start value -/

/-- Setting an index that is still 0 to `init`, and its start with it, keeps the start at 0 or
`init` and at or below the index. -/
theorem start_reinit {init g i : Nat} (hg : g = 0 ∨ g = init) (hgi : g ≤ i) :
    ((if i = 0 then init else g) = 0 ∨ (if i = 0 then init else g) = init) ∧
      (if i = 0 then init else g) ≤ (if i = 0 then init else i) := by
  by_cases h : i = 0 <;> simp [h, hg, hgi]

/-- Setting an index that is still 0 to `init`, and its start with it, raises no account's owed
amount: an account whose checkpoint is at or below the index was owed nothing, and still is. -/
theorem owed_reinit_le {init g i r : Nat} (u : Nat) (hr : r ≤ i) :
    u * ((if i = 0 then init else i) - effStart (if i = 0 then init else g) r) ≤
      u * (i - effStart g r) := by
  by_cases h : i = 0
  · have : r = 0 := by omega
    subst this; simp [h]
  · simp [h]

/-- Bringing the last update to now when an index is set drops its unindexed emission. -/
theorem unindexed_reinit_le (c : Prop) [Decidable c] (l r now : Nat) :
    unindexed (if c then now else l) r now ≤ unindexed l r now := by
  split
  · simp
  · exact Nat.le_refl _

end Market

end ProofForgeFin.Accumulator
