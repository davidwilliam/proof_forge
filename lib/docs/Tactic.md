# Proof automation: `ProofForgeFin.Tactic`

Models working through ProofForge write proofs as tactic scripts and read Lean's error
messages. The recorded attempts on `rc-knight-router` and `rw-compound-comp`
(`results/knight-1/*/events.jsonl`, `results/compound-1/*/events.jsonl`) fail again and again
on the same kinds of goals: projections of structure instances that nobody reduced
(`{ st := st, tr := tr }.st`, `(x.st, []).fst`), updates read at a position (`upd f k v j`),
conditions left as `if True ∧ True then ...`, matches on the result of a call, inductions over
event lists written by hand, and rounding bounds such as `K / t * s ≤ K * s / t` that `omega`
rejects as nonlinear. The accepted repair of `rc-knight-router` (`results/knight-1/A2-2`)
spends 84 theorems and 753 lines of proof on two invariants, most of them lemmas that unfold one
projection or one update.

`ProofForgeFin.Tactic` (imported by `ProofForgeFin`) adds two simp sets and seven tactics for
these goals. They are metaprograms: they add no axiom and every proof they build is checked by
the kernel. `lib/Audit.lean` reports 0 violations with them, and the source scan of
`tests/test_fin_lib.py` passes unchanged (the tactic sources use no `sorry`, `native_decide`,
`unsafe` or `implemented_by`, and no `partial` definition). Each tactic either makes progress or
fails with a message that names it; none loops (every loop has a fuel bound, the simp sets have
no commutativity or associativity lemma, and the one use of `Nat.mul_comm` is the ordered
rewriting of `round_bound`, which terminates).

Modules:

* `ProofForgeFin/Tactic/Attr.lean`: the simp sets `fin_simp` and `struct_simp`.
* `ProofForgeFin/Tactic/SimpSets.lean`: their lemmas, the simplification procedures `ctorEq`
  and `iteEqSubst`, and the lemmas they need (`ceilDiv_zero_right`, `ceilDiv_one_right`,
  `ceilDiv_mul_cancel_left`, `foldl_eq_run`, `Ledger.upd_apply`, `Ledger.adjust_apply`,
  `Ledger.transfer_apply`, `ite_apply_fun`, `ite_eq_subst_left`, `ite_eq_subst_right`,
  `Seq.runAll_cons`, `Seq.skip_apply`).
* `ProofForgeFin/Tactic/Struct.lean`: `struct_simp`, `step_cases`, `generalize_divs`.
* `ProofForgeFin/Tactic/Induction.lean`: `run_induction`.
* `ProofForgeFin/Tactic/Round.lean`: `fin_simp`, `div_norm`, `round_bound`, and the lemma
  `div_mul_le_mul_div`.
* Tests: `ProofForgeFinDemo/Tactic/` (root `ProofForgeFinDemo/Tactic.lean`).

No existing module was edited. The simp attributes on lemmas of `Rounding`, `FixedPoint`,
`Shares`, `Seq` and `Ledger` are added from `SimpSets.lean` with `attribute [...]`, which
applies wherever `ProofForgeFin` is imported.

## The usual shape of a proof

An invariant over every sequence of events of a router (the accepted repair of
`rc-knight-router`, `ProofForgeFinDemo/Tactic/Router.lean`):

```lean
theorem invWeak2_run (b : Build) (evs : List Event) : InvWeak2 (run step b evs) := by
  run_induction [run] with [advance, step, routeBySent, Truth.observe, Truth.record, upd, InvWeak2,
    Truth.sent, start, init, Truth.empty, sentFor]
  all_goals try step_cases
  case parent =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have h6 := fun id => my_sentFor_ge x.tr.kids x.tr.nOrders id h4
    grind
  case pos =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    simp only [sentFor_append, sentFor]
    grind
  case fill.some =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have hs := sentFor_set_done x.tr.kids child val (val.done + min q (val.qty - val.done)) hc
    have hm := List.mem_of_getElem? hc
    grind [List.mem_or_eq_of_mem_set]
```

`run_induction` turns the task's `run` (a left fold) into `Seq.run`, applies
`Seq.run_invariant` with the invariant read off the goal and leaves one goal per event
constructor, with the step function, the observation and the record unfolded and every
projection reduced; the initial state and the acknowledgement are closed on the way.
`step_cases` splits what remains on the router's condition and on the venue's lookup of the
child order, and closes the refused branches. What is left is the arithmetic of each event,
stated over the fields of the state before, which `grind` closes from the invariant. The same
proof without the automation fails at the first step: `simp` with the same definitions leaves
projections of conditions it cannot push through (`(if c then (s, l) else (s', l')).1.nParents`),
and `grind` gives up on all four events.

## `struct_simp`

```
struct_simp
struct_simp [h₁, f, ← e, *]
struct_simp [..] at h ⊢
```

`simp only` with the `struct_simp` set, `reduceCtorEq` and the given arguments (lemmas,
definitions to unfold, hypotheses, `*`). Two additions to plain `simp only`:

* for every hypothesis `h : ¬a = b` among the arguments (or in the context, with `*`) it also
  uses `Ne.symm h`, so `upd f k v j` is decided whether the hypothesis reads `j ≠ k` or `k ≠ j`
  (the knight run failed on exactly this with `simp [upd_neq _ _ _ _ hj]`);
* after each round it looks for structure projections applied to a condition,
  `(if c then a else b).f`, and runs again with `apply_ite f` and `apply_dite f`, for at most
  four rounds, so projections reach the structure instances in both branches.

The set: `Option.getD`, `map`, `isSome` of constructors, `Option.some.injEq`, `Prod.mk.injEq`;
`and_true`, `true_and`, `ite_true`, `ite_false`, `dite_true`, `dite_false`, `ite_self`,
`not_true_eq_false`, `eq_self_iff_true`, `ne_eq`, `false_implies`, `implies_true`,
`forall_eq`; `Nat.lt_irrefl`, `Nat.le_refl`, `Nat.zero_le`, `Nat.not_lt_zero`, units and zeros
of `+` and `-` on `Nat` and `Int`; `List.map`, `++` and `length` of constructors,
`List.getElem?` and `getElem` of `set` and `modify`, `Ledger.getD_modify`; the Ledger updates
applied to an argument (`upd_apply`, `adjust_apply`, `transfer_apply`, `upd_self`);
`Shares.Pool.add`, `Shares.Pool.sub`; `Seq.run_nil`, `run_cons`, `trace_nil`, `trace_cons`,
`accum_nil`, `accum_cons`, `runAll_nil`, `runAll_cons`, `skip_apply`; `ite_apply_fun`
(`(if c then f else g) a`). Simplification procedures: `ctorEq` (an equation between two
applications of one constructor of any inductive type is the conjunction of the equations of
the fields, the constructor's `injEq` theorem, which `simp only` does not use unless named) and
`iteEqSubst` (`if a = b then t else e` is `e` when `t` with `a` in place of `b` is `e`: an update
read back where the new value is the old one). Projections of structure instances, matches on
constructors and `have`/`let` are reduced by `simp` itself.

Example (`results/knight-1/A2-2/events.jsonl`, line 486):

```lean
example (x : Sys) (k q id : Nat) (_h : k < x.st.nChildren) (hj : ¬(x.st.children k).parent = id) :
    (upd x.st.parents (x.st.children k).parent { ... cum := ... + min q (...) } id).sent =
      (x.st.parents id).sent := by
  struct_simp [upd, hj]
```

Fails with `struct_simp: nothing to reduce: ...` when nothing changes. Limits: projections are
moved through `if` and dependent `if`, not through `match` (`step_cases` splits those); an update
function of a task (its own `upd`, there is no `Function.update` in core Lean) is reduced only
when its definition is passed; the `Ne.symm` addition covers hypotheses named in the arguments
or `*`, not hypotheses found by the discharger.

## `step_cases`

```
step_cases
step_cases op
step_cases op [step, f, h]
```

`cases op` when the variable `op` is given (the constructor fields keep their names), then in
every case `struct_simp` with the arguments, then repeated case splits on the first

* condition `c` of an `if` or dependent `if` (`by_cases hc : c`), or
* discriminant `d` of a `match`, or option consumed by `Option.getD`, `map`, `bind`, `isSome`,
  `isNone` (`cases hc : d`, or `cases d` for a variable), such as `impl s c` in
  `(impl s c).getD s`, or, when there is neither, `split`,

that mentions no bound variable. Conditions are found anywhere in the goal, under binders too:
`∀ id, (if child < n then ... else ...) = ...` is split on `child < n` although `split` refuses
it. The new hypotheses are named `hc`, `hc_1`, ...; a conjunction is split into its parts; each
branch is simplified with `struct_simp`, the arguments and the new hypotheses; goals closed by
`rfl`, an assumption, a contradiction, `omega` or `omega` after `generalize_divs` are dropped. At
most 64 splits are made, at most 12 nested, and a condition already split on the way is not
split again.

Example (`results/compound-1/implement-1/events.jsonl`, line 653, the lemma `ab_accrue_ge3`):

```lean
example (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  step_cases [accrueSide]
```

Example (every operation of the Comptroller model keeps the reserve when no call of the
implementation changes it; `ProofForgeFinDemo/Tactic/StructSimp.lean`):

```lean
example (impl : Impl) (s : St) (op : Op)
    (hhook : ∀ t c t', impl t c = some t' → t'.reserve = t.reserve) :
    (exec impl s op).reserve = s.reserve ∨ ∃ x, op = .drip x := by
  step_cases op [exec, St.withAcct]
  all_goals grind
```

Fails with `step_cases: nothing to split: ...` when it neither splits, unfolds nor closes
anything; under `all_goals`, write `all_goals try step_cases`. Limits: a condition that
mentions a bound variable (`if id = k` under `∀ id`) is not split (introduce the variable
first); contradictory branches that need a lemma (for example `l[k]? = some v` with
`¬k < l.length`) are left open; the budget can leave goals unsplit in a step function with more
than 64 branches.

## `run_induction`

```
run_induction                                   -- invariant read off the goal
run_induction using J                           -- a stronger invariant
run_induction total Inv                         -- a ghost total (Seq.accum)
run_induction [run_eq] with [step, f, -g]       -- rewrite first; simp the step goals
```

The goal must mention `Seq.run step s ops` or `List.foldl step s ops`; `run_induction [l₁, ...]`
rewrites the goal with the given lemmas or definitions first (the task's `run`, or a bridging
lemma such as `run_eq : run impl s ops = Seq.run (exec impl) s ops`).

| Goal | Principle | Goals left |
|---|---|---|
| `G (Seq.run step s ops)` | `Seq.run_invariant`, `I := fun x => G x` | `init : G s`; per constructor `c`, `G (step x (c ..))` with `ih : G x` |
| same, `using J` | `Seq.run_invariant_of_imp` | `imp : J x → G x`, `init : J s`, per constructor with `ih : J x` |
| `P (Seq.run step s ops) ≤ P s + (ops.map f).sum` | `Seq.run_le_add_sum` | per constructor `P (step x (c ..)) ≤ P x + f (c ..)` |
| same, `using J` | `Seq.run_le_add_sum_of_inv` | `init : J s`, `inv_c` goals for `J`, per constructor bound with `ih : J x` |
| mentions `Seq.accum next f g ops`, `total Inv` | `Seq.run_total_invariant`, total 0 at the start | main goal with `hrun : Inv (Seq.run next g ops) (Seq.accum next f g ops) (Seq.run step s ops)`, `init : Inv g 0 s`, per constructor `Inv (next g c) (e + f g c) (step x c)` with `ih : Inv g e x` |

In every per-constructor goal and its `ih`, and in `init`, the head constant of the step
function (and of `next` and `f`) is unfolded and `struct_simp` runs with the `with` arguments.
`with [-c]` keeps the head constant `c` folded, so that per-operation lemmas stated about
`c` apply unchanged. When the operation type is not inductive one step goal remains. Goals closed
by `rfl`, an assumption, a contradiction or `omega` are dropped; the tags are the constructor
names (`case parent => ...`).

Example (an escrow never releases more than was deposited, through the stronger invariant
that held and released funds add up to the deposits; `ProofForgeFinDemo/Tactic/RunInduction.lean`):

```lean
theorem released_le_deposited (e : Escrow) (h0 : e.released + e.held = e.deposited)
    (ops : List EOp) :
    (Seq.run estep e ops).released ≤ (Seq.run estep e ops).deposited := by
  run_induction using fun x => x.released + x.held = x.deposited
  step_cases
```

Example (the ghost-total form, `run_pot` of `rw-compound-comp` with the per-operation lemmas
as hypotheses):

```lean
  run_induction total (fun g e t => Inv g t ∧ P t ≤ P s + doubleScale * e)
    with [-exec, -nextSpeeds, -emittedBy]
  · exact hrun.2
  · exact ⟨h0, by omega⟩
  all_goals
    refine ⟨exec_inv _ _ _ ih.1, Nat.le_trans (exec_pot _ _ _ ih.1) ?_⟩
    rw [Nat.mul_add]
    omega
```

Fails with `run_induction: no Seq.run step s ops ...` when the goal has no run. Limits: the
invariant is the goal with every occurrence of the run abstracted syntactically (`kabstract`), so
a goal that states the run in two different forms needs `[lemmas]` to unify them first; a task's
own recursive `run` needs a bridging lemma (one line by induction, see `run_eq` in
`ProofForgeFinDemo/ShareVault.lean`); relations along a run (`Seq.run_rel`,
`Seq.run_rel_of_trace`), atomic runs (`Seq.runAll`) and `Seq.Reachable` are not handled (apply
the library lemma); the total form starts the total at 0.

## `fin_simp` and `div_norm`

```
fin_simp [h₁, ...] (at loc)?
div_norm [WAD, ...] (at loc)?
```

`fin_simp` is `simp only` with the `fin_simp` set: `mulDiv`, `mulDivUp`, `mulDown`, `mulUp`,
`divDown`, `divUp`, `scaleDown`, `scaleUp`, `unscaleDown`, `unscaleUp`, `convertDecimalsDown`,
`convertDecimalsUp` and the four `Shares.preview*` conversions as `a / b` and `ceilDiv a b`;
`ceilDiv` of zero, by zero, by one and of an exact multiple; `Nat.div_one`, `div_zero`,
`zero_div`, units and zeros of `*` and `+`, `Nat.mul_div_cancel`, `mul_div_cancel_left` (their
`0 < b` side conditions discharged by simp, for literals or from the given hypotheses),
`Nat.div_div_eq_div_mul`, `pow_zero`, `pow_one`; literal arithmetic is evaluated by the default
simprocs. `div_norm` adds `ceilDiv a b = (a + b - 1) / b`, `ge_iff_le`, `gt_iff_lt` and the given
definitions: `omega` handles division and remainder by literals, so after `div_norm` a goal whose
divisors are literals or named literal scales is linear.

```lean
example (a b : Nat) (h : 0 < b) : mulDiv (a * b) 1 b = a := by fin_simp [h]
example (a : Nat) : mulDown (10 ^ 18) a 1 * 10 ^ 18 ≤ a := by div_norm; omega
```

Both fail with a message when nothing changes.

## `round_bound`

```
round_bound
round_bound [h₁, hpos]          -- extra facts
round_bound with [WAD, creditFor]   -- definitions to unfold
```

Closes a bound or equation on `Nat` with rounding, in three stages, and restores the goal
when all three fail:

1. one library lemma by `apply`, with side goals closed by an assumption or `omega`: the floor
   and ceiling bounds, `mulDown ≤ mulUp ≤ mulDown + 1` and the same for `divDown`, `divUp`,
   `mulDiv`, `mulDivUp`, sums of rounded parts, `a / c * b ≤ a * b / c`, `t * a / s ≤ a`, the
   round trips, two products, the share conversions and monotonicity in each argument (53
   lemmas);
2. `div_norm` with the `with` definitions at the goal and the hypotheses, then `omega`;
3. cross-multiplication: a top-level quotient `a / b` on either side of `≤` or `<` (an equation
   is split into two inequalities) is replaced by the equivalent product comparison
   (`Nat.le_div_iff_mul_le` and its three companions), with `0 < b` proved by `omega` or, when
   that fails, a split on `b = 0` (the quotients are then 0); products are distributed over
   sums and differences and put in one canonical order; for every quotient `a / b` with a
   variable divisor in the goal or a hypothesis the facts `a / b * b ≤ a` and (for `0 < b`)
   `a < a / b * b + b`, their multiples by the other factors of each product of the goal that
   contains `a / b * b`, and for remainders `b * (a / b) + a % b = a` and `a % b < b` are added;
   then `omega`, and `omega` after `generalize_divs`.

The `[...]` facts are added as hypotheses first. Conjunctions are split and each part proved.

```lean
example (K t s : Nat) : K / t * s ≤ K * s / t := by round_bound
example (A S x : Nat) (hA : 0 < A) : A * (S - (x * S + A - 1) / A) ≤ (A - x) * S := by
  round_bound
example (u s i : Nat) : creditFor u s i * doubleScale ≤ u * (i - s) := by
  round_bound with [creditFor, doubleScale]
```

The second is the share value of a withdrawal rounded up in `rw-hundred-vault`
(`(assets - x) / (supply - sharesUp x)` does not fall, cross-multiplied); with `step_cases` it
proves the whole case analysis `exec_value` of that task in two lines
(`ProofForgeFinDemo/Tactic/RunInduction.lean`).

On failure: `round_bound: could not prove <goal> ... Give the missing facts as
round_bound [h₁, h₂] ...`; the goal is unchanged. Limits: hypotheses are not multiplied by
variables (from `h : q ≤ c` it does not derive `q * d ≤ c * d`), so a bound that needs the
monotonicity of a product in a hypothesis needs that product as a fact; products of two
quotients, quotients inside quotients and divisors that are themselves quotients get only the
plain floor facts; only `Nat` (signed rounding is not covered, as in the library); stage 1
unifies up to default transparency, so it sees through `mulDown` but not through a hypothesis.

## `generalize_divs`

`generalize_divs` replaces every `a / b` and `a % b` on `Nat` whose divisor mentions a local
variable, in the goal and the hypotheses, by a fresh variable. `omega` reads `a / b` as an
integer quotient of casts about which it knows nothing, not even that it is nonnegative, and so
fails on `sd.index ≤ sd.index + X / total`; after `generalize_divs` it succeeds. `step_cases`,
`run_induction` and `round_bound` use it after a failed `omega`.

## `lib_defs`

Specifications restate definitions the library has: a `sumOver` by `List.foldr`, an update
`upd f k v`, a ceiling division `(a + b - 1) / b`, a fixed-point product `a * b / ONE`. The
library's lemmas are stated over its own definitions, so `exact?` and `simp` do not find them for
the restated ones, although the two are definitionally equal. In the open goals of the runs that
were not accepted (`results/feedback-library-1/clusters.json`) this is the most frequent reason a
library fact was not used.

`lib_defs` looks at every constant of the goal and the hypotheses that is defined outside the
library and the Lean distribution, and finds a ProofForgeFin definition it is definitionally
equal to: the candidates are the library definitions with the same head constant in their value
(looking through library definitions written with other library definitions, up to three levels),
the ones that more library theorems mention first; the leading implicit and instance arguments of
both are instantiated (instances by synthesis), up to three leading explicit arguments of the
library's are left to unification (a scale constant), and the two must be definitionally equal as
functions at default transparency. Every application of the restated definition is then replaced
by the library's, in the goal and in every hypothesis, as a change up to definitional equality
(like `change`): no hypothesis, no axiom, checked by the kernel. `lib_defs?` also reports the
replacements. It fails, leaving the goal unchanged, when no definition matches.

```
def total {α : Type} (l : List α) (f : α → Int) : Int := l.foldr (fun a acc => f a + acc) 0
def setAt {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α := fun j => if j = k then v else f j

example (hl : l.Nodup) (hk : k ∈ l) : total l (setAt f k v) = total l f - f k + v := by
  lib_defs      -- total ↦ Ledger.sumOver, setAt ↦ Ledger.upd
  exact?        -- Machine.sumOver_upd hl f hk v
```

A sum restated by structural recursion on a list or a natural number (`S [] = 0`,
`S (x :: xs) = f x + S xs`, or `S 0 = 0`, `S (n + 1) = S n + f n`) is not definitionally equal to
a fold. For those, `lib_defs` then proves the equation `∀ x, S x = (x.map f).sum` (or the sum over
`List.range n`) with the lemmas of `ProofForgeFin.Sums.Eqns`, checking the defining equations by
`rfl`, and rewrites with it (`simp only ... at *`). Other definitions are not tried, so the tactic
does not unfold a large step function looking for a sum.

## Tests

`ProofForgeFinDemo/Tactic/` holds 103 examples and theorems; 74 use the automation and must be
closed for the build to succeed, the rest are the proofs without the automation kept for the
comparison below and lemmas copied from the tasks. Four check that a tactic fails cleanly
(`fail_if_success`) and that the goal is intact afterwards.

* `RoundBound.lean`: 39 goals: rounding facts, fixed-point and share conversions, named scales,
  the share-value arithmetic of `rw-hundred-vault`, 7 goals copied from failed attempts on
  `rw-compound-comp`, two failure tests.
* `StructSimp.lean`: 19 goals: records, options, updates, `List.modify`, constructor equations,
  7 goals copied from failed attempts on `rw-compound-comp` (`accrueSide`, `upgrade`,
  `accrualStart`, a rebuilt `Side`, decided conditions, a modified list), calls of the
  Comptroller model split on the implementation's result, a failure test.
* `RunInduction.lean`: `exec_value'` (the case analysis of `rw-hundred-vault`), an accumulated
  bound over the vault, an invariant through a stronger one, the ghost-total `run_pot'` of
  `rw-compound-comp`, a failure test.
* `LibDefs.lean`: `lib_defs` on a restated sum, update, ceiling division and fixed-point product
  (in the goal and in a hypothesis), the sum lemmas it opens, and a clean failure.
* `Router.lean`: 8 goals copied from failed attempts on `rc-knight-router` (the projections,
  updates and conditions above and the last goal of REQ-FILL-ACCOUNTING in the run that ran out
  of budget on it), the invariants `InvWeak2` and `InvFillAcc` of the accepted repair over every
  sequence of events, and REQ-NEVER-OVERROUTE and REQ-FILL-ACCOUNTING for the repair.

Definitions are copied without change from the task files named in each header (the unused
build argument of the repair's `step` is written `_`, since the build rejects warnings); no task
file is imported or modified. The four test modules elaborate in about 3 s together in the
pinned image, above the cost of their imports.

## Measurements

Tactic steps are tactic invocations (`t₁ <;> t₂` counts two, each `calc` step one, `case`
selectors none). "Without" is the shortest proof found with core tactics and the library, kept
in the test files next to the automated one; where a model attempt is cited, it failed.

| Goal (source) | With | Without |
|---|---|---|
| `K / t * s ≤ K * s / t` (compound implement-1, line 267) | 1 | 6 |
| `x / K + y / K ≤ (x + y) / K` (compound repair-A2-1, line 233) | 1 | 6 |
| `(S - b) / K + b / K ≤ S / K` (same line) | 1 | 2 |
| `tot * (em * K / tot) ≤ em * K` (same line) | 1 | 1 (`Nat.mul_div_le`; the model's attempt had a type mismatch) |
| `K / t * t * s ≤ K * s`, `K / t * s * t = K / t * t * s` (line 267) | 1 each | 1 each |
| `hd * c + tl.sum * c = (hd + tl.sum) * c` (compound implement-1, line 204) | 1 | 1 |
| share value of a deposit, a redemption, a withdrawal (rw-hundred-vault reference) | 1 each | 4, 5, 4 |
| `sd.index ≤ (accrueSide sd now total).index` (compound implement-1, line 653) | 1 | 4 |
| `{ index := sup.index, block := b, speed := sup.speed } = sup` (repair-A2-1, line 61) | 1 | 2 |
| `(if 0 = 0 then if compInitialIndex ≤ index then ..) ≤ index` (implement-2, line 40) | 1 | 4 |
| `(upgrade L).supplyState.index = ..` (implement-1, line 490) | 1 | 3 |
| `(xs.modify i f)[j] = xs[j]` (repair-A2-1, line 289) | 1 | 2 |
| `accrualStart idx idx = idx` (implement-1, `nb_as_selfX`) | 1 | 5 |
| knight A2-2 line 475, case `h_3` (projection of a pair) | 1 | 1 (`rfl`) |
| same line, case `h_4` (projection through the fill handler) | 1 | 2 |
| same line, case `h_2` (`routeBySent ...).fst.nParents`) | 1 | 4 (`split` alone fails on the `have` binders) |
| knight A2-2 line 486 (update, inequation the other way round) | 1 | 2 |
| knight A2-2 line 636 (implication from a refuted equation) | 1 | 2 |
| knight A2-2 line 689 (refuted conjunct, then the invariant) | 1 | 3 |
| knight A2-2 line 645, A2-1 line 1421 | 1 each | 1 each |
| `exec_value` of rw-hundred-vault | 2 | 41 (reference: 26 in the theorem, 15 in its three shape lemmas) |
| vault assets bounded by what was paid in | 2 | 26 (with `Seq.run_le_add_sum`) |
| escrow invariant through a stronger one | 2 | 10 (with `Seq.run_invariant_of_imp`, explicit `I`, `J` and `step`) |

The invariants of the accepted repair of `rc-knight-router`, counted over the declarations each
depends on in the file that proves it (`ProofForgeFinDemo/Tactic/Router.lean` and
`results/knight-1/A2-2/final.lean`; definitions and the task's own lemmas excluded):

| Statement | With: theorems, proof lines | Accepted repair: theorems, proof lines |
|---|---|---|
| `InvWeak2` after every sequence of events | 2, 25 | 49, 346 |
| `InvFillAcc` after every sequence of events | 2, 36 | 58, 465 |
| both | 4, 61 | 84, 753 |

The two invariants give REQ-NEVER-OVERROUTE (10 tactic steps) and REQ-FILL-ACCOUNTING (one term),
the latter the requirement the run `results/knight-1/A2-1` ran out of budget on. Without the
automation, the same plan (an induction over the fold, `simp` with the same definitions, then
`grind` with the same lemmas) fails on all four events of `InvWeak2`.

## Limits

* `grind` (core Lean 4.35) closes most of the per-operation goals the tactics leave, given the
  invariant at the state before and the task's lemmas; the tactics do not call it themselves,
  since its cost on large goals is not bounded.
* The tactics do not prove the per-operation lemmas of a task that are not arithmetic on the
  fields (for example `sentFor` of a modified list); they leave them stated over the fields of
  the state before, which is where a model can supply them.
* Importing `ProofForgeFin` now imports `Lean` (for the metaprograms). A task that uses the
  library therefore loads the Lean environment; no axiom and no new trust is involved.
