import ProofForgeFin.Seq
import ProofForgeFin.Ledger
/-!
# Parent and child orders

An order router receives parent orders and sends child orders to venues as liquidity appears.
Two families of requirements recur: bounds on what was sent and executed per parent (never send
more than the parent quantity, never execute more, stop when filled), and the accounting
relation between the router's own counters and what the venues actually executed. The model of
`realworld/tasks/rc-knight-router` keeps these quantities apart: the facts of a run are a list
of child orders with their executed shares, computed from the events and never from the
router's state. This module states that model once.

* `sumFor key f l id`: the sum of `f` over the records of `l` whose `key` is `id` (shares sent
  per parent, shares executed per parent, fills per order). The lemmas cover appending,
  updating one record in place with `List.set`, and pointwise bounds, for any record type, so a
  specification with its own child-order structure uses them after a one-line identification.
* `table f n`: the first `n` entries of a function table `Nat → β` as a list. A router that
  keeps child records in a function with a counter has the list of facts as a table:
  appending a new record is `Ledger.upd` at index `n`, updating one is `Ledger.upd` below `n`.
* `Child`, `sent`, `executed`, `execute`, `send`: the venue model. An execution report for
  child order `k` executes at most its unexecuted shares, and a report for a child order that
  was never sent executes nothing, so duplicate, oversized and unknown reports are covered.
  Over every sequence of sends and reports no child is executed beyond its quantity and the
  shares executed per parent never exceed the shares sent (`run_executed_le_sent`).
* `routeQty liq qty sent`: the child quantity a routing opportunity calls for, the available
  liquidity capped at the parent's shares not yet sent. Sending it never overroutes
  (`add_routeQty_le`), and it is zero once the parent is executed in full
  (`routeQty_eq_zero_of_filled`).
* `Counts key f ctr l`: the router's counter `ctr` agrees with `sumFor key f l` for every key.
  `Counts.set_add` and `Counts.append` are the two steps a router's bookkeeping takes;
  `Counts.execute` is the cumulative quantity function done right: the counter of the parent
  advances by what the venue executed, not by what the report said.
-/

namespace ProofForgeFin.Trading.Router

open ProofForgeFin.Seq ProofForgeFin.Ledger

universe u v w

variable {κ : Type u} {ι : Type v} [DecidableEq ι]

/-! ## Sums per key -/

/-- The sum of `f` over the records of `l` whose `key` is `id`. -/
def sumFor (key : κ → ι) (f : κ → Nat) : List κ → ι → Nat
  | [], _ => 0
  | c :: cs, id => (if key c = id then f c else 0) + sumFor key f cs id

/-- The sum over no records is zero. -/
@[simp] theorem sumFor_nil (key : κ → ι) (f : κ → Nat) (id : ι) : sumFor key f [] id = 0 := rfl

/-- The sum over `c :: cs`. -/
@[simp] theorem sumFor_cons (key : κ → ι) (f : κ → Nat) (c : κ) (cs : List κ) (id : ι) :
    sumFor key f (c :: cs) id = (if key c = id then f c else 0) + sumFor key f cs id := rfl

/-- The sum over a concatenation. -/
@[simp] theorem sumFor_append (key : κ → ι) (f : κ → Nat) (l₁ l₂ : List κ) (id : ι) :
    sumFor key f (l₁ ++ l₂) id = sumFor key f l₁ id + sumFor key f l₂ id := by
  induction l₁ with
  | nil => simp
  | cons c cs ih => simp [ih]; omega

/-- `sumFor` as a sum over the mapped list. -/
theorem sumFor_eq_sum (key : κ → ι) (f : κ → Nat) (l : List κ) (id : ι) :
    sumFor key f l id = (l.map fun c => if key c = id then f c else 0).sum := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- The sum over a mapped list. -/
theorem sumFor_map {α : Type w} (key : κ → ι) (f : κ → Nat) (g : α → κ) (l : List α) (id : ι) :
    sumFor key f (l.map g) id = sumFor (fun a => key (g a)) (fun a => f (g a)) l id := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- No record with key `id` contributes: the sum is zero. -/
theorem sumFor_eq_zero_of_forall_ne (key : κ → ι) (f : κ → Nat) {l : List κ} {id : ι}
    (h : ∀ c ∈ l, key c ≠ id) : sumFor key f l id = 0 := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [sumFor_cons, h c (by simp), ite_false, Nat.zero_add]
    exact ih (fun c' hc => h c' (List.mem_cons_of_mem _ hc))

/-- A function that is zero on every record sums to zero. -/
theorem sumFor_eq_zero_of_forall (key : κ → ι) (f : κ → Nat) {l : List κ} (id : ι)
    (h : ∀ c ∈ l, f c = 0) : sumFor key f l id = 0 := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [sumFor_cons, h c (by simp), ite_self, Nat.zero_add]
    exact ih (fun c' hc => h c' (List.mem_cons_of_mem _ hc))

/-- Pointwise bounds give a bound on the sums. -/
theorem sumFor_le_sumFor (key : κ → ι) {f g : κ → Nat} {l : List κ} (h : ∀ c ∈ l, f c ≤ g c)
    (id : ι) : sumFor key f l id ≤ sumFor key g l id := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    have h1 := h c (by simp)
    have h2 := ih (fun c' hc => h c' (List.mem_cons_of_mem _ hc))
    simp only [sumFor_cons]
    split <;> omega

/-- The sum for one key is at most the sum over all records. -/
theorem sumFor_le_sum (key : κ → ι) (f : κ → Nat) (l : List κ) (id : ι) :
    sumFor key f l id ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons c cs ih => simp only [sumFor_cons, List.map_cons, List.sum_cons]; split <;> omega

/-- A record with key `id` contributes its value. -/
theorem le_sumFor (key : κ → ι) (f : κ → Nat) {l : List κ} {c : κ} (hc : c ∈ l) :
    f c ≤ sumFor key f l (key c) := by
  induction l with
  | nil => simp at hc
  | cons a as ih =>
    simp only [sumFor_cons]
    rcases List.mem_cons.mp hc with h | h
    · subst h; simp
    · have := ih h; split <;> omega

/-- Replacing the record at position `k` by `c'`: the new sum plus the old record's
contribution is the old sum plus the new record's contribution. -/
theorem sumFor_set (key : κ → ι) (f : κ → Nat) {l : List κ} {k : Nat} {c : κ} (hk : l[k]? = some c)
    (c' : κ) (id : ι) :
    sumFor key f (l.set k c') id + (if key c = id then f c else 0) =
      sumFor key f l id + (if key c' = id then f c' else 0) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp only [List.set_cons_zero, sumFor_cons]
      omega
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      have := ih hk
      simp only [List.set_cons_succ, sumFor_cons]
      omega

/-- Replacing a record by one with the same key and the same value keeps every sum. -/
theorem sumFor_set_eq (key : κ → ι) (f : κ → Nat) {l : List κ} {k : Nat} {c c' : κ}
    (hk : l[k]? = some c) (hkey : key c' = key c) (hf : f c' = f c) (id : ι) :
    sumFor key f (l.set k c') id = sumFor key f l id := by
  have := sumFor_set key f hk c' id
  rw [hkey, hf] at this
  omega

/-- Replacing a record by one with the same key and `x` more value adds `x` to the sum of its
key. -/
theorem sumFor_set_add (key : κ → ι) (f : κ → Nat) {l : List κ} {k : Nat} {c c' : κ}
    (hk : l[k]? = some c) (hkey : key c' = key c) {x : Nat} (hf : f c' = f c + x) (id : ι) :
    sumFor key f (l.set k c') id = sumFor key f l id + (if key c = id then x else 0) := by
  have := sumFor_set key f hk c' id
  rw [hkey, hf] at this
  by_cases e : key c = id <;> simp only [e, ite_true, ite_false] at this ⊢ <;> omega

/-! ## Function tables as lists -/

/-- The entries `f 0, ..., f (n - 1)` of a function table as a list. -/
def table {β : Type w} (f : Nat → β) (n : Nat) : List β := (List.range n).map f

/-- A table of `n` entries has length `n`. -/
@[simp] theorem length_table {β : Type w} (f : Nat → β) (n : Nat) : (table f n).length = n := by
  simp [table]

/-- The empty table. -/
@[simp] theorem table_zero {β : Type w} (f : Nat → β) : table f 0 = [] := rfl

/-- A table of `n + 1` entries is the table of `n` entries followed by entry `n`. -/
theorem table_succ {β : Type w} (f : Nat → β) (n : Nat) : table f (n + 1) = table f n ++ [f n] := by
  simp [table, List.range_succ]

/-- Reading a table inside its bounds. -/
theorem getElem?_table {β : Type w} (f : Nat → β) {n k : Nat} (h : k < n) : (table f n)[k]? = some (f k) := by
  simp [table, h]

/-- Reading a table outside its bounds. -/
theorem getElem?_table_of_le {β : Type w} (f : Nat → β) {n k : Nat} (h : n ≤ k) : (table f n)[k]? = none := by
  simp [table]; omega

/-- The members of a table. -/
theorem mem_table {β : Type w} {f : Nat → β} {n : Nat} {x : β} : x ∈ table f n ↔ ∃ k, k < n ∧ f k = x := by
  simp [table]

/-- Tables agree when the functions agree below the length. -/
theorem table_congr {β : Type w} {f g : Nat → β} {n : Nat} (h : ∀ k, k < n → f k = g k) :
    table f n = table g n := by
  unfold table
  apply List.map_congr_left
  intro k hk
  exact h k (List.mem_range.mp hk)

/-- Writing a new entry at index `n` appends it to the table. -/
theorem table_upd_succ {β : Type w} (f : Nat → β) (n : Nat) (v : β) :
    table (upd f n v) (n + 1) = table f n ++ [v] := by
  rw [table_succ, upd_self]
  congr 1
  exact table_congr (fun k hk => upd_ne f v (by omega))

/-- Overwriting an entry below `n` is `List.set` on the table. -/
theorem set_table {β : Type w} (f : Nat → β) {n k : Nat} (h : k < n) (v : β) :
    (table f n).set k v = table (upd f k v) n := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  by_cases hj : j < n
  · rw [getElem?_table _ hj, getElem?_table _ hj]
    by_cases hkj : k = j
    · subst hkj; simp [h]
    · simp [hkj, upd_ne f v (Ne.symm hkj)]
  · rw [getElem?_table_of_le _ (by omega), getElem?_table_of_le _ (by omega)]
    simp; omega

/-- Reading an updated function through `g` is updating the function read through `g`. -/
theorem comp_upd_apply {α : Type w} {β : Type u} {γ : Type v} [DecidableEq α] (g : β → γ) (f : α → β)
    (n : α) (v : β) (j : α) : g (upd f n v j) = upd (fun k => g (f k)) n (g v) j := by
  unfold upd; split <;> rfl

/-- A table of a function read through `g`, after writing entry `n`: the old table followed by
`g v`. This is the shape of a router that keeps records in a function with a counter and whose
list of facts holds a projection of each record. -/
theorem table_comp_upd_succ {β : Type w} {γ : Type u} (g : β → γ) (f : Nat → β) (n : Nat) (v : β) :
    table (fun k => g (upd f n v k)) (n + 1) = table (fun k => g (f k)) n ++ [g v] := by
  have : (fun k => g (upd f n v k)) = upd (fun k => g (f k)) n (g v) := by
    funext k; unfold upd; split <;> rfl
  rw [this, table_upd_succ]

/-- A table of a function read through `g`, after overwriting entry `k < n`, is `List.set` on
the old table. -/
theorem set_table_comp {β : Type w} {γ : Type u} (g : β → γ) (f : Nat → β) {n k : Nat} (h : k < n) (v : β) :
    (table (fun j => g (f j)) n).set k (g v) = table (fun j => g (upd f k v j)) n := by
  rw [set_table _ h]
  apply table_congr
  intro j _
  unfold upd; split <;> rfl

/-! ## The venue model -/

/-- A child order as the venues see it: its parent, its quantity and the shares executed. -/
structure Child (ι : Type v) where
  /-- The parent order the child order represents. -/
  parent : ι
  /-- The quantity sent. -/
  qty : Nat
  /-- The quantity executed so far. -/
  done : Nat
  deriving DecidableEq, Repr

/-- Shares sent in the child orders of `l` for parent `id`. -/
def sent (l : List (Child ι)) (id : ι) : Nat := sumFor Child.parent Child.qty l id

/-- Shares executed in the child orders of `l` for parent `id`. -/
def executed (l : List (Child ι)) (id : ι) : Nat := sumFor Child.parent Child.done l id

/-- A newly sent child order: nothing executed. -/
def fresh (p : ι) (q : Nat) : Child ι := ⟨p, q, 0⟩

/-- The child orders after the router sends `out` (pairs of parent and quantity). -/
def send (l : List (Child ι)) (out : List (ι × Nat)) : List (Child ι) :=
  l ++ out.map (fun o => fresh o.1 o.2)

/-- The quantity an execution report of `q` on child order `k` executes: at most the child's
unexecuted shares, nothing for a child order that was never sent. -/
def execAmt (l : List (Child ι)) (k q : Nat) : Nat :=
  match l[k]? with
  | some c => min q (c.qty - c.done)
  | none => 0

/-- The child orders after an execution report of `q` on child order `k`. -/
def execute (l : List (Child ι)) (k q : Nat) : List (Child ι) :=
  match l[k]? with
  | some c => l.set k { c with done := c.done + min q (c.qty - c.done) }
  | none => l

/-- No child order is executed beyond its quantity. -/
def DoneLeQty (l : List (Child ι)) : Prop := ∀ c ∈ l, c.done ≤ c.qty

/-- `sent` over a concatenation. -/
@[simp] theorem sent_append (l₁ l₂ : List (Child ι)) (id : ι) :
    sent (l₁ ++ l₂) id = sent l₁ id + sent l₂ id := sumFor_append _ _ _ _ _

/-- `executed` over a concatenation. -/
@[simp] theorem executed_append (l₁ l₂ : List (Child ι)) (id : ι) :
    executed (l₁ ++ l₂) id = executed l₁ id + executed l₂ id := sumFor_append _ _ _ _ _

/-- `sent` over `c :: l`. -/
@[simp] theorem sent_cons (c : Child ι) (l : List (Child ι)) (id : ι) :
    sent (c :: l) id = (if c.parent = id then c.qty else 0) + sent l id := rfl

/-- `executed` over `c :: l`. -/
@[simp] theorem executed_cons (c : Child ι) (l : List (Child ι)) (id : ι) :
    executed (c :: l) id = (if c.parent = id then c.done else 0) + executed l id := rfl

/-- Nothing is sent over no child orders. -/
@[simp] theorem sent_nil (id : ι) : sent ([] : List (Child ι)) id = 0 := rfl

/-- Nothing is executed over no child orders. -/
@[simp] theorem executed_nil (id : ι) : executed ([] : List (Child ι)) id = 0 := rfl

/-- Newly sent child orders have nothing executed. -/
@[simp] theorem executed_map_fresh (out : List (ι × Nat)) (id : ι) :
    executed (out.map (fun o => fresh o.1 o.2)) id = 0 :=
  sumFor_eq_zero_of_forall _ _ id (fun c hc => by
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hc; rfl)

/-- Shares sent by a send. -/
theorem sent_send (l : List (Child ι)) (out : List (ι × Nat)) (id : ι) :
    sent (send l out) id = sent l id + sumFor Prod.fst Prod.snd out id := by
  simp only [send, sent_append]
  unfold sent
  rw [sumFor_map]
  rfl

/-- A send executes nothing. -/
@[simp] theorem executed_send (l : List (Child ι)) (out : List (ι × Nat)) (id : ι) :
    executed (send l out) id = executed l id := by
  simp [send]

omit [DecidableEq ι] in
/-- An execution report on a child order that was never sent changes nothing. -/
theorem execute_of_none {l : List (Child ι)} {k : Nat} (h : l[k]? = none) (q : Nat) :
    execute l k q = l := by
  simp [execute, h]

omit [DecidableEq ι] in
/-- An execution report on a child order that was never sent executes nothing. -/
theorem execAmt_of_none {l : List (Child ι)} {k : Nat} (h : l[k]? = none) (q : Nat) :
    execAmt l k q = 0 := by
  simp [execAmt, h]

omit [DecidableEq ι] in
/-- An execution report on child order `k` sets its executed shares. -/
theorem execute_of_some {l : List (Child ι)} {k : Nat} {c : Child ι} (h : l[k]? = some c) (q : Nat) :
    execute l k q = l.set k { c with done := c.done + min q (c.qty - c.done) } := by
  simp [execute, h]

omit [DecidableEq ι] in
/-- The quantity executed on a child order that was sent. -/
theorem execAmt_of_some {l : List (Child ι)} {k : Nat} {c : Child ι} (h : l[k]? = some c) (q : Nat) :
    execAmt l k q = min q (c.qty - c.done) := by
  simp [execAmt, h]

omit [DecidableEq ι] in
/-- An execution report executes at most the reported quantity. -/
theorem execAmt_le (l : List (Child ι)) (k q : Nat) : execAmt l k q ≤ q := by
  unfold execAmt; split <;> omega

omit [DecidableEq ι] in
/-- An execution report keeps the number of child orders. -/
@[simp] theorem length_execute (l : List (Child ι)) (k q : Nat) : (execute l k q).length = l.length := by
  unfold execute; split <;> simp

/-- An execution report does not change the shares sent. -/
@[simp] theorem sent_execute (l : List (Child ι)) (k q : Nat) (id : ι) :
    sent (execute l k q) id = sent l id := by
  unfold execute
  split
  · rename_i c hc
    exact sumFor_set_eq Child.parent Child.qty (c' := { c with done := c.done + min q (c.qty - c.done) })
      hc rfl rfl id
  · rfl

/-- An execution report adds what it executes to the parent of the child order it names. -/
theorem executed_execute {l : List (Child ι)} {k : Nat} {c : Child ι} (h : l[k]? = some c)
    (q : Nat) (id : ι) :
    executed (execute l k q) id = executed l id + (if c.parent = id then min q (c.qty - c.done) else 0) := by
  rw [execute_of_some h]
  exact sumFor_set_add Child.parent Child.done (c' := { c with done := c.done + min q (c.qty - c.done) })
    h rfl rfl id

/-- An execution report raises the executed shares of every parent by at most what it
executes. -/
theorem executed_execute_le (l : List (Child ι)) (k q : Nat) (id : ι) :
    executed (execute l k q) id ≤ executed l id + execAmt l k q := by
  cases h : l[k]? with
  | none => rw [execute_of_none h, execAmt_of_none h]; omega
  | some c => rw [executed_execute h, execAmt_of_some h]; split <;> omega

omit [DecidableEq ι] in
/-- The venue model never executes a child order beyond its quantity. -/
theorem doneLeQty_execute {l : List (Child ι)} (h : DoneLeQty l) (k q : Nat) :
    DoneLeQty (execute l k q) := by
  unfold execute
  split
  · rename_i c hc
    intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hx | hx
    · exact h x hx
    · subst hx
      have := h c (List.mem_of_getElem? hc)
      show c.done + min q (c.qty - c.done) ≤ c.qty; omega
  · exact h

omit [DecidableEq ι] in
/-- Newly sent child orders are within their quantity. -/
theorem doneLeQty_send {l : List (Child ι)} (h : DoneLeQty l) (out : List (ι × Nat)) :
    DoneLeQty (send l out) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · obtain ⟨o, _, rfl⟩ := List.mem_map.mp hx; exact Nat.zero_le _

/-- Shares executed never exceed shares sent, when no child order is executed beyond its
quantity. -/
theorem executed_le_sent {l : List (Child ι)} (h : DoneLeQty l) (id : ι) : executed l id ≤ sent l id :=
  sumFor_le_sumFor _ h id

/-- An event at the venues: the router sends child orders, or an execution report arrives. -/
inductive VenueEvent (ι : Type v) where
  /-- The router sends child orders (pairs of parent and quantity). -/
  | send (out : List (ι × Nat))
  /-- An execution report of `q` shares on child order `k` (possibly unknown, duplicate or
  oversized). -/
  | exec (k q : Nat)

/-- The child orders after one event. -/
def venueStep (l : List (Child ι)) : VenueEvent ι → List (Child ι)
  | .send out => send l out
  | .exec k q => execute l k q

omit [DecidableEq ι] in
/-- Every event keeps every child order within its quantity. -/
theorem venueStep_doneLeQty : Preserves (venueStep (ι := ι)) DoneLeQty := by
  intro l e h
  cases e with
  | send out => exact doneLeQty_send h out
  | exec k q => exact doneLeQty_execute h k q

/-- From no child orders, after any sequence of sends and execution reports (duplicate,
oversized and unknown ones included), the shares executed for every parent never exceed the
shares sent for it. -/
theorem run_executed_le_sent (es : List (VenueEvent ι)) (id : ι) :
    executed (run venueStep [] es) id ≤ sent (run venueStep [] es) id :=
  executed_le_sent (run_invariant venueStep_doneLeQty (fun _ h => by simp at h) es) id

/-! ## Routing arithmetic -/

/-- The child quantity a routing opportunity with `liq` shares available calls for, for a parent
of quantity `qty` that has sent `sent`: the liquidity capped at the shares not yet sent. -/
def routeQty (liq qty sent : Nat) : Nat := min liq (qty - sent)

/-- A route never exceeds the liquidity. -/
theorem routeQty_le_liq (liq qty sent : Nat) : routeQty liq qty sent ≤ liq := Nat.min_le_left _ _

/-- Never overroute: sending the route keeps the shares sent within the parent quantity. -/
theorem add_routeQty_le {liq qty sent : Nat} (h : sent ≤ qty) : sent + routeQty liq qty sent ≤ qty := by
  unfold routeQty; omega

/-- Shares sent after the route, exactly, when nothing was overrouted before. -/
theorem add_routeQty_eq {liq qty sent : Nat} (h : sent ≤ qty) :
    sent + routeQty liq qty sent = min (sent + liq) qty := by
  unfold routeQty; omega

/-- A route is empty exactly when there is no liquidity or nothing is left to send. -/
theorem routeQty_eq_zero_iff {liq qty sent : Nat} : routeQty liq qty sent = 0 ↔ liq = 0 ∨ qty ≤ sent := by
  unfold routeQty; omega

/-- A route is nonempty exactly when there is liquidity and something left to send. -/
theorem routeQty_pos_iff {liq qty sent : Nat} : 0 < routeQty liq qty sent ↔ 0 < liq ∧ sent < qty := by
  unfold routeQty; omega

/-- Stop when filled: once the shares executed reach the parent quantity, and executed shares
never exceed shares sent and shares sent never exceed the quantity, the route is empty. -/
theorem routeQty_eq_zero_of_filled {liq qty sent exec : Nat} (hes : exec ≤ sent) (hsq : sent ≤ qty)
    (h : exec = qty) : routeQty liq qty sent = 0 := by
  unfold routeQty; omega

/-- Executed shares stay within the parent quantity when the shares sent do. -/
theorem executed_le_qty {l : List (Child ι)} (h : DoneLeQty l) {id : ι} {qty : Nat}
    (hs : sent l id ≤ qty) : executed l id ≤ qty :=
  Nat.le_trans (executed_le_sent h id) hs

/-! ## Accounting: the router's counters against the venues -/

/-- The router's counter `ctr` agrees with `sumFor key f l` for every key. -/
def Counts (key : κ → ι) (f : κ → Nat) (ctr : ι → Nat) (l : List κ) : Prop :=
  ∀ id, ctr id = sumFor key f l id

/-- A counter equal pointwise to one that agrees, agrees. -/
theorem Counts.congr {key : κ → ι} {f : κ → Nat} {ctr ctr' : ι → Nat} {l : List κ}
    (h : Counts key f ctr l) (e : ∀ id, ctr' id = ctr id) : Counts key f ctr' l :=
  fun id => (e id).trans (h id)

/-- Resetting the counter of a key with no records to zero keeps the agreement (a new parent
order starts with nothing sent and nothing executed). -/
theorem Counts.upd_zero {key : κ → ι} {f : κ → Nat} {ctr : ι → Nat} {l : List κ}
    (h : Counts key f ctr l) {n : ι} (hn : ∀ c ∈ l, key c ≠ n) : Counts key f (upd ctr n 0) l := by
  intro id
  by_cases e : id = n
  · subst e; rw [upd_self, sumFor_eq_zero_of_forall_ne key f hn]
  · rw [upd_ne ctr 0 e, h id]

/-- Counting from nothing: a zero counter agrees with no records. -/
theorem counts_nil (key : κ → ι) (f : κ → Nat) : Counts key f (fun _ => 0) [] := fun _ => rfl

/-- Appending records: the counter of each key advances by their sum. -/
theorem Counts.append {key : κ → ι} {f : κ → Nat} {ctr : ι → Nat} {l : List κ} (h : Counts key f ctr l)
    (l' : List κ) : Counts key f (fun id => ctr id + sumFor key f l' id) (l ++ l') := by
  intro id; show ctr id + _ = _; rw [sumFor_append, h id]

/-- Appending one record: the counter of its key advances by its value. -/
theorem Counts.append_one {key : κ → ι} {f : κ → Nat} {ctr : ι → Nat} {l : List κ} (h : Counts key f ctr l)
    (c : κ) : Counts key f (upd ctr (key c) (ctr (key c) + f c)) (l ++ [c]) := by
  intro id
  rw [sumFor_append]
  by_cases e : id = key c
  · subst e; simp [upd, h (key c)]
  · simp [upd, e, Ne.symm e, h id]

/-- Appending records that contribute nothing keeps the counter. -/
theorem Counts.append_zero {key : κ → ι} {f : κ → Nat} {ctr : ι → Nat} {l : List κ} (h : Counts key f ctr l)
    {l' : List κ} (h' : ∀ c ∈ l', f c = 0) : Counts key f ctr (l ++ l') := by
  intro id; rw [sumFor_append, h id, sumFor_eq_zero_of_forall _ _ id h']; rfl

/-- Updating one record in place by `x` more value: the counter of its key advances by `x`. -/
theorem Counts.set_add {key : κ → ι} {f : κ → Nat} {ctr : ι → Nat} {l : List κ} (h : Counts key f ctr l)
    {k : Nat} {c c' : κ} (hk : l[k]? = some c) (hkey : key c' = key c) {x : Nat} (hf : f c' = f c + x) :
    Counts key f (upd ctr (key c) (ctr (key c) + x)) (l.set k c') := by
  intro id
  rw [sumFor_set_add key f hk hkey hf id]
  by_cases e : id = key c
  · subst e; simp [upd, h (key c)]
  · simp [upd, e, Ne.symm e, h id]

/-- Updating one record in place without changing its key or value keeps the counter. -/
theorem Counts.set_eq {key : κ → ι} {f : κ → Nat} {ctr : ι → Nat} {l : List κ} (h : Counts key f ctr l)
    {k : Nat} {c c' : κ} (hk : l[k]? = some c) (hkey : key c' = key c) (hf : f c' = f c) :
    Counts key f ctr (l.set k c') := by
  intro id; rw [sumFor_set_eq key f hk hkey hf id, h id]

/-- The cumulative executed quantity of each parent, kept right: on an execution report for a
child order that was sent, the counter of its parent advances by what the venue executed. -/
theorem Counts.execute {ctr : ι → Nat} {l : List (Child ι)} (h : Counts Child.parent Child.done ctr l)
    {k : Nat} {c : Child ι} (hk : l[k]? = some c) (q : Nat) :
    Counts Child.parent Child.done (upd ctr c.parent (ctr c.parent + min q (c.qty - c.done)))
      (Router.execute l k q) := by
  rw [execute_of_some hk]
  exact h.set_add (c' := { c with done := c.done + min q (c.qty - c.done) }) hk rfl rfl

/-- On an execution report for a child order that was never sent, the counter stays. -/
theorem Counts.execute_none {ctr : ι → Nat} {l : List (Child ι)} (h : Counts Child.parent Child.done ctr l)
    {k : Nat} (hk : l[k]? = none) (q : Nat) : Counts Child.parent Child.done ctr (Router.execute l k q) := by
  rw [execute_of_none hk]; exact h

/-- An execution report does not change the shares sent per parent. -/
theorem Counts.execute_sent {ctr : ι → Nat} {l : List (Child ι)} (h : Counts Child.parent Child.qty ctr l)
    (k q : Nat) : Counts Child.parent Child.qty ctr (Router.execute l k q) := by
  intro id; rw [h id]; exact (sent_execute l k q id).symm

/-- Counting the reported quantity instead of the executed one overcounts: one child order of
100 shares executed in full, then a duplicate report of 100 shares. The venue executed 100
shares; a counter that adds each reported quantity reads 200. -/
theorem reported_count_overcounts :
    let l : List (Child Nat) := execute (execute [fresh 0 100] 0 100) 0 100
    executed l 0 = 100 ∧ 100 + 100 ≠ executed l 0 := by
  decide

end ProofForgeFin.Trading.Router
