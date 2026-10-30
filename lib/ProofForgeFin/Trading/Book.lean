import ProofForgeFin.Trading.Basic
import ProofForgeFin.Seq
/-!
# Limit order book with price-time priority

A central limit order book keeps, for each side, the resting orders in priority order: the best
price first (highest bid, lowest ask) and, at one price, the earliest order first. An incoming
order trades against the other side from the best resting order on, level by level, at the
resting order's price, while the resting price is no worse than the incoming limit; what is left
rests on its own side behind every order at the same or a better price. This module states that
model once and proves the properties exchange rulebooks and matching-engine tests ask for.

* `Sorted s key l`, `insertBy s key x l`: a side in priority order and insertion with time
  priority, for any element type with a price key (`insertBy_split`, `sorted_insertBy`,
  `level_insertBy_self`: at one price level, the new element is served after every element
  already there).
* `level key p l`: the elements at price level `p` in priority order; `level_insert_at`,
  `level_remove_at` (FIFO bookkeeping for one insert and one removal).
* `runOut`, `flow_runOut`: a run that records each operation with its outcome, and the flow
  theorem "start followed by inflow equals outflow followed by end" for every run once it holds
  for every step (FIFO queues, priority classes).
* `Resting`, `Trade`, `Stp` (self-trade prevention: off, cancel resting, cancel incoming),
  `matchOrder` (walk the opposite side with partial fills over several levels), `Book`,
  `submit`, `cancel`, `step`.

The matching theorems: trades are at the maker's price and no worse than the incoming limit
(`matchOrder_price`, `matchOrder_maker`); quantity is conserved on the incoming side
(`matchOrder_traded_add_rest`) and on the resting side (`matchOrder_traded_add_total`); trades
consume the book in order (`matchOrder_shape`), so an order trades only after every order ahead of
it has left the book (`matchOrder_priority`); no trade has the same owner on both sides when
self-trade prevention is on (`matchOrder_no_self_trade`); the book stays sorted, with positive
quantities, and uncrossed after every submit and cancel and over every sequence of them
(`Wf.submit`, `Wf.cancel`, `wf_run`).

Prices and quantities are natural numbers in ticks and lots. Orders are limit orders, optionally
immediate-or-cancel; market orders are limit orders at the worst price. Not modelled: order
amendment, hidden and iceberg quantity, auctions, minimum quantities, pro-rata matching.
-/

namespace ProofForgeFin.Trading.Book

universe u v w x

/-! ## Sides in priority order -/

section Sorted

variable {α : Type u} {s : Side} {key : α → Nat}

/-- `l` is in priority order for side `s`: along the list, each element's price is at least as
good as the price of every later element (bids by decreasing price, asks by increasing price). -/
def Sorted (s : Side) (key : α → Nat) (l : List α) : Prop :=
  l.Pairwise (fun a b => s.le (key a) (key b))

/-- The empty side is in priority order. -/
@[simp] theorem sorted_nil : Sorted s key [] := List.Pairwise.nil

/-- A list headed by `a` is in priority order when `a` is at least as good as every later
element and the rest is in priority order. -/
theorem sorted_cons {a : α} {l : List α} :
    Sorted s key (a :: l) ↔ (∀ b ∈ l, s.le (key a) (key b)) ∧ Sorted s key l :=
  List.pairwise_cons

/-- The rest of a list in priority order is in priority order. -/
theorem Sorted.tail {a : α} {l : List α} (h : Sorted s key (a :: l)) : Sorted s key l :=
  (sorted_cons.1 h).2

/-- The head of a list in priority order is at least as good as every other element. -/
theorem Sorted.head_le {a : α} {l : List α} (h : Sorted s key (a :: l)) :
    ∀ b ∈ l, s.le (key a) (key b) :=
  (sorted_cons.1 h).1

/-- A sublist of a list in priority order is in priority order. -/
theorem Sorted.sublist {l l' : List α} (h : Sorted s key l) (hs : l'.Sublist l) : Sorted s key l' :=
  List.Pairwise.sublist hs h

/-- Removing elements (for example cancelled orders) keeps priority order. -/
theorem Sorted.filter {l : List α} (p : α → Bool) (h : Sorted s key l) :
    Sorted s key (l.filter p) :=
  h.sublist (List.filter_sublist)

/-- Insert `x` with time priority: after every element whose price is at least as good, before
the first element whose price is strictly worse. -/
def insertBy (s : Side) (key : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if s.lt (key x) (key y) then x :: y :: ys else y :: insertBy s key x ys

/-- Inserting into the empty side. -/
@[simp] theorem insertBy_nil (x : α) : insertBy s key x [] = [x] := rfl

/-- Inserting before a strictly worse element. -/
theorem insertBy_cons_of_lt {x y : α} (ys : List α) (h : s.lt (key x) (key y)) :
    insertBy s key x (y :: ys) = x :: y :: ys := by simp [insertBy, h]

/-- Inserting past an element at least as good. -/
theorem insertBy_cons_of_not_lt {x y : α} (ys : List α) (h : ¬ s.lt (key x) (key y)) :
    insertBy s key x (y :: ys) = y :: insertBy s key x ys := by simp [insertBy, h]

/-- Insertion adds exactly the new element: the result is a permutation of `x :: l`. -/
theorem perm_insertBy (x : α) (l : List α) : (insertBy s key x l).Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    by_cases h : s.lt (key x) (key y)
    · rw [insertBy_cons_of_lt ys h]
    · rw [insertBy_cons_of_not_lt ys h]
      exact (ih.cons y).trans (List.Perm.swap x y ys)

/-- The elements after insertion are the new element and the old ones. -/
@[simp] theorem mem_insertBy {x a : α} {l : List α} : a ∈ insertBy s key x l ↔ a = x ∨ a ∈ l := by
  rw [(perm_insertBy x l).mem_iff, List.mem_cons]

/-- Insertion adds one element. -/
@[simp] theorem length_insertBy (x : α) (l : List α) :
    (insertBy s key x l).length = l.length + 1 := by
  rw [(perm_insertBy x l).length_eq]; rfl

/-- Where insertion places the new element in a side in priority order: after the part `l₁` of
elements at least as good, before the part `l₂` of elements strictly worse, keeping the order of
the old elements. -/
theorem insertBy_split (x : α) : ∀ {l : List α}, Sorted s key l →
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ insertBy s key x l = l₁ ++ x :: l₂ ∧
      (∀ y ∈ l₁, s.le (key y) (key x)) ∧ (∀ y ∈ l₂, s.lt (key x) (key y))
  | [], _ => ⟨[], [], rfl, rfl, by simp, by simp⟩
  | y :: ys, h => by
    by_cases hlt : s.lt (key x) (key y)
    · refine ⟨[], y :: ys, rfl, insertBy_cons_of_lt ys hlt, by simp, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hlt
      · exact Side.lt_of_lt_of_le hlt (h.head_le z hz)
    · obtain ⟨l₁, l₂, h1, h2, h3, h4⟩ := insertBy_split x h.tail
      refine ⟨y :: l₁, l₂, by simp [h1], by rw [insertBy_cons_of_not_lt ys hlt, h2]; rfl, ?_, h4⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Side.not_lt_iff_le.mp hlt
      · exact h3 z hz

/-- Placing an element between a part at least as good and a part no better keeps priority
order. -/
theorem sorted_insert_at {l₁ l₂ : List α} {x : α} (hs : Sorted s key (l₁ ++ l₂))
    (h1 : ∀ y ∈ l₁, s.le (key y) (key x)) (h2 : ∀ y ∈ l₂, s.le (key x) (key y)) :
    Sorted s key (l₁ ++ x :: l₂) := by
  unfold Sorted at *
  rw [List.pairwise_append] at hs ⊢
  refine ⟨hs.1, List.pairwise_cons.2 ⟨h2, hs.2.1⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h1 a ha
  · exact hs.2.2 a ha b hb

/-- Insertion with time priority keeps a side in priority order. -/
theorem sorted_insertBy (x : α) {l : List α} (h : Sorted s key l) :
    Sorted s key (insertBy s key x l) := by
  obtain ⟨l₁, l₂, h1, h2, h3, h4⟩ := insertBy_split x h
  rw [h2]
  rw [h1] at h
  exact sorted_insert_at h h3 (fun y hy => Side.le_of_lt (h4 y hy))

end Sorted

/-! ## Price levels and time priority -/

section Level

variable {α : Type u} {s : Side} {key : α → Nat}

/-- The elements at price level `p`, in list order. In a side in priority order this is the
queue of the level, earliest first. -/
def level (key : α → Nat) (p : Nat) (l : List α) : List α := l.filter (fun y => key y == p)

/-- The level of the empty list is empty. -/
@[simp] theorem level_nil (p : Nat) : level key p [] = [] := rfl

/-- The level of a concatenation. -/
@[simp] theorem level_append (p : Nat) (l₁ l₂ : List α) :
    level key p (l₁ ++ l₂) = level key p l₁ ++ level key p l₂ := List.filter_append ..

/-- The level of a list headed by `y`. -/
theorem level_cons (p : Nat) (y : α) (l : List α) :
    level key p (y :: l) = if key y = p then y :: level key p l else level key p l := by
  unfold level; rw [List.filter_cons]; simp

/-- No element strictly worse than `x` is at the level of `x`. -/
theorem level_eq_nil_of_lt {x : α} {l : List α} (h : ∀ y ∈ l, s.lt (key x) (key y)) :
    level key (key x) l = [] := by
  unfold level
  rw [List.filter_eq_nil_iff]
  intro y hy
  have := h y hy
  simp only [beq_iff_eq]
  intro e
  rw [e] at this
  exact Side.lt_irrefl s _ this

/-- FIFO bookkeeping of one insertion: placing `x` before a part of strictly worse elements
appends `x` to the end of its level and changes no other level. -/
theorem level_insert_at (p : Nat) {l₁ l₂ : List α} {x : α} (h2 : ∀ y ∈ l₂, s.lt (key x) (key y)) :
    level key p (l₁ ++ x :: l₂) = level key p (l₁ ++ l₂) ++ level key p [x] := by
  by_cases hp : key x = p
  · have hnil := level_eq_nil_of_lt h2
    rw [hp] at hnil
    simp [level_cons, hp, hnil]
  · simp [level_cons, hp]

/-- FIFO bookkeeping of one removal: removing `x` from behind a part of strictly worse elements
removes the head of its level and changes no other level. -/
theorem level_remove_at (p : Nat) {l₁ l₂ : List α} {x : α} (h1 : ∀ y ∈ l₁, s.lt (key x) (key y)) :
    level key p (l₁ ++ x :: l₂) = level key p [x] ++ level key p (l₁ ++ l₂) := by
  by_cases hp : key x = p
  · have hnil := level_eq_nil_of_lt h1
    rw [hp] at hnil
    simp [level_cons, hp, hnil]
  · simp [level_cons, hp]

/-- Time priority of insertion: in a side in priority order, inserting `x` appends it to the end
of its level and leaves every other level unchanged. -/
theorem level_insertBy (p : Nat) (x : α) {l : List α} (h : Sorted s key l) :
    level key p (insertBy s key x l) = level key p l ++ level key p [x] := by
  obtain ⟨l₁, l₂, h1, h2, _, h4⟩ := insertBy_split x h
  rw [h2, h1, level_insert_at p h4]

/-- The new element is served after every element already at its price level. -/
theorem level_insertBy_self (x : α) {l : List α} (h : Sorted s key l) :
    level key (key x) (insertBy s key x l) = level key (key x) l ++ [x] := by
  rw [level_insertBy _ x h]; simp [level_cons]

/-- Removing the head of a list moves it to the front of its level. -/
theorem level_head (p : Nat) (x : α) (l : List α) :
    level key p (x :: l) = level key p [x] ++ level key p l := by
  simp [level_cons]; split <;> simp

end Level

/-! ## Runs with outcomes and flow conservation -/

section Flow

variable {σ : Type u} {α : Type v} {β : Type w} {γ δ : Type x}

/-- Run a list of operations from a state with a step that returns an outcome and the next
state; returns each operation with its outcome, and the final state. This is the `run` of the
queue task specifications. -/
def runOut (step : σ → α → β × σ) : σ → List α → List (α × β) × σ
  | s, [] => ([], s)
  | s, a :: as =>
    ((a, (step s a).1) :: (runOut step (step s a).2 as).1, (runOut step (step s a).2 as).2)

/-- The run of no operations. -/
@[simp] theorem runOut_nil (step : σ → α → β × σ) (s : σ) : runOut step s [] = ([], s) := rfl

/-- The outcomes of a run of `a :: as`. -/
@[simp] theorem runOut_cons_fst (step : σ → α → β × σ) (s : σ) (a : α) (as : List α) :
    (runOut step s (a :: as)).1 = (a, (step s a).1) :: (runOut step (step s a).2 as).1 := rfl

/-- The final state of a run of `a :: as`. -/
@[simp] theorem runOut_cons_snd (step : σ → α → β × σ) (s : σ) (a : α) (as : List α) :
    (runOut step s (a :: as)).2 = (runOut step (step s a).2 as).2 := rfl

/-- The final state of `runOut` is the state of `Seq.run`. -/
theorem runOut_snd (step : σ → α → β × σ) (s : σ) (as : List α) :
    (runOut step s as).2 = Seq.run (fun t a => (step t a).2) s as := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => exact ih _

/-- Flow conservation. Let `items s` be the contents of a queue, `inOf` and `outOf` the elements
an operation with its outcome adds and delivers, and `F` a view that distributes over
concatenation (the identity, or `level key p` for one priority class). If every step satisfies
"contents followed by inflow equals outflow followed by new contents", so does every run: what
was there and what arrived equals what left and what remains, in order. -/
theorem flow_runOut {step : σ → α → β × σ} (items : σ → List γ) (inOf outOf : α × β → List γ)
    (F : List γ → List δ) (hF : ∀ l₁ l₂, F (l₁ ++ l₂) = F l₁ ++ F l₂)
    (h : ∀ s a, F (items s) ++ F (inOf (a, (step s a).1)) =
      F (outOf (a, (step s a).1)) ++ F (items (step s a).2))
    (s : σ) (ops : List α) :
    F (items s) ++ F ((runOut step s ops).1.flatMap inOf) =
      F ((runOut step s ops).1.flatMap outOf) ++ F (items (runOut step s ops).2) := by
  have h0 : F [] = [] := by
    have := congrArg List.length (hF [] [])
    simp only [List.append_nil, List.length_append] at this
    exact List.length_eq_zero_iff.1 (by omega)
  induction ops generalizing s with
  | nil => simp [h0]
  | cons a as ih =>
    simp only [runOut_cons_fst, runOut_cons_snd, List.flatMap_cons, hF]
    rw [← List.append_assoc, h, List.append_assoc, ih, List.append_assoc]

end Flow

/-! ## Orders, trades and matching -/

/-- An order resting in the book: its identifier, the account that owns it (for self-trade
prevention), its limit price and its open quantity. -/
structure Resting where
  /-- The order identifier. -/
  id : Nat
  /-- The owning account or trading group. -/
  owner : Nat
  /-- The limit price, in ticks. -/
  px : Nat
  /-- The open quantity, in lots. -/
  qty : Nat
  deriving DecidableEq, Repr

/-- An execution between a resting order (the maker) and an incoming order (the taker). -/
structure Trade where
  /-- The identifier of the resting order. -/
  maker : Nat
  /-- The owner of the resting order. -/
  makerOwner : Nat
  /-- The owner of the incoming order. -/
  takerOwner : Nat
  /-- The execution price. -/
  px : Nat
  /-- The executed quantity. -/
  qty : Nat
  deriving DecidableEq, Repr

/-- Self-trade prevention: what the engine does when an incoming order would trade with a
resting order of the same owner. -/
inductive Stp where
  /-- No prevention: orders of the same owner trade. -/
  | off
  /-- Cancel the resting order and continue matching (cancel oldest). -/
  | cancelResting
  /-- Cancel the rest of the incoming order and stop matching (cancel newest). -/
  | cancelIncoming
  deriving DecidableEq, Repr

/-- The resting order `r` and an incoming order of `owner` form a prevented self-trade. -/
def isSelf (stp : Stp) (owner : Nat) (r : Resting) : Bool := stp != .off && r.owner == owner

/-- A prevented self-trade: prevention is on and the owners agree. -/
theorem isSelf_iff {stp : Stp} {owner : Nat} {r : Resting} :
    isSelf stp owner r = true ↔ stp ≠ .off ∧ r.owner = owner := by
  simp [isSelf]

/-- The trade of `q` lots of the resting order `r` with an incoming order of `owner`, at the
resting price. -/
def toTrade (owner : Nat) (r : Resting) (q : Nat) : Trade := ⟨r.id, r.owner, owner, r.px, q⟩

/-- The outcome of matching an incoming order against one side of the book. -/
structure Result where
  /-- The trades, in execution order. -/
  trades : List Trade
  /-- The quantity of the incoming order left unexecuted. -/
  rest : Nat
  /-- The side matched against, after matching. -/
  book : List Resting
  /-- Resting orders cancelled by self-trade prevention. -/
  canceled : List Resting
  /-- The incoming order was cancelled by self-trade prevention. -/
  killed : Bool

/-- Match `q` lots of an incoming order of side `s`, owner `owner` and limit `limit` against the
other side `book`, best resting order first. The walk stops when the incoming order is filled,
when the best resting price no longer crosses the limit, or when self-trade prevention cancels
the incoming order. A resting order larger than the remaining quantity is partly filled and
stays at the front; otherwise it is filled in full and removed, and matching continues at the
next order, possibly at the next price level. -/
def matchOrder (s : Side) (stp : Stp) (owner limit : Nat) : Nat → List Resting → Result
  | q, [] => ⟨[], q, [], [], false⟩
  | q, r :: rs =>
    if q = 0 then ⟨[], 0, r :: rs, [], false⟩
    else if ¬ s.le limit r.px then ⟨[], q, r :: rs, [], false⟩
    else if isSelf stp owner r then
      if stp = .cancelIncoming then ⟨[], q, r :: rs, [], true⟩
      else
        let m := matchOrder s stp owner limit q rs
        { m with canceled := r :: m.canceled }
    else if q < r.qty then ⟨[toTrade owner r q], 0, { r with qty := r.qty - q } :: rs, [], false⟩
    else
      let m := matchOrder s stp owner limit (q - r.qty) rs
      { m with trades := toTrade owner r r.qty :: m.trades }

/-- Total open quantity of a list of resting orders. -/
def total (l : List Resting) : Nat := (l.map Resting.qty).sum

/-- Total quantity of a list of trades. -/
def traded (ts : List Trade) : Nat := (ts.map Trade.qty).sum

/-- No resting orders hold no quantity. -/
@[simp] theorem total_nil : total [] = 0 := rfl

/-- The total of `r :: l`. -/
@[simp] theorem total_cons (r : Resting) (l : List Resting) : total (r :: l) = r.qty + total l := by
  simp [total]

/-- The total of a concatenation. -/
@[simp] theorem total_append (l₁ l₂ : List Resting) : total (l₁ ++ l₂) = total l₁ + total l₂ := by
  simp [total]

/-- No trades trade nothing. -/
@[simp] theorem traded_nil : traded [] = 0 := rfl

/-- The quantity of `t :: ts`. -/
@[simp] theorem traded_cons (t : Trade) (ts : List Trade) : traded (t :: ts) = t.qty + traded ts := by
  simp [traded]

/-- The quantity of a concatenation. -/
@[simp] theorem traded_append (l₁ l₂ : List Trade) : traded (l₁ ++ l₂) = traded l₁ + traded l₂ := by
  simp [traded]

/-- The fields of `toTrade`. -/
@[simp] theorem toTrade_qty (owner : Nat) (r : Resting) (q : Nat) : (toTrade owner r q).qty = q := rfl

/-- The execution price of `toTrade` is the resting price. -/
@[simp] theorem toTrade_px (owner : Nat) (r : Resting) (q : Nat) : (toTrade owner r q).px = r.px := rfl

/-- The maker of `toTrade` is the resting order. -/
@[simp] theorem toTrade_maker (owner : Nat) (r : Resting) (q : Nat) : (toTrade owner r q).maker = r.id := rfl

/-- The maker owner of `toTrade` is the owner of the resting order. -/
@[simp] theorem toTrade_makerOwner (owner : Nat) (r : Resting) (q : Nat) :
    (toTrade owner r q).makerOwner = r.owner := rfl

/-- The taker owner of `toTrade` is the incoming owner. -/
@[simp] theorem toTrade_takerOwner (owner : Nat) (r : Resting) (q : Nat) :
    (toTrade owner r q).takerOwner = owner := rfl

section Match

variable {s : Side} {stp : Stp} {owner limit : Nat}

/-- Matching against the empty side trades nothing. -/
@[simp] theorem matchOrder_nil (q : Nat) :
    matchOrder s stp owner limit q [] = ⟨[], q, [], [], false⟩ := rfl

/-- The six cases of one matching step against the resting order `r` at the front: the incoming
order is filled; the price does not cross; self-trade prevention cancels the incoming order; it
cancels the resting order; the resting order is partly filled; it is filled in full. -/
theorem matchOrder_cons (q : Nat) (r : Resting) (rs : List Resting) :
    (q = 0 ∧ matchOrder s stp owner limit q (r :: rs) = ⟨[], 0, r :: rs, [], false⟩) ∨
    (q ≠ 0 ∧ ¬ s.le limit r.px ∧
      matchOrder s stp owner limit q (r :: rs) = ⟨[], q, r :: rs, [], false⟩) ∨
    (q ≠ 0 ∧ s.le limit r.px ∧ isSelf stp owner r = true ∧ stp = .cancelIncoming ∧
      matchOrder s stp owner limit q (r :: rs) = ⟨[], q, r :: rs, [], true⟩) ∨
    (q ≠ 0 ∧ s.le limit r.px ∧ isSelf stp owner r = true ∧ stp ≠ .cancelIncoming ∧
      matchOrder s stp owner limit q (r :: rs) =
        { matchOrder s stp owner limit q rs with
          canceled := r :: (matchOrder s stp owner limit q rs).canceled }) ∨
    (q ≠ 0 ∧ s.le limit r.px ∧ isSelf stp owner r = false ∧ q < r.qty ∧
      matchOrder s stp owner limit q (r :: rs) =
        ⟨[toTrade owner r q], 0, { r with qty := r.qty - q } :: rs, [], false⟩) ∨
    (q ≠ 0 ∧ s.le limit r.px ∧ isSelf stp owner r = false ∧ r.qty ≤ q ∧
      matchOrder s stp owner limit q (r :: rs) =
        { matchOrder s stp owner limit (q - r.qty) rs with
          trades := toTrade owner r r.qty :: (matchOrder s stp owner limit (q - r.qty) rs).trades }) := by
  by_cases hq : q = 0
  · exact Or.inl ⟨hq, by simp [matchOrder, hq]⟩
  refine Or.inr ?_
  by_cases hc : s.le limit r.px
  · refine Or.inr ?_
    cases hs : isSelf stp owner r with
    | true =>
      by_cases hi : stp = .cancelIncoming
      · exact Or.inl ⟨hq, hc, rfl, hi, by subst hi; simp [matchOrder, hq, hc, hs]⟩
      · exact Or.inr (Or.inl ⟨hq, hc, rfl, hi, by simp [matchOrder, hq, hc, hs, hi]⟩)
    | false =>
      refine Or.inr (Or.inr ?_)
      by_cases hl : q < r.qty
      · exact Or.inl ⟨hq, hc, rfl, hl, by simp [matchOrder, hq, hc, hs, hl]⟩
      · exact Or.inr ⟨hq, hc, rfl, by omega, by simp [matchOrder, hq, hc, hs, hl]⟩
  · exact Or.inl ⟨hq, hc, by simp [matchOrder, hq, hc]⟩

/-- Conservation on the incoming side: the traded quantity plus the unexecuted rest is the
incoming quantity. -/
theorem matchOrder_traded_add_rest (q : Nat) (book : List Resting) :
    traded (matchOrder s stp owner limit q book).trades + (matchOrder s stp owner limit q book).rest = q := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨hq, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, h, e⟩ <;>
      rw [e] <;> simp
    · exact hq.symm
    · exact ih q
    · have := ih (q - r.qty); omega

/-- Conservation on the resting side: the traded quantity, the quantity left on the side and the
quantity cancelled by self-trade prevention add up to the quantity the side held. -/
theorem matchOrder_traded_add_total (q : Nat) (book : List Resting) :
    traded (matchOrder s stp owner limit q book).trades + total (matchOrder s stp owner limit q book).book +
      total (matchOrder s stp owner limit q book).canceled = total book := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, h, e⟩ | ⟨_, _, _, h, e⟩ <;>
      rw [e] <;> simp
    · have := ih q; omega
    · omega
    · have := ih (q - r.qty); omega

/-- Every trade is at a price no worse than the incoming limit: a buy at or below its limit, a
sell at or above it. -/
theorem matchOrder_price (q : Nat) (book : List Resting) :
    ∀ t ∈ (matchOrder s stp owner limit q book).trades, Crosses s limit t.px := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, hc, _, _, e⟩ | ⟨_, hc, _, _, e⟩ | ⟨_, hc, _, _, e⟩ <;>
      rw [e] <;> simp
    · exact ih q
    · exact hc
    · exact ⟨hc, ih (q - r.qty)⟩

/-- Every trade is with an order of the book, at its price, for its owner, for at most its open
quantity, and with the incoming owner as taker. -/
theorem matchOrder_maker (q : Nat) (book : List Resting) :
    ∀ t ∈ (matchOrder s stp owner limit q book).trades,
      ∃ r ∈ book, t = toTrade owner r t.qty ∧ t.qty ≤ r.qty := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, h, e⟩ | ⟨_, _, _, _, e⟩ <;>
      rw [e]
    · simp
    · simp
    · simp
    · intro t ht
      obtain ⟨r', hr', h'⟩ := ih q t ht
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact ⟨r, List.mem_cons_self, rfl, by simp; omega⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨r, List.mem_cons_self, rfl, Nat.le_refl _⟩
      · obtain ⟨r', hr', h'⟩ := ih (q - r.qty) t ht
        exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

/-- No self-trade: with self-trade prevention on, no trade has the same owner as maker and
taker. -/
theorem matchOrder_no_self_trade (hstp : stp ≠ .off) (q : Nat) (book : List Resting) :
    ∀ t ∈ (matchOrder s stp owner limit q book).trades, t.makerOwner ≠ t.takerOwner := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    have hown : isSelf stp owner r = false → r.owner ≠ owner := by
      intro h e
      have : isSelf stp owner r = true := isSelf_iff.2 ⟨hstp, e⟩
      rw [h] at this; cases this
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, hs, _, e⟩ | ⟨_, _, hs, _, e⟩ <;>
      rw [e] <;> simp
    · exact ih q
    · exact hown hs
    · exact ⟨hown hs, ih (q - r.qty)⟩

/-- With every resting order holding a positive quantity, every trade has a positive quantity. -/
theorem matchOrder_qty_pos (q : Nat) {book : List Resting} (hlive : ∀ r ∈ book, 0 < r.qty) :
    ∀ t ∈ (matchOrder s stp owner limit q book).trades, 0 < t.qty := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    have hr := hlive r List.mem_cons_self
    have hrs : ∀ r ∈ rs, 0 < r.qty := fun r' h => hlive r' (List.mem_cons_of_mem _ h)
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨hq, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ <;>
      rw [e] <;> simp
    · exact ih q hrs
    · omega
    · exact ⟨hr, ih (q - r.qty) hrs⟩

/-- Every order left on the side after matching is an order of the side before, with the same
identifier, owner and price and at most its quantity. -/
theorem matchOrder_book_mem (q : Nat) (book : List Resting) :
    ∀ y ∈ (matchOrder s stp owner limit q book).book,
      ∃ y' ∈ book, y.id = y'.id ∧ y.owner = y'.owner ∧ y.px = y'.px ∧ y.qty ≤ y'.qty := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    have hself : ∀ y ∈ r :: rs, ∃ y' ∈ r :: rs, y.id = y'.id ∧ y.owner = y'.owner ∧ y.px = y'.px ∧
        y.qty ≤ y'.qty := fun y hy => ⟨y, hy, rfl, rfl, rfl, Nat.le_refl _⟩
    have hsub : ∀ q', ∀ y ∈ (matchOrder s stp owner limit q' rs).book,
        ∃ y' ∈ r :: rs, y.id = y'.id ∧ y.owner = y'.owner ∧ y.px = y'.px ∧ y.qty ≤ y'.qty := by
      intro q' y hy
      obtain ⟨y', h1, h2⟩ := ih q' y hy
      exact ⟨y', List.mem_cons_of_mem _ h1, h2⟩
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ <;>
      rw [e]
    · exact hself
    · exact hself
    · exact hself
    · exact hsub q
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨r, List.mem_cons_self, rfl, rfl, rfl, Nat.sub_le _ _⟩
      · exact hself y (List.mem_cons_of_mem _ hy)
    · exact hsub (q - r.qty)

/-- The orders cancelled by self-trade prevention are orders of the side. -/
theorem matchOrder_canceled_mem (q : Nat) (book : List Resting) :
    ∀ y ∈ (matchOrder s stp owner limit q book).canceled, y ∈ book := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ <;>
      rw [e] <;> simp
    · intro y hy; exact Or.inr (ih q y hy)
    · intro y hy; exact Or.inr (ih (q - r.qty) y hy)

/-- Matching keeps the side it walks in priority order. -/
theorem matchOrder_sorted (q : Nat) {book : List Resting} (h : Sorted s.opp Resting.px book) :
    Sorted s.opp Resting.px (matchOrder s stp owner limit q book).book := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ <;>
      rw [e]
    · exact h
    · exact h
    · exact h
    · exact ih q h.tail
    · exact sorted_cons.2 ⟨h.head_le, h.tail⟩
    · exact ih (q - r.qty) h.tail

/-- Matching keeps every order left on the side at a positive quantity. -/
theorem matchOrder_live (q : Nat) {book : List Resting} (h : ∀ r ∈ book, 0 < r.qty) :
    ∀ y ∈ (matchOrder s stp owner limit q book).book, 0 < y.qty := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    have hrs : ∀ r ∈ rs, 0 < r.qty := fun r' h' => h r' (List.mem_cons_of_mem _ h')
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, hl, e⟩ | ⟨_, _, _, _, e⟩ <;>
      rw [e]
    · exact h
    · exact h
    · exact h
    · exact ih q hrs
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · simp; omega
      · exact hrs y hy
    · exact ih (q - r.qty) hrs

/-- Why matching stopped with quantity left: when the incoming order has an unexecuted rest and
was not cancelled, no order left on the (sorted) side crosses its limit. -/
theorem matchOrder_stop (q : Nat) {book : List Resting} (h : Sorted s.opp Resting.px book)
    (hrest : 0 < (matchOrder s stp owner limit q book).rest)
    (hkill : (matchOrder s stp owner limit q book).killed = false) :
    ∀ y ∈ (matchOrder s stp owner limit q book).book, ¬ Crosses s limit y.px := by
  induction book generalizing q with
  | nil => simp
  | cons r rs ih =>
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, hc, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ <;>
      rw [e] at hrest hkill ⊢
    · simp at hrest
    · intro y hy hy'
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hc hy'
      · exact hc (Side.le_trans hy' (Side.le_opp.1 (h.head_le y hy)))
    · simp at hkill
    · exact ih q h.tail hrest hkill
    · simp at hrest
    · exact ih (q - r.qty) h.tail hrest hkill

/-- The trades that fill each order of `l` in full, in order. -/
def fullTrades (owner : Nat) (l : List Resting) : List Trade := l.map (fun r => toTrade owner r r.qty)

/-- The shape of a match (price-time priority): the side splits into a consumed prefix `pre` and
the rest `post`. The orders of `pre` that are prevented self-trades are exactly the cancelled
ones; every other order of `pre` is filled in full, in book order; then either nothing else
trades and `post` is left, or the first order of `post` is partly filled by `k` lots and stays at
the front with the rest of its quantity. -/
theorem matchOrder_shape (q : Nat) (book : List Resting) :
    ∃ pre post, book = pre ++ post ∧
      (matchOrder s stp owner limit q book).canceled = pre.filter (isSelf stp owner) ∧
      (((matchOrder s stp owner limit q book).book = post ∧
          (matchOrder s stp owner limit q book).trades =
            fullTrades owner (pre.filter (fun r => !isSelf stp owner r))) ∨
        ∃ r rs k, post = r :: rs ∧ 0 < k ∧ k < r.qty ∧
          (matchOrder s stp owner limit q book).book = { r with qty := r.qty - k } :: rs ∧
          (matchOrder s stp owner limit q book).trades =
            fullTrades owner (pre.filter (fun r => !isSelf stp owner r)) ++ [toTrade owner r k]) := by
  induction book generalizing q with
  | nil => exact ⟨[], [], rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | cons r rs ih =>
    rcases matchOrder_cons (s := s) (stp := stp) (owner := owner) (limit := limit) q r rs with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, hs, _, e⟩ | ⟨hq, _, _, hl, e⟩ | ⟨_, _, hs, _, e⟩ <;>
      rw [e]
    · exact ⟨[], r :: rs, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨[], r :: rs, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨[], r :: rs, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨pre, post, h1, h2, h3⟩ := ih q
      refine ⟨r :: pre, post, by rw [h1]; rfl, ?_, ?_⟩
      · simp [hs, h2]
      · simpa [hs] using h3
    · exact ⟨[], r :: rs, rfl, rfl, Or.inr ⟨r, rs, q, rfl, by omega, hl, rfl, rfl⟩⟩
    · obtain ⟨pre, post, h1, h2, h3⟩ := ih (q - r.qty)
      refine ⟨r :: pre, post, by rw [h1]; rfl, ?_, ?_⟩
      · simp [hs, h2]
      · rcases h3 with ⟨h3, h4⟩ | ⟨r', rs', k, h3, h4, h5, h6, h7⟩
        · exact Or.inl ⟨h3, by simp [hs, h4, fullTrades]⟩
        · exact Or.inr ⟨r', rs', k, h3, h4, h5, h6, by simp [hs, h7, fullTrades]⟩

/-- In a list with distinct identifiers, an order whose identifier is found in a prefix `pre`
(or at the front of the rest) has everything ahead of it inside `pre`. -/
theorem ahead_subset {l₁ l₂ pre post : List Resting} {r r' : Resting}
    (hnd : ((pre ++ post).map Resting.id).Nodup) (he : pre ++ post = l₁ ++ r :: l₂)
    (hr' : r' ∈ pre ∨ post.head? = some r') (hid : r'.id = r.id) : ∀ y ∈ l₁, y ∈ pre := by
  induction l₁ generalizing pre with
  | nil => simp
  | cons a l₁ ih =>
    rw [List.cons_append] at he
    have hclash : ∀ {t : List Resting}, ((a :: t).map Resting.id).Nodup → r ∈ t → a.id ≠ r.id := by
      intro t hn hr e
      rw [List.map_cons, List.nodup_cons] at hn
      exact hn.1 (e ▸ List.mem_map_of_mem hr)
    cases pre with
    | nil =>
      simp only [List.nil_append] at he hnd
      subst he
      simp only [List.not_mem_nil, false_or, List.head?_cons, Option.some.injEq] at hr'
      subst hr'
      exact absurd hid (hclash hnd (by simp))
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      rw [List.cons_append] at hnd
      have hp : r' ≠ p := by
        intro e; subst e
        exact hclash hnd (by rw [he]; simp) hid
      have hr'' : r' ∈ pre ∨ post.head? = some r' := by
        rcases hr' with h | h
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h hp
          · exact Or.inl h
        · exact Or.inr h
      have hnd' : ((pre ++ post).map Resting.id).Nodup := by
        rw [List.map_cons, List.nodup_cons] at hnd; exact hnd.2
      have := ih hnd' he hr''
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (this y hy)

/-- Price-time priority. In a side with distinct order identifiers, if an order `r` trades, every
order ahead of it (at a better price, or at the same price and earlier) has left the book: it was
filled in full or cancelled by self-trade prevention. -/
theorem matchOrder_priority (q : Nat) {book l₁ l₂ : List Resting} {r : Resting}
    (hnd : (book.map Resting.id).Nodup) (hb : book = l₁ ++ r :: l₂)
    (ht : ∃ t ∈ (matchOrder s stp owner limit q book).trades, t.maker = r.id) :
    ∀ y ∈ l₁, y ∈ (matchOrder s stp owner limit q book).canceled ∨
      toTrade owner y y.qty ∈ (matchOrder s stp owner limit q book).trades := by
  obtain ⟨pre, post, h1, h2, h3⟩ := matchOrder_shape (s := s) (stp := stp) (owner := owner)
    (limit := limit) q book
  obtain ⟨t, ht, htm⟩ := ht
  have hfull : ∀ t ∈ fullTrades owner (pre.filter (fun r => !isSelf stp owner r)),
      ∃ r' ∈ pre, t.maker = r'.id := by
    intro t ht
    simp only [fullTrades, List.mem_map, List.mem_filter] at ht
    obtain ⟨r', ⟨hr', _⟩, rfl⟩ := ht
    exact ⟨r', hr', rfl⟩
  have hpos : ∃ r', (r' ∈ pre ∨ post.head? = some r') ∧ r'.id = r.id := by
    rcases h3 with ⟨_, h4⟩ | ⟨r₀, rs, k, h4, _, _, _, h7⟩
    · rw [h4] at ht
      obtain ⟨r', hr', e⟩ := hfull t ht
      exact ⟨r', Or.inl hr', e ▸ htm⟩
    · rw [h7, List.mem_append] at ht
      rcases ht with ht | ht
      · obtain ⟨r', hr', e⟩ := hfull t ht
        exact ⟨r', Or.inl hr', e ▸ htm⟩
      · rw [List.mem_singleton] at ht
        subst ht
        exact ⟨r₀, Or.inr (by rw [h4]; rfl), htm⟩
  obtain ⟨r', hr', hid⟩ := hpos
  have hsub := ahead_subset (h1 ▸ hnd) (h1 ▸ hb) hr' hid
  have hfulls : fullTrades owner (pre.filter (fun r => !isSelf stp owner r)) ⊆
      (matchOrder s stp owner limit q book).trades := by
    rcases h3 with ⟨_, h4⟩ | ⟨_, _, _, _, _, _, _, h7⟩
    · rw [h4]; exact List.Subset.refl _
    · rw [h7]; exact List.subset_append_left _ _
  intro y hy
  have hyp := hsub y hy
  cases hs : isSelf stp owner y with
  | true => exact Or.inl (by rw [h2, List.mem_filter]; exact ⟨hyp, hs⟩)
  | false =>
    refine Or.inr (hfulls ?_)
    simp only [fullTrades, List.mem_map, List.mem_filter]
    exact ⟨y, ⟨hyp, by simp [hs]⟩, rfl⟩

end Match

/-! ## The book -/

/-- A limit order book: the bids and the asks, each in priority order. -/
structure Book where
  /-- Resting buy orders, best (highest) price first. -/
  bids : List Resting
  /-- Resting sell orders, best (lowest) price first. -/
  asks : List Resting

/-- The resting orders of one side. -/
def Book.side (b : Book) : Side → List Resting
  | .buy => b.bids
  | .sell => b.asks

/-- The book with `own` as the orders of side `s` and `opp` as the orders of the other side. -/
def Book.ofSides : Side → List Resting → List Resting → Book
  | .buy, own, opp => ⟨own, opp⟩
  | .sell, own, opp => ⟨opp, own⟩

/-- The side `s` of `ofSides s own opp`. -/
@[simp] theorem Book.side_ofSides_self (s : Side) (own opp : List Resting) :
    (Book.ofSides s own opp).side s = own := by cases s <;> rfl

/-- The other side of `ofSides s own opp`. -/
@[simp] theorem Book.side_ofSides_opp (s : Side) (own opp : List Resting) :
    (Book.ofSides s own opp).side s.opp = opp := by cases s <;> rfl

/-- The empty book. -/
def Book.empty : Book := ⟨[], []⟩

/-- An incoming limit order. -/
structure Incoming where
  /-- The order identifier, used if the order rests. -/
  id : Nat
  /-- The owning account or trading group. -/
  owner : Nat
  /-- Buy or sell. -/
  side : Side
  /-- The limit price. -/
  limit : Nat
  /-- The quantity. -/
  qty : Nat
  /-- Immediate or cancel: an unexecuted rest is cancelled instead of resting. -/
  ioc : Bool

/-- The order that rests for an incoming order with unexecuted quantity `rest`. -/
def Incoming.toResting (o : Incoming) (rest : Nat) : Resting := ⟨o.id, o.owner, o.limit, rest⟩

/-- The match of an incoming order against the other side of the book. -/
def matchIncoming (stp : Stp) (b : Book) (o : Incoming) : Result :=
  matchOrder o.side stp o.owner o.limit o.qty (b.side o.side.opp)

/-- The rest of an incoming order rests when quantity is left, the order is not
immediate-or-cancel, and self-trade prevention did not cancel it. -/
def Rests (o : Incoming) (m : Result) : Prop := 0 < m.rest ∧ o.ioc = false ∧ m.killed = false

/-- Whether the remainder rests is decidable. -/
instance (o : Incoming) (m : Result) : Decidable (Rests o m) := by unfold Rests; infer_instance

/-- Submit an incoming order: match it against the other side, then rest its remainder on its
own side with time priority when it rests. Returns the new book and the trades. -/
def submit (stp : Stp) (b : Book) (o : Incoming) : Book × List Trade :=
  let m := matchIncoming stp b o
  (Book.ofSides o.side
    (if Rests o m then insertBy o.side Resting.px (o.toResting m.rest) (b.side o.side)
      else b.side o.side) m.book,
   m.trades)

/-- Cancel the resting order with identifier `id`, on either side. -/
def cancel (b : Book) (id : Nat) : Book :=
  ⟨b.bids.filter (fun r => r.id != id), b.asks.filter (fun r => r.id != id)⟩

/-- Book operations. -/
inductive Op where
  /-- Submit an incoming order. -/
  | submit (o : Incoming)
  /-- Cancel a resting order by identifier. -/
  | cancel (id : Nat)

/-- One book operation, discarding the trades. -/
def step (stp : Stp) (b : Book) : Op → Book
  | .submit o => (submit stp b o).1
  | .cancel id => cancel b id

/-- The book is uncrossed: every bid is strictly below every ask. -/
def Uncrossed (b : Book) : Prop := ∀ x ∈ b.bids, ∀ y ∈ b.asks, x.px < y.px

/-- A well-formed book: both sides in priority order, every resting order with a positive
quantity, and the book uncrossed. -/
structure Wf (b : Book) : Prop where
  /-- Each side is in priority order. -/
  sorted : ∀ s, Sorted s Resting.px (b.side s)
  /-- Every resting order has a positive quantity. -/
  live : ∀ s, ∀ r ∈ b.side s, 0 < r.qty
  /-- Every bid is below every ask. -/
  uncrossed : Uncrossed b

/-- Every side is `s` or `s.opp`. -/
theorem side_eq_or_opp (s t : Side) : t = s ∨ t = s.opp := by cases s <;> cases t <;> simp

/-- Uncrossed, seen from either side: no order of side `s` crosses an order of the other side. -/
theorem uncrossed_iff (b : Book) (s : Side) :
    Uncrossed b ↔ ∀ x ∈ b.side s, ∀ y ∈ b.side s.opp, ¬ Crosses s x.px y.px := by
  cases s
  · simp [Uncrossed, Book.side]
  · simp only [Uncrossed, Book.side, Side.opp_sell, Crosses, Side.le_sell, Nat.not_le]
    exact ⟨fun h x hx y hy => h y hy x hx, fun h x hx y hy => h y hy x hx⟩

/-- The empty book is well formed. -/
theorem wf_empty : Wf Book.empty :=
  ⟨fun s => by cases s <;> simp [Book.empty, Book.side], fun s => by cases s <;> simp [Book.empty, Book.side],
    by simp [Uncrossed, Book.empty]⟩

/-- Submitting an order keeps the book sorted on both sides, live and uncrossed. -/
theorem Wf.submit {stp : Stp} {b : Book} (h : Wf b) (o : Incoming) : Wf (submit stp b o).1 := by
  have hopp := h.sorted o.side.opp
  have hstop := matchOrder_stop (s := o.side) (stp := stp) (owner := o.owner) (limit := o.limit) o.qty hopp
  have hmem := matchOrder_book_mem (s := o.side) (stp := stp) (owner := o.owner) (limit := o.limit)
    o.qty (b.side o.side.opp)
  simp only [Trading.Book.submit]
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rcases side_eq_or_opp o.side t with rfl | rfl
    · rw [Book.side_ofSides_self]
      split
      · exact sorted_insertBy _ (h.sorted _)
      · exact h.sorted _
    · rw [Book.side_ofSides_opp]
      exact matchOrder_sorted _ hopp
  · intro t
    rcases side_eq_or_opp o.side t with rfl | rfl
    · rw [Book.side_ofSides_self]
      split
      · rename_i hr
        intro r hr'
        rcases mem_insertBy.1 hr' with rfl | hr'
        · exact hr.1
        · exact h.live _ r hr'
      · exact h.live _
    · rw [Book.side_ofSides_opp]
      exact matchOrder_live _ (h.live _)
  · rw [uncrossed_iff _ o.side, Book.side_ofSides_self, Book.side_ofSides_opp]
    have hold := (uncrossed_iff b o.side).1 h.uncrossed
    intro x hx y hy
    obtain ⟨y', hy', _, _, hpx, _⟩ := hmem y hy
    split at hx
    · rename_i hr
      rcases mem_insertBy.1 hx with rfl | hx
      · exact hstop hr.1 hr.2.2 y hy
      · rw [hpx]; exact hold x hx y' hy'
    · rw [hpx]; exact hold x hx y' hy'

/-- Cancelling an order keeps the book sorted on both sides, live and uncrossed. -/
theorem Wf.cancel {b : Book} (h : Wf b) (id : Nat) : Wf (cancel b id) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    cases s
    · exact (h.sorted .buy).filter _
    · exact (h.sorted .sell).filter _
  · intro s
    cases s
    · intro r hr; exact h.live .buy r (List.mem_filter.1 hr).1
    · intro r hr; exact h.live .sell r (List.mem_filter.1 hr).1
  · intro x hx y hy
    exact h.uncrossed x (List.mem_filter.1 hx).1 y (List.mem_filter.1 hy).1

/-- Every book operation keeps the book well formed. -/
theorem wf_step (stp : Stp) : Seq.Preserves (step stp) Wf := by
  intro b op h
  cases op with
  | submit o => exact h.submit o
  | cancel id => exact h.cancel id

/-- Over any sequence of submits and cancels from a well-formed book (for example the empty
book), both sides stay in priority order with positive quantities and the book stays
uncrossed. -/
theorem wf_run (stp : Stp) {b : Book} (h : Wf b) (ops : List Op) : Wf (Seq.run (step stp) b ops) :=
  Seq.run_invariant (wf_step stp) h ops

/-- Every trade of a submission is at a price no worse than the order's limit. -/
theorem submit_price (stp : Stp) (b : Book) (o : Incoming) :
    ∀ t ∈ (submit stp b o).2, Crosses o.side o.limit t.px :=
  matchOrder_price _ _

/-- With self-trade prevention on, no trade of a submission has the same owner on both sides. -/
theorem submit_no_self_trade {stp : Stp} (hstp : stp ≠ .off) (b : Book) (o : Incoming) :
    ∀ t ∈ (submit stp b o).2, t.makerOwner ≠ t.takerOwner :=
  matchOrder_no_self_trade hstp _ _

/-- A submission trades at most the order's quantity. -/
theorem submit_traded_le (stp : Stp) (b : Book) (o : Incoming) : traded (submit stp b o).2 ≤ o.qty := by
  have := matchOrder_traded_add_rest (s := o.side) (stp := stp) (owner := o.owner) (limit := o.limit)
    o.qty (b.side o.side.opp)
  simp only [Trading.Book.submit, matchIncoming]
  omega

/-- The quantity a submission trades leaves the other side: what the other side holds after,
plus what traded, plus what self-trade prevention cancelled, is what it held before. -/
theorem submit_conserves (stp : Stp) (b : Book) (o : Incoming) :
    traded (submit stp b o).2 + total ((submit stp b o).1.side o.side.opp) +
      total (matchIncoming stp b o).canceled = total (b.side o.side.opp) := by
  simp only [Trading.Book.submit, Book.side_ofSides_opp]
  exact matchOrder_traded_add_total _ _

end ProofForgeFin.Trading.Book
