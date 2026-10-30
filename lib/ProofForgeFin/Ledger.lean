import ProofForgeFin.Seq
/-!
# Conservation over accounts

Ledgers keep balances per account and requirements say that money is neither created nor
destroyed: a transfer moves an amount, a batch of transfers leaves the total unchanged, the
shares held by all holders add up to the supply. This module covers the three representations
task specifications use:

* balances as a function `κ → Int` summed over a list of accounts with `sumOver` (signed ledgers
  with overdrafts), updated with `adjust` and `transfer`;
* balances as a function `κ → Nat` summed with `(l.map f).sum` and updated with `upd` (share
  balances, with `SupplyMatches` stating that they add up to the supply);
* accounts as a `List` indexed by position, updated with `List.modify` and read with
  `List.getD` (the representation of the Compound task).

Sums over a list count an account once per occurrence, so the conservation theorems for
functions assume the account list has no duplicates (`List.Nodup`).
-/

namespace ProofForgeFin.Ledger

universe u v

variable {κ : Type u}

/-! ## Sums of integer balances -/

/-- Sum of an integer-valued function over a list, as a right fold. -/
def sumOver {α : Type v} (l : List α) (f : α → Int) : Int := l.foldr (fun a acc => f a + acc) 0

/-- The sum over no accounts is zero. -/
@[simp] theorem sumOver_nil {α : Type v} (f : α → Int) : sumOver [] f = 0 := rfl

/-- The sum over `a :: l` is `f a` plus the sum over `l`. -/
@[simp] theorem sumOver_cons {α : Type v} (a : α) (l : List α) (f : α → Int) :
    sumOver (a :: l) f = f a + sumOver l f := rfl

/-- `sumOver` is the sum of the mapped list. -/
theorem sumOver_eq_sum_map {α : Type v} (l : List α) (f : α → Int) : sumOver l f = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The sum over a concatenation. -/
theorem sumOver_append {α : Type v} (l₁ l₂ : List α) (f : α → Int) :
    sumOver (l₁ ++ l₂) f = sumOver l₁ f + sumOver l₂ f := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih]; omega

/-- The sum of a pointwise sum. -/
theorem sumOver_add {α : Type v} (l : List α) (f g : α → Int) :
    sumOver l (fun a => f a + g a) = sumOver l f + sumOver l g := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

/-- The sum of a pointwise difference. -/
theorem sumOver_sub {α : Type v} (l : List α) (f g : α → Int) :
    sumOver l (fun a => f a - g a) = sumOver l f - sumOver l g := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

/-- Sums agree when the functions agree on the list. -/
theorem sumOver_congr {α : Type v} (l : List α) {f g : α → Int} (h : ∀ a ∈ l, f a = g a) :
    sumOver l f = sumOver l g := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [sumOver_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- The sum of zero is zero. -/
@[simp] theorem sumOver_zero {α : Type v} (l : List α) : sumOver l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Summing an indicator over a duplicate-free list: `c` if the account is in the list, else 0. -/
theorem sumOver_ite_eq [DecidableEq κ] {l : List κ} (hl : l.Nodup) (x : κ) (c : Int) :
    sumOver l (fun a => if a = x then c else 0) = if x ∈ l then c else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [sumOver_cons, ih hl.2, List.mem_cons]
    by_cases hax : a = x
    · subst hax; simp [hl.1]
    · have : x ≠ a := fun h => hax h.symm
      simp [hax, this]

/-- Pointwise bounds give a bound on the sum. -/
theorem sumOver_le_sumOver {α : Type v} (l : List α) {f g : α → Int} (h : ∀ a ∈ l, f a ≤ g a) :
    sumOver l f ≤ sumOver l g := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [sumOver_cons]
    have := h a (by simp)
    have := ih (fun b hb => h b (by simp [hb]))
    omega

/-! ## Updating integer balances -/

/-- `bal` with `d` added to the balance of account `k`. -/
def adjust [DecidableEq κ] (bal : κ → Int) (k : κ) (d : Int) : κ → Int :=
  fun j => if j = k then bal j + d else bal j

/-- `bal` after moving `x` from `src` to `dst` (with no validity check; `src = dst` leaves every
balance unchanged). -/
def transfer [DecidableEq κ] (bal : κ → Int) (src dst : κ) (x : Int) : κ → Int :=
  fun j => bal j - (if j = src then x else 0) + (if j = dst then x else 0)

/-- The adjusted account. -/
@[simp] theorem adjust_self [DecidableEq κ] (bal : κ → Int) (k : κ) (d : Int) :
    adjust bal k d k = bal k + d := by simp [adjust]

/-- Every other account is unchanged. -/
theorem adjust_ne [DecidableEq κ] (bal : κ → Int) {k j : κ} (d : Int) (h : j ≠ k) :
    adjust bal k d j = bal j := by simp [adjust, h]

/-- Adjusting one account of a duplicate-free list changes the total by the adjustment. -/
theorem sumOver_adjust [DecidableEq κ] {l : List κ} (hl : l.Nodup) (bal : κ → Int) (k : κ)
    (d : Int) : sumOver l (adjust bal k d) = sumOver l bal + (if k ∈ l then d else 0) := by
  have : adjust bal k d = fun j => bal j + (if j = k then d else 0) := by
    funext j; unfold adjust; split <;> simp
  rw [this, sumOver_add, sumOver_ite_eq hl]

/-- The source of a transfer between two different accounts loses the amount. -/
theorem transfer_src [DecidableEq κ] (bal : κ → Int) {src dst : κ} (x : Int) (h : src ≠ dst) :
    transfer bal src dst x src = bal src - x := by simp [transfer, h]

/-- The destination of a transfer between two different accounts gains the amount. -/
theorem transfer_dst [DecidableEq κ] (bal : κ → Int) {src dst : κ} (x : Int) (h : src ≠ dst) :
    transfer bal src dst x dst = bal dst + x := by simp [transfer, Ne.symm h]

/-- A transfer leaves every other account unchanged. -/
theorem transfer_other [DecidableEq κ] (bal : κ → Int) {src dst j : κ} (x : Int) (hs : j ≠ src)
    (hd : j ≠ dst) : transfer bal src dst x j = bal j := by simp [transfer, hs, hd]

/-- The total after a transfer over a duplicate-free list: the amount leaves if the source is in
the list and arrives if the destination is. -/
theorem sumOver_transfer' [DecidableEq κ] {l : List κ} (hl : l.Nodup) (bal : κ → Int)
    (src dst : κ) (x : Int) :
    sumOver l (transfer bal src dst x) =
      sumOver l bal - (if src ∈ l then x else 0) + (if dst ∈ l then x else 0) := by
  unfold transfer
  rw [sumOver_add, sumOver_sub, sumOver_ite_eq hl, sumOver_ite_eq hl]

/-- Conservation: a transfer between two accounts of a duplicate-free list leaves the total
unchanged. -/
theorem sumOver_transfer [DecidableEq κ] {l : List κ} (hl : l.Nodup) (bal : κ → Int)
    {src dst : κ} (x : Int) (hs : src ∈ l) (hd : dst ∈ l) :
    sumOver l (transfer bal src dst x) = sumOver l bal := by
  rw [sumOver_transfer' hl]; simp [hs, hd]

/-- A transfer order: source, destination and amount. -/
structure Move (κ : Type u) where
  /-- The account debited. -/
  src : κ
  /-- The account credited. -/
  dst : κ
  /-- The amount moved. -/
  amount : Int

/-- Balances after applying the transfers of a list in order. -/
def applyMoves [DecidableEq κ] (bal : κ → Int) (ms : List (Move κ)) : κ → Int :=
  Seq.run (fun b m => transfer b m.src m.dst m.amount) bal ms

/-- Conservation over a batch: transfers between accounts of a duplicate-free list, applied in
order, leave the total unchanged. -/
theorem sumOver_applyMoves [DecidableEq κ] {l : List κ} (hl : l.Nodup) (bal : κ → Int)
    {ms : List (Move κ)} (h : ∀ m ∈ ms, m.src ∈ l ∧ m.dst ∈ l) :
    sumOver l (applyMoves bal ms) = sumOver l bal :=
  Seq.run_eq_of_mem (fun b => sumOver l b)
    (fun b m hm => sumOver_transfer hl b m.amount (h m hm).1 (h m hm).2) bal

/-- Accounts named by no transfer of a batch keep their balance. -/
theorem applyMoves_other [DecidableEq κ] (bal : κ → Int) {ms : List (Move κ)} {j : κ}
    (h : ∀ m ∈ ms, j ≠ m.src ∧ j ≠ m.dst) : applyMoves bal ms j = bal j :=
  Seq.run_eq_of_mem (fun b => b j)
    (fun b m hm => transfer_other b m.amount (h m hm).1 (h m hm).2) bal

/-! ## Sums of natural-number balances -/

/-- `f` with the value at `k` replaced by `v`. -/
def upd {β : Type v} [DecidableEq κ] (f : κ → β) (k : κ) (v : β) : κ → β :=
  fun j => if j = k then v else f j

/-- The updated position reads the new value. -/
@[simp] theorem upd_self {β : Type v} [DecidableEq κ] (f : κ → β) (k : κ) (v : β) :
    upd f k v k = v := by simp [upd]

/-- Other positions are unchanged. -/
theorem upd_ne {β : Type v} [DecidableEq κ] (f : κ → β) {k j : κ} (v : β) (h : j ≠ k) :
    upd f k v j = f j := by simp [upd, h]

/-- An account's balance is at most the total over any list that contains it. -/
theorem le_sum_map {α : Type v} {l : List α} (f : α → Nat) {a : α} (h : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; omega
    · have := ih h; omega

/-- Pointwise bounds give a bound on the sum. -/
theorem sum_map_le_sum_map {α : Type v} (l : List α) {f g : α → Nat} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp)
    have := ih (fun b hb => h b (by simp [hb]))
    omega

/-- Sums agree when the functions agree on the list. -/
theorem sum_map_congr {α : Type v} (l : List α) {f g : α → Nat} (h : ∀ a ∈ l, f a = g a) :
    (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

/-- Updating one account of a duplicate-free list: the new total plus the old value is the old
total plus the new value. -/
theorem sum_map_upd [DecidableEq κ] {l : List κ} (hl : l.Nodup) (f : κ → Nat) {k : κ} (v : Nat)
    (hk : k ∈ l) : (l.map (upd f k v)).sum + f k = (l.map f).sum + v := by
  induction l with
  | nil => simp at hk
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons]
    by_cases hak : a = k
    · subst hak
      have : (l.map (upd f a v)).sum = (l.map f).sum :=
        sum_map_congr l (fun b hb => upd_ne f v (fun e => hl.1 (e ▸ hb)))
      simp only [upd_self, this]; omega
    · have hk' : k ∈ l := by
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h.symm hak
        · exact h
      have := ih hl.2 hk'
      rw [upd_ne f v hak]; omega

/-- Updating an account outside the list leaves the total unchanged. -/
theorem sum_map_upd_of_not_mem [DecidableEq κ] {l : List κ} (f : κ → Nat) {k : κ} (v : Nat)
    (hk : k ∉ l) : (l.map (upd f k v)).sum = (l.map f).sum :=
  sum_map_congr l (fun _ hb => upd_ne f v (fun e => hk (e ▸ hb)))

/-! ## Share balances and the supply -/

/-- The shares held by the accounts of `holders` add up to `supply`. -/
def SupplyMatches (holders : List κ) (bal : κ → Nat) (supply : Nat) : Prop :=
  (holders.map bal).sum = supply

/-- With the supply matching, a holder holds at most the supply. -/
theorem SupplyMatches.balance_le {holders : List κ} {bal : κ → Nat} {supply : Nat}
    (h : SupplyMatches holders bal supply) {k : κ} (hk : k ∈ holders) : bal k ≤ supply :=
  h ▸ le_sum_map bal hk

/-- Minting `t` shares to a holder raises the supply by `t`. -/
theorem SupplyMatches.mint [DecidableEq κ] {holders : List κ} {bal : κ → Nat} {supply : Nat}
    (hl : holders.Nodup) (h : SupplyMatches holders bal supply) {k : κ} (hk : k ∈ holders)
    (t : Nat) : SupplyMatches holders (upd bal k (bal k + t)) (supply + t) := by
  unfold SupplyMatches at *
  have := sum_map_upd hl bal (bal k + t) hk
  omega

/-- Burning `t ≤ bal k` shares of a holder lowers the supply by `t`. -/
theorem SupplyMatches.burn [DecidableEq κ] {holders : List κ} {bal : κ → Nat} {supply : Nat}
    (hl : holders.Nodup) (h : SupplyMatches holders bal supply) {k : κ} (hk : k ∈ holders)
    {t : Nat} (ht : t ≤ bal k) : SupplyMatches holders (upd bal k (bal k - t)) (supply - t) := by
  unfold SupplyMatches at *
  have := sum_map_upd hl bal (bal k - t) hk
  omega

/-- Moving `x ≤ bal src` shares between two different holders leaves the supply unchanged. -/
theorem SupplyMatches.move [DecidableEq κ] {holders : List κ} {bal : κ → Nat} {supply : Nat}
    (hl : holders.Nodup) (h : SupplyMatches holders bal supply) {src dst : κ}
    (hs : src ∈ holders) (hd : dst ∈ holders) (hne : src ≠ dst) {x : Nat} (hx : x ≤ bal src) :
    SupplyMatches holders (upd (upd bal src (bal src - x)) dst (bal dst + x)) supply := by
  unfold SupplyMatches at *
  have h1 := sum_map_upd hl bal (bal src - x) hs
  have h2 := sum_map_upd hl (upd bal src (bal src - x)) (bal dst + x) hd
  rw [upd_ne bal _ (Ne.symm hne)] at h2
  omega

/-! ## Splitting an amount -/

/-- The sum of `n` copies of `a`. -/
theorem sum_replicate (n a : Nat) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

/-- `a` split into `n` parts that differ by at most one unit: the first `a % n` parts are
`a / n + 1` and the others `a / n`. -/
def equalSplit (a n : Nat) : List Nat :=
  List.replicate (a % n) (a / n + 1) ++ List.replicate (n - a % n) (a / n)

/-- A split into `n > 0` parts has `n` parts. -/
theorem length_equalSplit (a : Nat) {n : Nat} (hn : 0 < n) : (equalSplit a n).length = n := by
  have := Nat.mod_lt a hn
  simp only [equalSplit, List.length_append, List.length_replicate]
  omega

/-- A split conserves the amount: the parts add up to exactly `a`. -/
theorem sum_equalSplit (a : Nat) {n : Nat} (hn : 0 < n) : (equalSplit a n).sum = a := by
  have h1 := Nat.mod_lt a hn
  have h2 := Nat.div_add_mod a n
  simp only [equalSplit, List.sum_append, sum_replicate]
  have h3 : a % n * (a / n) + (n - a % n) * (a / n) = n * (a / n) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt h1)]
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Every part is within one unit of the exact share `a / n`: `x * n < a + n` and
`a < x * n + n`. -/
theorem mem_equalSplit_bounds (a : Nat) {n x : Nat} (hn : 0 < n) (hx : x ∈ equalSplit a n) :
    x * n < a + n ∧ a < x * n + n := by
  have h1 := Nat.mod_lt a hn
  have h2 := Nat.div_add_mod a n
  rw [Nat.mul_comm n (a / n)] at h2
  simp only [equalSplit, List.mem_append, List.mem_replicate] at hx
  rcases hx with ⟨hr, rfl⟩ | ⟨_, rfl⟩
  · rw [Nat.add_mul, Nat.one_mul]; omega
  · omega

/-- Any two parts differ by at most one unit. -/
theorem equalSplit_le_add_one (a n : Nat) {x y : Nat} (hx : x ∈ equalSplit a n)
    (hy : y ∈ equalSplit a n) : x ≤ y + 1 := by
  simp only [equalSplit, List.mem_append, List.mem_replicate] at hx hy
  omega

/-! ## Accounts indexed by position -/

/-- Reading a list after modifying one position. -/
theorem getD_modify {α : Type v} (l : List α) (i j : Nat) (f : α → α) (d : α) :
    (l.modify i f).getD j d = if i = j ∧ j < l.length then f (l.getD j d) else l.getD j d := by
  induction l generalizing i j with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ j => simp
    | succ i =>
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.modify_succ_cons, List.getD_cons_succ, List.length_cons]
        rw [ih]
        by_cases h : i = j <;> simp [h]

/-- The modified position reads the modified value. -/
theorem getD_modify_self {α : Type v} (l : List α) (i : Nat) (f : α → α) (d : α) (h : i < l.length) :
    (l.modify i f).getD i d = f (l.getD i d) := by
  rw [getD_modify]; simp [h]

/-- Other positions are unchanged. -/
theorem getD_modify_ne {α : Type v} (l : List α) {i j : Nat} (f : α → α) (d : α) (h : i ≠ j) :
    (l.modify i f).getD j d = l.getD j d := by
  rw [getD_modify]; simp [h]

/-- Modifying a position beyond the list changes nothing. -/
theorem modify_of_length_le {α : Type v} (l : List α) {i : Nat} (f : α → α) (h : l.length ≤ i) :
    l.modify i f = l := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      simp only [List.modify_succ_cons]
      rw [ih]
      simp only [List.length_cons] at h; omega

/-- The value read at a position is an element of the list or the default. -/
theorem getD_mem_or {α : Type v} (l : List α) (i : Nat) (d : α) : l.getD i d ∈ l ∨ l.getD i d = d := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getD_cons_succ]
      rcases ih i with h | h
      · exact Or.inl (List.mem_cons_of_mem a h)
      · exact Or.inr h

/-- The total after modifying one position inside the list: the new total plus the old value is
the old total plus the new value. -/
theorem sum_map_modify {α : Type v} (l : List α) {i : Nat} (f : α → α) (g : α → Nat) (d : α)
    (h : i < l.length) :
    ((l.modify i f).map g).sum + g (l.getD i d) = (l.map g).sum + g (f (l.getD i d)) := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero => simp only [List.modify_zero_cons, List.map_cons, List.sum_cons, List.getD_cons_zero]; omega
    | succ i =>
      simp only [List.modify_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ]
      have := ih (i := i) (by simp at h; omega)
      omega

/-- A modification that does not raise the modified value does not raise the total. -/
theorem sum_map_modify_le {α : Type v} (l : List α) (i : Nat) (f : α → α) (g : α → Nat) (d : α)
    (h : i < l.length → g (f (l.getD i d)) ≤ g (l.getD i d)) :
    ((l.modify i f).map g).sum ≤ (l.map g).sum := by
  by_cases hi : i < l.length
  · have := sum_map_modify l f g d hi; have := h hi; omega
  · rw [modify_of_length_le l f (by omega)]; exact Nat.le_refl _

/-- A modification that keeps the modified value keeps the total. -/
theorem sum_map_modify_eq {α : Type v} (l : List α) (i : Nat) (f : α → α) (g : α → Nat) (d : α)
    (h : i < l.length → g (f (l.getD i d)) = g (l.getD i d)) :
    ((l.modify i f).map g).sum = (l.map g).sum := by
  by_cases hi : i < l.length
  · have := sum_map_modify l f g d hi; have := h hi; omega
  · rw [modify_of_length_le l f (by omega)]

/-- Conservation between two positions: lowering the value at `i` by `x` and raising the value
at `j ≠ i` by `x` leaves the total unchanged. -/
theorem sum_map_modify_modify {α : Type v} (l : List α) {i j : Nat} (fi fj : α → α) (g : α → Nat)
    (d : α) (hi : i < l.length) (hj : j < l.length) (hij : i ≠ j) {x : Nat}
    (h1 : g (fi (l.getD i d)) + x = g (l.getD i d)) (h2 : g (fj (l.getD j d)) = g (l.getD j d) + x) :
    (((l.modify i fi).modify j fj).map g).sum = (l.map g).sum := by
  have e1 := sum_map_modify l fi g d hi
  have hj' : j < (l.modify i fi).length := by rw [List.length_modify]; exact hj
  have e2 := sum_map_modify (l.modify i fi) fj g d hj'
  rw [getD_modify_ne l fi d hij] at e2
  omega

/-- The value at a position is at most the total, when the default counts zero. -/
theorem getD_le_sum_map {α : Type v} (l : List α) (i : Nat) (d : α) (g : α → Nat) (hd : g d = 0) :
    g (l.getD i d) ≤ (l.map g).sum := by
  rcases getD_mem_or l i d with h | h
  · exact le_sum_map g h
  · rw [h, hd]; exact Nat.zero_le _

/-- A pointwise bound by a sum of two functions gives the bound on the totals. -/
theorem sum_map_le_add {α : Type v} (l : List α) (g g' h : α → Nat)
    (hle : ∀ a ∈ l, g' a ≤ g a + h a) : (l.map g').sum ≤ (l.map g).sum + (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := hle a (by simp)
    have := ih (fun b hb => hle b (by simp [hb]))
    omega

/-- A pointwise scaled bound gives the scaled bound on the totals. -/
theorem sum_map_mul_le {α : Type v} (l : List α) (f g : α → Nat) (c : Nat)
    (hle : ∀ a ∈ l, f a * c ≤ g a) : (l.map f).sum * c ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    have := hle a (by simp)
    have := ih (fun b hb => hle b (by simp [hb]))
    omega

/-- Scaling every value scales the total. -/
theorem sum_map_mul_right {α : Type v} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_mul]

end ProofForgeFin.Ledger
