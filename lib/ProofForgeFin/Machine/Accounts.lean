import ProofForgeFin.Machine.Record
/-!
# Account maps with explicit finite support

Ledger specifications keep balances as a function `bal : κ → Int` together with an explicit
list of accounts `l : List κ` (the account universe) and sum with `Ledger.sumOver l bal`. That
representation works well in proofs: a balance is read by application, an update is
`Ledger.upd` or `Ledger.adjust`, two balance functions are compared pointwise, and the total is
a fold. This module completes the interface of `Ledger` for that representation.

* Order and repetition: the total does not depend on the order of the account list
  (`sumOver_perm`), and two duplicate-free lists with the same accounts give the same total
  (`sumOver_eq_of_mem_iff`).
* Finite support: `Supported l bal` says every account outside `l` has balance zero. The total
  over any duplicate-free list containing the support is the same (`sumOver_eq_of_supported`).
* Algebra: negation, scaling, mapping the account list, splitting by a predicate, exchanging two
  sums (`sumOver_comm`, the step that turns "sum over accounts of the net of the lines" into
  "sum over lines"), casting natural-number sums.
* Updates: the total after `upd` at a member or a non-member, and conservation under any
  change by a function that sums to zero (`sumOver_add_of_sum_zero`), which covers every
  balanced multi-leg posting.

Every statement is about `Ledger.sumOver`, so it applies to the task definitions of
`sumOver` (they are the same fold, and equal to the library's by `rfl`).
-/

namespace ProofForgeFin.Machine

open Ledger (sumOver sumOver_nil sumOver_cons sumOver_add sumOver_sub sumOver_congr upd upd_self
  upd_ne sumOver_ite_eq)

universe u v

variable {κ : Type u} {α : Type v}

/-! ## Order of the account list -/

/-- The total is the same over a permutation of the account list. -/
theorem sumOver_perm {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → Int) :
    sumOver l₁ f = sumOver l₂ f := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp only [sumOver_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Two duplicate-free account lists with the same members give the same total. -/
theorem sumOver_eq_of_mem_iff {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) (f : α → Int) : sumOver l₁ f = sumOver l₂ f :=
  sumOver_perm ((List.perm_ext_iff_of_nodup h₁ h₂).mpr h) f

/-- The total over a reversed list. -/
theorem sumOver_reverse (l : List α) (f : α → Int) : sumOver l.reverse f = sumOver l f :=
  sumOver_perm (List.reverse_perm l) f

/-- The total over a concatenation does not depend on the order of the parts. -/
theorem sumOver_append_comm (l₁ l₂ : List α) (f : α → Int) :
    sumOver (l₁ ++ l₂) f = sumOver (l₂ ++ l₁) f :=
  sumOver_perm List.perm_append_comm f

/-! ## Algebra of sums -/

/-- The sum of a negated function. -/
theorem sumOver_neg (l : List α) (f : α → Int) : sumOver l (fun a => -f a) = -sumOver l f := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [sumOver_cons, ih]; omega

/-- A constant factor comes out of the sum. -/
theorem sumOver_mul_left (l : List α) (c : Int) (f : α → Int) :
    sumOver l (fun a => c * f a) = c * sumOver l f := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [sumOver_cons, ih, Int.mul_add]

/-- The sum of a constant. -/
theorem sumOver_const (l : List α) (c : Int) : sumOver l (fun _ => c) = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [sumOver_cons, ih, List.length_cons]; push_cast; rw [Int.add_mul]; omega

/-- Summing over a mapped list is summing the composite. -/
theorem sumOver_map {β : Type u} (g : β → α) (l : List β) (f : α → Int) :
    sumOver (l.map g) f = sumOver l (fun b => f (g b)) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

/-- A sum that vanishes term by term on the list is zero. -/
theorem sumOver_eq_zero {l : List α} {f : α → Int} (h : ∀ a ∈ l, f a = 0) : sumOver l f = 0 := by
  rw [sumOver_congr l h]; exact Ledger.sumOver_zero l

/-- A sum of nonnegative terms is nonnegative. -/
theorem sumOver_nonneg {l : List α} {f : α → Int} (h : ∀ a ∈ l, 0 ≤ f a) : 0 ≤ sumOver l f := by
  have := Ledger.sumOver_le_sumOver l (f := fun _ => 0) h
  simpa using this

/-- A nonnegative term is at most the sum, when every term is nonnegative. -/
theorem le_sumOver {l : List α} {f : α → Int} (h : ∀ a ∈ l, 0 ≤ f a) {a : α} (ha : a ∈ l) :
    f a ≤ sumOver l f := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [sumOver_cons]
    have hl : 0 ≤ sumOver l f := sumOver_nonneg (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rcases List.mem_cons.mp ha with e | e
    · subst e; omega
    · have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) e
      have := h b (by simp); omega

/-- Exchanging two sums. With `g a x := if x.1 = a then x.2 else 0` this turns the sum over
accounts of the net of a list of lines into the sum over lines of their sum over accounts. -/
theorem sumOver_comm {β : Type u} (l : List α) (m : List β) (g : α → β → Int) :
    sumOver l (fun a => sumOver m (g a)) = sumOver m (fun b => sumOver l (fun a => g a b)) := by
  induction l with
  | nil => simp only [sumOver_nil]; exact (Ledger.sumOver_zero m).symm
  | cons a l ih =>
    simp only [sumOver_cons, ih]
    exact (sumOver_add m (g a) (fun b => sumOver l (fun a => g a b))).symm

/-- A natural-number sum cast to `Int` is the integer sum of the casts. -/
theorem sumOver_natCast (l : List α) (f : α → Nat) :
    sumOver l (fun a => (f a : Int)) = (((l.map f).sum : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Summing an indicator over a duplicate-free list, with the equation in the order
`x = a` (the form `netOf` produces after exchanging sums). -/
theorem sumOver_ite_eq' [DecidableEq κ] {l : List κ} (hl : l.Nodup) (x : κ) (c : Int) :
    sumOver l (fun a => if x = a then c else 0) = if x ∈ l then c else 0 := by
  rw [← sumOver_ite_eq hl x c]
  apply sumOver_congr
  intro a _
  by_cases h : a = x
  · subst h; simp
  · simp [h, Ne.symm h]

/-- An indicator with a value depending on the account. -/
theorem sumOver_ite_eq_apply [DecidableEq κ] {l : List κ} (hl : l.Nodup) (x : κ) (f : κ → Int) :
    sumOver l (fun a => if a = x then f a else 0) = if x ∈ l then f x else 0 := by
  rw [← sumOver_ite_eq hl x (f x)]
  apply sumOver_congr
  intro a _
  by_cases h : a = x
  · subst h; simp
  · simp [h]

/-! ## Splitting by a predicate -/

/-- The total splits into the accounts satisfying `p` and the others. -/
theorem sumOver_filter_add (l : List α) (p : α → Bool) (f : α → Int) :
    sumOver l f = sumOver (l.filter p) f + sumOver (l.filter (fun a => !p a)) f := by
  rw [← Ledger.sumOver_append]
  exact (sumOver_perm (List.filter_append_perm p l) f).symm

/-- When `f` vanishes outside `p`, the total is the total over the accounts satisfying `p`. -/
theorem sumOver_eq_filter {l : List α} (p : α → Bool) {f : α → Int}
    (h : ∀ a ∈ l, p a = false → f a = 0) : sumOver l f = sumOver (l.filter p) f := by
  rw [sumOver_filter_add l p f, sumOver_eq_zero (l := l.filter (fun a => !p a))]
  · omega
  · intro a ha
    rw [List.mem_filter] at ha
    exact h a ha.1 (by simpa using ha.2)

/-- The sum of an `if` over the list: the sum of the `then` part over the accounts satisfying
the condition plus the sum of the `else` part over the others. -/
theorem sumOver_ite (l : List α) (p : α → Bool) (f g : α → Int) :
    sumOver l (fun a => if p a then f a else g a) =
      sumOver (l.filter p) f + sumOver (l.filter (fun a => !p a)) g := by
  rw [sumOver_filter_add l p]
  congr 1
  · apply sumOver_congr; intro a ha; rw [List.mem_filter] at ha; simp [ha.2]
  · apply sumOver_congr; intro a ha; rw [List.mem_filter] at ha; simp at ha; simp [ha.2]

/-! ## Finite support -/

/-- `bal` has its support in `l`: every account outside `l` has balance zero. -/
def Supported (l : List κ) (bal : κ → Int) : Prop := ∀ a, a ∉ l → bal a = 0

/-- The zero balance function is supported on every list. -/
theorem supported_zero (l : List κ) : Supported l (fun _ => 0) := fun _ _ => rfl

/-- Support grows with the list. -/
theorem Supported.mono {l l' : List κ} {bal : κ → Int} (h : Supported l bal)
    (hsub : ∀ a ∈ l, a ∈ l') : Supported l' bal :=
  fun a ha => h a (fun h' => ha (hsub a h'))

/-- The sum of two supported functions is supported. -/
theorem Supported.add {l : List κ} {f g : κ → Int} (hf : Supported l f) (hg : Supported l g) :
    Supported l (fun a => f a + g a) := fun a ha => by show f a + g a = 0; rw [hf a ha, hg a ha]; rfl

/-- An update at an account of the list keeps the support. -/
theorem Supported.upd [DecidableEq κ] {l : List κ} {bal : κ → Int} (h : Supported l bal) {k : κ}
    (hk : k ∈ l) (v : Int) : Supported l (Ledger.upd bal k v) := fun a ha => by
  have : a ≠ k := fun e => ha (e ▸ hk)
  rw [upd_ne bal v this]; exact h a ha

/-- The total of a supported function is the same over every duplicate-free list that
contains the support and is contained in a list where the function is supported: here, any
duplicate-free `l₂` with `l₁ ⊆ l₂`, when `f` vanishes on `l₂` outside `l₁`. -/
theorem sumOver_eq_of_subset [DecidableEq α] {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hsub : ∀ a ∈ l₁, a ∈ l₂) {f : α → Int} (hz : ∀ a ∈ l₂, a ∉ l₁ → f a = 0) :
    sumOver l₂ f = sumOver l₁ f := by
  rw [sumOver_eq_filter (fun a => decide (a ∈ l₁)) (fun a ha hp => hz a ha (by simpa using hp))]
  apply sumOver_eq_of_mem_iff (List.Nodup.sublist (List.filter_sublist) h₂) h₁
  intro a
  rw [List.mem_filter]
  constructor
  · intro h; simpa using h.2
  · intro h; exact ⟨hsub a h, by simpa using h⟩

/-- The total of a function supported on a duplicate-free list `l` is the same over every
duplicate-free list that contains `l`. -/
theorem sumOver_eq_of_supported [DecidableEq κ] {l l' : List κ} (hl : l.Nodup) (hl' : l'.Nodup)
    (hsub : ∀ a ∈ l, a ∈ l') {f : κ → Int} (hf : Supported l f) : sumOver l' f = sumOver l f :=
  sumOver_eq_of_subset hl hl' hsub (fun a _ ha => hf a ha)

/-! ## Updates and conservation -/

/-- The total after replacing the balance of a member of a duplicate-free list. -/
theorem sumOver_upd [DecidableEq κ] {l : List κ} (hl : l.Nodup) (bal : κ → Int) {k : κ}
    (hk : k ∈ l) (v : Int) : sumOver l (Ledger.upd bal k v) = sumOver l bal - bal k + v := by
  have : Ledger.upd bal k v = fun j => bal j + (if j = k then v - bal k else 0) := by
    funext j; unfold Ledger.upd; split
    · next h => subst h; omega
    · omega
  rw [this, sumOver_add, sumOver_ite_eq hl]; simp [hk]; omega

/-- Replacing the balance of an account outside the list leaves the total unchanged. -/
theorem sumOver_upd_of_not_mem [DecidableEq κ] {l : List κ} (bal : κ → Int) {k : κ} (hk : k ∉ l)
    (v : Int) : sumOver l (Ledger.upd bal k v) = sumOver l bal :=
  sumOver_congr l (fun _ ha => upd_ne bal v (fun e => hk (e ▸ ha)))

/-- Conservation under any change that sums to zero over the accounts: if every balance moves by
`d a` and the moves add up to zero, the total is unchanged. A balanced journal entry, a transfer
and a batch of transfers are all changes of this form. -/
theorem sumOver_add_of_sum_zero (l : List α) (f d : α → Int) (h : sumOver l d = 0) :
    sumOver l (fun a => f a + d a) = sumOver l f := by
  rw [sumOver_add, h]; omega

/-- The total after changing every balance by `d` is the old total plus the sum of `d`. -/
theorem sumOver_add_delta (l : List α) (f d : α → Int) :
    sumOver l (fun a => f a + d a) = sumOver l f + sumOver l d :=
  sumOver_add l f d

/-- Two balance functions with the same total stay equal in total after the same change. -/
theorem sumOver_eq_of_change {l : List α} {f g d : α → Int} (h : sumOver l f = sumOver l g) :
    sumOver l (fun a => f a + d a) = sumOver l (fun a => g a + d a) := by
  rw [sumOver_add, sumOver_add, h]

/-- A balance function that agrees with another on the accounts has the same total. -/
theorem sumOver_eq_of_eqOn {l : List α} {f g : α → Int} (h : ∀ a ∈ l, f a = g a) :
    sumOver l f = sumOver l g := sumOver_congr l h

/-! ## Natural-number totals -/

/-- The natural-number total does not depend on the order of the list. -/
theorem sum_map_perm {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → Nat) :
    (l₁.map f).sum = (l₂.map f).sum := by
  have := sumOver_perm h (fun a => (f a : Int))
  rw [sumOver_natCast, sumOver_natCast] at this
  exact Int.ofNat.inj this

/-- The natural-number total of a sum of two functions. -/
theorem sum_map_add (l : List α) (f g : α → Nat) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Summing a natural-number indicator over a duplicate-free list. -/
theorem sum_map_ite_eq [DecidableEq κ] {l : List κ} (hl : l.Nodup) (x : κ) (c : Nat) :
    (l.map (fun a => if a = x then c else 0)).sum = if x ∈ l then c else 0 := by
  have := sumOver_ite_eq hl x (c : Int)
  have e : sumOver l (fun a => if a = x then (c : Int) else 0) =
      sumOver l (fun a => ((if a = x then c else 0 : Nat) : Int)) := by
    apply sumOver_congr; intro a _; split <;> rfl
  rw [e, sumOver_natCast] at this
  split
  · next h => simp only [h, ite_true] at this; exact Int.ofNat.inj this
  · next h => simp only [h, ite_false] at this; exact Int.ofNat.inj this

/-! ## Per-key totals of a list of records

Specifications often keep the facts as a list of records (child orders with their parent and
executed shares, log entries with their account and amount) and define a per-key total by
recursion over the list (`sentFor`, `execFor`, `logSum`). `keyTotal key f l j` is that total:
the sum of `f x` over the records `x` of `l` with `key x = j`. -/

section KeyTotal

variable {ρ : Type v}

/-- The sum of `f x` over the records `x` of `l` whose key is `j`. -/
def keyTotal [DecidableEq κ] (key : ρ → κ) (f : ρ → Nat) (l : List ρ) (j : κ) : Nat :=
  (l.map fun x => if key x = j then f x else 0).sum

variable [DecidableEq κ] (key : ρ → κ) (f : ρ → Nat)

/-- No records, no total. -/
@[simp, machine_simps] theorem keyTotal_nil (j : κ) : keyTotal key f [] j = 0 := rfl

/-- The total of `x :: l`: `f x` if `x` has the key, plus the total of `l`. -/
@[simp, machine_simps] theorem keyTotal_cons (x : ρ) (l : List ρ) (j : κ) :
    keyTotal key f (x :: l) j = (if key x = j then f x else 0) + keyTotal key f l j := by
  simp [keyTotal]

/-- The total of a concatenation. -/
@[simp, machine_simps] theorem keyTotal_append (l₁ l₂ : List ρ) (j : κ) :
    keyTotal key f (l₁ ++ l₂) j = keyTotal key f l₁ j + keyTotal key f l₂ j := by
  simp [keyTotal]

/-- Records with other keys contribute nothing. -/
theorem keyTotal_eq_zero {l : List ρ} {j : κ} (h : ∀ x ∈ l, key x ≠ j) : keyTotal key f l j = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [keyTotal_cons, ite_eq_right_of_eq_false _ _ (eq_false (h x (by simp))),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Records whose field is zero contribute nothing (newly recorded child orders with nothing
executed yet, for example). -/
theorem keyTotal_eq_zero_of_field {l : List ρ} (h : ∀ x ∈ l, f x = 0) (j : κ) :
    keyTotal key f l j = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [keyTotal_cons, h x (by simp), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]; simp

/-- A pointwise bound on the field gives a bound on every per-key total. -/
theorem keyTotal_le_keyTotal {g : ρ → Nat} {l : List ρ} (h : ∀ x ∈ l, f x ≤ g x) (j : κ) :
    keyTotal key f l j ≤ keyTotal key g l j :=
  Ledger.sum_map_le_sum_map l (fun x hx => by split <;> simp [h x hx])

/-- A record's field, when the record has the key, is at most the total. -/
theorem le_keyTotal {l : List ρ} {x : ρ} (hx : x ∈ l) : f x ≤ keyTotal key f l (key x) := by
  have := Ledger.le_sum_map (fun y => if key y = key x then f y else 0) hx
  simp only [ite_true] at this
  exact this

/-- Replacing the record at position `k`: the new total plus the old record's contribution is the
old total plus the new record's contribution. -/
theorem keyTotal_set {l : List ρ} {k : Nat} {x : ρ} (h : l[k]? = some x) (x' : ρ) (j : κ) :
    keyTotal key f (l.set k x') j + (if key x = j then f x else 0) =
      keyTotal key f l j + (if key x' = j then f x' else 0) := by
  induction l generalizing k with
  | nil => simp at h
  | cons y l ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, keyTotal_cons]
      omega
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set_cons_succ, keyTotal_cons]
      have := ih h
      omega

/-- Replacing a record by one with the same key and a field larger by `d` raises the total of
that key by `d` and leaves the other keys unchanged. -/
theorem keyTotal_set_add {l : List ρ} {k : Nat} {x x' : ρ} (h : l[k]? = some x)
    (hk : key x' = key x) {d : Nat} (hd : f x' = f x + d) (j : κ) :
    keyTotal key f (l.set k x') j = keyTotal key f l j + (if key x = j then d else 0) := by
  have := keyTotal_set key f h x' j
  rw [hk, hd] at this
  split at this <;> simp_all <;> omega

/-- Replacing a record by one with the same key and the same field leaves every total unchanged. -/
theorem keyTotal_set_eq {l : List ρ} {k : Nat} {x x' : ρ} (h : l[k]? = some x)
    (hk : key x' = key x) (hf : f x' = f x) (j : κ) :
    keyTotal key f (l.set k x') j = keyTotal key f l j := by
  rw [keyTotal_set_add key f h hk (d := 0) (by rw [hf]; rfl)]; simp

/-- The total of zero is zero. -/
theorem sum_map_zero {β : Type u} (l : List β) : (l.map fun _ => (0 : Nat)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Conservation across keys: summing the per-key totals over a duplicate-free list containing
every record's key gives the total of the field over all records. -/
theorem sum_keyTotal {keys : List κ} (hk : keys.Nodup) {l : List ρ} (h : ∀ x ∈ l, key x ∈ keys) :
    (keys.map (keyTotal key f l)).sum = (l.map f).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact sum_map_zero keys
  | cons x l ih =>
    have e : keyTotal key f (x :: l) =
        fun j => (if j = key x then f x else 0) + keyTotal key f l j := by
      funext j; rw [keyTotal_cons]; by_cases hj : j = key x
      · subst hj; simp
      · simp [hj, Ne.symm hj]
    rw [e, sum_map_add, sum_map_ite_eq hk, ite_eq_left_of_eq_true _ _ (eq_true (h x (by simp))),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp

end KeyTotal

end ProofForgeFin.Machine
