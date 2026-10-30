import ProofForgeFin.Machine.Accounts
/-!
# Double-entry bookkeeping

A journal entry is a list of lines, each an account and a signed amount (positive for a debit,
negative for a credit), the representation of the ledger tasks (`Line := AccountId × Int`).
Posting an entry adds every line to its account. The definitions below are the ones the task
specifications write (`netOf`, `lineSum`, `postLines` with `adjust`), so task definitions unfold
to them by `rfl`.

* `netOf ls a`: the net amount the lines post to account `a`; `lineSum ls`: the sum of all lines;
  `post bal ls`: the balances after posting, `bal a + netOf ls a`; `postLines`: the line-by-line
  posting loop of the task solutions, equal to `post` (`postLines_eq_post`).
* Trial balance: over a duplicate-free account list containing every account of the lines, the
  total after posting is the old total plus the sum of the lines (`sumOver_post`), so a balanced
  entry keeps the total (`trial_balance_post`), and so does any sequence of balanced entries
  (`trial_balance_postAll`).
* Reversal: `negate ls` negates every amount; posting it after `ls` restores every balance
  exactly (`post_post_negate`), and reversing a whole sequence of entries in any order restores
  the opening balances (`postAll_reverse_restores`).
* Order: posting is commutative (`post_comm`); a sequence of entries posted in any order gives the
  same balances (`postAll_perm`).
* Debits and credits: `lineSum = debits - credits` (`lineSum_eq_debits_sub_credits`), so an
  entry balances exactly when its debits equal its credits.
* Reversal marks: `sumOver_mark` removes exactly the net of one entry from the sum over the
  entries not yet reversed, the step behind "every balance equals opening plus the net of the
  entries not reversed".
* T-accounts: `TBook` keeps a debit column and a credit column of natural numbers per account and
  posts `Leg`s; total debits equal total credits after any sequence of balanced entries
  (`TBook.balanced_run`), and the signed balance `dr - cr` moves by the signed lines
  (`TBook.net_postLegs`).
-/

namespace ProofForgeFin.Machine.Journal

open Ledger (sumOver sumOver_nil sumOver_cons sumOver_add sumOver_sub sumOver_congr sumOver_append
  sumOver_ite_eq upd upd_self upd_ne adjust)

universe u v

variable {κ : Type u} [DecidableEq κ]

/-! ## Lines -/

/-- The net amount the lines `ls` post to account `a`. -/
def netOf (ls : List (κ × Int)) (a : κ) : Int := sumOver ls (fun l => if l.1 = a then l.2 else 0)

/-- The sum of the amounts on the lines. -/
def lineSum (ls : List (κ × Int)) : Int := sumOver ls (·.2)

/-- No lines post nothing. -/
@[simp, machine_simps] theorem netOf_nil (a : κ) : netOf ([] : List (κ × Int)) a = 0 := rfl

/-- The net of `l :: ls`: the amount of `l` if it names `a`, plus the net of `ls`. -/
@[simp, machine_simps] theorem netOf_cons (l : κ × Int) (ls : List (κ × Int)) (a : κ) :
    netOf (l :: ls) a = (if l.1 = a then l.2 else 0) + netOf ls a := rfl

/-- The net of a concatenation. -/
theorem netOf_append (ls ms : List (κ × Int)) (a : κ) :
    netOf (ls ++ ms) a = netOf ls a + netOf ms a := sumOver_append ls ms _

/-- The net of one line. -/
theorem netOf_singleton (k : κ) (x : Int) (a : κ) :
    netOf [(k, x)] a = if k = a then x else 0 := by simp

/-- An account named by no line receives nothing. -/
theorem netOf_eq_zero {ls : List (κ × Int)} {a : κ} (h : ∀ l ∈ ls, l.1 ≠ a) : netOf ls a = 0 := by
  unfold netOf
  rw [sumOver_congr ls (g := fun _ => 0) (fun l hl => by simp [h l hl])]
  exact Ledger.sumOver_zero ls

omit [DecidableEq κ] in
/-- The sum of no lines is zero. -/
@[simp, machine_simps] theorem lineSum_nil : lineSum ([] : List (κ × Int)) = 0 := rfl

omit [DecidableEq κ] in
/-- The sum of `l :: ls`. -/
@[simp, machine_simps] theorem lineSum_cons (l : κ × Int) (ls : List (κ × Int)) :
    lineSum (l :: ls) = l.2 + lineSum ls := rfl

omit [DecidableEq κ] in
/-- The sum of a concatenation. -/
theorem lineSum_append (ls ms : List (κ × Int)) : lineSum (ls ++ ms) = lineSum ls + lineSum ms :=
  sumOver_append ls ms _

/-- An entry balances: its lines sum to zero. -/
def Balanced (ls : List (κ × Int)) : Prop := lineSum ls = 0

/-- Every line of the entry names an account of `l`. -/
def Known (l : List κ) (ls : List (κ × Int)) : Prop := ∀ x ∈ ls, x.1 ∈ l

/-- Summing the net of the lines over the accounts of a duplicate-free list gives the sum of the
lines that name an account of the list. -/
theorem sumOver_netOf_eq {l : List κ} (hl : l.Nodup) (ls : List (κ × Int)) :
    sumOver l (netOf ls) = sumOver ls (fun x => if x.1 ∈ l then x.2 else 0) := by
  unfold netOf
  rw [sumOver_comm]
  exact sumOver_congr ls (fun x _ => sumOver_ite_eq' hl x.1 x.2)

/-- Summing the net of the lines over a duplicate-free list containing every account of the lines
gives the sum of the lines. -/
theorem sumOver_netOf {l : List κ} (hl : l.Nodup) {ls : List (κ × Int)} (h : Known l ls) :
    sumOver l (netOf ls) = lineSum ls := by
  rw [sumOver_netOf_eq hl]
  exact sumOver_congr ls (fun x hx => by simp [h x hx])

/-! ## Posting -/

/-- The balances after posting the lines `ls`. -/
def post (bal : κ → Int) (ls : List (κ × Int)) : κ → Int := fun a => bal a + netOf ls a

/-- Reading a posted balance. -/
@[simp, machine_simps] theorem post_apply (bal : κ → Int) (ls : List (κ × Int)) (a : κ) :
    post bal ls a = bal a + netOf ls a := rfl

/-- Posting line by line with `adjust`, first to last: the loop of the task solutions. -/
def postLines : List (κ × Int) → (κ → Int) → (κ → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)

/-- The line-by-line loop adds the net of the lines to every account. -/
theorem postLines_apply (ls : List (κ × Int)) (bal : κ → Int) (a : κ) :
    postLines ls bal a = bal a + netOf ls a := by
  induction ls generalizing bal with
  | nil => simp [postLines]
  | cons l ls ih =>
    simp only [postLines, ih, adjust, netOf_cons]
    by_cases h : a = l.1
    · subst h; simp; omega
    · simp [h, Ne.symm h]

/-- The line-by-line loop is `post`. -/
theorem postLines_eq_post (ls : List (κ × Int)) (bal : κ → Int) : postLines ls bal = post bal ls := by
  funext a; exact postLines_apply ls bal a

/-- Posting no lines changes nothing. -/
@[simp, machine_simps] theorem post_nil (bal : κ → Int) : post bal [] = bal := by
  funext a; simp

/-- Posting a concatenation is posting the parts in order. -/
theorem post_append (bal : κ → Int) (ls ms : List (κ × Int)) :
    post bal (ls ++ ms) = post (post bal ls) ms := by
  funext a; simp only [post_apply, netOf_append]; omega

/-- Posting is commutative. -/
theorem post_comm (bal : κ → Int) (ls ms : List (κ × Int)) :
    post (post bal ls) ms = post (post bal ms) ls := by
  funext a; simp only [post_apply]; omega

/-- Posting one line is `adjust`. -/
theorem post_singleton (bal : κ → Int) (k : κ) (x : Int) : post bal [(k, x)] = adjust bal k x := by
  funext a; simp only [post_apply, netOf_singleton, adjust]
  by_cases h : a = k
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The total after posting: the old total plus the sum of the lines. -/
theorem sumOver_post {l : List κ} (hl : l.Nodup) (bal : κ → Int) {ls : List (κ × Int)}
    (h : Known l ls) : sumOver l (post bal ls) = sumOver l bal + lineSum ls := by
  unfold post; rw [sumOver_add, sumOver_netOf hl h]

/-- Trial balance: posting a balanced entry over known accounts keeps the total. -/
theorem trial_balance_post {l : List κ} (hl : l.Nodup) (bal : κ → Int) {ls : List (κ × Int)}
    (hk : Known l ls) (hb : Balanced ls) : sumOver l (post bal ls) = sumOver l bal := by
  rw [sumOver_post hl bal hk, hb]; omega

/-- Accounts named by no line keep their balance. -/
theorem post_of_not_named (bal : κ → Int) {ls : List (κ × Int)} {a : κ} (h : ∀ x ∈ ls, x.1 ≠ a) :
    post bal ls a = bal a := by
  simp [netOf_eq_zero h]

/-! ## Reversal -/

/-- The same lines with every amount negated: the reversing entry. -/
def negate (ls : List (κ × Int)) : List (κ × Int) := ls.map (fun l => (l.1, -l.2))

/-- The reversing entry posts the opposite net to every account. -/
@[simp, machine_simps] theorem netOf_negate (ls : List (κ × Int)) (a : κ) :
    netOf (negate ls) a = -netOf ls a := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [negate, List.map_cons, netOf_cons] at ih ⊢
    rw [ih]; split <;> omega

omit [DecidableEq κ] in
/-- The reversing entry sums to the opposite. -/
@[simp] theorem lineSum_negate (ls : List (κ × Int)) : lineSum (negate ls) = -lineSum ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [negate, List.map_cons, lineSum_cons] at ih ⊢
    rw [ih]; omega

omit [DecidableEq κ] in
/-- Negating twice gives the original lines. -/
@[simp] theorem negate_negate (ls : List (κ × Int)) : negate (negate ls) = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [negate, List.map_cons, Int.neg_neg] at ih ⊢
    rw [ih]

omit [DecidableEq κ] in
/-- The reversing entry of a balanced entry is balanced. -/
theorem Balanced.negate {ls : List (κ × Int)} (h : Balanced ls) : Balanced (negate ls) := by
  unfold Balanced at *; rw [lineSum_negate, h]; rfl

omit [DecidableEq κ] in
/-- The reversing entry names the same accounts. -/
theorem Known.negate {l : List κ} {ls : List (κ × Int)} (h : Known l ls) : Known l (negate ls) := by
  intro x hx
  simp only [Journal.negate, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h y hy

/-- Posting an entry and then its reversing entry restores every balance exactly. -/
@[simp, machine_simps] theorem post_post_negate (bal : κ → Int) (ls : List (κ × Int)) :
    post (post bal ls) (negate ls) = bal := by
  funext a; simp only [post_apply, netOf_negate]; omega

/-- Posting the reversing entry first and then the entry restores every balance exactly. -/
@[simp, machine_simps] theorem post_negate_post (bal : κ → Int) (ls : List (κ × Int)) :
    post (post bal (negate ls)) ls = bal := by
  funext a; simp only [post_apply, netOf_negate]; omega

/-- Posting the reversing entry subtracts the net of the entry. -/
theorem post_negate_apply (bal : κ → Int) (ls : List (κ × Int)) (a : κ) :
    post bal (negate ls) a = bal a - netOf ls a := by
  simp only [post_apply, netOf_negate]; omega

/-! ## Debits and credits -/

/-- The debit lines' total: the sum of the positive amounts. -/
def debits (ls : List (κ × Int)) : Int := sumOver ls (fun x => if 0 ≤ x.2 then x.2 else 0)

/-- The credit lines' total: the sum of the magnitudes of the negative amounts. -/
def credits (ls : List (κ × Int)) : Int := sumOver ls (fun x => if 0 ≤ x.2 then 0 else -x.2)

omit [DecidableEq κ] in
/-- The sum of the lines is debits minus credits. -/
theorem lineSum_eq_debits_sub_credits (ls : List (κ × Int)) :
    lineSum ls = debits ls - credits ls := by
  unfold lineSum debits credits
  rw [← sumOver_sub]
  exact sumOver_congr ls (fun x _ => by split <;> omega)

omit [DecidableEq κ] in
/-- An entry balances exactly when its debits equal its credits. -/
theorem balanced_iff_debits_eq_credits (ls : List (κ × Int)) :
    Balanced ls ↔ debits ls = credits ls := by
  unfold Balanced; rw [lineSum_eq_debits_sub_credits]; omega

omit [DecidableEq κ] in
/-- Debits are nonnegative. -/
theorem debits_nonneg (ls : List (κ × Int)) : 0 ≤ debits ls :=
  sumOver_nonneg (fun x _ => by split <;> omega)

omit [DecidableEq κ] in
/-- Credits are nonnegative. -/
theorem credits_nonneg (ls : List (κ × Int)) : 0 ≤ credits ls :=
  sumOver_nonneg (fun x _ => by split <;> omega)

/-! ## Sequences of entries -/

section Entries

variable {ε : Type v}

/-- The balances after posting the entries `es` in order, where `lines e` are the lines of the
entry `e` (for a task entry structure, `lines := (·.lines)`). -/
def postAll (lines : ε → List (κ × Int)) (bal : κ → Int) (es : List ε) : κ → Int :=
  Seq.run (fun b e => post b (lines e)) bal es

/-- Posting no entries changes nothing. -/
@[simp, machine_simps] theorem postAll_nil (lines : ε → List (κ × Int)) (bal : κ → Int) :
    postAll lines bal [] = bal := rfl

/-- Posting `e :: es`: `e` first, then the rest. -/
@[simp, machine_simps] theorem postAll_cons (lines : ε → List (κ × Int)) (bal : κ → Int) (e : ε)
    (es : List ε) : postAll lines bal (e :: es) = postAll lines (post bal (lines e)) es := rfl

/-- Posting a concatenation of entry lists. -/
theorem postAll_append (lines : ε → List (κ × Int)) (bal : κ → Int) (es fs : List ε) :
    postAll lines bal (es ++ fs) = postAll lines (postAll lines bal es) fs :=
  Seq.run_append _ _ _ _

/-- Every balance after a sequence of entries: the opening balance plus the net of every entry. -/
theorem postAll_apply (lines : ε → List (κ × Int)) (bal : κ → Int) (es : List ε) (a : κ) :
    postAll lines bal es a = bal a + sumOver es (fun e => netOf (lines e) a) := by
  induction es generalizing bal with
  | nil => simp
  | cons e es ih => rw [postAll_cons, ih, post_apply, sumOver_cons]; omega

/-- Posting the same entries in any order gives the same balances. -/
theorem postAll_perm (lines : ε → List (κ × Int)) (bal : κ → Int) {es fs : List ε}
    (h : es.Perm fs) : postAll lines bal es = postAll lines bal fs := by
  funext a; rw [postAll_apply, postAll_apply, sumOver_perm h]

/-- The total after a sequence of entries over known accounts: the old total plus the sum of
every entry's lines. -/
theorem sumOver_postAll {l : List κ} (hl : l.Nodup) (lines : ε → List (κ × Int)) (bal : κ → Int)
    {es : List ε} (h : ∀ e ∈ es, Known l (lines e)) :
    sumOver l (postAll lines bal es) = sumOver l bal + sumOver es (fun e => lineSum (lines e)) := by
  induction es generalizing bal with
  | nil => simp
  | cons e es ih =>
    rw [postAll_cons, ih (post bal (lines e)) (fun f hf => h f (List.mem_cons_of_mem _ hf)),
      sumOver_post hl bal (h e (by simp)), sumOver_cons]
    omega

/-- Trial balance over any sequence: posting balanced entries over known accounts, in order,
keeps the total of the balances. -/
theorem trial_balance_postAll {l : List κ} (hl : l.Nodup) (lines : ε → List (κ × Int))
    (bal : κ → Int) {es : List ε} (hk : ∀ e ∈ es, Known l (lines e))
    (hb : ∀ e ∈ es, Balanced (lines e)) : sumOver l (postAll lines bal es) = sumOver l bal := by
  rw [sumOver_postAll hl lines bal hk, Machine.sumOver_eq_zero (fun e he => hb e he)]; omega

/-- Reversing every entry of a sequence, in any order, restores the opening balances exactly:
`rs` is any rearrangement of `es` and each entry of `rs` is posted with negated lines. -/
theorem postAll_reverse_restores (lines : ε → List (κ × Int)) (bal : κ → Int) {es rs : List ε}
    (h : rs.Perm es) :
    postAll (fun e => negate (lines e)) (postAll lines bal es) rs = bal := by
  funext a
  rw [postAll_apply, postAll_apply, sumOver_perm h]
  simp only [netOf_negate]
  rw [Machine.sumOver_neg]; omega

/-- Reversing the entries in reverse order (the order an undo log replays) restores the opening
balances. -/
theorem postAll_reverse_restores' (lines : ε → List (κ × Int)) (bal : κ → Int) (es : List ε) :
    postAll (fun e => negate (lines e)) (postAll lines bal es) es.reverse = bal :=
  postAll_reverse_restores lines bal (List.reverse_perm es)

/-! ## Reversal marks -/

/-- Marking one entry as reversed removes exactly its contribution from the sum over the entries
not yet reversed. The journal `j` has distinct identifiers (`id`), `e` is the entry of `j` with
identifier `i`, `i` was not reversed (`i ∉ R`), and the new set of reversed identifiers `R'` is
`R` with `i` added. -/
theorem sumOver_mark {ι : Type v} [DecidableEq ι] (id : ε → ι) (g : ε → Int) {R R' : List ι} {i : ι} {e : ε}
    (hR : ∀ x, x ∈ R' ↔ x = i ∨ x ∈ R) (hi : i ∉ R) {j : List ε} (hj : (j.map id).Nodup)
    (he : e ∈ j) (hei : id e = i) :
    sumOver j (fun x => if id x ∈ R' then 0 else g x) =
      sumOver j (fun x => if id x ∈ R then 0 else g x) - g e := by
  induction j with
  | nil => simp at he
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hj
    simp only [sumOver_cons]
    by_cases hx : x = e
    · subst hx
      have hrest : sumOver xs (fun y => if id y ∈ R' then 0 else g y)
          = sumOver xs (fun y => if id y ∈ R then 0 else g y) := by
        apply sumOver_congr
        intro y hy
        have hyi : id y ≠ i := fun h' => hj.1 (hei ▸ h' ▸ List.mem_map_of_mem hy)
        have : (id y ∈ R') ↔ (id y ∈ R) := by rw [hR]; simp [hyi]
        simp only [this]
      have h1 : id x ∈ R' := (hR _).mpr (Or.inl hei)
      have h2 : id x ∉ R := hei ▸ hi
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h2), hrest]
      omega
    · have he' : e ∈ xs := by
        rcases List.mem_cons.mp he with h | h
        · exact absurd h.symm hx
        · exact h
      have hxi : id x ≠ i := fun h' => hj.1 (h' ▸ hei ▸ List.mem_map_of_mem he')
      have : (id x ∈ R') ↔ (id x ∈ R) := by rw [hR]; simp [hxi]
      simp only [this, ih hj.2 he']
      omega

end Entries

/-! ## T-accounts -/

/-- The side of a leg. -/
inductive Side where
  /-- A debit leg. -/
  | debit
  /-- A credit leg. -/
  | credit
  deriving DecidableEq, Repr

/-- One leg of a journal entry: an account, a side and an amount. -/
structure Leg (κ : Type u) where
  /-- The account. -/
  acct : κ
  /-- Debit or credit. -/
  side : Side
  /-- The amount, in minor units. -/
  amount : Nat

/-- A ledger of T-accounts: the debit column and the credit column of every account. -/
structure TBook (κ : Type u) where
  /-- The total debited to each account. -/
  dr : κ → Nat
  /-- The total credited to each account. -/
  cr : κ → Nat

/-- The amount a leg debits. -/
def Leg.debit (x : Leg κ) : Nat := match x.side with | .debit => x.amount | .credit => 0

/-- The amount a leg credits. -/
def Leg.credit (x : Leg κ) : Nat := match x.side with | .debit => 0 | .credit => x.amount

/-- A leg as a signed line: debits positive, credits negative. -/
def Leg.signed (x : Leg κ) : κ × Int := (x.acct, (x.debit : Int) - x.credit)

/-- The total debits of an entry. -/
def debitTotal (legs : List (Leg κ)) : Nat := (legs.map Leg.debit).sum

/-- The total credits of an entry. -/
def creditTotal (legs : List (Leg κ)) : Nat := (legs.map Leg.credit).sum

/-- Posting one leg to its column. -/
def TBook.postLeg (b : TBook κ) (x : Leg κ) : TBook κ :=
  { dr := upd b.dr x.acct (b.dr x.acct + x.debit), cr := upd b.cr x.acct (b.cr x.acct + x.credit) }

/-- Posting the legs of an entry in order. -/
def TBook.postLegs (b : TBook κ) (legs : List (Leg κ)) : TBook κ := Seq.run TBook.postLeg b legs

/-- Total debits equal total credits over the accounts of `l`. -/
def TBook.Balanced (l : List κ) (b : TBook κ) : Prop := (l.map b.dr).sum = (l.map b.cr).sum

/-- The debit column after posting the legs: every account gains the debits of its legs. -/
theorem TBook.dr_postLegs (b : TBook κ) (legs : List (Leg κ)) (a : κ) :
    (b.postLegs legs).dr a = b.dr a + ((legs.filter (fun x => x.acct = a)).map Leg.debit).sum := by
  induction legs generalizing b with
  | nil => simp [TBook.postLegs]
  | cons x xs ih =>
    show (TBook.postLegs (b.postLeg x) xs).dr a = _
    rw [ih]
    simp only [TBook.postLeg, List.filter_cons]
    by_cases h : x.acct = a
    · subst h; simp; omega
    · simp [h, upd_ne _ _ (Ne.symm h)]

/-- The credit column after posting the legs. -/
theorem TBook.cr_postLegs (b : TBook κ) (legs : List (Leg κ)) (a : κ) :
    (b.postLegs legs).cr a = b.cr a + ((legs.filter (fun x => x.acct = a)).map Leg.credit).sum := by
  induction legs generalizing b with
  | nil => simp [TBook.postLegs]
  | cons x xs ih =>
    show (TBook.postLegs (b.postLeg x) xs).cr a = _
    rw [ih]
    simp only [TBook.postLeg, List.filter_cons]
    by_cases h : x.acct = a
    · subst h; simp; omega
    · simp [h, upd_ne _ _ (Ne.symm h)]

/-- The total of the debit column after posting legs over known accounts: the old total plus the
entry's debits. -/
theorem TBook.drTotal_postLegs {l : List κ} (hl : l.Nodup) (b : TBook κ) {legs : List (Leg κ)}
    (hk : ∀ x ∈ legs, x.acct ∈ l) :
    (l.map (b.postLegs legs).dr).sum = (l.map b.dr).sum + debitTotal legs := by
  induction legs generalizing b with
  | nil => simp [TBook.postLegs, debitTotal]
  | cons x xs ih =>
    show (l.map (TBook.postLegs (b.postLeg x) xs).dr).sum = _
    rw [ih (b.postLeg x) (fun y hy => hk y (List.mem_cons_of_mem _ hy))]
    have := Ledger.sum_map_upd hl b.dr (b.dr x.acct + x.debit) (hk x (by simp))
    simp only [TBook.postLeg, debitTotal, List.map_cons, List.sum_cons] at this ⊢
    omega

/-- The total of the credit column after posting legs over known accounts. -/
theorem TBook.crTotal_postLegs {l : List κ} (hl : l.Nodup) (b : TBook κ) {legs : List (Leg κ)}
    (hk : ∀ x ∈ legs, x.acct ∈ l) :
    (l.map (b.postLegs legs).cr).sum = (l.map b.cr).sum + creditTotal legs := by
  induction legs generalizing b with
  | nil => simp [TBook.postLegs, creditTotal]
  | cons x xs ih =>
    show (l.map (TBook.postLegs (b.postLeg x) xs).cr).sum = _
    rw [ih (b.postLeg x) (fun y hy => hk y (List.mem_cons_of_mem _ hy))]
    have := Ledger.sum_map_upd hl b.cr (b.cr x.acct + x.credit) (hk x (by simp))
    simp only [TBook.postLeg, creditTotal, List.map_cons, List.sum_cons] at this ⊢
    omega

/-- Posting an entry whose debits equal its credits keeps total debits equal to total credits. -/
theorem TBook.Balanced.postLegs {l : List κ} (hl : l.Nodup) {b : TBook κ} (hb : b.Balanced l)
    {legs : List (Leg κ)} (hk : ∀ x ∈ legs, x.acct ∈ l) (he : debitTotal legs = creditTotal legs) :
    (b.postLegs legs).Balanced l := by
  unfold TBook.Balanced at *
  rw [TBook.drTotal_postLegs hl b hk, TBook.crTotal_postLegs hl b hk, hb, he]

/-- The trial balance after any sequence of entries: when every entry has equal debits and
credits and names only accounts of `l`, total debits equal total credits after the whole
sequence, starting from a balanced book. -/
theorem TBook.balanced_run {l : List κ} (hl : l.Nodup) {b : TBook κ} (hb : b.Balanced l)
    {entries : List (List (Leg κ))} (hk : ∀ e ∈ entries, ∀ x ∈ e, x.acct ∈ l)
    (he : ∀ e ∈ entries, debitTotal e = creditTotal e) :
    (Seq.run TBook.postLegs b entries).Balanced l :=
  Seq.run_invariant_of_mem (I := TBook.Balanced l)
    (fun _ e hmem hs => hs.postLegs hl (hk e hmem) (he e hmem)) hb

/-- The signed balance of an account, debits minus credits. -/
def TBook.net (b : TBook κ) (a : κ) : Int := (b.dr a : Int) - b.cr a

/-- The signed balance moves by the net of the entry's signed lines: the T-account ledger and
the signed-line ledger agree. -/
theorem TBook.net_postLegs (b : TBook κ) (legs : List (Leg κ)) (a : κ) :
    (b.postLegs legs).net a = b.net a + netOf (legs.map Leg.signed) a := by
  induction legs generalizing b with
  | nil => simp [TBook.postLegs, TBook.net]
  | cons x xs ih =>
    show (TBook.postLegs (b.postLeg x) xs).net a = _
    rw [ih]
    simp only [TBook.net, TBook.postLeg, List.map_cons, netOf_cons, Leg.signed]
    by_cases h : x.acct = a
    · subst h; simp only [upd_self, ite_true]; push_cast; omega
    · simp only [upd_ne _ _ (Ne.symm h), h, ite_false]; omega

omit [DecidableEq κ] in
/-- The signed lines of an entry sum to its debits minus its credits. -/
theorem lineSum_signed (legs : List (Leg κ)) :
    lineSum (legs.map Leg.signed) = (debitTotal legs : Int) - creditTotal legs := by
  induction legs with
  | nil => simp [debitTotal, creditTotal]
  | cons x xs ih =>
    simp only [List.map_cons, lineSum_cons, ih, debitTotal, creditTotal, List.sum_cons, Leg.signed]
    push_cast; omega

omit [DecidableEq κ] in
/-- An entry with equal debits and credits gives balanced signed lines. -/
theorem balanced_signed {legs : List (Leg κ)} (h : debitTotal legs = creditTotal legs) :
    Balanced (legs.map Leg.signed) := by
  unfold Balanced; rw [lineSum_signed, h]; omega

end ProofForgeFin.Machine.Journal
