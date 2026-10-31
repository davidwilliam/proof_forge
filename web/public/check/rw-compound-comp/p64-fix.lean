import CompRewards.Spec
/-!
Reference solution: the COMP distribution of Compound's Comptroller as fixed by Proposal 64
and kept by Proposal 65, with every requirement proved.

`comptroller` (at the end of the file) is a transcription of the shipped Solidity
(compound-finance/compound-protocol, `contracts/Comptroller.sol` at commit
32f765957e05560cbbd977d7a49c86a09a81282b, pull request 165, deployed as implementation
0x234b619b4f4e405665f7d94f2ce60c24256032b5; unchanged in commit
c05d7e09e57ff69582ddb621984e46099f1b4d4b, pull request 166, deployed as
0xbafe01ff935c7305907c33bf824352ee5979b526). It is the Proposal 62 code with
`supplyIndex >= compInitialIndex` and `borrowIndex >= compInitialIndex` in place of `>`. The
Proposal 64 lock in `grantCompInternal`, which Proposal 65 removed, is not included.

The proofs go through `specImpl`, the same distribution written with the specification's
definitions; `comptroller_eq` shows the transcription computes it. The sequence requirements
follow from two potentials that never grow except when blocks pass, and then by at most the
COMP emitted: the scaled COMP credited to all accounts plus their pending rewards plus the
unindexed emission (`Phi`), and the same for one account (`Psi`).
-/

namespace CompRewards

/-! ## List lemmas -/

theorem getD_modify {α} (l : List α) (i j : Nat) (f : α → α) (d : α) :
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

theorem getD_modify_self {α} (l : List α) (i : Nat) (f : α → α) (d : α) (h : i < l.length) :
    (l.modify i f).getD i d = f (l.getD i d) := by
  rw [getD_modify]; simp [h]

theorem getD_modify_ne {α} (l : List α) (i j : Nat) (f : α → α) (d : α) (h : i ≠ j) :
    (l.modify i f).getD j d = l.getD j d := by
  rw [getD_modify]; simp [h]

theorem getD_modify_out {α} (l : List α) (i : Nat) (f : α → α) (d : α) (h : ¬ i < l.length) :
    (l.modify i f).getD i d = l.getD i d := by
  rw [getD_modify]; simp [h]

theorem modify_out {α} (l : List α) (i : Nat) (f : α → α) (h : ¬ i < l.length) :
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

theorem modify_congr {α} (l : List α) (i : Nat) (f g : α → α) (d : α)
    (h : i < l.length → f (l.getD i d) = g (l.getD i d)) : l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.modify_zero_cons]
      have := h (by simp)
      simp only [List.getD_cons_zero] at this
      rw [this]
    | succ i =>
      simp only [List.modify_succ_cons]
      rw [ih]
      intro hi
      have := h (by simp; omega)
      simpa using this

theorem getD_mem_or {α} (l : List α) (i : Nat) (d : α) : l.getD i d ∈ l ∨ l.getD i d = d := by
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

theorem length_modify' {α} (l : List α) (i : Nat) (f : α → α) : (l.modify i f).length = l.length :=
  List.length_modify f l i

theorem sum_modify_le {α} (l : List α) (i : Nat) (f : α → α) (g : α → Nat) (d : α)
    (h : i < l.length → g (f (l.getD i d)) ≤ g (l.getD i d)) :
    ((l.modify i f).map g).sum ≤ (l.map g).sum := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.modify_zero_cons, List.map_cons, List.sum_cons]
      have := h (by simp)
      simp only [List.getD_cons_zero] at this
      omega
    | succ i =>
      simp only [List.modify_succ_cons, List.map_cons, List.sum_cons]
      have := ih i (fun hi => by have := h (by simp; omega); simpa using this)
      omega

theorem sum_modify_eq {α} (l : List α) (i : Nat) (f : α → α) (g : α → Nat) (d : α)
    (h : i < l.length → g (f (l.getD i d)) = g (l.getD i d)) :
    ((l.modify i f).map g).sum = (l.map g).sum := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.modify_zero_cons, List.map_cons, List.sum_cons]
      have := h (by simp)
      simp only [List.getD_cons_zero] at this
      omega
    | succ i =>
      simp only [List.modify_succ_cons, List.map_cons, List.sum_cons]
      have := ih i (fun hi => by have := h (by simp; omega); simpa using this)
      omega

theorem sum_le_add {α} (l : List α) (g g' h : α → Nat) (hle : ∀ a, g' a ≤ g a + h a) :
    (l.map g').sum ≤ (l.map g).sum + (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := hle a
    omega

theorem sum_mul_le {α} (l : List α) (f g : α → Nat) (c : Nat) (hle : ∀ a, f a * c ≤ g a) :
    (l.map f).sum * c ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    have := hle a
    omega

theorem getD_le_sum {α} (l : List α) (i : Nat) (d : α) (g : α → Nat) (hd : g d = 0) :
    g (l.getD i d) ≤ (l.map g).sum := by
  induction l generalizing i with
  | nil => simp [hd]
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getD_cons_succ, List.map_cons, List.sum_cons]
      have := ih i
      omega


/-! ## The distribution in the shape of the specification -/

def sdS (s : St) : Side := accrueSide s.supplyState s.blockNumber (totalSupply s)
def sdB (s : St) : Side := accrueSide s.borrowState s.blockNumber (totalBorrows s)

def supplyOk (s : St) (who : Account) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).supplierIndex (sdS s).index ≤ (sdS s).index

def borrowOk (s : St) (who : Account) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).borrowerIndex (sdB s).index ≤ (sdB s).index

instance (s : St) (who : Account) : Decidable (supplyOk s who) := by
  unfold supplyOk; infer_instance
instance (s : St) (who : Account) : Decidable (borrowOk s who) := by
  unfold borrowOk; infer_instance

/-- The record of an account credited for supply up to index `iS`. -/
def distS (iS : Nat) (a : Acct) : Acct :=
  { a with supplierIndex := iS,
           accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex iS) iS }

/-- The record of an account credited for borrowing up to index `iB`. -/
def distB (iB : Nat) (a : Acct) : Acct :=
  { a with borrowerIndex := iB,
           accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex iB) iB }

def supplyNext (s : St) (who : Account) : St :=
  { s with supplyState := sdS s, accts := s.accts.modify who (distS (sdS s).index) }

def borrowNext (s : St) (who : Account) : St :=
  { s with borrowState := sdB s, accts := s.accts.modify who (distB (sdB s).index) }

def speedsOk (s : St) (sup bor : Nat) : Prop :=
  (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
  (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber)

instance (s : St) (a b : Nat) : Decidable (speedsOk s a b) := by
  unfold speedsOk; infer_instance

def speedsNext (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState else { sdS s with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState else { sdB s with speed := bor } }

def specImpl : Impl := fun s c =>
  match c with
  | .supplyHook who => if supplyOk s who then some (supplyNext s who) else none
  | .borrowHook who => if borrowOk s who then some (borrowNext s who) else none
  | .claim who =>
    if borrowOk s who ∧ supplyOk (borrowNext s who) who then
      some (grant (supplyNext (borrowNext s who) who) who)
    else none
  | .setSpeeds a b => if speedsOk s a b then some (speedsNext s a b) else none

theorem supplyDistributed_of (s : St) (who : Account) (h : supplyOk s who) :
    SupplyDistributed s who (supplyNext s who) := ⟨h.1, h.2, rfl⟩

theorem borrowDistributed_of (s : St) (who : Account) (h : borrowOk s who) :
    BorrowDistributed s who (borrowNext s who) := ⟨h.1, h.2, rfl⟩

theorem spec_supply_hook : SupplyHookEffects specImpl := by
  intro s who s' h
  simp only [specImpl] at h
  split at h
  · cases h; exact supplyDistributed_of s who ‹_›
  · contradiction

theorem spec_borrow_hook : BorrowHookEffects specImpl := by
  intro s who s' h
  simp only [specImpl] at h
  split at h
  · cases h; exact borrowDistributed_of s who ‹_›
  · contradiction

theorem spec_claim : ClaimEffects specImpl := by
  intro s who s' h
  simp only [specImpl] at h
  split at h
  · rename_i hc
    cases h
    exact ⟨_, _, borrowDistributed_of s who hc.1, supplyDistributed_of _ who hc.2, rfl⟩
  · contradiction

theorem spec_set_speeds : SetSpeedsEffects specImpl := by
  intro s a b s' h
  simp only [specImpl] at h
  split at h
  · rename_i hc
    cases h
    exact ⟨hc.1, hc.2, rfl⟩
  · contradiction

/-! ## Facts about one side -/

theorem accrue_block (sd : Side) (now T : Nat) : (accrueSide sd now T).block = now := by
  unfold accrueSide; split <;> rfl

theorem accrue_speed (sd : Side) (now T : Nat) : (accrueSide sd now T).speed = sd.speed := by
  unfold accrueSide; split <;> rfl

theorem accrue_index (sd : Side) (now T : Nat) :
    ∃ inc, (accrueSide sd now T).index = sd.index + inc ∧
      T * inc ≤ (now - sd.block) * sd.speed * doubleScale := by
  unfold accrueSide
  split
  · exact ⟨_, rfl, Nat.mul_div_le _ _⟩
  · exact ⟨0, by simp, by simp⟩

theorem accrue_index_ge (sd : Side) (now T : Nat) : sd.index ≤ (accrueSide sd now T).index := by
  obtain ⟨inc, h, -⟩ := accrue_index sd now T
  omega

theorem accrue_current (sd : Side) (now T : Nat) (h : sd.block = now) : accrueSide sd now T = sd := by
  unfold accrueSide
  have : ¬ (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < T) := by omega
  simp only [this, ite_false]
  cases sd; simp_all

theorem accrualStart_le (u idx : Nat) (h : u ≤ idx) : accrualStart u idx ≤ idx := by
  unfold accrualStart
  split
  · split <;> omega
  · exact h

theorem acct_mem_or (s : St) (who : Account) : s.acct who ∈ s.accts ∨ s.acct who = noAcct :=
  getD_mem_or _ _ _

/-! ## REQ-CALLS-SUCCEED -/

theorem consistent_supplier (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  rcases acct_mem_or s who with hm | hm
  · exact (h.2.2 _ hm).1
  · rw [hm]; exact Nat.zero_le _

theorem consistent_borrower (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  rcases acct_mem_or s who with hm | hm
  · exact (h.2.2 _ hm).2
  · rw [hm]; exact Nat.zero_le _

theorem supplyOk_of_consistent (s : St) (who : Account) (h : Consistent s) : supplyOk s who :=
  ⟨h.1, accrualStart_le _ _ (Nat.le_trans (consistent_supplier s who h) (accrue_index_ge _ _ _))⟩

theorem borrowOk_of_consistent (s : St) (who : Account) (h : Consistent s) : borrowOk s who :=
  ⟨h.2.1, accrualStart_le _ _ (Nat.le_trans (consistent_borrower s who h) (accrue_index_ge _ _ _))⟩

theorem borrowNext_supplier (s : St) (who w : Account) :
    ((borrowNext s who).acct w).supplierIndex = (s.acct w).supplierIndex := by
  simp only [borrowNext, St.acct]
  rw [getD_modify]
  split <;> rfl

theorem supplyOk_after_borrow (s : St) (who : Account) (h : Consistent s) :
    supplyOk (borrowNext s who) who := by
  refine ⟨h.1, accrualStart_le _ _ ?_⟩
  rw [borrowNext_supplier]
  exact Nat.le_trans (consistent_supplier s who h) (accrue_index_ge _ _ _)

theorem spec_calls_succeed : CallsSucceed specImpl := by
  intro s c h
  cases c with
  | supplyHook who => simp [specImpl, supplyOk_of_consistent s who h]
  | borrowHook who => simp [specImpl, borrowOk_of_consistent s who h]
  | claim who =>
    simp [specImpl, borrowOk_of_consistent s who h, supplyOk_after_borrow s who h]
  | setSpeeds a b =>
    have : speedsOk s a b := ⟨fun _ => h.1, fun _ => h.2.1⟩
    simp [specImpl, this]


/-! ## Potentials

`gs` and `gb` are the values the supply and borrow indices started from (0 or
`compInitialIndex`). An account's pending rewards, scaled by 1e36, are its units times the index
gained since its start. The global potential is the scaled COMP credited to every account plus
every account's pending rewards plus the scaled COMP emitted and not yet in an index; the
potential of one account counts the unindexed COMP of a side only while it holds a position
there. Neither potential grows except when blocks pass, and then by at most the COMP emitted. -/

def GoodStart (g idx : Nat) : Prop := (g = 0 ∨ g = compInitialIndex) ∧ g ≤ idx

def pendAt (gs gb iS iB : Nat) (a : Acct) : Nat :=
  a.supply * (iS - legacyStart gs a.supplierIndex) + a.borrow * (iB - legacyStart gb a.borrowerIndex)

def term (gs gb iS iB : Nat) (a : Acct) : Nat :=
  (a.accrued + a.wallet) * doubleScale + pendAt gs gb iS iB a

def unS (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
def unB (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def Phi (gs gb : Nat) (s : St) : Nat :=
  (s.accts.map (term gs gb s.supplyState.index s.borrowState.index)).sum +
    doubleScale * (unS s + unB s)

def Psi (gs gb : Nat) (w : Account) (s : St) : Nat :=
  term gs gb s.supplyState.index s.borrowState.index (s.acct w) +
    doubleScale * ((if 0 < (s.acct w).supply then unS s else 0) +
      (if 0 < (s.acct w).borrow then unB s else 0))

def Inv0 (gs gb : Nat) (s : St) : Prop :=
  GoodStart gs s.supplyState.index ∧ GoodStart gb s.borrowState.index ∧
  s.supplyState.block ≤ s.blockNumber ∧ s.borrowState.block ≤ s.blockNumber

def Inv (gs gb : Nat) (sp : Nat × Nat) (s : St) : Prop :=
  Inv0 gs gb s ∧ s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2

/-! ### Arithmetic -/

theorem legacyStart_le_accrualStart (g u idx : Nat) (h : GoodStart g idx) :
    legacyStart g u ≤ accrualStart u idx := by
  unfold legacyStart accrualStart
  obtain ⟨h1, h2⟩ := h
  split
  · split <;> omega
  · exact Nat.le_refl _

theorem sub_legacyStart_self (g idx : Nat) : idx - legacyStart g idx = 0 := by
  unfold legacyStart; split <;> omega

theorem goodStart_mono {g i j : Nat} (h : GoodStart g i) (hij : i ≤ j) : GoodStart g j :=
  ⟨h.1, Nat.le_trans h.2 hij⟩

theorem sum_map_mul {α} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem div_bound (X Y P D : Nat) (hD : 0 < D) (h : X * D ≤ Y * D + P) : X ≤ Y + P / D := by
  by_cases hxy : X ≤ Y
  · exact Nat.le_add_right_of_le hxy
  · have h1 : (X - Y) * D ≤ P := by
      rw [Nat.sub_mul]
      omega
    have h2 : X - Y ≤ P / D := (Nat.le_div_iff_mul_le hD).2 h1
    omega

theorem doubleScale_pos : 0 < doubleScale := by unfold doubleScale; decide

/-! ### Terms of one account -/

theorem term_supply_dist (gs gb iS iB : Nat) (a : Acct) (hg : GoodStart gs iS) :
    term gs gb iS iB (distS iS a) ≤ term gs gb iS iB a := by
  unfold distS
  unfold term pendAt
  simp only
  rw [sub_legacyStart_self, Nat.mul_zero, Nat.zero_add]
  have h1 : creditFor a.supply (accrualStart a.supplierIndex iS) iS * doubleScale ≤
      a.supply * (iS - accrualStart a.supplierIndex iS) := Nat.div_mul_le_self _ _
  have h2 : a.supply * (iS - accrualStart a.supplierIndex iS) ≤
      a.supply * (iS - legacyStart gs a.supplierIndex) :=
    Nat.mul_le_mul_left _ (by have := legacyStart_le_accrualStart gs a.supplierIndex iS hg; omega)
  have h3 : (a.accrued + creditFor a.supply (accrualStart a.supplierIndex iS) iS + a.wallet) * doubleScale =
      (a.accrued + a.wallet) * doubleScale + creditFor a.supply (accrualStart a.supplierIndex iS) iS * doubleScale := by
    rw [← Nat.add_mul]; congr 1; omega
  omega

theorem term_borrow_dist (gs gb iS iB : Nat) (a : Acct) (hg : GoodStart gb iB) :
    term gs gb iS iB (distB iB a) ≤ term gs gb iS iB a := by
  unfold distB
  unfold term pendAt
  simp only
  rw [sub_legacyStart_self gb iB, Nat.mul_zero, Nat.add_zero]
  have h1 : creditFor a.borrow (accrualStart a.borrowerIndex iB) iB * doubleScale ≤
      a.borrow * (iB - accrualStart a.borrowerIndex iB) := Nat.div_mul_le_self _ _
  have h2 : a.borrow * (iB - accrualStart a.borrowerIndex iB) ≤
      a.borrow * (iB - legacyStart gb a.borrowerIndex) :=
    Nat.mul_le_mul_left _ (by have := legacyStart_le_accrualStart gb a.borrowerIndex iB hg; omega)
  have h3 : (a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex iB) iB + a.wallet) * doubleScale =
      (a.accrued + a.wallet) * doubleScale + creditFor a.borrow (accrualStart a.borrowerIndex iB) iB * doubleScale := by
    rw [← Nat.add_mul]; congr 1; omega
  omega

theorem term_supply_inc (gs gb iS iB inc : Nat) (a : Acct) :
    term gs gb (iS + inc) iB a ≤ term gs gb iS iB a + a.supply * inc := by
  unfold term pendAt
  have : a.supply * (iS + inc - legacyStart gs a.supplierIndex) ≤
      a.supply * (iS - legacyStart gs a.supplierIndex) + a.supply * inc := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  omega

theorem term_borrow_inc (gs gb iS iB inc : Nat) (a : Acct) :
    term gs gb iS (iB + inc) a ≤ term gs gb iS iB a + a.borrow * inc := by
  unfold term pendAt
  have : a.borrow * (iB + inc - legacyStart gb a.borrowerIndex) ≤
      a.borrow * (iB - legacyStart gb a.borrowerIndex) + a.borrow * inc := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  omega

theorem term_grant (gs gb iS iB : Nat) (a : Acct) :
    term gs gb iS iB { a with accrued := 0, wallet := a.wallet + a.accrued } = term gs gb iS iB a := by
  unfold term pendAt
  simp only
  congr 2
  omega

theorem term_supply_bal (gs gb iS iB : Nat) (a : Acct) (g : Nat → Nat) (h : a.supplierIndex = iS) :
    term gs gb iS iB { a with supply := g a.supply } = term gs gb iS iB a := by
  unfold term pendAt
  simp only
  rw [h, sub_legacyStart_self, Nat.mul_zero, Nat.mul_zero]

theorem term_borrow_bal (gs gb iS iB : Nat) (a : Acct) (g : Nat → Nat) (h : a.borrowerIndex = iB) :
    term gs gb iS iB { a with borrow := g a.borrow } = term gs gb iS iB a := by
  unfold term pendAt
  simp only
  rw [h, sub_legacyStart_self gb iB, Nat.mul_zero, Nat.mul_zero]

theorem credited_le_term (gs gb iS iB : Nat) (a : Acct) :
    (a.accrued + a.wallet) * doubleScale ≤ term gs gb iS iB a := by
  unfold term; omega


/-! ### The potentials on each step of a call -/

theorem acct_supplyNext (s : St) (who w : Account) :
    (supplyNext s who).acct w =
      if who = w ∧ w < s.accts.length then distS (sdS s).index (s.acct w) else s.acct w := by
  simp only [supplyNext, St.acct]; rw [getD_modify]

theorem acct_borrowNext (s : St) (who w : Account) :
    (borrowNext s who).acct w =
      if who = w ∧ w < s.accts.length then distB (sdB s).index (s.acct w) else s.acct w := by
  simp only [borrowNext, St.acct]; rw [getD_modify]

theorem unS_sdS (s : St) (x : St) (h : x.supplyState = sdS s) (hb : x.blockNumber = s.blockNumber) :
    unS x = 0 := by
  unfold unS; rw [h, hb]; simp [sdS, accrue_block]

theorem unB_sdB (s : St) (x : St) (h : x.borrowState = sdB s) (hb : x.blockNumber = s.blockNumber) :
    unB x = 0 := by
  unfold unB; rw [h, hb]; simp [sdB, accrue_block]

theorem inc_le_unS (s : St) (inc : Nat)
    (hinc : totalSupply s * inc ≤ (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale) :
    totalSupply s * inc ≤ doubleScale * unS s := by
  unfold unS; rw [Nat.mul_comm doubleScale]; exact hinc

theorem inc_le_unB (s : St) (inc : Nat)
    (hinc : totalBorrows s * inc ≤ (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale) :
    totalBorrows s * inc ≤ doubleScale * unB s := by
  unfold unB; rw [Nat.mul_comm doubleScale]; exact hinc

/-- Accruing the supply side: the global potential does not grow. `f` is any change of the
records that does not raise any term at the new index. -/
theorem phi_accrueS (gs gb : Nat) (s : St) (x : St) (hx1 : x.supplyState.index = (sdS s).index)
    (hx2 : x.borrowState = s.borrowState) (hx3 : unS x = 0) (hx4 : unB x = unB s)
    (hacc : (x.accts.map (term gs gb (sdS s).index s.borrowState.index)).sum ≤
      (s.accts.map (term gs gb (sdS s).index s.borrowState.index)).sum) :
    Phi gs gb x ≤ Phi gs gb s := by
  obtain ⟨inc, hidx, hinc⟩ := accrue_index s.supplyState s.blockNumber (totalSupply s)
  have h2 : (s.accts.map (term gs gb (sdS s).index s.borrowState.index)).sum ≤
      (s.accts.map (term gs gb s.supplyState.index s.borrowState.index)).sum +
        (s.accts.map fun a => a.supply * inc).sum := by
    rw [show (sdS s).index = s.supplyState.index + inc from hidx]
    exact sum_le_add _ _ _ _ (fun a => term_supply_inc _ _ _ _ _ a)
  have h3 : (s.accts.map fun a => a.supply * inc).sum = totalSupply s * inc := sum_map_mul _ _ _
  have h6 := inc_le_unS s inc hinc
  unfold Phi
  rw [hx1, hx2, hx3, hx4, Nat.mul_add, Nat.mul_add]
  omega

theorem phi_accrueB (gs gb : Nat) (s : St) (x : St) (hx1 : x.borrowState.index = (sdB s).index)
    (hx2 : x.supplyState = s.supplyState) (hx3 : unB x = 0) (hx4 : unS x = unS s)
    (hacc : (x.accts.map (term gs gb s.supplyState.index (sdB s).index)).sum ≤
      (s.accts.map (term gs gb s.supplyState.index (sdB s).index)).sum) :
    Phi gs gb x ≤ Phi gs gb s := by
  obtain ⟨inc, hidx, hinc⟩ := accrue_index s.borrowState s.blockNumber (totalBorrows s)
  have h2 : (s.accts.map (term gs gb s.supplyState.index (sdB s).index)).sum ≤
      (s.accts.map (term gs gb s.supplyState.index s.borrowState.index)).sum +
        (s.accts.map fun a => a.borrow * inc).sum := by
    rw [show (sdB s).index = s.borrowState.index + inc from hidx]
    exact sum_le_add _ _ _ _ (fun a => term_borrow_inc _ _ _ _ _ a)
  have h3 : (s.accts.map fun a => a.borrow * inc).sum = totalBorrows s * inc := sum_map_mul _ _ _
  have h6 := inc_le_unB s inc hinc
  unfold Phi
  rw [hx1, hx2, hx3, hx4, Nat.mul_add, Nat.mul_add]
  omega

theorem phi_supplyNext (gs gb : Nat) (s : St) (who : Account) (hI : Inv0 gs gb s) :
    Phi gs gb (supplyNext s who) ≤ Phi gs gb s := by
  have hg : GoodStart gs (sdS s).index := goodStart_mono hI.1 (accrue_index_ge _ _ _)
  exact phi_accrueS gs gb s _ rfl rfl (unS_sdS s _ rfl rfl) rfl
    (sum_modify_le _ _ _ _ noAcct (fun _ => term_supply_dist _ _ _ _ _ hg))

theorem phi_borrowNext (gs gb : Nat) (s : St) (who : Account) (hI : Inv0 gs gb s) :
    Phi gs gb (borrowNext s who) ≤ Phi gs gb s := by
  have hg : GoodStart gb (sdB s).index := goodStart_mono hI.2.1 (accrue_index_ge _ _ _)
  exact phi_accrueB gs gb s _ rfl rfl (unB_sdB s _ rfl rfl) rfl
    (sum_modify_le _ _ _ _ noAcct (fun _ => term_borrow_dist _ _ _ _ _ hg))

/-- Accruing the supply side, for the potential of one account. -/
theorem psi_accrueS (gs gb : Nat) (w : Account) (s : St) (x : St)
    (hx1 : x.supplyState.index = (sdS s).index) (hx2 : x.borrowState = s.borrowState)
    (hx3 : unS x = 0) (hx4 : unB x = unB s)
    (hsup : (x.acct w).supply = (s.acct w).supply) (hbor : (x.acct w).borrow = (s.acct w).borrow)
    (ht : term gs gb (sdS s).index s.borrowState.index (x.acct w) ≤
      term gs gb (sdS s).index s.borrowState.index (s.acct w)) :
    Psi gs gb w x ≤ Psi gs gb w s := by
  obtain ⟨inc, hidx, hinc⟩ := accrue_index s.supplyState s.blockNumber (totalSupply s)
  have ht2 : term gs gb (sdS s).index s.borrowState.index (s.acct w) ≤
      term gs gb s.supplyState.index s.borrowState.index (s.acct w) + (s.acct w).supply * inc := by
    rw [show (sdS s).index = s.supplyState.index + inc from hidx]; exact term_supply_inc _ _ _ _ _ _
  have hle : (s.acct w).supply ≤ totalSupply s := getD_le_sum s.accts w noAcct Acct.supply rfl
  have h6 := inc_le_unS s inc hinc
  have key : (s.acct w).supply * inc ≤
      doubleScale * (if 0 < (s.acct w).supply then unS s else 0) := by
    split
    · exact Nat.le_trans (Nat.mul_le_mul_right _ hle) h6
    · have : (s.acct w).supply = 0 := by omega
      simp [this]
  unfold Psi
  rw [hx1, hx2, hx3, hx4, hsup, hbor, ite_self, Nat.mul_add, Nat.mul_add, Nat.mul_zero]
  omega

theorem psi_accrueB (gs gb : Nat) (w : Account) (s : St) (x : St)
    (hx1 : x.borrowState.index = (sdB s).index) (hx2 : x.supplyState = s.supplyState)
    (hx3 : unB x = 0) (hx4 : unS x = unS s)
    (hsup : (x.acct w).supply = (s.acct w).supply) (hbor : (x.acct w).borrow = (s.acct w).borrow)
    (ht : term gs gb s.supplyState.index (sdB s).index (x.acct w) ≤
      term gs gb s.supplyState.index (sdB s).index (s.acct w)) :
    Psi gs gb w x ≤ Psi gs gb w s := by
  obtain ⟨inc, hidx, hinc⟩ := accrue_index s.borrowState s.blockNumber (totalBorrows s)
  have ht2 : term gs gb s.supplyState.index (sdB s).index (s.acct w) ≤
      term gs gb s.supplyState.index s.borrowState.index (s.acct w) + (s.acct w).borrow * inc := by
    rw [show (sdB s).index = s.borrowState.index + inc from hidx]; exact term_borrow_inc _ _ _ _ _ _
  have hle : (s.acct w).borrow ≤ totalBorrows s := getD_le_sum s.accts w noAcct Acct.borrow rfl
  have h6 := inc_le_unB s inc hinc
  have key : (s.acct w).borrow * inc ≤
      doubleScale * (if 0 < (s.acct w).borrow then unB s else 0) := by
    split
    · exact Nat.le_trans (Nat.mul_le_mul_right _ hle) h6
    · have : (s.acct w).borrow = 0 := by omega
      simp [this]
  unfold Psi
  rw [hx1, hx2, hx3, hx4, hsup, hbor, ite_self, Nat.mul_add, Nat.mul_add, Nat.mul_zero]
  omega

theorem psi_supplyNext (gs gb : Nat) (w : Account) (s : St) (who : Account) (hI : Inv0 gs gb s) :
    Psi gs gb w (supplyNext s who) ≤ Psi gs gb w s := by
  have hg : GoodStart gs (sdS s).index := goodStart_mono hI.1 (accrue_index_ge _ _ _)
  have ha := acct_supplyNext s who w
  refine psi_accrueS gs gb w s (supplyNext s who) rfl rfl (unS_sdS s _ rfl rfl) rfl ?_ ?_ ?_
  · rw [ha]; split <;> rfl
  · rw [ha]; split <;> rfl
  · rw [ha]; split
    · exact term_supply_dist _ _ _ _ _ hg
    · exact Nat.le_refl _

theorem psi_borrowNext (gs gb : Nat) (w : Account) (s : St) (who : Account) (hI : Inv0 gs gb s) :
    Psi gs gb w (borrowNext s who) ≤ Psi gs gb w s := by
  have hg : GoodStart gb (sdB s).index := goodStart_mono hI.2.1 (accrue_index_ge _ _ _)
  have ha := acct_borrowNext s who w
  refine psi_accrueB gs gb w s (borrowNext s who) rfl rfl (unB_sdB s _ rfl rfl) rfl ?_ ?_ ?_
  · rw [ha]; split <;> rfl
  · rw [ha]; split <;> rfl
  · rw [ha]; split
    · exact term_borrow_dist _ _ _ _ _ hg
    · exact Nat.le_refl _


theorem acct_grant (s : St) (who w : Account) (h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    (grant s who).acct w =
      if who = w ∧ w < s.accts.length then
        { (s.acct w) with accrued := 0, wallet := (s.acct w).wallet + (s.acct w).accrued }
      else s.acct w := by
  unfold grant
  rw [if_pos h]
  simp only [St.acct]; rw [getD_modify]

theorem phi_grant (gs gb : Nat) (s : St) (who : Account) : Phi gs gb (grant s who) ≤ Phi gs gb s := by
  unfold grant
  split
  · unfold Phi
    rw [sum_modify_eq _ _ _ _ noAcct (fun _ => term_grant _ _ _ _ _)]
    exact Nat.le_refl _
  · exact Nat.le_refl _

theorem psi_grant (gs gb : Nat) (w : Account) (s : St) (who : Account) :
    Psi gs gb w (grant s who) ≤ Psi gs gb w s := by
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · have ha := acct_grant s who w h
    have hs : (grant s who).supplyState = s.supplyState := by unfold grant; rw [if_pos h]
    have hb : (grant s who).borrowState = s.borrowState := by unfold grant; rw [if_pos h]
    have hn : (grant s who).blockNumber = s.blockNumber := by unfold grant; rw [if_pos h]
    have hu1 : unS (grant s who) = unS s := by unfold unS; rw [hs, hn]
    have hu2 : unB (grant s who) = unB s := by unfold unB; rw [hb, hn]
    unfold Psi
    rw [ha, hs, hb, hu1, hu2]
    split
    · rw [term_grant]; exact Nat.le_refl _
    · exact Nat.le_refl _
  · unfold grant; rw [if_neg h]; exact Nat.le_refl _

theorem phi_supplyBal (gs gb : Nat) (s : St) (w : Account) (g : Nat → Nat)
    (hu : (s.acct w).supplierIndex = s.supplyState.index) :
    Phi gs gb (s.withAcct w fun a => { a with supply := g a.supply }) ≤ Phi gs gb s := by
  unfold Phi St.withAcct
  rw [sum_modify_eq _ _ _ _ noAcct (fun _ => term_supply_bal _ _ _ _ _ g hu)]
  exact Nat.le_refl _

theorem phi_borrowBal (gs gb : Nat) (s : St) (w : Account) (g : Nat → Nat)
    (hu : (s.acct w).borrowerIndex = s.borrowState.index) :
    Phi gs gb (s.withAcct w fun a => { a with borrow := g a.borrow }) ≤ Phi gs gb s := by
  unfold Phi St.withAcct
  rw [sum_modify_eq _ _ _ _ noAcct (fun _ => term_borrow_bal _ _ _ _ _ g hu)]
  exact Nat.le_refl _

theorem acct_withAcct (s : St) (w v : Account) (f : Acct → Acct) :
    (s.withAcct w f).acct v = if w = v ∧ v < s.accts.length then f (s.acct v) else s.acct v := by
  simp only [St.withAcct, St.acct]; rw [getD_modify]

theorem psi_supplyBal (gs gb : Nat) (v : Account) (s : St) (w : Account) (g : Nat → Nat)
    (hu : (s.acct w).supplierIndex = s.supplyState.index) (hb : s.supplyState.block = s.blockNumber) :
    Psi gs gb v (s.withAcct w fun a => { a with supply := g a.supply }) ≤ Psi gs gb v s := by
  have h0 : unS s = 0 := by unfold unS; rw [hb]; simp
  have hu1 : unS (s.withAcct w fun a => { a with supply := g a.supply }) = unS s := rfl
  have hu2 : unB (s.withAcct w fun a => { a with supply := g a.supply }) = unB s := rfl
  unfold Psi
  rw [acct_withAcct, hu1, hu2]
  simp only [St.withAcct]
  split
  · rename_i h
    obtain ⟨hwv, -⟩ := h
    subst hwv
    rw [term_supply_bal gs gb s.supplyState.index s.borrowState.index (s.acct w) g hu, h0, ite_self, ite_self]
    exact Nat.le_refl _
  · exact Nat.le_refl _

theorem psi_borrowBal (gs gb : Nat) (v : Account) (s : St) (w : Account) (g : Nat → Nat)
    (hu : (s.acct w).borrowerIndex = s.borrowState.index) (hb : s.borrowState.block = s.blockNumber) :
    Psi gs gb v (s.withAcct w fun a => { a with borrow := g a.borrow }) ≤ Psi gs gb v s := by
  have h0 : unB s = 0 := by unfold unB; rw [hb]; simp
  have hu1 : unS (s.withAcct w fun a => { a with borrow := g a.borrow }) = unS s := rfl
  have hu2 : unB (s.withAcct w fun a => { a with borrow := g a.borrow }) = unB s := rfl
  unfold Psi
  rw [acct_withAcct, hu1, hu2]
  simp only [St.withAcct]
  split
  · rename_i h
    obtain ⟨hwv, -⟩ := h
    subst hwv
    rw [term_borrow_bal gs gb s.supplyState.index s.borrowState.index (s.acct w) g hu, h0, ite_self, ite_self]
    exact Nat.le_refl _
  · exact Nat.le_refl _

/-! ### Speed changes -/

def setS (s : St) (a : Nat) : St :=
  if s.supplyState.speed = a then s else { s with supplyState := { sdS s with speed := a } }

def setB (s : St) (b : Nat) : St :=
  if s.borrowState.speed = b then s else { s with borrowState := { sdB s with speed := b } }

theorem speedsNext_eq (s : St) (a b : Nat) : speedsNext s a b = setB (setS s a) b := by
  unfold speedsNext setS setB
  by_cases h1 : s.supplyState.speed = a <;> by_cases h2 : s.borrowState.speed = b <;>
    simp only [h1, h2, ite_true, ite_false] <;> rfl

theorem unS_setS (s : St) (a : Nat) (h : s.supplyState.speed ≠ a) :
    unS { s with supplyState := { sdS s with speed := a } } = 0 := by
  unfold unS; simp [sdS, accrue_block]

theorem unB_setB (s : St) (b : Nat) :
    unB { s with borrowState := { sdB s with speed := b } } = 0 := by
  unfold unB; simp [sdB, accrue_block]

theorem phi_setS (gs gb : Nat) (s : St) (a : Nat) : Phi gs gb (setS s a) ≤ Phi gs gb s := by
  unfold setS
  split
  · exact Nat.le_refl _
  · rename_i h
    exact phi_accrueS gs gb s _ rfl rfl (unS_setS s a h) rfl (Nat.le_refl _)

theorem phi_setB (gs gb : Nat) (s : St) (b : Nat) : Phi gs gb (setB s b) ≤ Phi gs gb s := by
  unfold setB
  split
  · exact Nat.le_refl _
  · exact phi_accrueB gs gb s _ rfl rfl (unB_setB s b) rfl (Nat.le_refl _)

theorem psi_setS (gs gb : Nat) (w : Account) (s : St) (a : Nat) : Psi gs gb w (setS s a) ≤ Psi gs gb w s := by
  unfold setS
  split
  · exact Nat.le_refl _
  · rename_i h
    exact psi_accrueS gs gb w s _ rfl rfl (unS_setS s a h) rfl rfl rfl (Nat.le_refl _)

theorem psi_setB (gs gb : Nat) (w : Account) (s : St) (b : Nat) : Psi gs gb w (setB s b) ≤ Psi gs gb w s := by
  unfold setB
  split
  · exact Nat.le_refl _
  · exact psi_accrueB gs gb w s _ rfl rfl (unB_setB s b) rfl rfl rfl (Nat.le_refl _)

/-! ### Blocks passing and COMP sent to the Comptroller -/

theorem un_advance (n b sp k : Nat) (h : b ≤ n) : (n + k - b) * sp = (n - b) * sp + k * sp := by
  rw [Nat.sub_add_comm h, Nat.add_mul]

theorem phi_advance (gs gb : Nat) (s : St) (k : Nat) (h1 : s.supplyState.block ≤ s.blockNumber)
    (h2 : s.borrowState.block ≤ s.blockNumber) :
    Phi gs gb { s with blockNumber := s.blockNumber + k } ≤
      Phi gs gb s + doubleScale * (k * (s.supplyState.speed + s.borrowState.speed)) := by
  unfold Phi unS unB
  simp only
  rw [un_advance _ _ _ _ h1, un_advance _ _ _ _ h2]
  rw [Nat.mul_add k, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  omega

theorem ite_add_le (c : Prop) [Decidable c] (x y : Nat) :
    (if c then x + y else 0) ≤ (if c then x else 0) + y := by
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

theorem mul_add_add (D X Y u v : Nat) : D * ((X + u) + (Y + v)) = D * (X + Y) + D * (u + v) := by
  rw [← Nat.mul_add]; congr 1; omega

theorem psi_advance (gs gb : Nat) (w : Account) (s : St) (k : Nat) (h1 : s.supplyState.block ≤ s.blockNumber)
    (h2 : s.borrowState.block ≤ s.blockNumber) :
    Psi gs gb w { s with blockNumber := s.blockNumber + k } ≤
      Psi gs gb w s + doubleScale * (k * (s.supplyState.speed + s.borrowState.speed)) := by
  have ha : ({ s with blockNumber := s.blockNumber + k } : St).acct w = s.acct w := rfl
  unfold Psi unS unB
  rw [ha]
  dsimp only
  rw [un_advance _ _ _ _ h1, un_advance _ _ _ _ h2, Nat.mul_add k]
  have e1 := ite_add_le (0 < (s.acct w).supply)
    ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (k * s.supplyState.speed)
  have e2 := ite_add_le (0 < (s.acct w).borrow)
    ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (k * s.borrowState.speed)
  have e3 := Nat.mul_le_mul_left doubleScale (Nat.add_le_add e1 e2)
  rw [mul_add_add] at e3
  omega

theorem phi_drip (gs gb : Nat) (s : St) (x : Nat) : Phi gs gb { s with reserve := s.reserve + x } ≤ Phi gs gb s :=
  Nat.le_refl _

theorem psi_drip (gs gb : Nat) (w : Account) (s : St) (x : Nat) :
    Psi gs gb w { s with reserve := s.reserve + x } ≤ Psi gs gb w s :=
  Nat.le_refl _

/-! ### The invariant -/

theorem inv_supplyNext (gs gb : Nat) (sp : Nat × Nat) (s : St) (who : Account) (h : Inv gs gb sp s) :
    Inv gs gb sp (supplyNext s who) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := h
  refine ⟨⟨goodStart_mono h1 (accrue_index_ge _ _ _), h2, ?_, h4⟩, ?_, h6⟩
  · show (sdS s).block ≤ s.blockNumber; simp [sdS, accrue_block]
  · show (sdS s).speed = sp.1; simp [sdS, accrue_speed, h5]

theorem inv_borrowNext (gs gb : Nat) (sp : Nat × Nat) (s : St) (who : Account) (h : Inv gs gb sp s) :
    Inv gs gb sp (borrowNext s who) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := h
  refine ⟨⟨h1, goodStart_mono h2 (accrue_index_ge _ _ _), h3, ?_⟩, h5, ?_⟩
  · show (sdB s).block ≤ s.blockNumber; simp [sdB, accrue_block]
  · show (sdB s).speed = sp.2; simp [sdB, accrue_speed, h6]

theorem grant_sides (s : St) (who : Account) :
    (grant s who).supplyState = s.supplyState ∧ (grant s who).borrowState = s.borrowState ∧
      (grant s who).blockNumber = s.blockNumber := by
  unfold grant; split <;> exact ⟨rfl, rfl, rfl⟩

theorem inv_grant (gs gb : Nat) (sp : Nat × Nat) (s : St) (who : Account) (h : Inv gs gb sp s) :
    Inv gs gb sp (grant s who) := by
  obtain ⟨e1, e2, e3⟩ := grant_sides s who
  unfold Inv Inv0 at *
  rw [e1, e2, e3]; exact h

theorem inv_withAcct (gs gb : Nat) (sp : Nat × Nat) (s : St) (w : Account) (f : Acct → Acct)
    (h : Inv gs gb sp s) : Inv gs gb sp (s.withAcct w f) := h

theorem inv_speeds (gs gb : Nat) (sp : Nat × Nat) (s : St) (a b : Nat) (h : Inv gs gb sp s) :
    Inv gs gb (a, b) (speedsNext s a b) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := h
  unfold speedsNext
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp only
  · split
    · exact h1
    · exact goodStart_mono h1 (accrue_index_ge _ _ _)
  · split
    · exact h2
    · exact goodStart_mono h2 (accrue_index_ge _ _ _)
  · split
    · exact h3
    · simp [sdS, accrue_block]
  · split
    · exact h4
    · simp [sdB, accrue_block]
  · split
    · assumption
    · rfl
  · split
    · assumption
    · rfl

theorem speedsOk_of_inv (gs gb : Nat) (sp : Nat × Nat) (s : St) (a b : Nat) (h : Inv gs gb sp s) :
    speedsOk s a b := ⟨fun _ => h.1.2.2.1, fun _ => h.1.2.2.2⟩


/-! ### One operation, then a run -/

structure PotOK (gs gb : Nat) (P : St → Nat) : Prop where
  supply : ∀ s who, Inv0 gs gb s → P (supplyNext s who) ≤ P s
  borrow : ∀ s who, Inv0 gs gb s → P (borrowNext s who) ≤ P s
  grant : ∀ s who, P (grant s who) ≤ P s
  supplyBal : ∀ s w (g : Nat → Nat), (s.acct w).supplierIndex = s.supplyState.index →
    s.supplyState.block = s.blockNumber → P (s.withAcct w fun a => { a with supply := g a.supply }) ≤ P s
  borrowBal : ∀ s w (g : Nat → Nat), (s.acct w).borrowerIndex = s.borrowState.index →
    s.borrowState.block = s.blockNumber → P (s.withAcct w fun a => { a with borrow := g a.borrow }) ≤ P s
  setS : ∀ s a, P (setS s a) ≤ P s
  setB : ∀ s b, P (setB s b) ≤ P s
  advance : ∀ s k, s.supplyState.block ≤ s.blockNumber → s.borrowState.block ≤ s.blockNumber →
    P { s with blockNumber := s.blockNumber + k } ≤
      P s + doubleScale * (k * (s.supplyState.speed + s.borrowState.speed))
  drip : ∀ s x, P { s with reserve := s.reserve + x } ≤ P s

theorem phi_ok (gs gb : Nat) : PotOK gs gb (Phi gs gb) :=
  ⟨phi_supplyNext gs gb, phi_borrowNext gs gb, phi_grant gs gb,
   fun s w g hu _ => phi_supplyBal gs gb s w g hu, fun s w g hu _ => phi_borrowBal gs gb s w g hu,
   phi_setS gs gb, phi_setB gs gb, phi_advance gs gb, phi_drip gs gb⟩

theorem psi_ok (gs gb : Nat) (v : Account) : PotOK gs gb (Psi gs gb v) :=
  ⟨fun s who h => psi_supplyNext gs gb v s who h, fun s who h => psi_borrowNext gs gb v s who h,
   fun s who => psi_grant gs gb v s who,
   fun s w g hu hb => psi_supplyBal gs gb v s w g hu hb, fun s w g hu hb => psi_borrowBal gs gb v s w g hu hb,
   psi_setS gs gb v, psi_setB gs gb v, psi_advance gs gb v, psi_drip gs gb v⟩

theorem supplyNext_length (s : St) (who : Account) : (supplyNext s who).accts.length = s.accts.length :=
  List.length_modify _ _ _

theorem borrowNext_length (s : St) (who : Account) : (borrowNext s who).accts.length = s.accts.length :=
  List.length_modify _ _ _

theorem supplyNext_self (s : St) (who : Account) (h : who < s.accts.length) :
    ((supplyNext s who).acct who).supplierIndex = (supplyNext s who).supplyState.index := by
  rw [acct_supplyNext, if_pos ⟨rfl, h⟩]; rfl

theorem borrowNext_self (s : St) (who : Account) (h : who < s.accts.length) :
    ((borrowNext s who).acct who).borrowerIndex = (borrowNext s who).borrowState.index := by
  rw [acct_borrowNext, if_pos ⟨rfl, h⟩]; rfl

theorem supplyNext_current (s : St) (who : Account) :
    (supplyNext s who).supplyState.block = (supplyNext s who).blockNumber := by
  show (sdS s).block = s.blockNumber; simp [sdS, accrue_block]

theorem borrowNext_current (s : St) (who : Account) :
    (borrowNext s who).borrowState.block = (borrowNext s who).blockNumber := by
  show (sdB s).block = s.blockNumber; simp [sdB, accrue_block]

/-- After the supply hooks of a transfer, both accounts are up to date. -/
theorem transfer_facts (s : St) (src dst : Account) (hs : src < s.accts.length)
    (hd : dst < s.accts.length) (hne : src ≠ dst) :
    let s₂ := supplyNext (supplyNext s src) dst
    (s₂.acct src).supplierIndex = s₂.supplyState.index ∧ s₂.supplyState.block = s₂.blockNumber ∧
    (s₂.acct dst).supplierIndex = s₂.supplyState.index := by
  intro s₂
  have hcur : (supplyNext s src).supplyState.block = (supplyNext s src).blockNumber :=
    supplyNext_current s src
  have hidx : s₂.supplyState.index = (supplyNext s src).supplyState.index := by
    show (sdS (supplyNext s src)).index = _
    unfold sdS; rw [accrue_current _ _ _ hcur]
  refine ⟨?_, supplyNext_current _ _, ?_⟩
  · show ((supplyNext (supplyNext s src) dst).acct src).supplierIndex = _
    rw [acct_supplyNext, if_neg (fun h => hne h.1.symm), hidx]
    exact supplyNext_self s src hs
  · exact supplyNext_self _ dst (by rw [supplyNext_length]; exact hd)

theorem exec_inv (gs gb : Nat) (sp : Nat × Nat) (s : St) (hI : Inv gs gb sp s) (op : Op) :
    Inv gs gb (nextSpeeds sp op) (exec specImpl s op) := by
  cases op with
  | mint who x =>
    simp only [exec, nextSpeeds]
    split
    · by_cases hok : supplyOk s who
      · simp only [specImpl, hok, ite_true]
        exact inv_withAcct _ _ _ _ _ _ (inv_supplyNext _ _ _ _ _ hI)
      · simp only [specImpl, hok, ite_false]; exact hI
    · exact hI
  | redeem who x =>
    simp only [exec, nextSpeeds]
    split
    · by_cases hok : supplyOk s who
      · simp only [specImpl, hok, ite_true]
        split
        · exact inv_withAcct _ _ _ _ _ _ (inv_supplyNext _ _ _ _ _ hI)
        · exact hI
      · simp only [specImpl, hok, ite_false]; exact hI
    · exact hI
  | transfer src dst x =>
    simp only [exec, nextSpeeds]
    split
    · by_cases hok : supplyOk s src
      · by_cases hok2 : supplyOk (supplyNext s src) dst
        · simp only [specImpl, hok, hok2, ite_true]
          split
          · exact inv_withAcct _ _ _ _ _ _ (inv_withAcct _ _ _ _ _ _
              (inv_supplyNext _ _ _ _ _ (inv_supplyNext _ _ _ _ _ hI)))
          · exact hI
        · simp only [specImpl, hok, hok2, ite_true, ite_false]; exact hI
      · simp only [specImpl, hok, ite_false]; exact hI
    · exact hI
  | borrow who x =>
    simp only [exec, nextSpeeds]
    split
    · by_cases hok : borrowOk s who
      · simp only [specImpl, hok, ite_true]
        exact inv_withAcct _ _ _ _ _ _ (inv_borrowNext _ _ _ _ _ hI)
      · simp only [specImpl, hok, ite_false]; exact hI
    · exact hI
  | repay who x =>
    simp only [exec, nextSpeeds]
    split
    · by_cases hok : borrowOk s who
      · simp only [specImpl, hok, ite_true]
        split
        · exact inv_withAcct _ _ _ _ _ _ (inv_borrowNext _ _ _ _ _ hI)
        · exact hI
      · simp only [specImpl, hok, ite_false]; exact hI
    · exact hI
  | claim who =>
    simp only [exec, nextSpeeds]
    by_cases hc : borrowOk s who ∧ supplyOk (borrowNext s who) who
    · simp only [specImpl, hc, and_self, ite_true, Option.getD_some]
      exact inv_grant _ _ _ _ _ (inv_supplyNext _ _ _ _ _ (inv_borrowNext _ _ _ _ _ hI))
    · simp only [specImpl, hc, ite_false, Option.getD_none]; exact hI
  | setSpeeds a b =>
    simp only [exec, nextSpeeds, specImpl, speedsOk_of_inv gs gb sp s a b hI, ite_true, Option.getD_some]
    exact inv_speeds _ _ _ _ _ _ hI
  | advance k =>
    simp only [exec, nextSpeeds]
    obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := hI
    exact ⟨⟨h1, h2, Nat.le_trans h3 (Nat.le_add_right _ _), Nat.le_trans h4 (Nat.le_add_right _ _)⟩, h5, h6⟩
  | drip x =>
    simp only [exec, nextSpeeds]
    exact hI

theorem exec_pot (gs gb : Nat) (P : St → Nat) (hP : PotOK gs gb P) (sp : Nat × Nat) (s : St)
    (hI : Inv gs gb sp s) (op : Op) :
    P (exec specImpl s op) ≤ P s + doubleScale * emittedBy sp op := by
  cases op with
  | mint who x =>
    simp only [exec, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hlt
      by_cases hok : supplyOk s who
      · simp only [specImpl, hok, ite_true]
        exact Nat.le_trans (hP.supplyBal _ who (fun y => y + x) (supplyNext_self s who hlt)
          (supplyNext_current s who)) (hP.supply s who hI.1)
      · simp only [specImpl, hok, ite_false]; exact Nat.le_refl _
    · exact Nat.le_refl _
  | redeem who x =>
    simp only [exec, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hlt
      by_cases hok : supplyOk s who
      · simp only [specImpl, hok, ite_true]
        split
        · exact Nat.le_trans (hP.supplyBal _ who (fun y => y - x) (supplyNext_self s who hlt)
            (supplyNext_current s who)) (hP.supply s who hI.1)
        · exact Nat.le_refl _
      · simp only [specImpl, hok, ite_false]; exact Nat.le_refl _
    · exact Nat.le_refl _
  | transfer src dst x =>
    simp only [exec, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hc
      obtain ⟨hs, hd, hne⟩ := hc
      by_cases hok : supplyOk s src
      · by_cases hok2 : supplyOk (supplyNext s src) dst
        · simp only [specImpl, hok, hok2, ite_true]
          split
          · obtain ⟨f1, f2, f3⟩ := transfer_facts s src dst hs hd hne
            have hI1 : Inv0 gs gb (supplyNext s src) := (inv_supplyNext _ _ _ _ _ hI).1
            have e3 : ((supplyNext (supplyNext s src) dst).withAcct src
                fun a => { a with supply := a.supply - x }).acct dst =
                (supplyNext (supplyNext s src) dst).acct dst := by
              rw [acct_withAcct, if_neg (fun h => hne h.1)]
            refine Nat.le_trans (hP.supplyBal _ dst (fun y => y + x) ?_ f2) ?_
            · rw [e3]; exact f3
            · refine Nat.le_trans (hP.supplyBal _ src (fun y => y - x) f1 f2) ?_
              exact Nat.le_trans (hP.supply _ dst hI1) (hP.supply s src hI.1)
          · exact Nat.le_refl _
        · simp only [specImpl, hok, hok2, ite_true, ite_false]; exact Nat.le_refl _
      · simp only [specImpl, hok, ite_false]; exact Nat.le_refl _
    · exact Nat.le_refl _
  | borrow who x =>
    simp only [exec, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hlt
      by_cases hok : borrowOk s who
      · simp only [specImpl, hok, ite_true]
        exact Nat.le_trans (hP.borrowBal _ who (fun y => y + x) (borrowNext_self s who hlt)
          (borrowNext_current s who)) (hP.borrow s who hI.1)
      · simp only [specImpl, hok, ite_false]; exact Nat.le_refl _
    · exact Nat.le_refl _
  | repay who x =>
    simp only [exec, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hlt
      by_cases hok : borrowOk s who
      · simp only [specImpl, hok, ite_true]
        split
        · exact Nat.le_trans (hP.borrowBal _ who (fun y => y - x) (borrowNext_self s who hlt)
            (borrowNext_current s who)) (hP.borrow s who hI.1)
        · exact Nat.le_refl _
      · simp only [specImpl, hok, ite_false]; exact Nat.le_refl _
    · exact Nat.le_refl _
  | claim who =>
    simp only [exec, emittedBy, Nat.mul_zero, Nat.add_zero]
    by_cases hc : borrowOk s who ∧ supplyOk (borrowNext s who) who
    · simp only [specImpl, hc, and_self, ite_true, Option.getD_some]
      have hI1 : Inv0 gs gb (borrowNext s who) := (inv_borrowNext _ _ _ _ _ hI).1
      exact Nat.le_trans (hP.grant _ who) (Nat.le_trans (hP.supply _ who hI1) (hP.borrow s who hI.1))
    · simp only [specImpl, hc, ite_false, Option.getD_none]; exact Nat.le_refl _
  | setSpeeds a b =>
    simp only [exec, emittedBy, Nat.mul_zero, Nat.add_zero, specImpl,
      speedsOk_of_inv gs gb sp s a b hI, ite_true, Option.getD_some]
    rw [speedsNext_eq]
    exact Nat.le_trans (hP.setB _ b) (hP.setS s a)
  | advance k =>
    simp only [exec, emittedBy]
    have := hP.advance s k hI.1.2.2.1 hI.1.2.2.2
    rw [hI.2.1, hI.2.2] at this
    exact this
  | drip x =>
    simp only [exec, emittedBy, Nat.mul_zero, Nat.add_zero]
    exact hP.drip s x

theorem run_inv (gs gb : Nat) (ops : List Op) : ∀ (sp : Nat × Nat) (s : St), Inv gs gb sp s →
    Inv gs gb (speedsAfter sp ops) (run specImpl s ops) := by
  induction ops with
  | nil => intro sp s h; exact h
  | cons op ops ih =>
    intro sp s h
    exact ih _ _ (exec_inv gs gb sp s h op)

theorem run_pot (gs gb : Nat) (P : St → Nat) (hP : PotOK gs gb P) (ops : List Op) :
    ∀ (sp : Nat × Nat) (s : St), Inv gs gb sp s →
      P (run specImpl s ops) ≤ P s + doubleScale * emitted sp ops := by
  induction ops with
  | nil => intro sp s _; simp [run, emitted]
  | cons op ops ih =>
    intro sp s h
    have h1 := ih _ _ (exec_inv gs gb sp s h op)
    have h2 := exec_pot gs gb P hP sp s h op
    simp only [run, emitted, Nat.mul_add]
    omega


/-! ### The upgrade -/

/-- The value each index starts from after the upgrade: `compInitialIndex` for an index the
upgrade initialized, otherwise the value it started from before. -/
def gsOf (L : Legacy) : Nat := if L.supplyIndex = 0 then compInitialIndex else L.supplyStart
def gbOf (L : Legacy) : Nat := if L.borrowIndex = 0 then compInitialIndex else L.borrowStart

theorem initSide_index (now : Nat) (sd : Side) :
    (initSide now sd).index = if sd.index = 0 then compInitialIndex else sd.index := by
  unfold initSide; split <;> rfl

theorem initSide_block (now : Nat) (sd : Side) :
    (initSide now sd).block = if sd.index = 0 then now else sd.block := by
  unfold initSide; split <;> rfl

theorem initSide_speed (now : Nat) (sd : Side) : (initSide now sd).speed = sd.speed := by
  unfold initSide; split <;> rfl

theorem goodStart_init (idx start : Nat) (h1 : start = 0 ∨ start = compInitialIndex) (h2 : start ≤ idx) :
    GoodStart (if idx = 0 then compInitialIndex else start) (if idx = 0 then compInitialIndex else idx) := by
  split
  · exact ⟨Or.inr rfl, Nat.le_refl _⟩
  · exact ⟨h1, h2⟩

theorem inv_upgrade (L : Legacy) (h : L.WellFormed) :
    Inv (gsOf L) (gbOf L) (L.compSpeed, L.compSpeed) (upgrade L) := by
  obtain ⟨hs1, hs2, hb1, hb2, hbs, hbb, -⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show GoodStart (gsOf L) (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).index
    rw [initSide_index]; exact goodStart_init _ _ hs1 hs2
  · show GoodStart (gbOf L) (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).index
    rw [initSide_index]; exact goodStart_init _ _ hb1 hb2
  · show (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block ≤ L.blockNumber
    rw [initSide_block]; split
    · exact Nat.le_refl _
    · exact hbs
  · show (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block ≤ L.blockNumber
    rw [initSide_block]; split
    · exact Nat.le_refl _
    · exact hbb
  · exact initSide_speed _ _
  · exact initSide_speed _ _

theorem side_pend (idx start u units : Nat) (hu : u ≤ idx) :
    units * ((if idx = 0 then compInitialIndex else idx) -
        legacyStart (if idx = 0 then compInitialIndex else start) u) ≤
      units * (idx - legacyStart start u) := by
  split
  · rename_i h0
    have : u = 0 := by omega
    subst this
    simp [legacyStart]
  · exact Nat.le_refl _

theorem pend_upgrade (L : Legacy) (a : Acct)
    (ha : a.supplierIndex ≤ L.supplyIndex ∧ a.borrowerIndex ≤ L.borrowIndex) :
    pendAt (gsOf L) (gbOf L) (upgrade L).supplyState.index (upgrade L).borrowState.index a ≤
      L.pendingScaled a := by
  unfold pendAt Legacy.pendingScaled gsOf gbOf
  show a.supply * ((initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).index - _) +
    a.borrow * ((initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).index - _) ≤ _
  rw [initSide_index, initSide_index]
  exact Nat.add_le_add (side_pend _ _ _ _ ha.1) (side_pend _ _ _ _ ha.2)

theorem unS_upgrade (L : Legacy) : unS (upgrade L) ≤ L.unindexedSupply := by
  unfold unS Legacy.unindexedSupply
  show (L.blockNumber - (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block) *
    (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).speed ≤ _
  rw [initSide_block, initSide_speed]
  split
  · simp
  · exact Nat.le_refl _

theorem unB_upgrade (L : Legacy) : unB (upgrade L) ≤ L.unindexedBorrow := by
  unfold unB Legacy.unindexedBorrow
  show (L.blockNumber - (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block) *
    (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).speed ≤ _
  rw [initSide_block, initSide_speed]
  split
  · simp
  · exact Nat.le_refl _

theorem sum_le_add_mem {α} (l : List α) (g g' h : α → Nat) (hle : ∀ a ∈ l, g' a ≤ g a + h a) :
    (l.map g').sum ≤ (l.map g).sum + (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hle a (List.mem_cons_self ..)
    have h2 := ih (fun b hb => hle b (List.mem_cons_of_mem a hb))
    omega

theorem phi_upgrade (L : Legacy) (hw : L.WellFormed) :
    Phi (gsOf L) (gbOf L) (upgrade L) ≤
      (upgrade L).credited * doubleScale + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  have h1 : ((upgrade L).accts.map
      (term (gsOf L) (gbOf L) (upgrade L).supplyState.index (upgrade L).borrowState.index)).sum ≤
      (L.accts.map fun a => (a.accrued + a.wallet) * doubleScale).sum + (L.accts.map L.pendingScaled).sum := by
    apply sum_le_add_mem
    intro a ha
    unfold term
    have := pend_upgrade L a (hw.2.2.2.2.2.2 a ha)
    omega
  have h2 : (L.accts.map fun a => (a.accrued + a.wallet) * doubleScale).sum =
      (upgrade L).credited * doubleScale := sum_map_mul _ _ _
  have h3 := unS_upgrade L
  have h4 := unB_upgrade L
  have h5 : doubleScale * (unS (upgrade L) + unB (upgrade L)) ≤
      doubleScale * (L.unindexedSupply + L.unindexedBorrow) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add h3 h4)
  unfold Phi
  omega

theorem psi_upgrade (L : Legacy) (hw : L.WellFormed) (who : Account) :
    Psi (gsOf L) (gbOf L) who (upgrade L) ≤
      (upgrade L).creditedTo who * doubleScale + L.pendingScaled (L.accts.getD who noAcct) +
        doubleScale * ((if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
          (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)) := by
  have hacct : (upgrade L).acct who = L.accts.getD who noAcct := rfl
  have hp : pendAt (gsOf L) (gbOf L) (upgrade L).supplyState.index (upgrade L).borrowState.index
      (L.accts.getD who noAcct) ≤ L.pendingScaled (L.accts.getD who noAcct) := by
    rcases getD_mem_or L.accts who noAcct with hm | hm
    · exact pend_upgrade L _ (hw.2.2.2.2.2.2 _ hm)
    · rw [hm]; simp [pendAt, noAcct]
  have hi : (if 0 < (L.accts.getD who noAcct).supply then unS (upgrade L) else 0) +
      (if 0 < (L.accts.getD who noAcct).borrow then unB (upgrade L) else 0) ≤
      (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
      (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0) := by
    have h3 := unS_upgrade L
    have h4 := unB_upgrade L
    split <;> split <;> omega
  have h5 := Nat.mul_le_mul_left doubleScale hi
  unfold Psi term St.creditedTo
  rw [hacct]
  omega

theorem credited_le_phi (gs gb : Nat) (s : St) : s.credited * doubleScale ≤ Phi gs gb s := by
  have := sum_mul_le s.accts (fun a => a.accrued + a.wallet)
    (term gs gb s.supplyState.index s.borrowState.index) doubleScale
    (fun a => credited_le_term _ _ _ _ a)
  unfold Phi St.credited
  omega

theorem creditedTo_le_psi (gs gb : Nat) (w : Account) (s : St) :
    s.creditedTo w * doubleScale ≤ Psi gs gb w s := by
  have := credited_le_term gs gb s.supplyState.index s.borrowState.index (s.acct w)
  unfold Psi St.creditedTo
  omega

/-! ### The sequence requirements for the specification-shaped implementation -/

theorem spec_rewards_bounded : RewardsBounded specImpl := by
  intro L ops hw
  have hI := inv_upgrade L hw
  have h1 := run_pot _ _ _ (phi_ok (gsOf L) (gbOf L)) ops _ _ hI
  have h2 := phi_upgrade L hw
  have h3 := credited_le_phi (gsOf L) (gbOf L) (run specImpl (upgrade L) ops)
  have key : (run specImpl (upgrade L) ops).credited * doubleScale ≤
      ((upgrade L).credited + L.unindexedSupply + L.unindexedBorrow +
        emitted (L.compSpeed, L.compSpeed) ops) * doubleScale + (L.accts.map L.pendingScaled).sum := by
    simp only [Nat.add_mul, Nat.mul_add] at *
    rw [Nat.mul_comm L.unindexedSupply, Nat.mul_comm L.unindexedBorrow,
      Nat.mul_comm (emitted _ ops)]
    omega
  have := div_bound _ _ _ _ doubleScale_pos key
  unfold Legacy.owed
  omega

theorem spec_account_bounded : AccountBounded specImpl := by
  intro L ops who hw
  have hI := inv_upgrade L hw
  have h1 := run_pot _ _ _ (psi_ok (gsOf L) (gbOf L) who) ops _ _ hI
  have h2 := psi_upgrade L hw who
  have h3 := creditedTo_le_psi (gsOf L) (gbOf L) who (run specImpl (upgrade L) ops)
  have key : (run specImpl (upgrade L) ops).creditedTo who * doubleScale ≤
      ((upgrade L).creditedTo who +
        ((if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
          (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)) +
        emitted (L.compSpeed, L.compSpeed) ops) * doubleScale + L.pendingScaled (L.accts.getD who noAcct) := by
    simp only [Nat.add_mul, Nat.mul_add] at *
    rw [Nat.mul_comm (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0),
      Nat.mul_comm (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0),
      Nat.mul_comm (emitted _ ops)]
    omega
  have := div_bound _ _ _ _ doubleScale_pos key
  unfold Legacy.owedTo
  omega

theorem psi_noPosition (gs gb : Nat) (s : St) (who : Account) (hpos : NoPosition s who) :
    Psi gs gb who s = s.creditedTo who * doubleScale := by
  have e1 : pendAt gs gb s.supplyState.index s.borrowState.index (s.acct who) = 0 := by
    unfold pendAt; rw [hpos.1, hpos.2, Nat.zero_mul, Nat.zero_mul]
  have e2 : (if 0 < (s.acct who).supply then unS s else 0) = 0 := by
    rw [hpos.1]; exact if_neg (Nat.lt_irrefl 0)
  have e3 : (if 0 < (s.acct who).borrow then unB s else 0) = 0 := by
    rw [hpos.2]; exact if_neg (Nat.lt_irrefl 0)
  unfold Psi term
  rw [e1, e2, e3, Nat.add_zero, Nat.mul_zero, Nat.add_zero]
  rfl

theorem spec_no_backdated : NoBackdatedRewards specImpl := by
  intro L history ops who hw hpos
  have hI := run_inv _ _ history _ _ (inv_upgrade L hw)
  have h1 := run_pot _ _ _ (psi_ok (gsOf L) (gbOf L) who) ops _ _ hI
  have h3 := creditedTo_le_psi (gsOf L) (gbOf L) who
    (run specImpl (run specImpl (upgrade L) history) ops)
  have h0 := psi_noPosition (gsOf L) (gbOf L) _ who hpos
  rw [h0] at h1
  have key : (run specImpl (run specImpl (upgrade L) history) ops).creditedTo who * doubleScale ≤
      ((run specImpl (upgrade L) history).creditedTo who +
        emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops) * doubleScale := by
    rw [Nat.add_mul, Nat.mul_comm (emitted _ ops)]
    omega
  exact Nat.le_of_mul_le_mul_right key doubleScale_pos


/-! ## The shipped fix, transcribed from Solidity

The distribution of the Comptroller as fixed by Proposal 64 and kept by Proposal 65
(compound-finance/compound-protocol, commit 32f765957e05560cbbd977d7a49c86a09a81282b, the head
of pull request 165, and commit c05d7e09e57ff69582ddb621984e46099f1b4d4b, the head of pull
request 166): the same functions as the Proposal 62 code, with `>=` in place of `>` in the
condition for an account with no recorded index. The Proposal 64 lock in `grantCompInternal`,
removed by Proposal 65, is not included. -/

def fraction (a b : Nat) : Nat := a * doubleScale / b

def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale

def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

def updateCompSupplyIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.supplyState.block with
  | none => none
  | some deltaBlocks =>
    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
      let supplyTokens := totalSupply s
      let compAccrued := deltaBlocks * s.supplyState.speed
      let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
      some { s with supplyState :=
        { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
    else if deltaBlocks > 0 then
      some { s with supplyState := { s.supplyState with block := s.blockNumber } }
    else some s

def updateCompBorrowIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.borrowState.block with
  | none => none
  | some deltaBlocks =>
    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
      let borrowAmount := totalBorrows s
      let compAccrued := deltaBlocks * s.borrowState.speed
      let ratio := if borrowAmount > 0 then fraction compAccrued borrowAmount else 0
      some { s with borrowState :=
        { s.borrowState with index := s.borrowState.index + ratio, block := s.blockNumber } }
    else if deltaBlocks > 0 then
      some { s with borrowState := { s.borrowState with block := s.blockNumber } }
    else some s

def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  let supplyIndex := s.supplyState.index
  let supplierIndex :=
    if (s.acct supplier).supplierIndex = 0 ∧ supplyIndex ≥ compInitialIndex then compInitialIndex
    else (s.acct supplier).supplierIndex
  match subChecked supplyIndex supplierIndex with
  | none => none
  | some deltaIndex =>
    let supplierDelta := mulDouble (s.acct supplier).supply deltaIndex
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := supplyIndex, accrued := a.accrued + supplierDelta })

def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let borrowIndex := s.borrowState.index
  let borrowerIndex :=
    if (s.acct borrower).borrowerIndex = 0 ∧ borrowIndex ≥ compInitialIndex then compInitialIndex
    else (s.acct borrower).borrowerIndex
  match subChecked borrowIndex borrowerIndex with
  | none => none
  | some deltaIndex =>
    let borrowerDelta := mulDouble (s.acct borrower).borrow deltaIndex
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := borrowIndex, accrued := a.accrued + borrowerDelta })

def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if amount > 0 ∧ amount ≤ s.reserve then
    { s with reserve := s.reserve - amount,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + amount } }
  else s

def claimComp (s : St) (holder : Account) : Option St := do
  let s ← updateCompBorrowIndex s
  let s ← distributeBorrowerComp s holder
  let s ← updateCompSupplyIndex s
  let s ← distributeSupplierComp s holder
  return grantCompInternal s holder

/-- The supply branch of `setCompSpeedInternal`: when the supply speed changes, accrue at the
old speed, then store the new one. -/
def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed ≠ supplySpeed then
    (updateCompSupplyIndex s).map fun s =>
      { s with supplyState := { s.supplyState with speed := supplySpeed } }
  else some s

/-- The borrow branch of `setCompSpeedInternal`. -/
def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed ≠ borrowSpeed then
    (updateCompBorrowIndex s).map fun s =>
      { s with borrowState := { s.borrowState with speed := borrowSpeed } }
  else some s

/-- `setCompSpeedInternal(cToken, supplySpeed, borrowSpeed)`: the supply branch, then the borrow
branch. -/
def setCompSpeedInternal (s : St) (supplySpeed borrowSpeed : Nat) : Option St :=
  (setSupplySpeed s supplySpeed).bind fun s => setBorrowSpeed s borrowSpeed

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => do
    let s ← updateCompSupplyIndex s
    distributeSupplierComp s who
  | .borrowHook who => do
    let s ← updateCompBorrowIndex s
    distributeBorrowerComp s who
  | .claim who => claimComp s who
  | .setSpeeds a b => setCompSpeedInternal s a b

/-! ### The transcription computes the specification-shaped implementation -/

theorem upd_supply (s : St) :
    updateCompSupplyIndex s =
      if s.supplyState.block ≤ s.blockNumber then some { s with supplyState := sdS s } else none := by
  unfold updateCompSupplyIndex subChecked sdS accrueSide fraction
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp only [hb, ite_true]
    by_cases h1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · simp only [h1, ite_true]
      by_cases h2 : totalSupply s > 0
      · have h3 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s :=
          ⟨h1.1, h1.2, h2⟩
        simp only [h2, ite_true, and_self]
      · simp only [h2, ite_false, Nat.add_zero, and_self, and_false, ite_true]
    · have h3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) :=
        fun h => h1 ⟨h.1, h.2.1⟩
      simp only [h1, h3, ite_false]
      by_cases h4 : s.blockNumber - s.supplyState.block > 0
      · simp only [h4, ite_true]
      · simp only [h4, ite_false]
        have : s.supplyState.block = s.blockNumber := by omega
        cases s with
        | mk n ss bs r ac => cases ss; simp_all
  · simp only [hb, ite_false]

theorem upd_borrow (s : St) :
    updateCompBorrowIndex s =
      if s.borrowState.block ≤ s.blockNumber then some { s with borrowState := sdB s } else none := by
  unfold updateCompBorrowIndex subChecked sdB accrueSide fraction
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp only [hb, ite_true]
    by_cases h1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · simp only [h1, ite_true]
      by_cases h2 : totalBorrows s > 0
      · have h3 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s :=
          ⟨h1.1, h1.2, h2⟩
        simp only [h2, ite_true, and_self]
      · simp only [h2, ite_false, Nat.add_zero, and_self, and_false, ite_true]
    · have h3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) :=
        fun h => h1 ⟨h.1, h.2.1⟩
      simp only [h1, h3, ite_false]
      by_cases h4 : s.blockNumber - s.borrowState.block > 0
      · simp only [h4, ite_true]
      · simp only [h4, ite_false]
        have : s.borrowState.block = s.blockNumber := by omega
        cases s with
        | mk n ss bs r ac => cases bs; simp_all
  · simp only [hb, ite_false]

theorem start_eq (u idx : Nat) :
    (if u = 0 ∧ idx ≥ compInitialIndex then compInitialIndex else u) = accrualStart u idx := by
  unfold accrualStart
  by_cases hu : u = 0
  · by_cases hi : compInitialIndex ≤ idx
    · simp [hu, hi]
    · simp [hu, hi]
  · simp [hu]

theorem dist_supply (s : St) (who : Account) :
    distributeSupplierComp s who =
      if accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index then
        some { s with accts := s.accts.modify who (distS s.supplyState.index) }
      else none := by
  unfold distributeSupplierComp subChecked
  simp only [start_eq]
  by_cases hc : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp only [hc, ite_true]
    unfold St.withAcct
    congr 2
    apply modify_congr _ _ _ _ noAcct
    intro _
    rfl
  · simp only [hc, ite_false]

theorem dist_borrow (s : St) (who : Account) :
    distributeBorrowerComp s who =
      if accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index then
        some { s with accts := s.accts.modify who (distB s.borrowState.index) }
      else none := by
  unfold distributeBorrowerComp subChecked
  simp only [start_eq]
  by_cases hc : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hc, ite_true]
    unfold St.withAcct
    congr 2
    apply modify_congr _ _ _ _ noAcct
    intro _
    rfl
  · simp only [hc, ite_false]

theorem hook_supply (s : St) (who : Account) :
    (updateCompSupplyIndex s).bind (fun s => distributeSupplierComp s who) =
      if supplyOk s who then some (supplyNext s who) else none := by
  rw [upd_supply]
  unfold supplyOk
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp only [hb, ite_true, Option.bind_some, true_and]
    rw [dist_supply]
    rfl
  · simp [hb]

theorem hook_borrow (s : St) (who : Account) :
    (updateCompBorrowIndex s).bind (fun s => distributeBorrowerComp s who) =
      if borrowOk s who then some (borrowNext s who) else none := by
  rw [upd_borrow]
  unfold borrowOk
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp only [hb, ite_true, Option.bind_some, true_and]
    rw [dist_borrow]
    rfl
  · simp [hb]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [gt_iff_lt, h, and_self, ite_true]
    congr 1
    apply modify_congr _ _ _ _ noAcct
    intro _
    rfl
  · simp only [gt_iff_lt, h, ite_false]

theorem claim_eq (s : St) (who : Account) :
    claimComp s who =
      if borrowOk s who ∧ supplyOk (borrowNext s who) who then
        some (grant (supplyNext (borrowNext s who) who) who)
      else none := by
  have e : claimComp s who =
      ((updateCompBorrowIndex s).bind (fun s => distributeBorrowerComp s who)).bind fun s =>
        ((updateCompSupplyIndex s).bind (fun s => distributeSupplierComp s who)).bind fun s =>
          some (grantCompInternal s who) := by
    unfold claimComp
    simp only [Option.bind_assoc]
    rfl
  rw [e, hook_borrow]
  by_cases h1 : borrowOk s who
  · simp only [h1, ite_true, Option.bind_some, true_and]
    rw [hook_supply]
    by_cases h2 : supplyOk (borrowNext s who) who
    · simp only [h2, ite_true, Option.bind_some, grant_eq]
    · simp only [h2, ite_false, Option.bind_none]
  · simp only [h1, ite_false, Option.bind_none, false_and]

theorem stepS_eq (s : St) (a : Nat) :
    setSupplySpeed s a =
      if (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) then some (setS s a) else none := by
  unfold setSupplySpeed
  rw [upd_supply]
  unfold setS
  by_cases h1 : s.supplyState.speed = a
  · simp [h1]
  · by_cases h2 : s.supplyState.block ≤ s.blockNumber
    · simp [h1, h2]
    · simp [h1, h2]

theorem stepB_eq (s : St) (b : Nat) :
    setBorrowSpeed s b =
      if (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) then some (setB s b) else none := by
  unfold setBorrowSpeed
  rw [upd_borrow]
  unfold setB
  by_cases h1 : s.borrowState.speed = b
  · simp [h1]
  · by_cases h2 : s.borrowState.block ≤ s.blockNumber
    · simp [h1, h2]
    · simp [h1, h2]

theorem speeds_eq (s : St) (a b : Nat) :
    setCompSpeedInternal s a b = if speedsOk s a b then some (speedsNext s a b) else none := by
  unfold setCompSpeedInternal
  rw [stepS_eq, speedsNext_eq]
  unfold speedsOk
  by_cases c1 : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber)
  · rw [if_pos c1, Option.bind_some, stepB_eq]
    have hb : (setS s a).borrowState = s.borrowState := by unfold setS; split <;> rfl
    have hn : (setS s a).blockNumber = s.blockNumber := by unfold setS; split <;> rfl
    rw [hb, hn]
    by_cases c2 : (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber)
    · rw [if_pos c2, if_pos ⟨c1, c2⟩]
    · rw [if_neg c2, if_neg (fun h => c2 h.2)]
  · rw [if_neg c1, if_neg (fun h => c1 h.1)]
    rfl

theorem comptroller_eq : comptroller = specImpl := by
  funext s c
  cases c with
  | supplyHook who => exact hook_supply s who
  | borrowHook who => exact hook_borrow s who
  | claim who => exact claim_eq s who
  | setSpeeds a b => exact speeds_eq s a b

/-! ## The locked requirements -/

theorem req_calls_succeed       : CallsSucceed comptroller := by rw [comptroller_eq]; exact spec_calls_succeed
theorem req_supply_hook         : SupplyHookEffects comptroller := by rw [comptroller_eq]; exact spec_supply_hook
theorem req_borrow_hook         : BorrowHookEffects comptroller := by rw [comptroller_eq]; exact spec_borrow_hook
theorem req_claim               : ClaimEffects comptroller := by rw [comptroller_eq]; exact spec_claim
theorem req_set_speeds          : SetSpeedsEffects comptroller := by rw [comptroller_eq]; exact spec_set_speeds
theorem req_rewards_bounded     : RewardsBounded comptroller := by rw [comptroller_eq]; exact spec_rewards_bounded
theorem req_account_bounded     : AccountBounded comptroller := by rw [comptroller_eq]; exact spec_account_bounded
theorem req_no_backdated        : NoBackdatedRewards comptroller := by rw [comptroller_eq]; exact spec_no_backdated

end CompRewards
