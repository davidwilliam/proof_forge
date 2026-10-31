import CompRewards.Spec
import ProofForgeFin.DeFi
/-!
Test candidate for `rw-compound-comp` that imports ProofForgeFin (tests/test_fin_integration.py).

The implementation and the five per-call requirements are those of the reference solution
(`reference/SolutionA.lean`: the specification-shaped implementation `specImpl`, the Solidity
transcription `comptroller` and `comptroller_eq`). The three sequence requirements are not
proved with the reference's own potential argument: they come from the library argument of
`lib/ProofForgeFinDemo/DeFi/Compound.lean` (its section "Re-proved with the library", copied into
`namespace CompRewards.Lib`), which proves them for every implementation that meets the
per-call requirements, from `ProofForgeFin.DeFi.Rewards` and `ProofForgeFin.Seq`.

Four steps are stated so that every kernel of `lake comparator --paranoid` accepts them. As first
written in the demonstration, `psi_moves` (its `advance` field), `psi_upgrade`, `psi_noPosition` and
the last step of `no_backdated` were accepted by Lean's kernels, lean4lean and nanoda, but con-leche
and con-ron stopped with "fuel exhausted: whnfCore": they unfold `doubleScale = 10 ^ 36` in
equations such as `A * doubleScale + 0 = A * doubleScale` that Lean's kernel settles without
unfolding. Here `psi_moves` has one theorem per field, and the arithmetic of those steps is proved
over an abstract scale `D` (`advance_arith`, `upgrade_arith`, `noPosition_arith`,
`le_mul_add_zero`, `le_of_le_add_zero_div`) and then instantiated, the way the reference
solution's `div_bound` is; the demonstration now proves those steps the same way
(`harness/fin_kernels.py` checks it).
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


/-! ### Speed changes -/

def setS (s : St) (a : Nat) : St :=
  if s.supplyState.speed = a then s else { s with supplyState := { sdS s with speed := a } }

def setB (s : St) (b : Nat) : St :=
  if s.borrowState.speed = b then s else { s with borrowState := { sdB s with speed := b } }

theorem speedsNext_eq (s : St) (a b : Nat) : speedsNext s a b = setB (setS s a) b := by
  unfold speedsNext setS setB
  by_cases h1 : s.supplyState.speed = a <;> by_cases h2 : s.borrowState.speed = b <;>
    simp only [h1, h2, ite_true, ite_false] <;> rfl


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


namespace Lib

/-! ## Re-proved with the library

Everything below is new. The bounds are proved for every implementation that meets the four
per-call effect requirements, so they hold for the reference implementation (which proves those
four) and for any other implementation that does. -/

open ProofForgeFin ProofForgeFin.DeFi.Rewards

/-- The index scale is positive. -/
theorem doubleScale_pos : 0 < doubleScale := by unfold doubleScale; decide

/-! ### The task's arithmetic is the library's -/

/-- `creditFor` is the library's `credit` at scale `doubleScale`. -/
theorem creditFor_eq (u s i : Nat) : creditFor u s i = credit doubleScale u s i := rfl

/-- `legacyStart` is the library's `effStart`. -/
theorem legacyStart_eq (g r : Nat) : legacyStart g r = effStart g r := rfl

/-- `accrualStart` is the library's `firstStart` with `init = compInitialIndex`. -/
theorem accrualStart_eq (r i : Nat) : accrualStart r i = firstStart compInitialIndex r i := rfl

/-- The task's `run` is the library's. -/
theorem run_eq (impl : Impl) (s : St) (ops : List Op) :
    run impl s ops = Seq.run (exec impl) s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih _

/-- The speeds after a sequence are a library run of `nextSpeeds`. -/
theorem speedsAfter_eq (sp : Nat × Nat) (ops : List Op) :
    speedsAfter sp ops = Seq.run nextSpeeds sp ops := by
  induction ops generalizing sp with
  | nil => rfl
  | cons op ops ih => exact ih _

/-- The COMP emitted is a library ghost accumulator with the speeds as ghost state. -/
theorem emitted_eq (sp : Nat × Nat) (ops : List Op) :
    emitted sp ops = Seq.accum nextSpeeds emittedBy sp ops := by
  induction ops generalizing sp with
  | nil => rfl
  | cons op ops ih => simp only [emitted, Seq.accum_cons, ih]

/-! ### One side brought up to date -/

/-- The side is up to date at the current block. -/
theorem accrueSide_block (sd : Side) (now T : Nat) : (accrueSide sd now T).block = now := by
  unfold accrueSide; split <;> rfl

/-- The speed is unchanged. -/
theorem accrueSide_speed (sd : Side) (now T : Nat) : (accrueSide sd now T).speed = sd.speed := by
  unfold accrueSide; split <;> rfl

/-- The index grows by an increment that the COMP emitted since the side's block covers. -/
theorem accrueSide_index (sd : Side) (now T : Nat) :
    sd.index ≤ (accrueSide sd now T).index ∧
      T * ((accrueSide sd now T).index - sd.index) ≤ doubleScale * ((now - sd.block) * sd.speed) := by
  unfold accrueSide
  split
  · dsimp only
    refine ⟨Nat.le_add_right _ _, ?_⟩
    rw [Nat.add_sub_cancel_left, Nat.mul_comm doubleScale]
    exact total_mul_indexDelta_le doubleScale _ T
  · simp

/-- A side already up to date is unchanged. -/
theorem accrueSide_current {sd : Side} {now : Nat} (T : Nat) (h : sd.block = now) :
    accrueSide sd now T = sd := by
  subst h; unfold accrueSide; simp

/-! ### The potentials

`gs` and `gb` are the values the supply and borrow indices started from. An account's term is the
COMP credited to it, at scale `doubleScale`, plus the COMP pending on each side from its effective
start (`effStart`); the global potential `Phi` adds the scaled COMP emitted and not yet in either
index, and the potential `Psi` of one account adds it for each side on which the account holds a
position. -/

/-- The potential term of an account at indices `iS` and `iB`. -/
def term (gs gb iS iB : Nat) (a : Acct) : Nat :=
  (a.accrued + a.wallet) * doubleScale + pending a.supply (effStart gs a.supplierIndex) iS +
    pending a.borrow (effStart gb a.borrowerIndex) iB

/-- COMP emitted on the supply side since its index was last brought up to date. -/
def unS (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

/-- COMP emitted on the borrow side since its index was last brought up to date. -/
def unB (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

/-- The global potential. -/
def Phi (gs gb : Nat) (s : St) : Nat :=
  (s.accts.map (term gs gb s.supplyState.index s.borrowState.index)).sum +
    doubleScale * unS s + doubleScale * unB s

/-- The potential of account `w`. -/
def Psi (gs gb : Nat) (w : Account) (s : St) : Nat :=
  term gs gb s.supplyState.index s.borrowState.index (s.acct w) +
    doubleScale * (if 0 < (s.acct w).supply then unS s else 0) +
    doubleScale * (if 0 < (s.acct w).borrow then unB s else 0)

/-! ### Terms of one account -/

/-- Raising the indices raises a term by at most the units times the increments. -/
theorem term_index_le (gs gb : Nat) {iS iS' iB iB' : Nat} (hS : iS ≤ iS') (hB : iB ≤ iB')
    (a : Acct) :
    term gs gb iS' iB' a ≤ term gs gb iS iB a + a.supply * (iS' - iS) + a.borrow * (iB' - iB) := by
  have h1 := pending_le_add a.supply (effStart gs a.supplierIndex) hS
  have h2 := pending_le_add a.borrow (effStart gb a.borrowerIndex) hB
  unfold term; omega

/-- Settling the supply side of an account from a start at or after its effective start does not
raise its term, whatever its supply afterwards. -/
theorem term_settleS {gs gb iS iB q : Nat} {a b : Acct} (hq : effStart gs a.supplierIndex ≤ q)
    (hk : b.supplierIndex = iS) (hb : b.borrow = a.borrow) (hbi : b.borrowerIndex = a.borrowerIndex)
    (hc : b.accrued + b.wallet = a.accrued + a.wallet + credit doubleScale a.supply q iS) :
    term gs gb iS iB b ≤ term gs gb iS iB a := by
  have := settle_le_self hc hq
  unfold term; rw [hk, pending_effStart_self, hb, hbi]; omega

/-- Settling the borrow side, likewise. -/
theorem term_settleB {gs gb iS iB q : Nat} {a b : Acct} (hq : effStart gb a.borrowerIndex ≤ q)
    (hk : b.borrowerIndex = iB) (hb : b.supply = a.supply) (hbi : b.supplierIndex = a.supplierIndex)
    (hc : b.accrued + b.wallet = a.accrued + a.wallet + credit doubleScale a.borrow q iB) :
    term gs gb iS iB b ≤ term gs gb iS iB a := by
  have := settle_le_self hc hq
  unfold term; rw [hk, pending_effStart_self, hb, hbi]; omega

/-- A supply balance change of an account settled at the supply index keeps its term. -/
theorem term_balS {gs gb iS iB : Nat} {a : Acct} (x : Nat) (hk : a.supplierIndex = iS) :
    term gs gb iS iB { a with supply := x } = term gs gb iS iB a := by
  unfold term; dsimp only; rw [hk, pending_effStart_self, pending_effStart_self]

/-- A borrow balance change of an account settled at the borrow index keeps its term. -/
theorem term_balB {gs gb iS iB : Nat} {a : Acct} (x : Nat) (hk : a.borrowerIndex = iB) :
    term gs gb iS iB { a with borrow := x } = term gs gb iS iB a := by
  unfold term; dsimp only; rw [hk, pending_effStart_self, pending_effStart_self]

/-- A paid claim keeps the term. -/
theorem term_grant (gs gb iS iB : Nat) (a : Acct) :
    term gs gb iS iB { a with accrued := 0, wallet := a.wallet + a.accrued } = term gs gb iS iB a := by
  unfold term; dsimp only; rw [Nat.zero_add, Nat.add_comm a.wallet]

/-! ### The next states the effect requirements fix -/

/-- The supply side brought up to date. -/
def sideS (s : St) : Side := accrueSide s.supplyState s.blockNumber (totalSupply s)

/-- The borrow side brought up to date. -/
def sideB (s : St) : Side := accrueSide s.borrowState s.blockNumber (totalBorrows s)

/-- An account credited for its supply up to index `i`. -/
def distS (i : Nat) (a : Acct) : Acct :=
  { a with supplierIndex := i,
           accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex i) i }

/-- An account credited for its borrow up to index `i`. -/
def distB (i : Nat) (a : Acct) : Acct :=
  { a with borrowerIndex := i,
           accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex i) i }

/-- The state `SupplyDistributed` fixes. -/
def supplyNext (s : St) (who : Account) : St :=
  { s with supplyState := sideS s, accts := s.accts.modify who (distS (sideS s).index) }

/-- The state `BorrowDistributed` fixes. -/
def borrowNext (s : St) (who : Account) : St :=
  { s with borrowState := sideB s, accts := s.accts.modify who (distB (sideB s).index) }

/-- The supply side after a supply hook. -/
@[simp] theorem supplyNext_supplyState (s : St) (who : Account) :
    (supplyNext s who).supplyState = sideS s := rfl

/-- The borrow side after a borrow hook. -/
@[simp] theorem borrowNext_borrowState (s : St) (who : Account) :
    (borrowNext s who).borrowState = sideB s := rfl

/-- The state `SpeedsSet` fixes. -/
def speedsNext (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState else { sideS s with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState else { sideB s with speed := bor } }

section Effects

variable {impl : Impl}

/-- REQ-SUPPLY-HOOK fixes the state after a successful supply hook. -/
theorem supply_eq (h : SupplyHookEffects impl) {s s' : St} {who : Account}
    (e : impl s (.supplyHook who) = some s') : s' = supplyNext s who := (h s who s' e).2.2

/-- REQ-BORROW-HOOK fixes the state after a successful borrow hook. -/
theorem borrow_eq (h : BorrowHookEffects impl) {s s' : St} {who : Account}
    (e : impl s (.borrowHook who) = some s') : s' = borrowNext s who := (h s who s' e).2.2

/-- REQ-CLAIM fixes the state after a successful claim. -/
theorem claim_eq (h : ClaimEffects impl) {s s' : St} {who : Account}
    (e : impl s (.claim who) = some s') : s' = grant (supplyNext (borrowNext s who) who) who := by
  obtain ⟨_, _, ⟨-, -, rfl⟩, ⟨-, -, rfl⟩, rfl⟩ := h s who s' e; rfl

/-- REQ-SET-SPEEDS fixes the state after a successful speed change. -/
theorem speeds_eq (h : SetSpeedsEffects impl) {s s' : St} {a b : Nat}
    (e : impl s (.setSpeeds a b) = some s') : s' = speedsNext s a b := (h s a b s' e).2.2

end Effects

/-! ### Facts about the next states -/

/-- Reading an account after a change of one account. -/
theorem acct_withAcct (s : St) (w v : Account) (f : Acct → Acct) :
    (s.withAcct w f).acct v = if w = v ∧ v < s.accts.length then f (s.acct v) else s.acct v :=
  Ledger.getD_modify _ _ _ _ _

/-- Reading an account after a supply hook. -/
theorem acct_supplyNext (s : St) (who w : Account) :
    (supplyNext s who).acct w =
      if who = w ∧ w < s.accts.length then distS (sideS s).index (s.acct w) else s.acct w :=
  Ledger.getD_modify _ _ _ _ _

/-- Reading an account after a borrow hook. -/
theorem acct_borrowNext (s : St) (who w : Account) :
    (borrowNext s who).acct w =
      if who = w ∧ w < s.accts.length then distB (sideB s).index (s.acct w) else s.acct w :=
  Ledger.getD_modify _ _ _ _ _

/-- An account holds at most the total supply. -/
theorem supply_le_total (s : St) (w : Account) : (s.acct w).supply ≤ totalSupply s :=
  Ledger.getD_le_sum_map _ _ _ _ rfl

/-- An account holds at most the total borrows. -/
theorem borrow_le_total (s : St) (w : Account) : (s.acct w).borrow ≤ totalBorrows s :=
  Ledger.getD_le_sum_map _ _ _ _ rfl

/-- After a supply hook, nothing is unindexed on the supply side. -/
theorem unS_supplyNext (s : St) (who : Account) : unS (supplyNext s who) = 0 := by
  simp [unS, supplyNext, sideS, accrueSide_block]

/-- After a borrow hook, nothing is unindexed on the borrow side. -/
theorem unB_borrowNext (s : St) (who : Account) : unB (borrowNext s who) = 0 := by
  simp [unB, borrowNext, sideB, accrueSide_block]

/-- After a supply hook, every account settled at the supply index before stays settled, and the
hooked account is settled. -/
theorem supplyNext_settled (s : St) (who w : Account)
    (h : (who = w ∧ w < s.accts.length) ∨
      ((s.acct w).supplierIndex = s.supplyState.index ∧ s.supplyState.block = s.blockNumber)) :
    ((supplyNext s who).acct w).supplierIndex = (supplyNext s who).supplyState.index := by
  rw [acct_supplyNext]
  split
  · rfl
  · rename_i hn
    rcases h with h | ⟨h1, h2⟩
    · exact absurd h hn
    · show _ = (sideS s).index
      rw [sideS, accrueSide_current _ h2, h1]

/-- After a borrow hook, likewise on the borrow side. -/
theorem borrowNext_settled (s : St) (who w : Account)
    (h : (who = w ∧ w < s.accts.length) ∨
      ((s.acct w).borrowerIndex = s.borrowState.index ∧ s.borrowState.block = s.blockNumber)) :
    ((borrowNext s who).acct w).borrowerIndex = (borrowNext s who).borrowState.index := by
  rw [acct_borrowNext]
  split
  · rfl
  · rename_i hn
    rcases h with h | ⟨h1, h2⟩
    · exact absurd h hn
    · show _ = (sideB s).index
      rw [sideB, accrueSide_current _ h2, h1]

/-! ### The potentials along a step

`phi_le` and `psi_le` are the only places where the potentials are unfolded: every step below
is one of them with its hypotheses checked. -/

/-- The global potential does not grow from `s` to `s'` when both indices grow by increments the
unindexed COMP of `s` covers, net of what `s'` leaves unindexed, and the accounts of `s'` have, at
the new indices, terms no larger in total than those of `s`. -/
theorem phi_le {gs gb : Nat} {s s' : St}
    (hS : s.supplyState.index ≤ s'.supplyState.index) (hB : s.borrowState.index ≤ s'.borrowState.index)
    (eS : totalSupply s * (s'.supplyState.index - s.supplyState.index) + doubleScale * unS s' ≤
      doubleScale * unS s)
    (eB : totalBorrows s * (s'.borrowState.index - s.borrowState.index) + doubleScale * unB s' ≤
      doubleScale * unB s)
    (ha : (s'.accts.map (term gs gb s'.supplyState.index s'.borrowState.index)).sum ≤
      (s.accts.map (term gs gb s'.supplyState.index s'.borrowState.index)).sum) :
    Phi gs gb s' ≤ Phi gs gb s := by
  have := sum_le_of_index_le₂ s.accts (term gs gb s.supplyState.index s.borrowState.index)
    (term gs gb s'.supplyState.index s'.borrowState.index) Acct.supply Acct.borrow
    (fun a _ => term_index_le gs gb hS hB a) (Nat.le_refl _)
  unfold Phi; unfold totalSupply at eS; unfold totalBorrows at eB; omega

/-- The potential of account `w` does not grow from `s` to `s'` under the same conditions on the
indices, when its record at the new indices has a term no larger than before and, on each side,
its units are unchanged or nothing is left unindexed. -/
theorem psi_le {gs gb : Nat} {w : Account} {s s' : St}
    (hS : s.supplyState.index ≤ s'.supplyState.index) (hB : s.borrowState.index ≤ s'.borrowState.index)
    (eS : totalSupply s * (s'.supplyState.index - s.supplyState.index) + doubleScale * unS s' ≤
      doubleScale * unS s)
    (eB : totalBorrows s * (s'.borrowState.index - s.borrowState.index) + doubleScale * unB s' ≤
      doubleScale * unB s)
    (ht : term gs gb s'.supplyState.index s'.borrowState.index (s'.acct w) ≤
      term gs gb s'.supplyState.index s'.borrowState.index (s.acct w))
    (uS : (s'.acct w).supply = (s.acct w).supply ∨ unS s' = 0)
    (uB : (s'.acct w).borrow = (s.acct w).borrow ∨ unB s' = 0) :
    Psi gs gb w s' ≤ Psi gs gb w s := by
  have h1 := term_index_le gs gb hS hB (s.acct w)
  have h2 := ite_accrue_le (units := (s.acct w).supply) (supply_le_total s w) eS uS
  have h3 := ite_accrue_le (units := (s.acct w).borrow) (borrow_le_total s w) eB uB
  unfold Psi; omega

/-- The side conditions of `phi_le` and `psi_le` for a side left as it is. -/
theorem side_same {T i i' u u' : Nat} (hi : i' = i) (hu : u' = u) :
    i ≤ i' ∧ T * (i' - i) + doubleScale * u' ≤ doubleScale * u := by
  subst hi hu; simp

/-- The side conditions for a side brought up to date (and then given any speed). -/
theorem side_accrued (sd : Side) (now T : Nat) {sd' : Side} (hi : sd'.index = (accrueSide sd now T).index)
    (hb : sd'.block = now) (sp : Nat) :
    sd.index ≤ sd'.index ∧
      T * (sd'.index - sd.index) + doubleScale * ((now - sd'.block) * sp) ≤
        doubleScale * ((now - sd.block) * sd.speed) := by
  have := accrueSide_index sd now T
  rw [hi, hb]; simp only [Nat.sub_self, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]; exact this

/-- `phi_le` for a step that changes the accounts only. -/
theorem phi_accts {gs gb : Nat} {s s' : St} (hS : s'.supplyState = s.supplyState)
    (hB : s'.borrowState = s.borrowState) (hn : s'.blockNumber = s.blockNumber)
    (ha : (s'.accts.map (term gs gb s.supplyState.index s.borrowState.index)).sum ≤
      (s.accts.map (term gs gb s.supplyState.index s.borrowState.index)).sum) :
    Phi gs gb s' ≤ Phi gs gb s := by
  unfold Phi unS unB; rw [hS, hB, hn]; omega

/-- `psi_le` for a step that changes the accounts only. -/
theorem psi_accts {gs gb : Nat} {w : Account} {s s' : St} (hS : s'.supplyState = s.supplyState)
    (hB : s'.borrowState = s.borrowState) (hn : s'.blockNumber = s.blockNumber)
    (ht : term gs gb s.supplyState.index s.borrowState.index (s'.acct w) ≤
      term gs gb s.supplyState.index s.borrowState.index (s.acct w))
    (uS : (s'.acct w).supply = (s.acct w).supply ∨ unS s = 0)
    (uB : (s'.acct w).borrow = (s.acct w).borrow ∨ unB s = 0) : Psi gs gb w s' ≤ Psi gs gb w s := by
  have e1 : unS s' = unS s := by unfold unS; rw [hS, hn]
  have e2 : unB s' = unB s := by unfold unB; rw [hB, hn]
  obtain ⟨h1, h2⟩ := side_same (T := totalSupply s) (congrArg Side.index hS) e1
  obtain ⟨h3, h4⟩ := side_same (T := totalBorrows s) (congrArg Side.index hB) e2
  exact psi_le h1 h3 h2 h4 (by rw [hS, hB]; exact ht) (by rw [e1]; exact uS) (by rw [e2]; exact uB)

/-- The side conditions of a speed change, for both sides. -/
theorem speeds_sides (s : St) (a b : Nat) :
    (s.supplyState.index ≤ (speedsNext s a b).supplyState.index ∧
      totalSupply s * ((speedsNext s a b).supplyState.index - s.supplyState.index) +
        doubleScale * unS (speedsNext s a b) ≤ doubleScale * unS s) ∧
    (s.borrowState.index ≤ (speedsNext s a b).borrowState.index ∧
      totalBorrows s * ((speedsNext s a b).borrowState.index - s.borrowState.index) +
        doubleScale * unB (speedsNext s a b) ≤ doubleScale * unB s) := by
  unfold speedsNext unS unB; dsimp only
  constructor <;> split
  · exact side_same rfl rfl
  · exact side_accrued _ _ _ rfl (accrueSide_block _ _ _) a
  · exact side_same rfl rfl
  · exact side_accrued _ _ _ rfl (accrueSide_block _ _ _) b

/-- The invariant: each index started from 0 or `compInitialIndex` and has not fallen below its
start, no side's block lies ahead, the speeds are the ghost speeds `sp`, and no recorded index lies
above the market's (so the state is `Consistent` and REQ-CALLS-SUCCEED applies). -/
structure Inv (gs gb : Nat) (sp : Nat × Nat) (s : St) : Prop where
  /-- The supply index started from `gs`. -/
  startS : (gs = 0 ∨ gs = compInitialIndex) ∧ gs ≤ s.supplyState.index
  /-- The borrow index started from `gb`. -/
  startB : (gb = 0 ∨ gb = compInitialIndex) ∧ gb ≤ s.borrowState.index
  /-- The supply side is not ahead. -/
  blockS : s.supplyState.block ≤ s.blockNumber
  /-- The borrow side is not ahead. -/
  blockB : s.borrowState.block ≤ s.blockNumber
  /-- The supply speed is the ghost one. -/
  speedS : s.supplyState.speed = sp.1
  /-- The borrow speed is the ghost one. -/
  speedB : s.borrowState.speed = sp.2
  /-- No recorded index lies above the market's. -/
  accts : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index

/-- A potential `P` that no step of a call raises and that blocks passing raise by at most the
COMP emitted. `Phi` and every `Psi` are such potentials. -/
structure Moves (gs gb : Nat) (P : St → Nat) : Prop where
  /-- A supply hook. -/
  supply : ∀ sp s who, Inv gs gb sp s → P (supplyNext s who) ≤ P s
  /-- A borrow hook. -/
  borrow : ∀ sp s who, Inv gs gb sp s → P (borrowNext s who) ≤ P s
  /-- A payment. -/
  grant : ∀ s who, P (grant s who) ≤ P s
  /-- A supply balance change of a settled account at an up-to-date side. -/
  balS : ∀ s w (g : Nat → Nat), (s.acct w).supplierIndex = s.supplyState.index →
    s.supplyState.block = s.blockNumber → P (s.withAcct w fun a => { a with supply := g a.supply }) ≤ P s
  /-- A borrow balance change of a settled account at an up-to-date side. -/
  balB : ∀ s w (g : Nat → Nat), (s.acct w).borrowerIndex = s.borrowState.index →
    s.borrowState.block = s.blockNumber → P (s.withAcct w fun a => { a with borrow := g a.borrow }) ≤ P s
  /-- A speed change. -/
  speeds : ∀ s a b, P (speedsNext s a b) ≤ P s
  /-- Blocks passing. -/
  advance : ∀ sp s k, Inv gs gb sp s →
    P { s with blockNumber := s.blockNumber + k } ≤ P s + doubleScale * (k * (sp.1 + sp.2))
  /-- COMP sent to the Comptroller. -/
  drip : ∀ s x, P { s with reserve := s.reserve + x } ≤ P s

/-- `Phi` is such a potential. -/
theorem phi_moves (gs gb : Nat) : Moves gs gb (Phi gs gb) where
  supply sp s who hI := by
    obtain ⟨h1, h2⟩ := side_accrued s.supplyState s.blockNumber (totalSupply s)
      (sd' := sideS s) rfl (accrueSide_block _ _ _) (sideS s).speed
    obtain ⟨h3, h4⟩ := side_same (T := totalBorrows s) (i := s.borrowState.index) (u := unB s) rfl rfl
    exact phi_le h1 h3 h2 h4 (Ledger.sum_map_modify_le _ _ _ _ noAcct fun _ =>
      term_settleS (effStart_le_firstStart _ hI.startS.1 (Nat.le_trans hI.startS.2 h1)) rfl rfl rfl
        (by simp only [distS, creditFor_eq, accrualStart_eq, supplyNext_supplyState]; omega))
  borrow sp s who hI := by
    obtain ⟨h1, h2⟩ := side_accrued s.borrowState s.blockNumber (totalBorrows s)
      (sd' := sideB s) rfl (accrueSide_block _ _ _) (sideB s).speed
    obtain ⟨h3, h4⟩ := side_same (T := totalSupply s) (i := s.supplyState.index) (u := unS s) rfl rfl
    exact phi_le h3 h1 h4 h2 (Ledger.sum_map_modify_le _ _ _ _ noAcct fun _ =>
      term_settleB (effStart_le_firstStart _ hI.startB.1 (Nat.le_trans hI.startB.2 h1)) rfl rfl rfl
        (by simp only [distB, creditFor_eq, accrualStart_eq, borrowNext_borrowState]; omega))
  grant s who := by
    unfold grant; split
    · exact phi_accts rfl rfl rfl
        (Nat.le_of_eq (Ledger.sum_map_modify_eq _ _ _ _ noAcct fun _ => term_grant _ _ _ _ _))
    · exact Nat.le_refl _
  balS s w g hk _ := phi_accts rfl rfl rfl
    (Ledger.sum_map_modify_le _ _ _ _ noAcct fun _ => Nat.le_of_eq (term_balS _ hk))
  balB s w g hk _ := phi_accts rfl rfl rfl
    (Ledger.sum_map_modify_le _ _ _ _ noAcct fun _ => Nat.le_of_eq (term_balB _ hk))
  speeds s a b :=
    have h := speeds_sides s a b
    phi_le h.1.1 h.2.1 h.1.2 h.2.2 (Nat.le_refl _)
  advance sp s k hI := by
    have e1 := elapsed_add_mul k s.supplyState.speed hI.blockS
    have e2 := elapsed_add_mul k s.borrowState.speed hI.blockB
    unfold Phi unS unB; dsimp only
    rw [e1, e2, ← hI.speedS, ← hI.speedB]
    simp only [Nat.mul_add]; omega
  drip _ _ := Nat.le_refl _

/-- The `supply` field of `psi_moves`. -/
theorem psi_moves_supply (gs gb : Nat) (w : Account) : ∀ sp s who, Inv gs gb sp s → Psi gs gb w (supplyNext s who) ≤ Psi gs gb w s := by
    intro sp s who hI
    obtain ⟨h1, h2⟩ := side_accrued s.supplyState s.blockNumber (totalSupply s)
      (sd' := sideS s) rfl (accrueSide_block _ _ _) (sideS s).speed
    obtain ⟨h3, h4⟩ := side_same (T := totalBorrows s) (i := s.borrowState.index) (u := unB s) rfl rfl
    refine psi_le h1 h3 h2 h4 ?_ (Or.inr (unS_supplyNext s who)) (Or.inl ?_)
    · rw [acct_supplyNext]; split
      · exact term_settleS (effStart_le_firstStart _ hI.startS.1 (Nat.le_trans hI.startS.2 h1))
          rfl rfl rfl (by simp only [distS, creditFor_eq, accrualStart_eq, supplyNext_supplyState]; omega)
      · exact Nat.le_refl _
    · rw [acct_supplyNext]; split <;> rfl

/-- The `borrow` field of `psi_moves`. -/
theorem psi_moves_borrow (gs gb : Nat) (w : Account) : ∀ sp s who, Inv gs gb sp s → Psi gs gb w (borrowNext s who) ≤ Psi gs gb w s := by
    intro sp s who hI
    obtain ⟨h1, h2⟩ := side_accrued s.borrowState s.blockNumber (totalBorrows s)
      (sd' := sideB s) rfl (accrueSide_block _ _ _) (sideB s).speed
    obtain ⟨h3, h4⟩ := side_same (T := totalSupply s) (i := s.supplyState.index) (u := unS s) rfl rfl
    refine psi_le h3 h1 h4 h2 ?_ (Or.inl ?_) (Or.inr (unB_borrowNext s who))
    · rw [acct_borrowNext]; split
      · exact term_settleB (effStart_le_firstStart _ hI.startB.1 (Nat.le_trans hI.startB.2 h1))
          rfl rfl rfl (by simp only [distB, creditFor_eq, accrualStart_eq, borrowNext_borrowState]; omega)
      · exact Nat.le_refl _
    · rw [acct_borrowNext]; split <;> rfl

/-- The `grant` field of `psi_moves`. -/
theorem psi_moves_grant (gs gb : Nat) (w : Account) : ∀ s who, Psi gs gb w (grant s who) ≤ Psi gs gb w s := by
    intro s who
    unfold grant; split
    · have e := Ledger.getD_modify s.accts who w
        (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) noAcct
      refine psi_accts (w := w) rfl rfl rfl ?_ (Or.inl ?_) (Or.inl ?_)
      · show term _ _ _ _ ((s.accts.modify who _).getD w noAcct) ≤ _
        rw [e]; split
        · exact Nat.le_of_eq (term_grant _ _ _ _ _)
        · exact Nat.le_refl _
      · show ((s.accts.modify who _).getD w noAcct).supply = _
        rw [e]; split <;> rfl
      · show ((s.accts.modify who _).getD w noAcct).borrow = _
        rw [e]; split <;> rfl
    · exact Nat.le_refl _

/-- The `balS` field of `psi_moves`. -/
theorem psi_moves_balS (gs gb : Nat) (w : Account) : ∀ s v (g : Nat → Nat), (s.acct v).supplierIndex = s.supplyState.index → s.supplyState.block = s.blockNumber → Psi gs gb w (s.withAcct v fun a => { a with supply := g a.supply }) ≤ Psi gs gb w s := by
    intro s v g hk hc
    refine psi_accts rfl rfl rfl ?_ (Or.inr (by unfold unS; rw [hc]; simp)) (Or.inl ?_)
    · rw [acct_withAcct]; split
      · rename_i h; obtain ⟨rfl, -⟩ := h; exact Nat.le_of_eq (term_balS _ hk)
      · exact Nat.le_refl _
    · rw [acct_withAcct]; split <;> rfl

/-- The `balB` field of `psi_moves`. -/
theorem psi_moves_balB (gs gb : Nat) (w : Account) : ∀ s v (g : Nat → Nat), (s.acct v).borrowerIndex = s.borrowState.index → s.borrowState.block = s.blockNumber → Psi gs gb w (s.withAcct v fun a => { a with borrow := g a.borrow }) ≤ Psi gs gb w s := by
    intro s v g hk hc
    refine psi_accts rfl rfl rfl ?_ (Or.inl ?_) (Or.inr (by unfold unB; rw [hc]; simp))
    · rw [acct_withAcct]; split
      · rename_i h; obtain ⟨rfl, -⟩ := h; exact Nat.le_of_eq (term_balB _ hk)
      · exact Nat.le_refl _
    · rw [acct_withAcct]; split <;> rfl

/-- The `speeds` field of `psi_moves`. -/
theorem psi_moves_speeds (gs gb : Nat) (w : Account) : ∀ s a b, Psi gs gb w (speedsNext s a b) ≤ Psi gs gb w s :=
  fun s a b =>
    have h := speeds_sides s a b
    psi_le h.1.1 h.2.1 h.1.2 h.2.2 (Nat.le_refl _) (Or.inl rfl) (Or.inl rfl)

/-- `Psi` after blocks pass, with the account record and the indices of the state before. -/
theorem psi_advance_eq (gs gb : Nat) (w : Account) (s : St) (k : Nat) :
    Psi gs gb w { s with blockNumber := s.blockNumber + k } =
      term gs gb s.supplyState.index s.borrowState.index (s.acct w) +
        doubleScale * (if 0 < (s.acct w).supply then unS { s with blockNumber := s.blockNumber + k } else 0) +
        doubleScale * (if 0 < (s.acct w).borrow then unB { s with blockNumber := s.blockNumber + k } else 0) := rfl

/-- The unindexed supply emission after blocks pass. -/
theorem unS_advance (s : St) (k : Nat) (h : s.supplyState.block ≤ s.blockNumber) :
    unS { s with blockNumber := s.blockNumber + k } = unS s + k * s.supplyState.speed := by
  unfold unS; exact elapsed_add_mul k s.supplyState.speed h

/-- The unindexed borrow emission after blocks pass. -/
theorem unB_advance (s : St) (k : Nat) (h : s.borrowState.block ≤ s.blockNumber) :
    unB { s with blockNumber := s.blockNumber + k } = unB s + k * s.borrowState.speed := by
  unfold unB; exact elapsed_add_mul k s.borrowState.speed h

/-- The arithmetic of blocks passing for one account. -/
theorem advance_arith (D T u v a b k : Nat) (c1 c2 : Prop) [Decidable c1] [Decidable c2] :
    T + D * (if c1 then u + k * a else 0) + D * (if c2 then v + k * b else 0) ≤
      T + D * (if c1 then u else 0) + D * (if c2 then v else 0) + D * (k * (a + b)) := by
  split <;> split <;> simp only [Nat.mul_add, Nat.mul_zero, Nat.add_zero] <;> omega

/-- The `advance` field of `psi_moves`. -/
theorem psi_moves_advance (gs gb : Nat) (w : Account) : ∀ sp s k, Inv gs gb sp s →
    Psi gs gb w { s with blockNumber := s.blockNumber + k } ≤ Psi gs gb w s + doubleScale * (k * (sp.1 + sp.2)) := by
  intro sp s k hI
  rw [psi_advance_eq, unS_advance s k hI.blockS, unB_advance s k hI.blockB, hI.speedS, hI.speedB]
  exact advance_arith _ _ _ _ _ _ _ _ _
/-- The `drip` field of `psi_moves`. -/
theorem psi_moves_drip (gs gb : Nat) (w : Account) : ∀ s x, Psi gs gb w { s with reserve := s.reserve + x } ≤ Psi gs gb w s :=
  fun _ _ => Nat.le_refl _

/-- Every `Psi` is such a potential. -/
theorem psi_moves (gs gb : Nat) (w : Account) : Moves gs gb (Psi gs gb w) where
  supply := psi_moves_supply gs gb w
  borrow := psi_moves_borrow gs gb w
  grant := psi_moves_grant gs gb w
  balS := psi_moves_balS gs gb w
  balB := psi_moves_balB gs gb w
  speeds := psi_moves_speeds gs gb w
  advance := psi_moves_advance gs gb w
  drip := psi_moves_drip gs gb w

/-! ### One operation -/

/-- The invariant is kept by a state with the same sides and block whose accounts record no index
above the market's. -/
theorem Inv.of_eq {gs gb : Nat} {sp : Nat × Nat} {s s' : St} (h : Inv gs gb sp s)
    (hS : s'.supplyState = s.supplyState) (hB : s'.borrowState = s.borrowState)
    (hn : s'.blockNumber = s.blockNumber)
    (ha : ∀ a ∈ s'.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index) :
    Inv gs gb sp s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  exact ⟨hS ▸ h1, hB ▸ h2, hS ▸ hn ▸ h3, hB ▸ hn ▸ h4, hS ▸ h5, hB ▸ h6, hS ▸ hB ▸ ha⟩

/-- A state with the invariant is consistent. -/
theorem Inv.consistent {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) : Consistent s :=
  ⟨h.blockS, h.blockB, h.accts⟩

/-- A supply hook keeps the invariant. -/
theorem inv_supplyNext {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (who : Account) :
    Inv gs gb sp (supplyNext s who) :=
  have hi := (accrueSide_index s.supplyState s.blockNumber (totalSupply s)).1
  ⟨⟨h.startS.1, Nat.le_trans h.startS.2 hi⟩, h.startB,
    Nat.le_of_eq (accrueSide_block _ _ _), h.blockB, (accrueSide_speed _ _ _).trans h.speedS, h.speedB,
    forall_mem_modify (fun a ha => ⟨Nat.le_trans (h.accts a ha).1 hi, (h.accts a ha).2⟩)
      (fun a ha => ⟨Nat.le_refl _, (h.accts a ha).2⟩)⟩

/-- A borrow hook keeps the invariant. -/
theorem inv_borrowNext {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (who : Account) :
    Inv gs gb sp (borrowNext s who) :=
  have hi := (accrueSide_index s.borrowState s.blockNumber (totalBorrows s)).1
  ⟨h.startS, ⟨h.startB.1, Nat.le_trans h.startB.2 hi⟩, h.blockS,
    Nat.le_of_eq (accrueSide_block _ _ _), h.speedS, (accrueSide_speed _ _ _).trans h.speedB,
    forall_mem_modify (fun a ha => ⟨(h.accts a ha).1, Nat.le_trans (h.accts a ha).2 hi⟩)
      (fun a ha => ⟨(h.accts a ha).1, Nat.le_refl _⟩)⟩

/-- A balance change keeps the invariant. -/
theorem inv_withAcct {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (w : Account)
    {f : Acct → Acct}
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex ∧ (f a).borrowerIndex = a.borrowerIndex) :
    Inv gs gb sp (s.withAcct w f) :=
  h.of_eq rfl rfl rfl (forall_mem_modify h.accts fun a ha => (hf a).1 ▸ (hf a).2 ▸ h.accts a ha)

/-- A payment keeps the invariant. -/
theorem inv_grant {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (who : Account) :
    Inv gs gb sp (grant s who) := by
  unfold CompRewards.grant; split
  · exact h.of_eq rfl rfl rfl (forall_mem_modify h.accts fun a ha => h.accts a ha)
  · exact h

/-- A speed change keeps the invariant with the new ghost speeds. -/
theorem inv_speedsNext {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (a b : Nat) :
    Inv gs gb (a, b) (speedsNext s a b) := by
  obtain ⟨h1, h2, h3, h4, -, -, h7⟩ := h
  have iS : s.supplyState.index ≤ (speedsNext s a b).supplyState.index := by
    unfold CompRewards.Lib.speedsNext; dsimp only; split
    · exact Nat.le_refl _
    · exact (accrueSide_index _ _ _).1
  have iB : s.borrowState.index ≤ (speedsNext s a b).borrowState.index := by
    unfold CompRewards.Lib.speedsNext; dsimp only; split
    · exact Nat.le_refl _
    · exact (accrueSide_index _ _ _).1
  refine ⟨⟨h1.1, Nat.le_trans h1.2 iS⟩, ⟨h2.1, Nat.le_trans h2.2 iB⟩, ?_, ?_, ?_, ?_,
    fun x hx => ⟨Nat.le_trans (h7 x hx).1 iS, Nat.le_trans (h7 x hx).2 iB⟩⟩ <;>
    unfold CompRewards.Lib.speedsNext <;> dsimp only <;> split
  all_goals first
    | exact h3 | exact h4 | exact Nat.le_of_eq (accrueSide_block _ _ _) | assumption | rfl

/-- The facts a balance change after a supply hook needs: the account is settled and the side is
up to date. -/
theorem supplyNext_ready (s : St) (who : Account) (h : who < s.accts.length) :
    ((supplyNext s who).acct who).supplierIndex = (supplyNext s who).supplyState.index ∧
      (supplyNext s who).supplyState.block = (supplyNext s who).blockNumber :=
  ⟨supplyNext_settled s who who (Or.inl ⟨rfl, h⟩), accrueSide_block _ _ _⟩

/-- The same after a borrow hook. -/
theorem borrowNext_ready (s : St) (who : Account) (h : who < s.accts.length) :
    ((borrowNext s who).acct who).borrowerIndex = (borrowNext s who).borrowState.index ∧
      (borrowNext s who).borrowState.block = (borrowNext s who).blockNumber :=
  ⟨borrowNext_settled s who who (Or.inl ⟨rfl, h⟩), accrueSide_block _ _ _⟩

section Exec

variable {impl : Impl} (hOK : CallsSucceed impl) (hS : SupplyHookEffects impl)
  (hB : BorrowHookEffects impl) (hC : ClaimEffects impl) (hP : SetSpeedsEffects impl)
include hOK hS hB hC hP

/-- One operation keeps the invariant, with the ghost speeds following `nextSpeeds` (a speed
change cannot be refused, by REQ-CALLS-SUCCEED, so the stored speeds follow the ghost speeds), and
raises a potential with `Moves` by at most `doubleScale` times the COMP it emits. -/
theorem exec_step {gs gb : Nat} {P : St → Nat} (hm : Moves gs gb P) (sp : Nat × Nat) (s : St)
    (op : Op) (h : Inv gs gb sp s) :
    Inv gs gb (nextSpeeds sp op) (exec impl s op) ∧
      P (exec impl s op) ≤ P s + doubleScale * emittedBy sp op := by
  have keep : Inv gs gb sp s ∧ P s ≤ P s := ⟨h, Nat.le_refl _⟩
  cases op with
  | mint who x | redeem who x =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hlt
      split
      · rename_i e; rw [supply_eq hS e]
        have hr := supplyNext_ready s who hlt
        have hi := inv_supplyNext h who
        try split
        all_goals first
          | exact ⟨inv_withAcct hi who fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balS _ who (· + x) hr.1 hr.2) (hm.supply sp s who h)⟩
          | exact ⟨inv_withAcct hi who fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balS _ who (· - x) hr.1 hr.2) (hm.supply sp s who h)⟩
          | exact keep
      · exact keep
    · exact keep
  | borrow who x | repay who x =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hlt
      split
      · rename_i e; rw [borrow_eq hB e]
        have hr := borrowNext_ready s who hlt
        have hi := inv_borrowNext h who
        try split
        all_goals first
          | exact ⟨inv_withAcct hi who fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balB _ who (· + x) hr.1 hr.2) (hm.borrow sp s who h)⟩
          | exact ⟨inv_withAcct hi who fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balB _ who (· - x) hr.1 hr.2) (hm.borrow sp s who h)⟩
          | exact keep
      · exact keep
    · exact keep
  | transfer src dst x =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hc
      obtain ⟨hs, hd, hne⟩ := hc
      split
      · rename_i e₁; rw [supply_eq hS e₁]
        split
        · rename_i e₂; rw [supply_eq hS e₂]
          split
          · have r1 := supplyNext_ready s src hs
            have r2 := supplyNext_ready (supplyNext s src) dst
              (by rw [show (supplyNext s src).accts.length = s.accts.length from
                List.length_modify _ _ _]; exact hd)
            have r3 := supplyNext_settled (supplyNext s src) dst src (Or.inr r1)
            refine ⟨inv_withAcct (inv_withAcct (inv_supplyNext (inv_supplyNext h src) dst) src
                fun _ => by exact ⟨rfl, rfl⟩) dst fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balS _ dst (· + x) ?_ r2.2) (Nat.le_trans (hm.balS _ src (· - x) r3 r2.2)
                (Nat.le_trans (hm.supply sp _ dst (inv_supplyNext h src)) (hm.supply sp s src h)))⟩
            rw [acct_withAcct, ite_eq_right (fun h => hne h.1)]
            exact r2.1
          · exact keep
        · exact keep
      · exact keep
    · exact keep
  | claim who =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    cases e : impl s (.claim who) with
    | none => exact keep
    | some s' =>
      rw [Option.getD_some, claim_eq hC e]
      exact ⟨inv_grant (inv_supplyNext (inv_borrowNext h who) who) who, Nat.le_trans (hm.grant _ who)
        (Nat.le_trans (hm.supply sp _ who (inv_borrowNext h who)) (hm.borrow sp s who h))⟩
  | setSpeeds a b =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    cases e : impl s (.setSpeeds a b) with
    | none => have := hOK s (.setSpeeds a b) h.consistent; rw [e] at this; cases this
    | some s' =>
      rw [Option.getD_some, speeds_eq hP e]; exact ⟨inv_speedsNext h a b, hm.speeds s a b⟩
  | advance k =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨⟨h1, h2, Nat.le_trans h3 (Nat.le_add_right _ _), Nat.le_trans h4 (Nat.le_add_right _ _),
      h5, h6, h7⟩, hm.advance sp s k ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
  | drip x =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    exact ⟨h.of_eq rfl rfl rfl h.accts, hm.drip s x⟩

end Exec

/-! ### The upgrade -/

/-- The value the supply index starts from after the upgrade: `compInitialIndex` for an index the
upgrade initialized, otherwise the value it started from before. -/
def gsOf (L : Legacy) : Nat := if L.supplyIndex = 0 then compInitialIndex else L.supplyStart

/-- The value the borrow index starts from after the upgrade. -/
def gbOf (L : Legacy) : Nat := if L.borrowIndex = 0 then compInitialIndex else L.borrowStart

/-- The index of an initialized side. -/
theorem initSide_index (now : Nat) (sd : Side) :
    (initSide now sd).index = if sd.index = 0 then compInitialIndex else sd.index := by
  unfold initSide; split <;> rfl

/-- The block of an initialized side. -/
theorem initSide_block (now : Nat) (sd : Side) :
    (initSide now sd).block = if sd.index = 0 then now else sd.block := by
  unfold initSide; split <;> rfl

/-- The speed of an initialized side. -/
theorem initSide_speed (now : Nat) (sd : Side) : (initSide now sd).speed = sd.speed := by
  unfold initSide; split <;> rfl

/-- The upgrade of a well-formed state satisfies the invariant. -/
theorem inv_upgrade (L : Legacy) (hw : L.WellFormed) :
    Inv (gsOf L) (gbOf L) (L.compSpeed, L.compSpeed) (upgrade L) := by
  obtain ⟨hs1, hs2, hb1, hb2, hbs, hbb, ha⟩ := hw
  refine ⟨?_, ?_, ?_, ?_, initSide_speed _ _, initSide_speed _ _, ?_⟩ <;>
    simp only [upgrade, initSide_index, initSide_block, gsOf, gbOf]
  · split
    · exact ⟨Or.inr rfl, Nat.le_refl _⟩
    · exact ⟨hs1, hs2⟩
  · split
    · exact ⟨Or.inr rfl, Nat.le_refl _⟩
    · exact ⟨hb1, hb2⟩
  · split
    · exact Nat.le_refl _
    · exact hbs
  · split
    · exact Nat.le_refl _
    · exact hbb
  · intro a hm
    obtain ⟨h1, h2⟩ := ha a hm
    constructor <;> split <;> omega

/-- The pending COMP of one side at the upgrade is at most what it was before. -/
theorem pend_upgrade (idx start r u : Nat) (h : r ≤ idx) :
    pending u (effStart (if idx = 0 then compInitialIndex else start) r)
        (if idx = 0 then compInitialIndex else idx) ≤ u * (idx - legacyStart start r) := by
  split
  · have : r = 0 := by omega
    subst this; simp
  · exact Nat.le_refl _

/-- An account's term at the upgrade is its COMP credited, scaled, plus what it was owed. -/
theorem term_upgrade (L : Legacy) (a : Acct)
    (ha : a.supplierIndex ≤ L.supplyIndex ∧ a.borrowerIndex ≤ L.borrowIndex) :
    term (gsOf L) (gbOf L) (upgrade L).supplyState.index (upgrade L).borrowState.index a ≤
      (a.accrued + a.wallet) * doubleScale + L.pendingScaled a := by
  have h1 := pend_upgrade L.supplyIndex L.supplyStart a.supplierIndex a.supply ha.1
  have h2 := pend_upgrade L.borrowIndex L.borrowStart a.borrowerIndex a.borrow ha.2
  simp only [term, Legacy.pendingScaled, upgrade, initSide_index, gsOf, gbOf]
  omega

/-- Nothing unindexed at the upgrade beyond what was unindexed before, supply side. -/
theorem unS_upgrade (L : Legacy) : unS (upgrade L) ≤ L.unindexedSupply := by
  simp only [unS, Legacy.unindexedSupply, upgrade, initSide_block, initSide_speed]
  split
  · simp
  · exact Nat.le_refl _

/-- Nothing unindexed at the upgrade beyond what was unindexed before, borrow side. -/
theorem unB_upgrade (L : Legacy) : unB (upgrade L) ≤ L.unindexedBorrow := by
  simp only [unB, Legacy.unindexedBorrow, upgrade, initSide_block, initSide_speed]
  split
  · simp
  · exact Nat.le_refl _

/-- The global potential at the upgrade. -/
theorem phi_upgrade (L : Legacy) (hw : L.WellFormed) :
    Phi (gsOf L) (gbOf L) (upgrade L) ≤
      ((upgrade L).credited + L.unindexedSupply + L.unindexedBorrow) * doubleScale +
        (L.accts.map L.pendingScaled).sum := by
  have h1 := Ledger.sum_map_le_add L.accts (fun a => (a.accrued + a.wallet) * doubleScale)
    (term (gsOf L) (gbOf L) (upgrade L).supplyState.index (upgrade L).borrowState.index)
    L.pendingScaled (fun a ha => term_upgrade L a (hw.2.2.2.2.2.2 a ha))
  rw [Ledger.sum_map_mul_right] at h1
  have h2 := Nat.mul_le_mul_left doubleScale (unS_upgrade L)
  have h3 := Nat.mul_le_mul_left doubleScale (unB_upgrade L)
  have e : (upgrade L).accts = L.accts := rfl
  unfold Phi St.credited
  rw [e, Nat.add_mul, Nat.add_mul, Nat.mul_comm L.unindexedSupply, Nat.mul_comm L.unindexedBorrow]
  omega

/-- The arithmetic of an account's potential at the upgrade. -/
theorem upgrade_arith (D T u v U V acc P : Nat) (c1 c2 : Prop) [Decidable c1] [Decidable c2]
    (hT : T ≤ acc * D + P) (hu : D * u ≤ D * U) (hv : D * v ≤ D * V) :
    T + D * (if c1 then u else 0) + D * (if c2 then v else 0) ≤
      (acc + ((if c1 then U else 0) + (if c2 then V else 0))) * D + P := by
  split <;> split <;>
    simp only [Nat.add_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.mul_comm U, Nat.mul_comm V] <;> omega

/-- The potential of one account at the upgrade. -/
theorem psi_upgrade (L : Legacy) (hw : L.WellFormed) (who : Account) :
    Psi (gsOf L) (gbOf L) who (upgrade L) ≤
      ((upgrade L).creditedTo who +
          ((if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
            (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0))) * doubleScale +
        L.pendingScaled (L.accts.getD who noAcct) := by
  have hacct : (upgrade L).acct who = L.accts.getD who noAcct := rfl
  have hp : term (gsOf L) (gbOf L) (upgrade L).supplyState.index (upgrade L).borrowState.index
      (L.accts.getD who noAcct) ≤
        ((L.accts.getD who noAcct).accrued + (L.accts.getD who noAcct).wallet) * doubleScale +
          L.pendingScaled (L.accts.getD who noAcct) := by
    rcases Ledger.getD_mem_or L.accts who noAcct with hm | hm
    · exact term_upgrade L _ (hw.2.2.2.2.2.2 _ hm)
    · rw [hm]; simp [term, noAcct]
  have h2 := Nat.mul_le_mul_left doubleScale (unS_upgrade L)
  have h3 := Nat.mul_le_mul_left doubleScale (unB_upgrade L)
  unfold Psi St.creditedTo
  rw [hacct]
  exact upgrade_arith _ _ _ _ _ _ _ _ _ _ hp h2 h3

/-- COMP credited, scaled, is covered by the global potential. -/
theorem credited_le_phi (gs gb : Nat) (s : St) : s.credited * doubleScale ≤ Phi gs gb s := by
  have := sum_mul_le_of_le s.accts (fun a => a.accrued + a.wallet)
    (term gs gb s.supplyState.index s.borrowState.index) doubleScale (fun a _ => by unfold term; omega)
  unfold Phi St.credited; omega

/-- COMP credited to one account, scaled, is covered by its potential. -/
theorem creditedTo_le_psi (gs gb : Nat) (w : Account) (s : St) :
    s.creditedTo w * doubleScale ≤ Psi gs gb w s := by
  unfold Psi term St.creditedTo; omega

/-- The arithmetic of the potential of an account without a position, at any scale `D`. -/
theorem noPosition_arith (D A x y p q u v : Nat) (hx : x = 0) (hy : y = 0) :
    A * D + x * p + y * q + D * (if 0 < x then u else 0) + D * (if 0 < y then v else 0) = A * D := by
  subst hx; subst hy
  rw [if_neg (Nat.lt_irrefl 0), if_neg (Nat.lt_irrefl 0)]
  simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero]

/-- The potential of an account without a position is its COMP credited, scaled. -/
theorem psi_noPosition (gs gb : Nat) (s : St) (who : Account) (h : NoPosition s who) :
    Psi gs gb who s = s.creditedTo who * doubleScale := by
  unfold Psi term St.creditedTo pending
  exact noPosition_arith _ _ _ _ _ _ _ _ h.1 h.2

/-- An equation to a multiple, as the bound `run_bound_via_potential` takes, at any scale. -/
theorem le_mul_add_zero (P Q D : Nat) (h : P = Q * D) : P ≤ Q * D + 0 := by
  rw [h, Nat.add_zero]; exact Nat.le_refl _

/-- A bound with no remainder, at any scale. -/
theorem le_of_le_add_zero_div (X Y D : Nat) (h : X ≤ Y + 0 / D) : X ≤ Y := by
  rw [Nat.zero_div, Nat.add_zero] at h; exact h

/-! ### The three bounds -/

section Bounds

variable {impl : Impl} (hOK : CallsSucceed impl) (hS : SupplyHookEffects impl)
  (hB : BorrowHookEffects impl) (hC : ClaimEffects impl) (hP : SetSpeedsEffects impl)
include hOK hS hB hC hP

/-- REQ-REWARDS-BOUNDED for every implementation that meets the five per-call requirements. -/
theorem rewards_bounded : RewardsBounded impl := by
  intro L ops hw
  have h := Seq.run_bound_via_potential (Inv (gsOf L) (gbOf L)) (Phi (gsOf L) (gbOf L))
    St.credited doubleScale_pos (fun sp s op hI => (exec_step hOK hS hB hC hP (phi_moves _ _) sp s op hI).1)
    (fun sp s op hI => (exec_step hOK hS hB hC hP (phi_moves _ _) sp s op hI).2)
    (fun _ s _ => credited_le_phi _ _ s) (inv_upgrade L hw) (phi_upgrade L hw) ops
  rw [run_eq, emitted_eq]
  unfold Legacy.owed
  omega

/-- REQ-ACCOUNT-BOUNDED for every implementation that meets the five per-call requirements. -/
theorem account_bounded : AccountBounded impl := by
  intro L ops who hw
  have h := Seq.run_bound_via_potential (Inv (gsOf L) (gbOf L)) (Psi (gsOf L) (gbOf L) who)
    (fun t => t.creditedTo who) doubleScale_pos
    (fun sp s op hI => (exec_step hOK hS hB hC hP (psi_moves _ _ who) sp s op hI).1)
    (fun sp s op hI => (exec_step hOK hS hB hC hP (psi_moves _ _ who) sp s op hI).2)
    (fun _ s _ => creditedTo_le_psi _ _ who s) (inv_upgrade L hw) (psi_upgrade L hw who) ops
  rw [run_eq, emitted_eq]
  unfold Legacy.owedTo
  omega

/-- REQ-NO-BACKDATED-REWARDS for every implementation that meets the five per-call
requirements. -/
theorem no_backdated : NoBackdatedRewards impl := by
  intro L history ops who hw hpos
  simp only [run_eq] at hpos ⊢
  rw [speedsAfter_eq, emitted_eq]
  have hI := (Seq.run_le_accum (Inv (gsOf L) (gbOf L)) (fun _ => 0) (f := emittedBy)
    (fun sp s op hI => (exec_step hOK hS hB hC hP (phi_moves _ _) sp s op hI).1)
    (fun _ _ _ _ => Nat.zero_le _)
    (inv_upgrade L hw) history).2
  have h := Seq.run_bound_via_potential (Inv (gsOf L) (gbOf L)) (Psi (gsOf L) (gbOf L) who)
    (fun t => t.creditedTo who) doubleScale_pos
    (fun sp s op hI => (exec_step hOK hS hB hC hP (psi_moves _ _ who) sp s op hI).1)
    (fun sp s op hI => (exec_step hOK hS hB hC hP (psi_moves _ _ who) sp s op hI).2)
    (fun _ s _ => creditedTo_le_psi _ _ who s) hI
    (B := (Seq.run (exec impl) (upgrade L) history).creditedTo who) (R := 0)
    (le_mul_add_zero _ _ _ (psi_noPosition _ _ _ _ hpos)) ops
  exact le_of_le_add_zero_div _ _ _ h

/-- The three sequence requirements of `rw-compound-comp` follow from the five per-call
requirements (REQ-CALLS-SUCCEED, REQ-SUPPLY-HOOK, REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS), for
every implementation. -/
theorem bounds_of_calls :
    RewardsBounded impl ∧ AccountBounded impl ∧ NoBackdatedRewards impl :=
  ⟨rewards_bounded hOK hS hB hC hP, account_bounded hOK hS hB hC hP, no_backdated hOK hS hB hC hP⟩

end Bounds

end Lib

/-! ## The locked requirements -/

theorem req_calls_succeed       : CallsSucceed comptroller := by rw [comptroller_eq]; exact spec_calls_succeed
theorem req_supply_hook         : SupplyHookEffects comptroller := by rw [comptroller_eq]; exact spec_supply_hook
theorem req_borrow_hook         : BorrowHookEffects comptroller := by rw [comptroller_eq]; exact spec_borrow_hook
theorem req_claim               : ClaimEffects comptroller := by rw [comptroller_eq]; exact spec_claim
theorem req_set_speeds          : SetSpeedsEffects comptroller := by rw [comptroller_eq]; exact spec_set_speeds
theorem req_rewards_bounded     : RewardsBounded comptroller :=
  Lib.rewards_bounded req_calls_succeed req_supply_hook req_borrow_hook req_claim req_set_speeds
theorem req_account_bounded     : AccountBounded comptroller :=
  Lib.account_bounded req_calls_succeed req_supply_hook req_borrow_hook req_claim req_set_speeds
theorem req_no_backdated        : NoBackdatedRewards comptroller :=
  Lib.no_backdated req_calls_succeed req_supply_hook req_borrow_hook req_claim req_set_speeds

end CompRewards
