import CompRewards.Spec
namespace CompRewards
def supplyAcc (s : St) : Side := accrueSide s.supplyState s.blockNumber (totalSupply s)
def borrowAcc (s : St) : Side := accrueSide s.borrowState s.blockNumber (totalBorrows s)
def supplyExec (s : St) (who : Account) : St := ({ s with supplyState := (supplyAcc s) }).withAcct who fun a => { a with supplierIndex := (supplyAcc s).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (supplyAcc s).index) (supplyAcc s).index }
def borrowExec (s : St) (who : Account) : St := ({ s with borrowState := (borrowAcc s) }).withAcct who fun a => { a with borrowerIndex := (borrowAcc s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borrowAcc s).index) (borrowAcc s).index }
def speedsExec (s : St) (sup bor : Nat) : St := { { s with supplyState := (if s.supplyState.speed = sup then s.supplyState else { (supplyAcc s) with speed := sup }) } with borrowState := (if s.borrowState.speed = bor then s.borrowState else { (borrowAcc s) with speed := bor }) }
theorem accrue_ge (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · rename_i hc
    exact Nat.le_add_right sd.index _
  · rename_i hc
    exact Nat.le_refl _
theorem accrue_block (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rename_i hc
    rfl
  · rename_i hc
    rfl
theorem accrualStart_le (recorded index : Nat) (h : recorded ≤ index) : accrualStart recorded index ≤ index := by
  unfold accrualStart
  split
  · rename_i hr
    split
    · rename_i hi
      exact hi
    · rename_i hi
      exact Nat.zero_le index
  · rename_i hr
    simpa [hr] using h
theorem acct_mem (s : St) (who : Account) (hw : who < s.accts.length) : s.acct who ∈ s.accts := by
  unfold St.acct
  have heq : s.accts[who]'hw = s.accts.getD who noAcct := List.getElem_eq_getD noAcct
  rw [← heq]
  exact List.getElem_mem hw
theorem acct_supplier_le_old (s : St) (hc : Consistent s) (who : Account) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  obtain ⟨_, _, hall⟩ := hc
  by_cases hw : who < s.accts.length
  · have hm : s.acct who ∈ s.accts := acct_mem s who hw
    exact (hall (s.acct who) hm).1
  · have hle : s.accts.length ≤ who := Nat.le_of_not_lt hw
    have hnone : s.accts[who]? = none := List.getElem?_eq_none hle
    have hget : s.accts.getD who noAcct = noAcct := by simp [List.getD, hnone]
    unfold St.acct
    rw [hget]
    exact Nat.zero_le _
theorem acct_borrower_le_old (s : St) (hc : Consistent s) (who : Account) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  obtain ⟨_, _, hall⟩ := hc
  by_cases hw : who < s.accts.length
  · have hm : s.acct who ∈ s.accts := acct_mem s who hw
    exact (hall (s.acct who) hm).2
  · have hle : s.accts.length ≤ who := Nat.le_of_not_lt hw
    have hnone : s.accts[who]? = none := List.getElem?_eq_none hle
    have hget : s.accts.getD who noAcct = noAcct := by simp [List.getD, hnone]
    unfold St.acct
    rw [hget]
    exact Nat.zero_le _
theorem supplyAcc_ge (s : St) : s.supplyState.index ≤ (supplyAcc s).index := accrue_ge s.supplyState s.blockNumber (totalSupply s)
theorem borrowAcc_ge (s : St) : s.borrowState.index ≤ (borrowAcc s).index := accrue_ge s.borrowState s.blockNumber (totalBorrows s)
theorem supplyAcc_block (s : St) : (supplyAcc s).block = s.blockNumber := accrue_block s.supplyState s.blockNumber (totalSupply s)
theorem borrowAcc_block (s : St) : (borrowAcc s).block = s.blockNumber := accrue_block s.borrowState s.blockNumber (totalBorrows s)
theorem borrowExec_supplyState (s : St) (who : Account) : (borrowExec s who).supplyState = s.supplyState := rfl
theorem borrowExec_blockNumber (s : St) (who : Account) : (borrowExec s who).blockNumber = s.blockNumber := rfl
theorem supplyExec_borrowState (s : St) (who : Account) : (supplyExec s who).borrowState = s.borrowState := rfl
theorem supplyExec_blockNumber (s : St) (who : Account) : (supplyExec s who).blockNumber = s.blockNumber := rfl
theorem borrowExec_supplierIndex (s : St) (who : Account) : ((borrowExec s who).acct who).supplierIndex = ((s.acct who).supplierIndex) := by
  unfold borrowExec St.acct St.withAcct
  simp only
  by_cases hw : who < s.accts.length
  · have hlen : who < (s.accts.modify who fun a => { a with borrowerIndex := (borrowAcc s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borrowAcc s).index) (borrowAcc s).index }).length := by
      rw [List.length_modify]
      exact hw
    have heq1 : (s.accts.modify who fun a => { a with borrowerIndex := (borrowAcc s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borrowAcc s).index) (borrowAcc s).index })[who]'hlen = (fun a => { a with borrowerIndex := (borrowAcc s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borrowAcc s).index) (borrowAcc s).index }) (s.accts[who]'hw) := by
      have h := List.getElem_modify (fun a => { a with borrowerIndex := (borrowAcc s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borrowAcc s).index) (borrowAcc s).index }) who s.accts who hlen
      simpa using h
    have heqD1 : (s.accts.modify who fun a => { a with borrowerIndex := (borrowAcc s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borrowAcc s).index) (borrowAcc s).index }).getD who noAcct = (s.accts.modify who fun a => { a with borrowerIndex := (borrowAcc s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borrowAcc s).index) (borrowAcc s).index })[who]'hlen := (List.getElem_eq_getD noAcct).symm
    have heqD0 : s.accts.getD who noAcct = s.accts[who]'hw := (List.getElem_eq_getD noAcct).symm
    rw [heqD1, heq1, ← heqD0]
  · have hle : s.accts.length ≤ who := Nat.le_of_not_lt hw
    have hnone : s.accts[who]? = none := List.getElem?_eq_none hle
    simp [hnone]
theorem modify_consistent_supply_aux (l : List Acct) (who : Nat) (newIdx : Nat) (oldSupIdx : Nat) (borIdx : Nat) (f : Acct → Acct) (hall : ∀ a ∈ l, a.supplierIndex ≤ oldSupIdx ∧ a.borrowerIndex ≤ borIdx) (hf_sup : ∀ a, (f a).supplierIndex = newIdx) (hf_bor : ∀ a, (f a).borrowerIndex = a.borrowerIndex) (hle : oldSupIdx ≤ newIdx) : ∀ a ∈ l.modify who f, a.supplierIndex ≤ newIdx ∧ a.borrowerIndex ≤ borIdx := by
  induction l generalizing who with
  | nil =>
    intro a ha
    simp at ha
  | cons x xs ih =>
    cases who with
    | zero =>
      have hmod : (x :: xs).modify 0 f = f x :: xs := rfl
      intro a ha
      rw [hmod, List.mem_cons] at ha
      cases ha with
      | inl heq2 =>
        rw [heq2]
        refine ⟨?_, ?_⟩
        · rw [hf_sup x]
          exact Nat.le_refl _
        · rw [hf_bor x]
          have hx : x ∈ x :: xs := List.mem_cons_self
          exact (hall x hx).2
      | inr hmem =>
        have hxmem : a ∈ x :: xs := List.mem_cons_of_mem x hmem
        have hold2 := hall a hxmem
        exact ⟨Nat.le_trans hold2.1 hle, hold2.2⟩
    | succ n =>
      have hmod : (x :: xs).modify (n + 1) f = x :: xs.modify n f := rfl
      intro a ha
      rw [hmod, List.mem_cons] at ha
      cases ha with
      | inl heq2 =>
        rw [heq2]
        have hx : x ∈ x :: xs := List.mem_cons_self
        have hold2 := hall x hx
        exact ⟨Nat.le_trans hold2.1 hle, hold2.2⟩
      | inr hmem =>
        have hall_xs : ∀ a ∈ xs, a.supplierIndex ≤ oldSupIdx ∧ a.borrowerIndex ≤ borIdx := by
          intro b hb
          exact hall b (List.mem_cons_of_mem x hb)
        exact ih n hall_xs a hmem
theorem modify_consistent_borrow_aux (l : List Acct) (who : Nat) (supIdx : Nat) (newIdx : Nat) (oldBorIdx : Nat) (f : Acct → Acct) (hall : ∀ a ∈ l, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ oldBorIdx) (hf_sup : ∀ a, (f a).supplierIndex = a.supplierIndex) (hf_bor : ∀ a, (f a).borrowerIndex = newIdx) (hle : oldBorIdx ≤ newIdx) : ∀ a ∈ l.modify who f, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ newIdx := by
  induction l generalizing who with
  | nil =>
    intro a ha
    simp at ha
  | cons x xs ih =>
    cases who with
    | zero =>
      have hmod : (x :: xs).modify 0 f = f x :: xs := rfl
      intro a ha
      rw [hmod, List.mem_cons] at ha
      cases ha with
      | inl heq2 =>
        rw [heq2]
        refine ⟨?_, ?_⟩
        · rw [hf_sup x]
          have hx : x ∈ x :: xs := List.mem_cons_self
          exact (hall x hx).1
        · rw [hf_bor x]
          exact Nat.le_refl _
      | inr hmem =>
        have hxmem : a ∈ x :: xs := List.mem_cons_of_mem x hmem
        have hold2 := hall a hxmem
        exact ⟨hold2.1, Nat.le_trans hold2.2 hle⟩
    | succ n =>
      have hmod : (x :: xs).modify (n + 1) f = x :: xs.modify n f := rfl
      intro a ha
      rw [hmod, List.mem_cons] at ha
      cases ha with
      | inl heq2 =>
        rw [heq2]
        have hx : x ∈ x :: xs := List.mem_cons_self
        have hold2 := hall x hx
        exact ⟨hold2.1, Nat.le_trans hold2.2 hle⟩
      | inr hmem =>
        have hall_xs : ∀ a ∈ xs, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ oldBorIdx := by
          intro b hb
          exact hall b (List.mem_cons_of_mem x hb)
        exact ih n hall_xs a hmem
theorem modify_consistent_both_aux (l : List Acct) (who : Nat) (supIdx : Nat) (borIdx : Nat) (f : Acct → Acct) (hall : ∀ a ∈ l, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx) (hf_sup : ∀ a, (f a).supplierIndex = a.supplierIndex) (hf_bor : ∀ a, (f a).borrowerIndex = a.borrowerIndex) : ∀ a ∈ l.modify who f, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx := by
  induction l generalizing who with
  | nil =>
    intro a ha
    simp at ha
  | cons x xs ih =>
    cases who with
    | zero =>
      have hmod : (x :: xs).modify 0 f = f x :: xs := rfl
      intro a ha
      rw [hmod, List.mem_cons] at ha
      cases ha with
      | inl heq2 =>
        rw [heq2]
        rw [hf_sup x, hf_bor x]
        have hx : x ∈ x :: xs := List.mem_cons_self
        exact hall x hx
      | inr hmem =>
        exact hall a (List.mem_cons_of_mem x hmem)
    | succ n =>
      have hmod : (x :: xs).modify (n + 1) f = x :: xs.modify n f := rfl
      intro a ha
      rw [hmod, List.mem_cons] at ha
      cases ha with
      | inl heq2 =>
        rw [heq2]
        have hx : x ∈ x :: xs := List.mem_cons_self
        exact hall x hx
      | inr hmem =>
        have hall_xs : ∀ a ∈ xs, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx := by
          intro b hb
          exact hall b (List.mem_cons_of_mem x hb)
        exact ih n hall_xs a hmem
theorem supplyDist_consistent (s : St) (who : Account) (s' : St) (hc : Consistent s) (h : SupplyDistributed s who s') : Consistent s' := by
  obtain ⟨hsup, hbor, hall⟩ := hc
  obtain ⟨hblock, hstart, heq⟩ := h
  have hacc_block : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber := accrue_block _ _ _
  have hacc_ge : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accrue_ge _ _ _
  have hs'_block : s'.blockNumber = s.blockNumber := by rw [heq]
  have hs'_supply : s'.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by rw [heq]
  have hs'_borrow : s'.borrowState = s.borrowState := by rw [heq]
  have hs'_accts : s'.accts = s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } := by rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs'_supply, hacc_block, hs'_block]
    exact Nat.le_refl _
  · rw [hs'_borrow, hs'_block]; exact hbor
  · rw [hs'_accts, hs'_supply, hs'_borrow]
    exact modify_consistent_supply_aux s.accts who (accrueSide s.supplyState s.blockNumber (totalSupply s)).index s.supplyState.index s.borrowState.index (fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) hall (fun a => rfl) (fun a => rfl) hacc_ge
theorem borrowDist_consistent (s : St) (who : Account) (s' : St) (hc : Consistent s) (h : BorrowDistributed s who s') : Consistent s' := by
  obtain ⟨hsup, hbor, hall⟩ := hc
  obtain ⟨hblock, hstart, heq⟩ := h
  have hacc_block : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber := accrue_block _ _ _
  have hacc_ge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrue_ge _ _ _
  have hs'_block : s'.blockNumber = s.blockNumber := by rw [heq]
  have hs'_supply : s'.supplyState = s.supplyState := by rw [heq]
  have hs'_borrow : s'.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [heq]
  have hs'_accts : s'.accts = s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } := by rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs'_supply, hs'_block]; exact hsup
  · rw [hs'_borrow, hacc_block, hs'_block]
    exact Nat.le_refl _
  · rw [hs'_accts, hs'_supply, hs'_borrow]
    exact modify_consistent_borrow_aux s.accts who s.supplyState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index s.borrowState.index (fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }) hall (fun a => rfl) (fun a => rfl) hacc_ge
theorem grant_consistent (s : St) (who : Account) (hc : Consistent s) : Consistent (grant s who) := by
  obtain ⟨hsup, hbor, hall⟩ := hc
  unfold grant
  split
  · rename_i hcnd
    refine ⟨hsup, hbor, ?_⟩
    exact modify_consistent_both_aux s.accts who s.supplyState.index s.borrowState.index (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) hall (fun a => rfl) (fun a => rfl)
  · rename_i hcnd
    exact ⟨hsup, hbor, hall⟩
theorem speedsSet_consistent (s : St) (sup bor : Nat) (s' : St) (hc : Consistent s) (h : SpeedsSet s sup bor s') : Consistent s' := by
  obtain ⟨hsup, hbor, hall⟩ := hc
  obtain ⟨h1, h2, heq⟩ := h
  have hs'_block : s'.blockNumber = s.blockNumber := by rw [heq]
  have hs'_accts : s'.accts = s.accts := by rw [heq]
  have hsup_new : s.supplyState.index ≤ s'.supplyState.index := by
    rw [heq]
    by_cases heq2 : s.supplyState.speed = sup
    · simp [heq2]
    · simp [heq2]
      exact accrue_ge _ _ _
  have hbor_new : s.borrowState.index ≤ s'.borrowState.index := by
    rw [heq]
    by_cases heq2 : s.borrowState.speed = bor
    · simp [heq2]
    · simp [heq2]
      exact accrue_ge _ _ _
  have hsup_block : s'.supplyState.block ≤ s'.blockNumber := by
    rw [heq]
    by_cases heq2 : s.supplyState.speed = sup
    · simp [heq2]
      exact hsup
    · simp [heq2]
      rw [accrue_block]
      exact Nat.le_refl _
  have hbor_block : s'.borrowState.block ≤ s'.blockNumber := by
    rw [heq]
    by_cases heq2 : s.borrowState.speed = bor
    · simp [heq2]
      exact hbor
    · simp [heq2]
      rw [accrue_block]
      exact Nat.le_refl _
  refine ⟨hsup_block, hbor_block, ?_⟩
  · rw [hs'_accts]
    intro a ha
    obtain ⟨hsle, hble⟩ := hall a ha
    exact ⟨Nat.le_trans hsle hsup_new, Nat.le_trans hble hbor_new⟩
theorem withAcct_consistent (s : St) (who : Account) (f : Acct → Acct) (hc : Consistent s) (hf_sup : ∀ a, (f a).supplierIndex = a.supplierIndex) (hf_bor : ∀ a, (f a).borrowerIndex = a.borrowerIndex) : Consistent (s.withAcct who f) := by
  obtain ⟨hsup, hbor, hall⟩ := hc
  unfold St.withAcct
  refine ⟨hsup, hbor, ?_⟩
  exact modify_consistent_both_aux s.accts who s.supplyState.index s.borrowState.index f hall hf_sup hf_bor
theorem claim_consistent (s : St) (who : Account) (s' : St) (hc : Consistent s) (h : Claimed s who s') : Consistent s' := by
  obtain ⟨m1, m2, hb, hs, heq⟩ := h
  have hc1 : Consistent m1 := borrowDist_consistent s who m1 hc hb
  have hc2 : Consistent m2 := supplyDist_consistent m1 who m2 hc1 hs
  rw [heq]
  exact grant_consistent m2 who hc2
def comptroller : Impl := fun s c => match c with | .supplyHook who => (if hh : s.supplyState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).supplierIndex (supplyAcc s).index ≤ (supplyAcc s).index then some (supplyExec s who) else none) | .borrowHook who => (if hh : s.borrowState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).borrowerIndex (borrowAcc s).index ≤ (borrowAcc s).index then some (borrowExec s who) else none) | .claim who => (if hh1 : s.borrowState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).borrowerIndex (borrowAcc s).index ≤ (borrowAcc s).index then (if hh2 : (borrowExec s who).supplyState.block ≤ (borrowExec s who).blockNumber ∧ accrualStart ((borrowExec s who).acct who).supplierIndex (supplyAcc (borrowExec s who)).index ≤ (supplyAcc (borrowExec s who)).index then some (grant (supplyExec (borrowExec s who) who) who) else none) else none) | .setSpeeds a b => (if hh1 : s.supplyState.speed = a ∨ s.supplyState.block ≤ s.blockNumber then (if hh2 : s.borrowState.speed = b ∨ s.borrowState.block ≤ s.blockNumber then some (speedsExec s a b) else none) else none)
theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  split at h
  · rename_i hc
    have heq : supplyExec s who = s' := by simpa using h
    obtain ⟨h1, h2⟩ := hc
    refine ⟨h1, by simpa [supplyAcc] using h2, by rw [← heq]; rfl⟩
  · rename_i hc
    cases h
theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  obtain ⟨hsup, hbor, hall⟩ := hc
  cases c with
  | supplyHook who =>
    have hrec : (s.acct who).supplierIndex ≤ (supplyAcc s).index := by
      have hold : (s.acct who).supplierIndex ≤ s.supplyState.index := acct_supplier_le_old s ⟨hsup, hbor, hall⟩ who
      exact Nat.le_trans hold (supplyAcc_ge s)
    have hcond : s.supplyState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).supplierIndex (supplyAcc s).index ≤ (supplyAcc s).index :=
      ⟨hsup, accrualStart_le _ _ hrec⟩
    unfold comptroller
    simp only
    simp [hcond]
  | borrowHook who =>
    have hrec : (s.acct who).borrowerIndex ≤ (borrowAcc s).index := by
      have hold : (s.acct who).borrowerIndex ≤ s.borrowState.index := acct_borrower_le_old s ⟨hsup, hbor, hall⟩ who
      exact Nat.le_trans hold (borrowAcc_ge s)
    have hcond : s.borrowState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).borrowerIndex (borrowAcc s).index ≤ (borrowAcc s).index :=
      ⟨hbor, accrualStart_le _ _ hrec⟩
    unfold comptroller
    simp only
    simp [hcond]
  | claim who =>
    have hrecB : (s.acct who).borrowerIndex ≤ (borrowAcc s).index := by
      have hold : (s.acct who).borrowerIndex ≤ s.borrowState.index := acct_borrower_le_old s ⟨hsup, hbor, hall⟩ who
      exact Nat.le_trans hold (borrowAcc_ge s)
    have hcondB : s.borrowState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).borrowerIndex (borrowAcc s).index ≤ (borrowAcc s).index :=
      ⟨hbor, accrualStart_le _ _ hrecB⟩
    have hsup1 : (borrowExec s who).supplyState.block ≤ (borrowExec s who).blockNumber := by
      rw [borrowExec_supplyState, borrowExec_blockNumber]
      exact hsup
    have hrecS : ((borrowExec s who).acct who).supplierIndex ≤ (supplyAcc (borrowExec s who)).index := by
      have holdOld : (s.acct who).supplierIndex ≤ s.supplyState.index := acct_supplier_le_old s ⟨hsup, hbor, hall⟩ who
      have heqIdx : ((borrowExec s who).acct who).supplierIndex = (s.acct who).supplierIndex := borrowExec_supplierIndex s who
      have hge : s.supplyState.index ≤ (supplyAcc (borrowExec s who)).index := by
        have h1 : s.supplyState = (borrowExec s who).supplyState := (borrowExec_supplyState s who).symm
        have h2 : s.blockNumber = (borrowExec s who).blockNumber := (borrowExec_blockNumber s who).symm
        have hge0 : (borrowExec s who).supplyState.index ≤ (supplyAcc (borrowExec s who)).index := supplyAcc_ge (borrowExec s who)
        rw [← h1] at hge0
        exact hge0
      rw [heqIdx]
      exact Nat.le_trans holdOld hge
    have hcondS : (borrowExec s who).supplyState.block ≤ (borrowExec s who).blockNumber ∧ accrualStart ((borrowExec s who).acct who).supplierIndex (supplyAcc (borrowExec s who)).index ≤ (supplyAcc (borrowExec s who)).index :=
      ⟨hsup1, accrualStart_le _ _ hrecS⟩
    unfold comptroller
    simp only
    simp [hcondB, hcondS]
  | setSpeeds a b =>
    have hcond1 : s.supplyState.speed = a ∨ s.supplyState.block ≤ s.blockNumber := by
      by_cases heq : s.supplyState.speed = a
      · exact Or.inl heq
      · exact Or.inr hsup
    have hcond2 : s.borrowState.speed = b ∨ s.borrowState.block ≤ s.blockNumber := by
      by_cases heq : s.borrowState.speed = b
      · exact Or.inl heq
      · exact Or.inr hbor
    unfold comptroller
    simp only
    simp [hcond1, hcond2]
theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  split at h
  · rename_i hc
    have heq : borrowExec s who = s' := by simpa using h
    obtain ⟨h1, h2⟩ := hc
    refine ⟨h1, by simpa [borrowAcc] using h2, by rw [← heq]; rfl⟩
  · rename_i hc
    cases h
theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  split at h
  · rename_i hc1
    split at h
    · rename_i hc2
      have heq : grant (supplyExec (borrowExec s who) who) who = s' := by simpa using h
      obtain ⟨h1, h2⟩ := hc1
      obtain ⟨h3, h4⟩ := hc2
      exact ⟨borrowExec s who, supplyExec (borrowExec s who) who, ⟨h1, by simpa [borrowAcc] using h2, rfl⟩, ⟨h3, by simpa [supplyAcc] using h4, rfl⟩, heq.symm⟩
    · rename_i hc2
      cases h
  · rename_i hc1
    cases h
theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller at h
  simp only at h
  split at h
  · rename_i hc1
    split at h
    · rename_i hc2
      have heq : speedsExec s a b = s' := by simpa using h
      have h1 : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber := by
        intro hne
        cases hc1 with
        | inl heq2 => exact absurd heq2 hne
        | inr hle => exact hle
      have h2 : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber := by
        intro hne
        cases hc2 with
        | inl heq2 => exact absurd heq2 hne
        | inr hle => exact hle
      refine ⟨h1, h2, by rw [← heq]; rfl⟩
    · rename_i hc2
      cases h
  · rename_i hc1
    cases h
theorem consistent_exec (s : St) (op : Op) (hc : Consistent s) : Consistent (exec comptroller s op) := by
  cases op with
  | mint who x => sorry
  | redeem who x => sorry
  | transfer src dst x => sorry
  | borrow who x => sorry
  | repay who x => sorry
  | claim who =>
    have hsome : (comptroller s (.claim who)).isSome := req_calls_succeed s (.claim who) hc
    unfold exec
    simp only
    cases hcall : comptroller s (.claim who) with
    | none =>
      simp [hcall] at hsome
    | some s' =>
      simp [hcall]
      have hcl : Claimed s who s' := req_claim s who s' hcall
      exact claim_consistent s who s' hc hcl
  | setSpeeds a b =>
    have hsome : (comptroller s (.setSpeeds a b)).isSome := req_calls_succeed s (.setSpeeds a b) hc
    unfold exec
    simp only
    cases hcall : comptroller s (.setSpeeds a b) with
    | none =>
      simp [hcall] at hsome
    | some s' =>
      simp [hcall]
      have hss : SpeedsSet s a b s' := req_set_speeds s a b s' hcall
      exact speedsSet_consistent s a b s' hc hss
  | advance k =>
    obtain ⟨hsup, hbor, hall⟩ := hc
    unfold exec
    simp only
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.le_trans hsup (Nat.le_add_right _ _)
    · exact Nat.le_trans hbor (Nat.le_add_right _ _)
    · intro a ha
      obtain ⟨hsle, hble⟩ := hall a ha
      simp only
      exact ⟨hsle, hble⟩
  | drip x =>
    obtain ⟨hsup, hbor, hall⟩ := hc
    unfold exec
    simp only
    exact ⟨hsup, hbor, hall⟩
theorem consistent_run (s : St) (ops : List Op) (hc : Consistent s) : Consistent (run comptroller s ops) := by
  induction ops generalizing s with
  | nil => exact hc
  | cons op ops ih => exact ih (exec comptroller s op) (consistent_exec s op hc)
theorem consistent_upgrade (L : Legacy) (hwf : L.WellFormed) : Consistent (upgrade L) := by
  obtain ⟨hs1, hle1, hb1, hle2, hsb, hbb, hall⟩ := hwf
  unfold upgrade initSide Consistent
  simp only
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : L.supplyIndex = 0
    · simp [h0]
    · simp [h0]
      exact hsb
  · by_cases h0 : L.borrowIndex = 0
    · simp [h0]
    · simp [h0]
      exact hbb
  · intro a ha
    obtain ⟨hsup_le, hbor_le⟩ := hall a ha
    refine ⟨?_, ?_⟩
    · by_cases h0 : L.supplyIndex = 0
      · have hr0 : a.supplierIndex = 0 := Nat.eq_zero_of_le_zero (by rw [h0] at hsup_le; exact hsup_le)
        rw [hr0]
        simp [h0]
      · simp [h0]
        exact hsup_le
    · by_cases h0 : L.borrowIndex = 0
      · have hr0 : a.borrowerIndex = 0 := Nat.eq_zero_of_le_zero (by rw [h0] at hbor_le; exact hbor_le)
        rw [hr0]
        simp [h0]
      · simp [h0]
        exact hbor_le
theorem div_mul_le (a b c : Nat) : (a * b / c) * c ≤ a * b := by
  have h := Nat.div_add_mod (a * b) c
  have hcomm : (a * b / c) * c = c * (a * b / c) := Nat.mul_comm _ _
  have heq : (a * b / c) * c + (a * b % c) = a * b := by rw [hcomm]; exact h
  have hle : (a * b / c) * c ≤ (a * b / c) * c + (a * b % c) := Nat.le_add_right _ _
  rw [heq] at hle
  exact hle
theorem credit_mul_le (u start index : Nat) : creditFor u start index * doubleScale ≤ u * (index - start) := by
  unfold creditFor
  exact div_mul_le u (index - start) doubleScale
def potSupplyPend (s : St) (who : Account) : Nat := (s.acct who).supply * ((s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index))
def potBorrowPend (s : St) (who : Account) : Nat := (s.acct who).borrow * ((s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index))
def potSupplyBonus (s : St) (who : Account) : Nat := if 0 < (s.acct who).supply then (s.blockNumber - s.supplyState.block) * s.supplyState.speed else 0
def potBorrowBonus (s : St) (who : Account) : Nat := if 0 < (s.acct who).borrow then (s.blockNumber - s.borrowState.block) * s.borrowState.speed else 0
def potQ (s : St) (who : Account) : Nat := doubleScale * (s.creditedTo who) + potSupplyPend s who + potBorrowPend s who + doubleScale * (potSupplyBonus s who + potBorrowBonus s who)
def potSupplySum (s : St) : Nat := (s.accts.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum
def potBorrowSum (s : St) : Nat := (s.accts.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum
def potUnindexedSupply (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
def potUnindexedBorrow (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed
def potP (s : St) : Nat := doubleScale * s.credited + potSupplySum s + potBorrowSum s + doubleScale * (potUnindexedSupply s + potUnindexedBorrow s)
theorem getD_supply_le_sum (l : List Acct) (who : Nat) : (l.getD who noAcct).supply ≤ (l.map Acct.supply).sum := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp
    | succ n =>
      simp
      have h1 : (xs.getD n noAcct).supply ≤ (xs.map Acct.supply).sum := ih n
      have h2 : (xs.map Acct.supply).sum ≤ x.supply + (xs.map Acct.supply).sum := Nat.le_add_left _ _
      exact Nat.le_trans h1 h2
theorem getD_borrow_le_sum (l : List Acct) (who : Nat) : (l.getD who noAcct).borrow ≤ (l.map Acct.borrow).sum := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp
    | succ n =>
      simp
      have h1 : (xs.getD n noAcct).borrow ≤ (xs.map Acct.borrow).sum := ih n
      have h2 : (xs.map Acct.borrow).sum ≤ x.borrow + (xs.map Acct.borrow).sum := Nat.le_add_left _ _
      exact Nat.le_trans h1 h2
theorem supply_le_total (s : St) (who : Account) : (s.acct who).supply ≤ totalSupply s := by
  unfold totalSupply St.acct
  exact getD_supply_le_sum s.accts who
theorem borrow_le_total (s : St) (who : Account) : (s.acct who).borrow ≤ totalBorrows s := by
  unfold totalBorrows St.acct
  exact getD_borrow_le_sum s.accts who
theorem sum_supply_mul (l : List Acct) (k : Nat) : ((l.map fun a => a.supply * k).sum) = ((l.map Acct.supply).sum) * k := by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    simp
    rw [ih]
    exact (Nat.add_mul _ _ _).symm
theorem sum_borrow_mul (l : List Acct) (k : Nat) : ((l.map fun a => a.borrow * k).sum) = ((l.map Acct.borrow).sum) * k := by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    simp
    rw [ih]
    exact (Nat.add_mul _ _ _).symm
theorem supplyRatio_bound (s : St) : ((supplyAcc s).index - s.supplyState.index) * (totalSupply s) ≤ (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale := by
  unfold supplyAcc accrueSide
  split
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    have heq : s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s - s.supplyState.index = (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s := Nat.add_sub_cancel_left _ _
    rw [heq]
    have hle := div_mul_le ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) doubleScale (totalSupply s)
    have hass : (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale = ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale := rfl
    rw [hass]
    exact hle
  · rename_i hc
    simp
theorem borrowRatio_bound (s : St) : ((borrowAcc s).index - s.borrowState.index) * (totalBorrows s) ≤ (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale := by
  unfold borrowAcc accrueSide
  split
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    have heq : s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s - s.borrowState.index = (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s := Nat.add_sub_cancel_left _ _
    rw [heq]
    have hle := div_mul_le ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) doubleScale (totalBorrows s)
    have hass : (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale = ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale := rfl
    rw [hass]
    exact hle
  · rename_i hc
    simp
theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry
end CompRewards
