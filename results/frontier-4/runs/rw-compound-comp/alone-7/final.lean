import CompRewards.Spec
namespace CompRewards

def comptroller : Impl := fun s c => match c with
  | .supplyHook who =>
    let supNew := accrueSide s.supplyState s.blockNumber (totalSupply s)
    let start := accrualStart (s.acct who).supplierIndex supNew.index
    if s.supplyState.block ≤ s.blockNumber ∧ start ≤ supNew.index then
      some { s with supplyState := supNew, accts := s.accts.modify who fun a => { a with supplierIndex := supNew.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex supNew.index) supNew.index } }
    else none
  | .borrowHook who =>
    let borNew := accrueSide s.borrowState s.blockNumber (totalBorrows s)
    let bstart := accrualStart (s.acct who).borrowerIndex borNew.index
    if s.borrowState.block ≤ s.blockNumber ∧ bstart ≤ borNew.index then
      some { s with borrowState := borNew, accts := s.accts.modify who fun a => { a with borrowerIndex := borNew.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex borNew.index) borNew.index } }
    else none
  | .claim who =>
    let borNew := accrueSide s.borrowState s.blockNumber (totalBorrows s)
    let bstart := accrualStart (s.acct who).borrowerIndex borNew.index
    if s.borrowState.block ≤ s.blockNumber ∧ bstart ≤ borNew.index then
      let mid1 : St :=
        { s with borrowState := borNew, accts := s.accts.modify who fun a => { a with borrowerIndex := borNew.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex borNew.index) borNew.index } }
      let supNew := accrueSide mid1.supplyState mid1.blockNumber (totalSupply mid1)
      let sstart := accrualStart (mid1.acct who).supplierIndex supNew.index
      if mid1.supplyState.block ≤ mid1.blockNumber ∧ sstart ≤ supNew.index then
        let mid2 : St :=
          { mid1 with supplyState := supNew, accts := mid1.accts.modify who fun a => { a with supplierIndex := supNew.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex supNew.index) supNew.index } }
        some (grant mid2 who)
      else none
    else none
  | .setSpeeds a b =>
    if (s.supplyState.speed = a ∨ s.supplyState.block ≤ s.blockNumber) ∧
       (s.borrowState.speed = b ∨ s.borrowState.block ≤ s.blockNumber) then
      let supNew := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }
      let borNew := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }
      some { s with supplyState := supNew, borrowState := borNew }
    else none

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  dsimp only at h
  split at h
  next hcond =>
    obtain rfl := Option.some_inj.mp h
    exact ⟨hcond.1, hcond.2, rfl⟩
  next hcond =>
    cases h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  dsimp only at h
  split at h
  next hcond =>
    obtain rfl := Option.some_inj.mp h
    exact ⟨hcond.1, hcond.2, rfl⟩
  next hcond =>
    cases h

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  dsimp only at h
  split at h
  next hcond =>
    split at h
    next hcond2 =>
      obtain rfl := Option.some_inj.mp h
      exact ⟨_, _, ⟨hcond.1, hcond.2, rfl⟩, ⟨hcond2.1, hcond2.2, rfl⟩, rfl⟩
    next hcond2 =>
      cases h
  next hcond =>
    cases h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller at h
  dsimp only at h
  split at h
  next hcond =>
    obtain rfl := Option.some_inj.mp h
    refine ⟨?_, ?_, rfl⟩
    · intro hne
      exact Or.resolve_left hcond.1 hne
    · intro hne
      exact Or.resolve_left hcond.2 hne
  next hcond =>
    cases h

private theorem accrue_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · simp only
    exact Nat.le_add_right _ _
  · simp only
    exact Nat.le_refl _

private theorem accrual_le (rec idx : Nat) (hle : rec ≤ idx) :
    accrualStart rec idx ≤ idx := by
  unfold accrualStart
  split
  · next heq =>
    split
    · next hle2 => exact hle2
    · next _ => exact Nat.zero_le _
  · next hne => exact hle

private theorem getD_supplier_le (l : List Acct) (who idx : Nat)
    (hall : ∀ a ∈ l, a.supplierIndex ≤ idx) :
    (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD]
    exact Nat.zero_le _
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD]
      exact hall hd List.mem_cons_self
    | succ n =>
      simp only [List.getD]
      exact ih n (fun a ha => hall a (List.mem_cons_of_mem hd ha))

private theorem getD_borrower_le (l : List Acct) (who idx : Nat)
    (hall : ∀ a ∈ l, a.borrowerIndex ≤ idx) :
    (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD]
    exact Nat.zero_le _
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD]
      exact hall hd List.mem_cons_self
    | succ n =>
      simp only [List.getD]
      exact ih n (fun a ha => hall a (List.mem_cons_of_mem hd ha))

private theorem modify_supplier_bound (l : List Acct) (who : Nat)
    (f : Acct → Acct) (idx : Nat)
    (hall : ∀ a ∈ l, a.supplierIndex ≤ idx)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ∀ a ∈ l.modify who f, a.supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    intro a ha
    simp at ha
  | cons hd tl ih =>
    cases who with
    | zero =>
      intro a ha
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq, hf]
        exact hall hd List.mem_cons_self
      | inr hmem =>
        exact hall a (List.mem_cons_of_mem hd hmem)
    | succ n =>
      intro a ha
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq]
        exact hall hd List.mem_cons_self
      | inr hmem =>
        have h1 : ∀ a ∈ tl, a.supplierIndex ≤ idx :=
          fun a ha => hall a (List.mem_cons_of_mem hd ha)
        exact ih n h1 a hmem

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    have hb : s.supplyState.block ≤ s.blockNumber := hc.1
    have hall : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
      fun a ha => (hc.2.2 a ha).1
    have hrec : (s.acct who).supplierIndex ≤ s.supplyState.index :=
      getD_supplier_le s.accts who s.supplyState.index hall
    have hge : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrue_ge _ _ _
    have hrec2 : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      Nat.le_trans hrec hge
    have hstart : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrual_le _ _ hrec2
    have hcond : s.supplyState.block ≤ s.blockNumber ∧
        accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      ⟨hb, hstart⟩
    unfold comptroller
    simp [hcond]
  | borrowHook who =>
    have hb : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hall : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
      fun a ha => (hc.2.2 a ha).2
    have hrec : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
      getD_borrower_le s.accts who s.borrowState.index hall
    have hge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_ge _ _ _
    have hrec2 : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans hrec hge
    have hstart : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrual_le _ _ hrec2
    have hcond : s.borrowState.block ≤ s.blockNumber ∧
        accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      ⟨hb, hstart⟩
    unfold comptroller
    simp [hcond]
  | claim who =>
    have hb : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hb2 : s.supplyState.block ≤ s.blockNumber := hc.1
    have hallS : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
      fun a ha => (hc.2.2 a ha).1
    have hallB : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
      fun a ha => (hc.2.2 a ha).2
    have hrecB : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
      getD_borrower_le s.accts who s.borrowState.index hallB
    have hgeB : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_ge _ _ _
    have hrecB2 : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans hrecB hgeB
    have hstartB : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrual_le _ _ hrecB2
    have hcondB : s.borrowState.block ≤ s.blockNumber ∧
        accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      ⟨hb, hstartB⟩
    let fB : Acct → Acct := fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }
    have hallS_mid : ∀ a ∈ s.accts.modify who fB, a.supplierIndex ≤ s.supplyState.index :=
      modify_supplier_bound _ _ _ _ hallS (fun a => rfl)
    let mid1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fB }
    have hrecS_mid : (mid1.acct who).supplierIndex ≤ mid1.supplyState.index := by
      have h1 : (mid1.acct who).supplierIndex ≤ s.supplyState.index :=
        getD_supplier_le _ _ _ hallS_mid
      have h2 : mid1.supplyState.index = s.supplyState.index := rfl
      rw [h2] at h1
      exact h1
    have hgeS_mid : mid1.supplyState.index ≤ (accrueSide mid1.supplyState mid1.blockNumber (totalSupply mid1)).index :=
      accrue_ge _ _ _
    have hrecS2 : (mid1.acct who).supplierIndex ≤ (accrueSide mid1.supplyState mid1.blockNumber (totalSupply mid1)).index :=
      Nat.le_trans hrecS_mid hgeS_mid
    have hstartS : accrualStart (mid1.acct who).supplierIndex (accrueSide mid1.supplyState mid1.blockNumber (totalSupply mid1)).index ≤
        (accrueSide mid1.supplyState mid1.blockNumber (totalSupply mid1)).index :=
      accrual_le _ _ hrecS2
    have hcondS : mid1.supplyState.block ≤ mid1.blockNumber ∧
        accrualStart (mid1.acct who).supplierIndex (accrueSide mid1.supplyState mid1.blockNumber (totalSupply mid1)).index ≤
        (accrueSide mid1.supplyState mid1.blockNumber (totalSupply mid1)).index :=
      ⟨hb2, hstartS⟩
    unfold comptroller
    simp [hcondB, hcondS, fB, mid1]
  | setSpeeds a b =>
    have hbS : s.supplyState.speed = a ∨ s.supplyState.block ≤ s.blockNumber := by
      by_cases heq : s.supplyState.speed = a
      · exact Or.inl heq
      · exact Or.inr hc.1
    have hbB : s.borrowState.speed = b ∨ s.borrowState.block ≤ s.blockNumber := by
      by_cases heq : s.borrowState.speed = b
      · exact Or.inl heq
      · exact Or.inr hc.2.1
    have hcond : (s.supplyState.speed = a ∨ s.supplyState.block ≤ s.blockNumber) ∧
        (s.borrowState.speed = b ∨ s.borrowState.block ≤ s.blockNumber) := ⟨hbS, hbB⟩
    unfold comptroller
    simp [hcond]

private theorem doubleScale_pos : 0 < doubleScale := by
  unfold doubleScale
  decide

private theorem accrualStart_mono (rec idx1 idx2 : Nat) (hle : idx1 ≤ idx2) :
    accrualStart rec idx1 ≤ accrualStart rec idx2 := by
  unfold accrualStart
  split
  · next heq =>
    split
    · next h1 =>
      split
      · next h2 => exact Nat.le_refl _
      · next h2 => omega
    · next h1 =>
      split
      · next h2 => exact Nat.zero_le _
      · next h2 => exact Nat.le_refl _
  · next hne =>
    exact Nat.le_refl _

private theorem accrue_bound (sd : Side) (now total : Nat) :
    total * ((accrueSide sd now total).index - sd.index) ≤
      (now - sd.block) * sd.speed * doubleScale := by
  unfold accrueSide
  split
  · next hcond =>
    have h1 : (sd.index + (now - sd.block) * sd.speed * doubleScale / total) - sd.index =
        (now - sd.block) * sd.speed * doubleScale / total :=
      Nat.add_sub_cancel_left _ _
    rw [h1]
    have h3 : ((now - sd.block) * sd.speed * doubleScale / total) * total ≤
        (now - sd.block) * sd.speed * doubleScale :=
      Nat.div_mul_le_self _ _
    have h4 : total * ((now - sd.block) * sd.speed * doubleScale / total) =
        ((now - sd.block) * sd.speed * doubleScale / total) * total :=
      Nat.mul_comm _ _
    rw [h4]
    exact h3
  · next hcond =>
    have h0 : sd.index - sd.index = 0 := Nat.sub_self _
    simp only [h0, Nat.mul_zero]
    exact Nat.zero_le _

private theorem supply_le_total_aux (l : List Acct) (who : Nat) :
    (l.getD who noAcct).supply ≤ (l.map Acct.supply).sum := by
  induction l generalizing who with
  | nil =>
    exact Nat.le_refl _
  | cons hd tl ih =>
    cases who with
    | zero =>
      exact Nat.le_add_right _ _
    | succ n =>
      have h := ih n
      have hle : (tl.map Acct.supply).sum ≤ hd.supply + (tl.map Acct.supply).sum :=
        Nat.le_add_left _ _
      exact Nat.le_trans h hle

private theorem borrow_le_total_aux (l : List Acct) (who : Nat) :
    (l.getD who noAcct).borrow ≤ (l.map Acct.borrow).sum := by
  induction l generalizing who with
  | nil =>
    exact Nat.le_refl _
  | cons hd tl ih =>
    cases who with
    | zero =>
      exact Nat.le_add_right _ _
    | succ n =>
      have h := ih n
      have hle : (tl.map Acct.borrow).sum ≤ hd.borrow + (tl.map Acct.borrow).sum :=
        Nat.le_add_left _ _
      exact Nat.le_trans h hle

private def supplyTermAcct (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)

private def borrowTermAcct (s : St) (who : Account) : Nat :=
  (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)

private def unindexedSupplySt (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed

private def unindexedBorrowSt (s : St) : Nat :=
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

private def Pacct (s : St) (who : Account) : Nat :=
  s.creditedTo who + supplyTermAcct s who / doubleScale + borrowTermAcct s who / doubleScale +
    (if (s.acct who).supply > 0 then unindexedSupplySt s else 0) +
    (if (s.acct who).borrow > 0 then unindexedBorrowSt s else 0)

private theorem div_add_le (a b d : Nat) (hpos : 0 < d) : a / d + b / d ≤ (a + b) / d := by
  have h1 : (a / d) * d ≤ a := Nat.div_mul_le_self _ _
  have h2 : (b / d) * d ≤ b := Nat.div_mul_le_self _ _
  have h3 : (a / d + b / d) * d ≤ a + b := by
    have heq : (a / d + b / d) * d = (a / d) * d + (b / d) * d := Nat.add_mul _ _ _
    rw [heq]
    exact Nat.add_le_add h1 h2
  exact (Nat.le_div_iff_mul_le hpos).mpr h3

private theorem supplyUp_le_legacy (L : Legacy) (who : Account) (hwf : L.WellFormed) :
    supplyTermAcct (upgrade L) who ≤
      (L.accts.getD who noAcct).supply * (L.supplyIndex - legacyStart L.supplyStart (L.accts.getD who noAcct).supplierIndex) := by
  unfold Legacy.WellFormed at hwf
  obtain ⟨hss0, hss_le, hbs0, hbs_le, hsb_le, hbb_le, hall⟩ := hwf
  have hallS : ∀ a ∈ L.accts, a.supplierIndex ≤ L.supplyIndex :=
    fun a ha => (hall a ha).1
  have hrec : (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex :=
    getD_supplier_le L.accts who L.supplyIndex hallS
  have hup_acct : (upgrade L).acct who = L.accts.getD who noAcct := rfl
  have hup_supply : ((upgrade L).acct who).supply = (L.accts.getD who noAcct).supply := by
    rw [hup_acct]
  have hup_rec : ((upgrade L).acct who).supplierIndex = (L.accts.getD who noAcct).supplierIndex := by
    rw [hup_acct]
  have hup_idx : (upgrade L).supplyState.index =
      (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := by
    unfold upgrade initSide
    by_cases h : L.supplyIndex = 0 <;> simp [h]
  have hinner : (upgrade L).supplyState.index -
      accrualStart ((upgrade L).acct who).supplierIndex (upgrade L).supplyState.index ≤
      L.supplyIndex - legacyStart L.supplyStart (L.accts.getD who noAcct).supplierIndex := by
    rw [hup_idx, hup_rec]
    by_cases hidx0 : L.supplyIndex = 0
    · have hrec0 : (L.accts.getD who noAcct).supplierIndex = 0 := by omega
      have hss0' : L.supplyStart = 0 := by
        cases hss0 with
        | inl h => exact h
        | inr h => omega
      rw [hidx0, hrec0, hss0']
      simp [legacyStart, accrualStart]
    · have hup_eq : (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) = L.supplyIndex := by
        simp [hidx0]
      rw [hup_eq]
      by_cases hrec0 : (L.accts.getD who noAcct).supplierIndex = 0
      · have hrec0' : (L.accts.getD who noAcct).supplierIndex = 0 := hrec0
        simp only [hrec0'] at *
        unfold legacyStart accrualStart
        split
        · next heq =>
          split
          · next hI =>
            cases hss0 with
            | inl h =>
              simp [h] at hss_le
              omega
            | inr h =>
              omega
          · next hI =>
            have hss0'' : L.supplyStart = 0 := by
              cases hss0 with
              | inl h => exact h
              | inr h => omega
            simp only [hss0''] at hI ⊢
            omega
      · have hstart_ge : legacyStart L.supplyStart (L.accts.getD who noAcct).supplierIndex ≤
            accrualStart (L.accts.getD who noAcct).supplierIndex L.supplyIndex := by
          unfold legacyStart accrualStart
          simp only [if_neg hrec0]
        have hle1 : accrualStart (L.accts.getD who noAcct).supplierIndex L.supplyIndex ≤ L.supplyIndex :=
          accrual_le _ _ hrec
        have hle2 : legacyStart L.supplyStart (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex := by
          unfold legacyStart
          split
          · next heq => omega
          · next hne => exact hrec
        omega
  have hmul : supplyTermAcct (upgrade L) who ≤
      (L.accts.getD who noAcct).supply * (L.supplyIndex - legacyStart L.supplyStart (L.accts.getD who noAcct).supplierIndex) := by
    unfold supplyTermAcct
    rw [hup_supply]
    exact Nat.mul_le_mul_left _ hinner
  exact hmul

private theorem Pacct_upgrade_le (L : Legacy) (who : Account) (hwf : L.WellFormed) :
    Pacct (upgrade L) who ≤ (upgrade L).creditedTo who + Legacy.owedTo L who := by
  sorry

private theorem supply_pmid_le (s : St) (q : Account) (hc : Consistent s) :
    (s.acct q).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
      accrualStart (s.acct q).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale ≤
    (s.acct q).supply * (s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) / doubleScale +
    (if (s.acct q).supply > 0 then unindexedSupplySt s else 0) := by
  by_cases hsup : (s.acct q).supply > 0
  · have hall : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
      fun a ha => (hc.2.2 a ha).1
    have hrec : (s.acct q).supplierIndex ≤ s.supplyState.index :=
      getD_supplier_le s.accts q s.supplyState.index hall
    have hge : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrue_ge _ _ _
    have hrecNew : (s.acct q).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      Nat.le_trans hrec hge
    have hstartOld_le : accrualStart (s.acct q).supplierIndex s.supplyState.index ≤ s.supplyState.index :=
      accrual_le _ _ hrec
    have hstartMid_le : accrualStart (s.acct q).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrual_le _ _ hrecNew
    have hstartMono : accrualStart (s.acct q).supplierIndex s.supplyState.index ≤
        accrualStart (s.acct q).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrualStart_mono _ _ _ hge
    have hsup_le_total : (s.acct q).supply ≤ totalSupply s :=
      supply_le_total_aux s.accts q
    have haccrue : totalSupply s * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) ≤
        (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale :=
      accrue_bound _ _ _
    have hidx_arith : (accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        accrualStart (s.acct q).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) +
        ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) := by
      omega
    have hmul_mono : (s.acct q).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        accrualStart (s.acct q).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) ≤
        (s.acct q).supply * ((s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) +
        ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index)) :=
      Nat.mul_le_mul_left _ hidx_arith
    have hmul_add : (s.acct q).supply * ((s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) +
        ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index)) =
        (s.acct q).supply * (s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) +
        (s.acct q).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) :=
      Nat.mul_add _ _ _
    have hsup_delta : (s.acct q).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) ≤
        (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale := by
      have h1 : (s.acct q).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) ≤
          totalSupply s * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) :=
        Nat.mul_le_mul_right _ hsup_le_total
      exact Nat.le_trans h1 haccrue
    have hterm_le : (s.acct q).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        accrualStart (s.acct q).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) ≤
        (s.acct q).supply * (s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) +
        (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale := by
      have h2 : (s.acct q).supply * ((s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) +
          ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index)) ≤
          (s.acct q).supply * (s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) +
          (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale := by
        rw [hmul_add]
        exact Nat.add_le_add_left hsup_delta _
      exact Nat.le_trans hmul_mono h2
    have hdiv_le : (s.acct q).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        accrualStart (s.acct q).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale ≤
        ((s.acct q).supply * (s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) +
        (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale) / doubleScale :=
      Nat.div_le_div_right hterm_le
    have heq : ((s.acct q).supply * (s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) +
        (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale) / doubleScale =
        (s.acct q).supply * (s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) / doubleScale +
        (s.blockNumber - s.supplyState.block) * s.supplyState.speed := by
      have heq2 : (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale =
          ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale := rfl
      rw [heq2]
      exact Nat.add_mul_div_right _ _ doubleScale_pos
    have hfinal : (s.acct q).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        accrualStart (s.acct q).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale ≤
        (s.acct q).supply * (s.supplyState.index - accrualStart (s.acct q).supplierIndex s.supplyState.index) / doubleScale +
        (s.blockNumber - s.supplyState.block) * s.supplyState.speed := by
      rw [heq] at hdiv_le
      exact hdiv_le
    have hunfold : unindexedSupplySt s = (s.blockNumber - s.supplyState.block) * s.supplyState.speed := rfl
    have hif : (if (s.acct q).supply > 0 then unindexedSupplySt s else 0) = (s.blockNumber - s.supplyState.block) * s.supplyState.speed := by
      simp [hsup, hunfold]
    rw [hif]
    exact hfinal
  · have h0 : (s.acct q).supply = 0 := by omega
    simp [h0]

private theorem borrow_pmid_le (s : St) (q : Account) (hc : Consistent s) :
    (s.acct q).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
      accrualStart (s.acct q).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale ≤
    (s.acct q).borrow * (s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) / doubleScale +
    (if (s.acct q).borrow > 0 then unindexedBorrowSt s else 0) := by
  by_cases hsup : (s.acct q).borrow > 0
  · have hall : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
      fun a ha => (hc.2.2 a ha).2
    have hrec : (s.acct q).borrowerIndex ≤ s.borrowState.index :=
      getD_borrower_le s.accts q s.borrowState.index hall
    have hge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_ge _ _ _
    have hrecNew : (s.acct q).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans hrec hge
    have hstartOld_le : accrualStart (s.acct q).borrowerIndex s.borrowState.index ≤ s.borrowState.index :=
      accrual_le _ _ hrec
    have hstartMid_le : accrualStart (s.acct q).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrual_le _ _ hrecNew
    have hstartMono : accrualStart (s.acct q).borrowerIndex s.borrowState.index ≤
        accrualStart (s.acct q).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrualStart_mono _ _ _ hge
    have hsup_le_total : (s.acct q).borrow ≤ totalBorrows s :=
      borrow_le_total_aux s.accts q
    have haccrue : totalBorrows s * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) ≤
        (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale :=
      accrue_bound _ _ _
    have hidx_arith : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
        accrualStart (s.acct q).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) +
        ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) := by
      omega
    have hmul_mono : (s.acct q).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
        accrualStart (s.acct q).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) ≤
        (s.acct q).borrow * ((s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) +
        ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index)) :=
      Nat.mul_le_mul_left _ hidx_arith
    have hmul_add : (s.acct q).borrow * ((s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) +
        ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index)) =
        (s.acct q).borrow * (s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) +
        (s.acct q).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) :=
      Nat.mul_add _ _ _
    have hsup_delta : (s.acct q).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) ≤
        (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale := by
      have h1 : (s.acct q).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) ≤
          totalBorrows s * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) :=
        Nat.mul_le_mul_right _ hsup_le_total
      exact Nat.le_trans h1 haccrue
    have hterm_le : (s.acct q).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
        accrualStart (s.acct q).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) ≤
        (s.acct q).borrow * (s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) +
        (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale := by
      have h2 : (s.acct q).borrow * ((s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) +
          ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index)) ≤
          (s.acct q).borrow * (s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) +
          (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale := by
        rw [hmul_add]
        exact Nat.add_le_add_left hsup_delta _
      exact Nat.le_trans hmul_mono h2
    have hdiv_le : (s.acct q).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
        accrualStart (s.acct q).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale ≤
        ((s.acct q).borrow * (s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) +
        (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale) / doubleScale :=
      Nat.div_le_div_right hterm_le
    have heq : ((s.acct q).borrow * (s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) +
        (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale) / doubleScale =
        (s.acct q).borrow * (s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) / doubleScale +
        (s.blockNumber - s.borrowState.block) * s.borrowState.speed := by
      have heq2 : (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale =
          ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale := rfl
      rw [heq2]
      exact Nat.add_mul_div_right _ _ doubleScale_pos
    have hfinal : (s.acct q).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
        accrualStart (s.acct q).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale ≤
        (s.acct q).borrow * (s.borrowState.index - accrualStart (s.acct q).borrowerIndex s.borrowState.index) / doubleScale +
        (s.blockNumber - s.borrowState.block) * s.borrowState.speed := by
      rw [heq] at hdiv_le
      exact hdiv_le
    have hunfold : unindexedBorrowSt s = (s.blockNumber - s.borrowState.block) * s.borrowState.speed := rfl
    have hif : (if (s.acct q).borrow > 0 then unindexedBorrowSt s else 0) = (s.blockNumber - s.borrowState.block) * s.borrowState.speed := by
      simp [hsup, hunfold]
    rw [hif]
    exact hfinal
  · have h0 : (s.acct q).borrow = 0 := by omega
    simp [h0]

theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
