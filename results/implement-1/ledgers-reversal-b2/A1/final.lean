import Reversal.Spec
import Reversal.Lemmas

namespace Reversal

def validPostCheck (s : State) (e : Entry) : Bool :=
  match e.lines with
  | [] => false
  | _ :: _ =>
    e.lines.all (fun l => decide (l.1 ∈ s.accounts)) &&
    e.lines.all (fun l => decide (l.2 ≠ 0)) &&
    decide (lineSum e.lines = 0) &&
    !decide (e.id ∈ ids s.journal) &&
    !decide (e.id ∈ s.reversed)

def step : Impl
  | s, .post e =>
    if validPostCheck s e then
      (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a })
    else
      (Outcome.rejected, s)
  | s, .reverse i =>
    match findEntry s.journal i with
    | none => (Outcome.rejected, s)
    | some e =>
      if i ∈ s.reversed then (Outcome.rejected, s)
      else (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed })

theorem tmpProbe : True := by
  have h : ∀ (l : List Nat) (p : Nat → Bool), (l.all p = true) ↔ ∀ x ∈ l, p x = true := by
    intro l p
    simp [List.all_eq_true]
  trivial
#print axioms tmpProbe
#check @List.all_eq_true

theorem probeMem (hd : Line) (tl : List Line) (hh : ∀ l ∈ hd :: tl, l.2 ≠ 0)
    (l : Line) (hl : l ∈ tl) : l.2 ≠ 0 :=
  hh l (List.mem_cons_of_mem hd hl)
#check @List.mem_cons_of_mem
#check @List.Mem.tail

theorem probeCheck3 (s : State) (e : Entry) (hd : Line) (tl : List Line)
    (hl : e.lines = hd :: tl)
    (h1' : ((hd :: tl).all (fun l => decide (l.1 ∈ s.accounts)) = true))
    (h2' : ((hd :: tl).all (fun l => decide (l.2 ≠ 0)) = true))
    (h3' : decide (lineSum (hd :: tl) = 0) = true)
    (h4 : decide (e.id ∈ ids s.journal) = false)
    (h5 : decide (e.id ∈ s.reversed) = false) : validPostCheck s e = true := by
  have hrew : validPostCheck s e =
    (((hd :: tl).all (fun l => decide (l.1 ∈ s.accounts))) &&
     ((hd :: tl).all (fun l => decide (l.2 ≠ 0))) &&
     decide (lineSum (hd :: tl) = 0) &&
     (!decide (e.id ∈ ids s.journal)) &&
     (!decide (e.id ∈ s.reversed))) := by
    unfold validPostCheck
    rw [hl]
  rw [hrew, h1', h2', h3', h4, h5]
  rfl

theorem myFindAux : True := trivial

theorem probeFindEq (e : Entry) (es : List Entry) (i : EntryId) : findEntry (e :: es) i = (if e.id = i then some e else findEntry es i) := by rfl

theorem probeMemOr2 (e : Entry) (es : List Entry) (i : EntryId) (h : i ∈ ids (e :: es)) : (e.id = i ∨ i ∈ ids es) := by
  have hrw : ids (e :: es) = e.id :: ids es := rfl
  rw [hrw] at h
  simp at h
  cases h with
  | inl hh =>
    exact Or.inl (Eq.symm hh)
  | inr hh =>
    exact Or.inr hh

theorem findEntry_mem_ids4 {j : List Entry} {i : EntryId} {e : Entry}
    (h : findEntry j i = some e) : i ∈ ids j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    unfold findEntry at h
    split at h
    · rename_i heq
      cases h; simp [ids, heq]
    · rename_i heq
      have ihh := ih h
      simp only [ids, List.map_cons, List.mem_cons]
      exact Or.inr ihh

theorem probeAll (l : List Line) (p : Line → Bool) : (l.all p = true) ↔ ∀ x ∈ l, p x = true := by
  exact List.all_eq_true
#check @List.all_eq_true

theorem probeAll2 (l : List Line) (p : Line → Bool) (h : l.all p = true) (x : Line) (hx : x ∈ l) : p x = true := by
  have h2 := (List.all_eq_true.mp h) x hx
  exact h2
#check @List.all_eq_true

theorem probeUnfold (s : State) (e : Entry) : validPostCheck s e =
  match e.lines with
  | [] => false
  | _ :: _ =>
    e.lines.all (fun l => decide (l.1 ∈ s.accounts)) &&
    e.lines.all (fun l => decide (l.2 ≠ 0)) &&
    decide (lineSum e.lines = 0) &&
    !decide (e.id ∈ ids s.journal) &&
    !decide (e.id ∈ s.reversed) := by rfl

theorem findEntry_eq_some_id {j : List Entry} {i : EntryId} {e : Entry}
    (h : findEntry j i = some e) : e.id = i := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    unfold findEntry at h
    split at h
    · rename_i heq; cases h; exact heq
    · rename_i heq; exact ih h

theorem req_post_effects_try : PostEffects step := by
  intro s e hok
  by_cases hvc : validPostCheck s e = true
  · have hstep : step s (.post e) = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
      simp [step, hvc]
    rw [hstep]
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro a
    rfl
  · have hstep : step s (.post e) = (Outcome.rejected, s) := by
      simp [step, hvc]
    rw [hstep] at hok
    simp at hok

theorem tmp_reverse_unfold (s : State) (i : EntryId) :
    step s (.reverse i) =
    (match findEntry s.journal i with
    | none => (Outcome.rejected, s)
    | some e => if i ∈ s.reversed then (Outcome.rejected, s)
      else (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed })) := by
  rfl

theorem tmpBoolCheck (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all
#check Bool.and_eq_true
#check decide_eq_true
#check decide_eq_false

theorem tmp_and_parts (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

theorem tmp_dec_true2 (p : Prop) [Decidable p] (h : decide p = true) : p :=
  of_decide_eq_true h

theorem tmp_dec_false2 (p : Prop) [Decidable p] (h : decide p = false) : ¬ p :=
  of_decide_eq_false h

theorem tmp_bang_dec (p : Prop) [Decidable p] (h : (!decide p) = true) : ¬ p := by
  intro hp
  have : decide p = true := by simp [hp]
  simp [this] at h

theorem findNone_of_notMem2 {j : List Entry} {i : EntryId} (h : i ∉ ids j) : findEntry j i = none := by
  induction j with
  | nil => rfl
  | cons hd tl ih =>
    simp only [ids, List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, htl⟩ := h
    have hne2 : ¬ (hd.id = i) := fun heq => hne heq.symm
    simp only [findEntry, hne2, ↓reduceIte]
    exact ih htl

theorem findSome_append_new2 {j : List Entry} {e : Entry} (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    simp only [ids, List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, htl⟩ := h
    have hne2 : ¬ (hd.id = e.id) := fun heq => hne heq.symm
    simp only [List.cons_append, findEntry, hne2, ↓reduceIte]
    exact ih htl

theorem and_true_imp_left (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

theorem and_true_imp_right (a b : Bool) (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

theorem bang_dec_true_iff (p : Prop) [Decidable p] : ((!decide p) = true) ↔ ¬ p := by
  cases h : decide p <;> simp_all

theorem validPostCheck_true_intro (s : State) (e : Entry) (h : validPostCheck s e = true) :
    e.lines ≠ [] := by
  intro hnil
  have : validPostCheck s e = false := by simp [validPostCheck, hnil]
  rw [this] at h
  contradiction

theorem validPostCheck_ids_false (s : State) (e : Entry) (hm : e.id ∈ ids s.journal) :
    validPostCheck s e = false := by
  have hD : (!decide (e.id ∈ ids s.journal)) = false := by simp [hm]
  cases hl : e.lines with
  | nil => simp [validPostCheck, hl]
  | cons hd tl => simp [validPostCheck, hl, hD]

theorem validPostCheck_rev_false (s : State) (e : Entry) (hm : e.id ∈ s.reversed) :
    validPostCheck s e = false := by
  have hD : (!decide (e.id ∈ s.reversed)) = false := by simp [hm]
  cases hl : e.lines with
  | nil => simp [validPostCheck, hl]
  | cons hd tl => simp [validPostCheck, hl, hD]

theorem tb_zero (accts : List AccountId) : sumOver accts (fun _ => (0 : Int)) = 0 := by
  induction accts with
  | nil => rfl
  | cons hd tl ih => simp only [sumOver_cons] at ih ⊢; omega

theorem tb_ite_swap (accts : List AccountId) (l : Line) (hN : accts.Nodup) :
    sumOver accts (fun a => if l.1 = a then l.2 else 0) = if l.1 ∈ accts then l.2 else 0 := by
  have hcong : ∀ a ∈ accts, (if l.1 = a then l.2 else (0 : Int)) = (if a = l.1 then l.2 else 0) := by
    intro a _
    by_cases h1 : l.1 = a
    · subst h1; simp
    · have h2 : ¬ (a = l.1) := fun heq => h1 heq.symm
      simp only [h1, h2, ↓reduceIte]
  have h1 : sumOver accts (fun a => if l.1 = a then l.2 else (0 : Int))
    = sumOver accts (fun a => if a = l.1 then l.2 else (0 : Int)) :=
    sumOver_congr accts _ _ hcong
  rw [h1]
  exact sumOver_ite_eq hN l.1 l.2

theorem tb_sum_net (ls : List Line) (accts : List AccountId) (hN : accts.Nodup)
    (hMem : ∀ l ∈ ls, l.1 ∈ accts) :
    sumOver accts (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have hz : sumOver accts (fun a => netOf ([] : List Line) a) = sumOver accts (fun _ => (0 : Int)) := by
      apply sumOver_congr
      intro a _
      rfl
    rw [hz, tb_zero]
    rfl
  | cons hd tl ih =>
    have hhd : hd.1 ∈ accts := hMem hd (by simp)
    have htl : ∀ l ∈ tl, l.1 ∈ accts := fun l hl => hMem l (List.mem_cons_of_mem hd hl)
    have ih' := ih htl
    have hexpand : ∀ a : AccountId, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      intro a; rfl
    have hcong : (fun a => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else (0 : Int)) + netOf tl a) := by
      funext a; exact hexpand a
    have hsum : sumOver accts (fun a => netOf (hd :: tl) a)
      = sumOver accts (fun a => if hd.1 = a then hd.2 else 0) + sumOver accts (fun a => netOf tl a) := by
      rw [hcong]
      exact sumOver_add accts _ _
    have h1 : sumOver accts (fun a => if hd.1 = a then hd.2 else (0 : Int)) = hd.2 := by
      have hrw := tb_ite_swap accts hd hN
      simp only [hhd, ↓reduceIte] at hrw
      exact hrw
    have h2 : lineSum (hd :: tl) = hd.2 + lineSum tl := by rfl
    rw [hsum, h1, ih', h2]

theorem tb_probe_extract (a b c d e : Bool) (h : ((a && b && c && d && e) = true)) :
    a = true ∧ c = true := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h3⟩

theorem tmpT : True := trivial

theorem wfDecAllMem (s : State) (e : Entry) (h : validPostCheck s e = true) :
    ∀ l ∈ e.lines, l.1 ∈ s.accounts := by
  have hunf := probeUnfold s e
  rw [hunf] at h
  cases hl : e.lines with
  | nil => simp [hl] at h
  | cons hd tl =>
    simp only [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := h
    have hAm : ∀ x ∈ hd :: tl, decide (x.1 ∈ s.accounts) = true := (List.all_eq_true.mp hA)
    intro l hlmem
    have hx := hAm l hlmem
    exact of_decide_eq_true hx

theorem wfDecLineSum (s : State) (e : Entry) (h : validPostCheck s e = true) :
    lineSum e.lines = 0 := by
  have hunf := probeUnfold s e
  rw [hunf] at h
  cases hl : e.lines with
  | nil => simp [hl] at h
  | cons hd tl =>
    simp only [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := h
    exact of_decide_eq_true hC

theorem wfDecNotMemIds (s : State) (e : Entry) (h : validPostCheck s e = true) :
    e.id ∉ ids s.journal := by
  have hunf := probeUnfold s e
  rw [hunf] at h
  cases hl : e.lines with
  | nil => simp [hl] at h
  | cons hd tl =>
    simp only [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := h
    have : ¬ (e.id ∈ ids s.journal) := by
      have hd2 : (!decide (e.id ∈ ids s.journal)) = true := hD
      cases hh : decide (e.id ∈ ids s.journal) with
      | true => simp [hh] at hd2
      | false => exact of_decide_eq_false hh
    exact this

theorem wfTmpSig : True := trivial
#check @List.nodup_append

theorem ids_append_single2 (j : List Entry) (e : Entry) : ids (j ++ [e]) = ids j ++ [e.id] := by
  simp [ids]

theorem probeListA : True := trivial
#check List.nodup_append
#check List.mem_append
#check List.not_mem_nil
#check List.mem_singleton

theorem nodup_append_singleton6 {α : Type} (l : List α) (x : α) (h1 : l.Nodup) (h2 : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil =>
    simp only [List.nil_append]
    exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | cons hd tl ih =>
    have hcons : (hd :: tl) ++ [x] = hd :: (tl ++ [x]) := rfl
    rw [hcons]
    rw [List.nodup_cons] at h1 ⊢
    obtain ⟨hhd, htl⟩ := h1
    have h2tl : x ∉ tl := fun hm => h2 (List.mem_cons_of_mem hd hm)
    have ih' := ih htl h2tl
    refine ⟨?_, ih'⟩
    intro hmem
    have hmem2 := List.mem_append.mp hmem
    cases hmem2 with
    | inl h => exact hhd h
    | inr h =>
      have heq : hd = x := by simpa using h
      subst heq
      exact h2 (by simp)

theorem activeNet_post_eq (s : State) (e : Entry) (a : AccountId) (h : e.id ∉ s.reversed) :
    activeNet { s with journal := s.journal ++ [e] } a = activeNet s a + netOf e.lines a := by
  unfold activeNet
  simp only
  rw [sumOver_append]
  simp only [sumOver_cons, sumOver_nil]
  simp [h]

theorem wfDecNotMemRev (s : State) (e : Entry) (h : validPostCheck s e = true) :
    e.id ∉ s.reversed := by
  have hunf := probeUnfold s e
  rw [hunf] at h
  cases hl : e.lines with
  | nil => simp [hl] at h
  | cons hd tl =>
    simp only [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := h
    have : ¬ (e.id ∈ s.reversed) := by
      have hd2 : (!decide (e.id ∈ s.reversed)) = true := hE
      cases hh : decide (e.id ∈ s.reversed) with
      | true => simp [hh] at hd2
      | false => exact of_decide_eq_false hh
    exact this

theorem activeNet_rev_unchanged (j : List Entry) (r : List EntryId) (i : EntryId) (a : AccountId)
    (h : i ∉ ids j) :
    sumOver j (fun e => if e.id ∈ i :: r then (0 : Int) else netOf e.lines a)
    = sumOver j (fun e => if e.id ∈ r then (0 : Int) else netOf e.lines a) := by
  induction j with
  | nil => rfl
  | cons hd tl ih =>
    simp only [ids, List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, htl⟩ := h
    have hne2 : ¬ (hd.id = i) := fun heq => hne heq.symm
    simp only [sumOver_cons]
    have hhead : (if hd.id ∈ i :: r then (0 : Int) else netOf hd.lines a)
      = (if hd.id ∈ r then (0 : Int) else netOf hd.lines a) := by
      simp only [List.mem_cons]
      by_cases hm : hd.id ∈ r
      · simp [hm]
      · have hni : ¬ (hd.id = i) := hne2
        simp [hm, hni]
    rw [hhead, ih htl]

theorem activeNet_reverse_aux2 (j : List Entry) (r : List EntryId) (i : EntryId) (e : Entry)
    (a : AccountId) (hN : (ids j).Nodup) (hfind : findEntry j i = some e) (hnot : i ∉ r) :
    sumOver j (fun e' => if e'.id ∈ i :: r then (0 : Int) else netOf e'.lines a)
    = sumOver j (fun e' => if e'.id ∈ r then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  induction j with
  | nil => simp [findEntry] at hfind
  | cons hd tl ih =>
    have hmap : ids (hd :: tl) = hd.id :: ids tl := rfl
    have hN' : (hd.id :: ids tl).Nodup := hmap ▸ hN
    have hNtl : (ids tl).Nodup := (List.nodup_cons.mp hN').2
    have hni : hd.id ∉ ids tl := (List.nodup_cons.mp hN').1
    have hfe : findEntry (hd :: tl) i = (if hd.id = i then some hd else findEntry tl i) := rfl
    rw [hfe] at hfind
    by_cases heq : hd.id = i
    · rw [if_pos heq] at hfind
      have hde : hd = e := by simpa using hfind
      subst hde
      subst heq
      have htail := activeNet_rev_unchanged tl r hd.id a hni
      simp only [sumOver_cons]
      have hhd_old : (if hd.id ∈ r then (0 : Int) else netOf hd.lines a) = netOf hd.lines a := by
        simp [hnot]
      have hhd_new : (if hd.id ∈ hd.id :: r then (0 : Int) else netOf hd.lines a) = 0 := by
        simp
      rw [hhd_new, hhd_old, htail]
      omega
    · rw [if_neg heq] at hfind
      have ih' := ih hNtl hfind
      simp only [sumOver_cons]
      have hhead : (if hd.id ∈ i :: r then (0 : Int) else netOf hd.lines a)
        = (if hd.id ∈ r then (0 : Int) else netOf hd.lines a) := by
        simp only [List.mem_cons]
        by_cases hm : hd.id ∈ r
        · simp [hm]
        · simp [hm, heq]
      rw [hhead, ih']
      omega

theorem req_consistent_aux_post_active (s : State) (e : Entry) (a : AccountId)
    (h : e.id ∉ s.reversed) :
    activeNet ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) a
    = activeNet s a + netOf e.lines a :=
  activeNet_post_eq s e a h

theorem req_consistent_aux_rev_active (s : State) (i : EntryId) (e : Entry) (a : AccountId)
    (hN : (ids s.journal).Nodup) (hfind : findEntry s.journal i = some e) (hnot : i ∉ s.reversed) :
    activeNet ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) a
    = activeNet s a - netOf e.lines a := by
  have h := activeNet_reverse_aux2 s.journal s.reversed i e a hN hfind hnot
  unfold activeNet at h ⊢
  simp only at h ⊢
  exact h

theorem findEntry_some_of_mem_aux (j : List Entry) (i : EntryId) (h : i ∈ ids j) :
    ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons hd tl ih =>
    unfold findEntry
    split
    · exact ⟨hd, rfl⟩
    · rename_i hne
      simp only [ids, List.map_cons, List.mem_cons] at h
      cases h with
      | inl heq =>
        have : hd.id = i := heq.symm
        contradiction
      | inr hmem =>
        obtain ⟨e, he⟩ := ih hmem
        exact ⟨e, he⟩

theorem wfDecNezAux2 (s : State) (e : Entry) (h : validPostCheck s e = true) :
    ∀ l ∈ e.lines, l.2 ≠ 0 := by
  have hunf := probeUnfold s e
  rw [hunf] at h
  cases hl : e.lines with
  | nil => simp [hl] at h
  | cons hd tl =>
    simp only [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := h
    have hBm : ∀ x ∈ hd :: tl, decide (x.2 ≠ 0) = true := (List.all_eq_true.mp hB)
    intro l hlmem
    have hx := hBm l hlmem
    exact of_decide_eq_true hx

theorem findEntry_mem_aux {j : List Entry} {i : EntryId} {e : Entry}
    (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    split at h
    · rename_i heq; cases h; simp
    · rename_i heq
      have := ih h
      simp [this]

theorem req_post_succeeds : PostSucceeds step := by
  intro s e hV
  obtain ⟨hne, hmem, hnez, hsum, hnid, hnrev⟩ := hV
  have hCheck : validPostCheck s e = true := by
    cases hlines : e.lines with
    | nil => exact absurd hlines hne
    | cons hd tl =>
      have hA : ((hd :: tl).all (fun l => decide (l.1 ∈ s.accounts)) = true) :=
        List.all_eq_true.mpr (fun x hx => by
          have hx2 : x ∈ e.lines := by rw [hlines]; exact hx
          exact decide_eq_true (hmem x hx2))
      have hB : ((hd :: tl).all (fun l => decide (l.2 ≠ 0)) = true) :=
        List.all_eq_true.mpr (fun x hx => by
          have hx2 : x ∈ e.lines := by rw [hlines]; exact hx
          exact decide_eq_true (hnez x hx2))
      have hC : decide (lineSum (hd :: tl) = 0) = true := by
        have hsum2 : lineSum (hd :: tl) = 0 := by rw [← hlines]; exact hsum
        exact decide_eq_true hsum2
      have hD : decide (e.id ∈ ids s.journal) = false :=
        decide_eq_false hnid
      have hE : decide (e.id ∈ s.reversed) = false :=
        decide_eq_false hnrev
      exact probeCheck3 s e hd tl hlines hA hB hC hD hE
  show (step s (.post e)).1 = _
  simp only [step, hCheck, ↓reduceIte]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i hV
  obtain ⟨hmem, hnot⟩ := hV
  obtain ⟨e, he⟩ := findEntry_some_of_mem_aux s.journal i hmem
  show (step s (.reverse i)).1 = _
  have hunfold := tmp_reverse_unfold s i
  rw [he] at hunfold
  rw [hunfold]
  simp [hnot]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c hInv
  cases c with
  | post e =>
    simp only [Valid] at hInv
    by_cases hvc : validPostCheck s e = true
    · exfalso
      apply hInv
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact validPostCheck_true_intro s e hvc
      · exact wfDecAllMem s e hvc
      · exact wfDecNezAux2 s e hvc
      · exact wfDecLineSum s e hvc
      · exact wfDecNotMemIds s e hvc
      · exact wfDecNotMemRev s e hvc
    · simp [step, hvc]
  | reverse i =>
    simp only [Valid, ValidReverse] at hInv
    have hunfold := tmp_reverse_unfold s i
    cases hfe : findEntry s.journal i with
    | none =>
      rw [hunfold, hfe]
    | some e =>
      have hmem_ids : i ∈ ids s.journal := findEntry_mem_ids4 hfe
      have hid : i ∈ s.reversed := by
        cases Decidable.em (i ∈ s.reversed) with
        | inl h => exact h
        | inr h => exfalso; exact hInv ⟨hmem_ids, h⟩
      rw [hunfold, hfe]
      simp [hid]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  by_cases hvc : validPostCheck s e = true
  · have hstep : step s (.post e) = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
      simp [step, hvc]
    rw [hstep]
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro a
    rfl
  · have hstep : step s (.post e) = (Outcome.rejected, s) := by
      simp [step, hvc]
    rw [hstep] at hok
    simp at hok

theorem req_reverse_effects  : ReverseEffects step := by
  intro s i e hok hfind
  have hunfold : step s (.reverse i) =
    (match findEntry s.journal i with
    | none => (Outcome.rejected, s)
    | some e => if i ∈ s.reversed then (Outcome.rejected, s)
      else (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed })) :=
    tmp_reverse_unfold s i
  rw [hfind] at hunfold
  by_cases hmem : i ∈ s.reversed
  · simp [hmem] at hunfold
    rw [hunfold] at hok
    simp at hok
  · simp [hmem] at hunfold
    rw [hunfold]
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro x
      simp only [List.mem_cons]
    · intro a
      rfl

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  have hunfold : step s (.reverse i) =
    (match findEntry s.journal i with
    | none => (Outcome.rejected, s)
    | some e => if i ∈ s.reversed then (Outcome.rejected, s)
      else (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed })) :=
    tmp_reverse_unfold s i
  cases hfe : findEntry s.journal i with
  | none =>
    rw [hfe] at hunfold
    simp at hunfold
    rw [hunfold] at hok
    simp at hok
  | some e =>
    rw [hfe] at hunfold
    simp only at hunfold
    by_cases hmem : i ∈ s.reversed
    · simp [hmem] at hunfold
      rw [hunfold] at hok
      simp at hok
    · simp [hmem] at hunfold
      have hstep : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := hunfold
      have hs2eq : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
        rw [hstep]
      have hj : (step s (.reverse i)).2.journal = s.journal := by rw [hs2eq]
      have hr : (step s (.reverse i)).2.reversed = i :: s.reversed := by rw [hs2eq]
      have hunfold2 : step (step s (.reverse i)).2 (.reverse i) =
        (match findEntry (step s (.reverse i)).2.journal i with
        | none => (Outcome.rejected, (step s (.reverse i)).2)
        | some e2 => if i ∈ (step s (.reverse i)).2.reversed then (Outcome.rejected, (step s (.reverse i)).2)
          else (Outcome.ok, { (step s (.reverse i)).2 with balance := fun a => (step s (.reverse i)).2.balance a - netOf e2.lines a, reversed := i :: (step s (.reverse i)).2.reversed })) := by
        rfl
      rw [hj, hfe] at hunfold2
      simp only at hunfold2
      have hmem2 : i ∈ (step s (.reverse i)).2.reversed := by rw [hr]; simp
      simp [hmem2] at hunfold2
      exact hunfold2

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  by_cases hvc : validPostCheck s e = true
  · have hstepP : step s (.post e) = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
      simp [step, hvc]
    have hs2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
      rw [hstepP]
    have hNotIds : e.id ∉ ids s.journal := wfDecNotMemIds s e hvc
    have hNotRev : e.id ∉ s.reversed := wfDecNotMemRev s e hvc
    have hfind : findEntry (s.journal ++ [e]) e.id = some e :=
      findSome_append_new2 hNotIds
    have hj : (step s (.post e)).2.journal = s.journal ++ [e] := by rw [hs2]
    have hr : (step s (.post e)).2.reversed = s.reversed := by rw [hs2]
    have hfind' : findEntry (step s (.post e)).2.journal e.id = some e := by rw [hj]; exact hfind
    have hnotrev' : e.id ∉ (step s (.post e)).2.reversed := by rw [hr]; exact hNotRev
    have hunfold2 := tmp_reverse_unfold (step s (.post e)).2 e.id
    rw [hfind'] at hunfold2
    simp only [hnotrev', ↓reduceIte] at hunfold2
    have hok2 : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by
      rw [hunfold2]
    refine ⟨hok2, ?_⟩
    have hbal2 : (step (step s (.post e)).2 (.reverse e.id)).2 =
      ({ (step s (.post e)).2 with balance := fun a => (step s (.post e)).2.balance a - netOf e.lines a, reversed := e.id :: (step s (.post e)).2.reversed } : State) := by
      rw [hunfold2]
    rw [hbal2]
    funext a
    show (({ (step s (.post e)).2 with balance := fun a => (step s (.post e)).2.balance a - netOf e.lines a, reversed := e.id :: (step s (.post e)).2.reversed } : State).balance a = s.balance a)
    simp only
    have hbal_s' : (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by
      rw [hs2]
    rw [hbal_s']
    omega
  · have hstep : step s (.post e) = (Outcome.rejected, s) := by
      simp [step, hvc]
    rw [hstep] at hok
    simp at hok

theorem req_trial_balance : TrialBalance step := by
  intro s c hWF hok
  obtain ⟨hNacc, hNids, hrevsub, hbal0⟩ := hWF
  cases c with
  | post e =>
    by_cases hvc : validPostCheck s e = true
    · have hstep : step s (.post e) = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
        simp [step, hvc]
      have hs2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        rw [hstep]
      have htotal : total (step s (.post e)).2 = total s := by
        rw [hs2]
        unfold total
        simp only
        have hadd : sumOver s.accounts (fun a => s.balance a + netOf e.lines a)
          = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) :=
          sumOver_add s.accounts s.balance _
        rw [hadd]
        have hmem : ∀ l ∈ e.lines, l.1 ∈ s.accounts := wfDecAllMem s e hvc
        have hnet : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
          tb_sum_net e.lines s.accounts hNacc hmem
        have hsum0 : lineSum e.lines = 0 := wfDecLineSum s e hvc
        rw [hnet, hsum0]
        simp
      exact htotal
    · have hstep : step s (.post e) = (Outcome.rejected, s) := by
        simp [step, hvc]
      rw [hstep] at hok
      simp at hok
  | reverse i =>
    have hunfold := tmp_reverse_unfold s i
    cases hfe : findEntry s.journal i with
    | none =>
      have hstep : step s (.reverse i) = (Outcome.rejected, s) := by
        rw [hunfold, hfe]
      rw [hstep] at hok
      simp at hok
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · have hstep : step s (.reverse i) = (Outcome.rejected, s) := by
          rw [hunfold, hfe]
          simp [hmem]
        rw [hstep] at hok
        simp at hok
      · have hstep : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
          rw [hunfold, hfe]
          simp [hmem]
        have hs2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
          rw [hstep]
        have hemem : e ∈ s.journal := findEntry_mem_aux hfe
        have heWF := hbal0 e hemem
        obtain ⟨hememAcc, hsum0⟩ := heWF
        have htotal : total (step s (.reverse i)).2 = total s := by
          rw [hs2]
          unfold total
          simp only
          have hsub : sumOver s.accounts (fun a => s.balance a - netOf e.lines a)
            = sumOver s.accounts s.balance - sumOver s.accounts (fun a => netOf e.lines a) :=
            sumOver_sub s.accounts s.balance _
          rw [hsub]
          have hnet : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
            tb_sum_net e.lines s.accounts hNacc hememAcc
          rw [hnet, hsum0]
          simp
        exact htotal

theorem req_well_formed : StaysWellFormed step := by
  intro s c hWF
  obtain ⟨hNacc, hNids, hrevsub, hbal0⟩ := hWF
  cases c with
  | post e =>
    by_cases hvc : validPostCheck s e = true
    · have hstep : step s (.post e) = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
        simp [step, hvc]
      have hs2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        rw [hstep]
      rw [hs2]
      have hmem : ∀ l ∈ e.lines, l.1 ∈ s.accounts := wfDecAllMem s e hvc
      have hsum0 : lineSum e.lines = 0 := wfDecLineSum s e hvc
      have hnid : e.id ∉ ids s.journal := wfDecNotMemIds s e hvc
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only
        exact hNacc
      · simp only
        have hids : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := ids_append_single2 s.journal e
        rw [hids]
        exact nodup_append_singleton6 (ids s.journal) e.id hNids hnid
      · simp only
        intro i hi
        have hold := hrevsub i hi
        have hids : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := ids_append_single2 s.journal e
        rw [hids]
        exact List.mem_append.mpr (Or.inl hold)
      · simp only
        intro e' he'
        have hmem' : e' ∈ s.journal ++ [e] := he'
        have hor := List.mem_append.mp hmem'
        cases hor with
        | inl h =>
          have heWF := hbal0 e' h
          obtain ⟨h1, h2⟩ := heWF
          exact ⟨h1, h2⟩
        | inr h =>
          simp only [List.mem_singleton] at h
          subst h
          exact ⟨hmem, hsum0⟩
    · have hstep : step s (.post e) = (Outcome.rejected, s) := by
        simp [step, hvc]
      have hs2 : (step s (.post e)).2 = s := by rw [hstep]
      rw [hs2]
      exact ⟨hNacc, hNids, hrevsub, hbal0⟩
  | reverse i =>
    have hunfold := tmp_reverse_unfold s i
    cases hfe : findEntry s.journal i with
    | none =>
      have hstep : step s (.reverse i) = (Outcome.rejected, s) := by
        rw [hunfold, hfe]
      have hs2 : (step s (.reverse i)).2 = s := by rw [hstep]
      rw [hs2]
      exact ⟨hNacc, hNids, hrevsub, hbal0⟩
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · have hstep : step s (.reverse i) = (Outcome.rejected, s) := by
          rw [hunfold, hfe]
          simp [hmem]
        have hs2 : (step s (.reverse i)).2 = s := by rw [hstep]
        rw [hs2]
        exact ⟨hNacc, hNids, hrevsub, hbal0⟩
      · have hstep : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
          rw [hunfold, hfe]
          simp [hmem]
        have hs2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
          rw [hstep]
        rw [hs2]
        have hi_ids : i ∈ ids s.journal := findEntry_mem_ids4 hfe
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only
          exact hNacc
        · simp only
          exact hNids
        · simp only
          intro j hj
          simp only [List.mem_cons] at hj
          cases hj with
          | inl heq => subst heq; exact hi_ids
          | inr hm => exact hrevsub j hm
        · simp only
          intro e' he'
          exact hbal0 e' he'

theorem req_consistent : StaysConsistent step := by
  intro s c hWF hCons
  cases c with
  | post e =>
    by_cases hvc : validPostCheck s e = true
    · have hstep : step s (.post e) = (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
        simp [step, hvc]
      have hs2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        rw [hstep]
      rw [hs2]
      intro a
      have hnot : e.id ∉ s.reversed := wfDecNotMemRev s e hvc
      have hbal : (({ s with journal := s.journal ++ [e], balance := fun a' => s.balance a' + netOf e.lines a' } : State).balance) a
        = s.balance a + netOf e.lines a := rfl
      have hopen : (({ s with journal := s.journal ++ [e], balance := fun a' => s.balance a' + netOf e.lines a' } : State).opening) a
        = s.opening a := rfl
      rw [hbal, hopen]
      have hact := req_consistent_aux_post_active s e a hnot
      -- hact : activeNet new = activeNet s + net
      have hcon := hCons a
      -- rewrite hact's LHS is activeNet of new state
      rw [hact] at *
      omega
    · have hstep : step s (.post e) = (Outcome.rejected, s) := by
        simp [step, hvc]
      have hs2 : (step s (.post e)).2 = s := by rw [hstep]
      rw [hs2]
      exact hCons
  | reverse i =>
    have hunfold := tmp_reverse_unfold s i
    cases hfe : findEntry s.journal i with
    | none =>
      have hstep : step s (.reverse i) = (Outcome.rejected, s) := by
        rw [hunfold, hfe]
      have hs2 : (step s (.reverse i)).2 = s := by rw [hstep]
      rw [hs2]
      exact hCons
    | some e =>
      by_cases hmem : i ∈ s.reversed
      · have hstep : step s (.reverse i) = (Outcome.rejected, s) := by
          rw [hunfold, hfe]
          simp [hmem]
        have hs2 : (step s (.reverse i)).2 = s := by rw [hstep]
        rw [hs2]
        exact hCons
      · have hstep : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
          rw [hunfold, hfe]
          simp [hmem]
        have hs2 : (step s (.reverse i)).2 = ({ s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } : State) := by
          rw [hstep]
        rw [hs2]
        obtain ⟨hNacc, hNids, hrevsub, hbal0⟩ := hWF
        intro a
        have hbal : (({ s with balance := fun a' => s.balance a' - netOf e.lines a', reversed := i :: s.reversed } : State).balance) a
          = s.balance a - netOf e.lines a := rfl
        have hopen : (({ s with balance := fun a' => s.balance a' - netOf e.lines a', reversed := i :: s.reversed } : State).opening) a
          = s.opening a := rfl
        rw [hbal, hopen]
        have hact := req_consistent_aux_rev_active s i e a hNids hfe hmem
        have hcon := hCons a
        rw [hact] at *
        omega

end Reversal
