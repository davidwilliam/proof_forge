import Reversal.Spec
import Reversal.Lemmas

namespace Reversal

def step : Impl := fun s c =>
  match c with
  | .post e =>
    let accountsOk : Bool := e.lines.all (fun l => s.accounts.contains l.1)
    let nonZeroOk : Bool := e.lines.all (fun l => l.2 != 0)
    let balanced : Bool := lineSum e.lines == 0
    let idFreshJ : Bool := !((ids s.journal).contains e.id)
    let idFreshR : Bool := !(s.reversed.contains e.id)
    let nonEmpty : Bool := !e.lines.isEmpty
    if accountsOk && nonZeroOk && balanced && idFreshJ && idFreshR && nonEmpty then
      (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a })
    else
      (Outcome.rejected, s)
  | .reverse i =>
    let inJ : Bool := (ids s.journal).contains i
    let notR : Bool := !(s.reversed.contains i)
    if inJ && notR then
      match findEntry s.journal i with
      | some e => (Outcome.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a })
      | none => (Outcome.rejected, s)
    else
      (Outcome.rejected, s)

theorem dummy2 : True := trivial

theorem probe_all : ∀ {α : Type} {p : α → Bool} {l : List α}, l.all p = true ↔ ∀ x, x ∈ l → p x = true := @List.all_eq_true
#check @List.elem_eq_mem
#check List.contains
#check @List.contains_eq_mem
#check @decide_eq_true

theorem dummy3 : True := trivial

theorem dummy_probe3 : True := trivial

theorem probe_stmt : True := trivial

theorem probe_names_ok : True := trivial

theorem helper_contains_mem : ∀ (l : List Nat) (x : Nat), l.contains x = decide (x ∈ l) := fun l x => List.contains_eq_mem x l

theorem helper_reverse_inJ : ∀ (s : State) (i : EntryId), i ∈ ids s.journal → ((ids s.journal).contains i) = true := by
  intro s i h
  rw [helper_contains_mem]
  simp [h]

theorem helper_reverse_notR : ∀ (s : State) (i : EntryId), i ∉ s.reversed → (!(s.reversed.contains i)) = true := by
  intro s i h
  rw [helper_contains_mem]
  simp [h]

theorem helper_ids_cons : ∀ (e : Entry) (es : List Entry), ids (e :: es) = e.id :: ids es := fun _ _ => rfl

theorem helper_findEntry_of_mem2 : ∀ (j : List Entry) (i : EntryId), i ∈ ids j → ∃ e, findEntry j i = some e := by
  intro j i h
  induction j with
  | nil => simp [ids] at h
  | cons e es ih =>
    have hcons : i = e.id ∨ i ∈ ids es := by
      have heq : ids (e :: es) = e.id :: ids es := rfl
      rw [heq] at h
      exact (List.mem_cons.mp h)
    have hfind : findEntry (e :: es) i = (if e.id = i then some e else findEntry es i) := by
      simp [findEntry]
    rw [hfind]
    by_cases he : e.id = i
    · simp [he]
    · simp [he]
      cases hcons with
      | inl heq => simp [heq] at he
      | inr hmem => exact ih hmem

theorem tmp2 : ReverseSucceeds step := by
  intro s i h
  obtain ⟨hinJ, hnotR⟩ := h
  obtain ⟨e, he⟩ := helper_findEntry_of_mem2 s.journal i hinJ
  unfold step
  simp [hinJ, hnotR, he]

theorem probeA : ∀ (l : List Nat) (x : Nat), (decide (x ∈ l) = true) ↔ x ∈ l := by
  intro l x; simp

theorem probeB : ∀ (b : Bool), ((!b) = true) ↔ (b = false) := by intro b; cases b <;> simp
#check List.all_eq_true
#check decide_eq_true
#check Bool.and_eq_true
#check beq_iff_eq
#check List.contains_eq_mem
#check List.isEmpty
#check List.elem_eq_mem

theorem aux_contains_true_iff_memX : ∀ (l : List Nat) (x : Nat),
  ((l.contains x) = true) ↔ x ∈ l := by
  intro l x
  rw [helper_contains_mem]
  simp

theorem aux_all_accounts2 : ∀ (e : Entry) (s : State),
  ((e.lines.all (fun l => s.accounts.contains l.1) = true) ↔ ∀ l ∈ e.lines, l.1 ∈ s.accounts) := by
  intro e s
  rw [List.all_eq_true]
  constructor
  · intro h l hl
    have h1 : s.accounts.contains l.1 = true := h l hl
    exact (aux_contains_true_iff_memX s.accounts l.1).mp h1
  · intro h l hl
    have h1 : l.1 ∈ s.accounts := h l hl
    have h2 : s.accounts.contains l.1 = true := (aux_contains_true_iff_memX s.accounts l.1).mpr h1
    exact h2

theorem tmp_rfl_check (s : State) (e : Entry) :
  step s (.post e) =
    (let accountsOk : Bool := e.lines.all (fun l => s.accounts.contains l.1);
     let nonZeroOk : Bool := e.lines.all (fun l => l.2 != 0);
     let balanced : Bool := lineSum e.lines == 0;
     let idFreshJ : Bool := !((ids s.journal).contains e.id);
     let idFreshR : Bool := !(s.reversed.contains e.id);
     let nonEmpty : Bool := !e.lines.isEmpty;
    if accountsOk && nonZeroOk && balanced && idFreshJ && idFreshR && nonEmpty then
      (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a })
    else
      (Outcome.rejected, s)) := rfl

theorem tmp_plain (s : State) (e : Entry) :
  step s (.post e) = if (e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) then
      (Outcome.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a })
    else
      (Outcome.rejected, s) := rfl

theorem req_post_effects_proof2 : PostEffects step := by
  intro s e h
  rw [tmp_plain] at h ⊢
  by_cases hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)
  · rw [if_pos hc]
    exact ⟨rfl, rfl, rfl, rfl, fun a => rfl⟩
  · have h2 : ¬ ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true) := hc
    rw [if_neg h2] at h
    simp at h

theorem tmp_rev_plain2 (s : State) (i : EntryId) :
  step s (.reverse i) = if ((ids s.journal).contains i && !(s.reversed.contains i)) then
      (match findEntry s.journal i with
      | some e => (Outcome.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a })
      | none => (Outcome.rejected, s))
    else
      (Outcome.rejected, s) := rfl

theorem req_reverse_effects2  : ReverseEffects step := by
  intro s i e hOk hFind
  have hplain := tmp_rev_plain2 s i
  rw [hplain] at hOk ⊢
  by_cases hc : (((ids s.journal).contains i && !(s.reversed.contains i)) = true)
  · rw [if_pos hc] at hOk ⊢
    rw [hFind] at hOk ⊢
    refine ⟨rfl, rfl, rfl, ?_, fun a => rfl⟩
    intro x
    simp
  · exfalso
    rw [if_neg hc] at hOk
    simp at hOk

theorem req_reverse_once_aux_clean : True := trivial

theorem myProbeBool (a b : Bool) (h : (a && b) = true) : a = true := by
  have h2 := (Bool.and_eq_true_iff.mp h).1
  exact h2
#check Bool.and_eq_true_iff
#check List.contains_eq_mem
#check findEntry

theorem myProbeFind (e : Entry) (rest : List Entry) (i : EntryId) (hne : e.id ≠ i) :
  findEntry (e :: rest) i = findEntry rest i := by
  simp [findEntry, hne]

theorem myProbeFind2 (e : Entry) (rest : List Entry) :
  findEntry (e :: rest) e.id = some e := by
  simp [findEntry]

theorem myProbeIds (e : Entry) (es : List Entry) : ids (e :: es) = e.id :: ids es := rfl

theorem myProbeMemIds (e : Entry) (es : List Entry) (i : EntryId) (hm : i ∈ ids es) :
  i ∈ ids (e :: es) := by
  rw [myProbeIds]
  exact List.mem_cons_of_mem e.id hm

theorem myProbeMemHead (e : Entry) (es : List Entry) : e.id ∈ ids (e :: es) := by
  rw [myProbeIds]
  exact List.Mem.head _

theorem myRT_find_append5 (l₁ : List Entry) (l₂ : List Entry) (i : EntryId)
  (h : i ∉ ids l₁) : findEntry (l₁ ++ l₂) i = findEntry l₂ i := by
  induction l₁ with
  | nil => rfl
  | cons e es ih =>
    have hne : e.id ≠ i := by
      intro heq
      apply h
      rw [← heq]
      exact myProbeMemHead e es
    have hmem : i ∉ ids es := by
      intro hm
      apply h
      exact myProbeMemIds e es i hm
    simp only [List.cons_append]
    rw [myProbeFind e (es ++ l₂) i hne]
    exact ih hmem

theorem myRT_find_single (e : Entry) : findEntry [e] e.id = some e :=
  myProbeFind2 e []

theorem myRT_post_find (s : State) (e : Entry) (hJ : e.id ∉ ids s.journal) :
  findEntry (s.journal ++ [e]) e.id = some e := by
  have h1 : findEntry (s.journal ++ [e]) e.id = findEntry [e] e.id := by
    apply myRT_find_append5 s.journal [e] e.id hJ
  rw [h1]
  exact myRT_find_single e

theorem helper_single_net2 : ∀ (accounts : List AccountId) (p : Line),
  p.1 ∈ accounts → accounts.Nodup →
  sumOver accounts (fun a => if p.1 = a then p.2 else 0) = p.2 := by
  intro accounts p hmem hnodup
  have hcongr : ∀ a ∈ accounts, (if p.1 = a then p.2 else (0 : Int)) = (if a = p.1 then p.2 else 0) := by
    intro a _
    by_cases h : p.1 = a
    · subst h; simp
    · have h2 : ¬ (a = p.1) := fun hh => h hh.symm
      simp [h, h2]
  rw [sumOver_congr _ _ _ hcongr]
  rw [sumOver_ite_eq hnodup p.1 p.2]
  rw [if_pos hmem]

theorem helper_net_single : ∀ (accounts : List AccountId) (p : Line),
  accounts.Nodup →
  sumOver accounts (fun a => if p.1 = a then p.2 else (0 : Int)) = (if p.1 ∈ accounts then p.2 else 0) := by
  intro accounts p hnodup
  have hcongr : ∀ a ∈ accounts, (if p.1 = a then p.2 else (0 : Int)) = (if a = p.1 then p.2 else 0) := by
    intro a _
    by_cases h : p.1 = a
    · subst h; rfl
    · have h2 : ¬ (a = p.1) := fun hh => h hh.symm
      simp [h, h2]
  rw [sumOver_congr _ _ _ hcongr]
  exact sumOver_ite_eq hnodup p.1 p.2

theorem helper_sum_zero : ∀ (accounts : List AccountId),
  sumOver accounts (fun _ : AccountId => (0 : Int)) = 0 := by
  intro accounts
  induction accounts with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem helper_beq_zero : ∀ (x : Int), (x == 0) = true → x = 0 := by
  intro x h
  exact (beq_iff_eq.mp h)

theorem helper_and_true_left : ∀ (a b : Bool), ((a && b) = true) → a = true := by
  intro a b h
  exact (Bool.and_eq_true_iff.mp h).1

theorem helper_and_true_right : ∀ (a b : Bool), ((a && b) = true) → b = true := by
  intro a b h
  exact (Bool.and_eq_true_iff.mp h).2

theorem helper_post_ok_balanced2 : ∀ (s : State) (e : Entry),
  (step s (.post e)).1 = .ok → lineSum e.lines = 0 := by
  intro s e hok
  rw [tmp_plain] at hok
  by_cases hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)
  · rw [if_pos hc] at hok
    have h1 : (((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id)) && !e.lines.isEmpty) = true) := hc
    have h2 := helper_and_true_left _ _ h1
    have h3 := helper_and_true_left _ _ h2
    have h4 := helper_and_true_left _ _ h3
    have h5 := helper_and_true_right _ _ h4
    exact helper_beq_zero _ h5
  · rw [if_neg hc] at hok
    simp at hok

theorem probe_and_split (a b c d e f : Bool) (h : ((a && b && c && d && e && f) = true)) : a = true ∧ f = true := by
  simp only [Bool.and_eq_true_iff] at h
  exact ⟨h.1.1.1.1.1, h.2⟩

theorem probe_and_parse (A B C D E F : Bool)
  (hc : ((A && B && C && D && E && F) = true)) :
  A = true ∧ B = true ∧ C = true ∧ D = true ∧ E = true ∧ F = true := by
  simp only [Bool.and_eq_true_iff] at hc
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩ := hc
  exact ⟨hA, hB, hC, hD, hE, hF⟩

theorem helper_post_true_split (s : State) (e : Entry)
  (hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)) :
  (e.lines.all (fun l => s.accounts.contains l.1) = true) ∧
  ((lineSum e.lines == 0) = true) ∧
  ((!((ids s.journal).contains e.id)) = true) := by
  have h := probe_and_parse _ _ _ _ _ _ hc
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

theorem probe_nodup_app_single2 {l : List Nat} (h : l.Nodup) (x : Nat) (hx : x ∉ l) :
  (l ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨h, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
  intro a ha b hb
  simp at hb
  subst hb
  intro hcontra
  subst hcontra
  exact hx ha

theorem wf_post_accounts_of_ok (s : State) (e : Entry)
  (hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)) :
  ∀ l ∈ e.lines, l.1 ∈ s.accounts := by
  have h := probe_and_parse _ _ _ _ _ _ hc
  have hall : e.lines.all (fun l => s.accounts.contains l.1) = true := h.1
  exact (aux_all_accounts2 e s).mp hall

theorem wf_post_bal_of_ok (s : State) (e : Entry)
  (hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)) :
  lineSum e.lines = 0 := by
  have h := probe_and_parse _ _ _ _ _ _ hc
  exact helper_beq_zero _ h.2.2.1

theorem wf_post_freshJ_of_ok (s : State) (e : Entry)
  (hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)) :
  e.id ∉ ids s.journal := by
  have h := probe_and_parse _ _ _ _ _ _ hc
  have hd : ((!((ids s.journal).contains e.id)) = true) := h.2.2.2.1
  have hcon : ((ids s.journal).contains e.id) = false := by cases hh : ((ids s.journal).contains e.id) <;> simp_all
  rw [helper_contains_mem] at hcon
  simp at hcon
  exact hcon

theorem wf_rev_mem_of_ok (s : State) (i : EntryId)
  (hc : (((ids s.journal).contains i && !(s.reversed.contains i)) = true)) :
  i ∈ ids s.journal := by
  have h := (Bool.and_eq_true_iff.mp hc).1
  have hmem : ((ids s.journal).contains i) = true := h
  rw [helper_contains_mem] at hmem
  simp at hmem
  exact hmem

theorem wf_need3c (s : State) (e : Entry) (hw : WellFormed s)
  (hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)) :
  ∀ e' ∈ (s.journal ++ [e]), (∀ l ∈ e'.lines, l.1 ∈ s.accounts) ∧ lineSum e'.lines = 0 := by
  intro e' hm
  rw [List.mem_append] at hm
  cases hm with
  | inl h => exact hw.2.2.2 e' h
  | inr h =>
    have heq : e' = e := by simpa using h
    rw [heq]
    exact ⟨wf_post_accounts_of_ok s e hc, wf_post_bal_of_ok s e hc⟩

theorem wf_need1c (s : State) (e : Entry) (hw : WellFormed s)
  (hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)) :
  (ids (s.journal ++ [e])).Nodup := by
  have hnod := hw.2.1
  have hfresh := wf_post_freshJ_of_ok s e hc
  have hids : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := by simp [ids]
  rw [hids]
  exact probe_nodup_app_single2 hnod e.id hfresh

theorem cons_find_mem2 (j : List Entry) (i : EntryId) (e : Entry) (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; subst h; exact List.Mem.head tl
    · simp [heq] at h; exact List.Mem.tail hd (ih h)

theorem cons_find_id2 (j : List Entry) (i : EntryId) (e : Entry) (h : findEntry j i = some e) : e.id = i := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; subst h; exact heq
    · simp [heq] at h; exact ih h

theorem cons_active_post (s : State) (e : Entry) (a : AccountId) (h : e.id ∉ s.reversed) :
  activeNet { s with journal := s.journal ++ [e], reversed := s.reversed } a =
  activeNet s a + netOf e.lines a := by
  unfold activeNet
  simp only
  rw [sumOver_append]
  simp only [sumOver_cons, sumOver_nil]
  have hif : (if e.id ∈ s.reversed then (0 : Int) else netOf e.lines a) = netOf e.lines a := by
    simp [h]
  -- need sumOver_append gives + ; adjust
  rw [hif]
  omega

theorem probe_mem_cases (hd : Entry) (tl : List Entry) (e : Entry) (hm : e ∈ hd :: tl) : e = hd ∨ e ∈ tl := List.mem_cons.mp hm

theorem probe_nez (x : Int) (h : x ≠ 0) : ((x != 0) = true) := by
  simp [h]

theorem probe_beq0 (x : Int) (h : x = 0) : ((x == 0) = true) := by
  simp [h]

theorem probe_all_nz (e : Entry) (h : ∀ l ∈ e.lines, l.2 ≠ 0) :
  (e.lines.all (fun l => l.2 != 0) = true) := by
  rw [List.all_eq_true]
  intro x hx
  exact probe_nez x.2 (h x hx)

theorem probe_dec1 (l : List Nat) (x : Nat) (h : x ∉ l) : (l.contains x = false) := by
  rw [helper_contains_mem, decide_eq_false h]

theorem probe_dec2 (l : List Nat) (x : Nat) (h : x ∈ l) : (l.contains x = true) := by
  rw [helper_contains_mem, decide_eq_true h]

theorem probe_true_and : ((true && true && true && true && true && true) = true) := rfl

theorem probe_true_and2 : ((true && true) = true) := rfl

theorem probe_post_parts (s : State) (e : Entry)
  (hacc : ∀ l ∈ e.lines, l.1 ∈ s.accounts)
  (hbal : lineSum e.lines = 0)
  (hfreshJ : e.id ∉ ids s.journal)
  (hfreshR : e.id ∉ s.reversed)
  (hne : e.lines ≠ []) :
  (e.lines.all (fun l => s.accounts.contains l.1) = true) ∧
  ((lineSum e.lines == 0) = true) ∧
  ((!((ids s.journal).contains e.id)) = true) ∧
  ((!(s.reversed.contains e.id)) = true) ∧
  ((!e.lines.isEmpty) = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (aux_all_accounts2 e s).mpr hacc
  · rw [hbal]; rfl
  · have hc : ((ids s.journal).contains e.id) = false := probe_dec1 _ _ hfreshJ
    rw [hc]; rfl
  · have hc : (s.reversed.contains e.id = false) := probe_dec1 _ _ hfreshR
    rw [hc]; rfl
  · cases he : e.lines with
    | nil => simp [he] at hne
    | cons hd tl => rfl

theorem helper_post_nz_of_ok (s : State) (e : Entry)
  (hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)) :
  ∀ l ∈ e.lines, l.2 ≠ 0 := by
  have h := probe_and_parse _ _ _ _ _ _ hc
  have hB : (e.lines.all (fun l => l.2 != 0) = true) := h.2.1
  rw [List.all_eq_true] at hB
  intro l hl h0
  have hx := hB l hl
  rw [h0] at hx
  simp at hx

theorem helper_post_nonempty_of_ok (s : State) (e : Entry)
  (hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)) :
  e.lines ≠ [] := by
  have h := probe_and_parse _ _ _ _ _ _ hc
  have hF : ((!e.lines.isEmpty) = true) := h.2.2.2.2.2
  intro hcon
  rw [hcon] at hF
  simp at hF

theorem helper_post_freshR_of_ok (s : State) (e : Entry)
  (hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)) :
  e.id ∉ s.reversed := by
  have h := probe_and_parse _ _ _ _ _ _ hc
  have hd : ((!(s.reversed.contains e.id)) = true) := h.2.2.2.2.1
  have h1 : (s.reversed.contains e.id) = decide (e.id ∈ s.reversed) := helper_contains_mem _ _
  rw [h1] at hd
  simp at hd
  exact hd

theorem helper_rev_notR_of_ok (s : State) (i : EntryId)
  (hc : (((ids s.journal).contains i && !(s.reversed.contains i)) = true)) :
  i ∉ s.reversed := by
  have h2 := (Bool.and_eq_true_iff.mp hc).2
  have h1 : (s.reversed.contains i) = decide (i ∈ s.reversed) := helper_contains_mem _ _
  rw [h1] at h2
  simp at h2
  exact h2

theorem trial_total_post_aux2 (s : State) (e : Entry) (hAcc : (step s (.post e)).2.accounts = s.accounts)
  (hBal : ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a) :
  total (step s (.post e)).2 = total s + sumOver s.accounts (fun a => netOf e.lines a) := by
  unfold total
  rw [hAcc]
  have hcongr : ∀ a ∈ s.accounts, (step s (.post e)).2.balance a = (s.balance a + netOf e.lines a) :=
    fun a _ => hBal a
  rw [sumOver_congr _ _ _ hcongr, sumOver_add]

theorem trial_total_rev_aux2 (s : State) (i : EntryId) (e : Entry)
  (hAcc : (step s (.reverse i)).2.accounts = s.accounts)
  (hBal : ∀ a, (step s (.reverse i)).2.balance a = s.balance a - netOf e.lines a) :
  total (step s (.reverse i)).2 = total s - sumOver s.accounts (fun a => netOf e.lines a) := by
  unfold total
  rw [hAcc]
  have hcongr : ∀ a ∈ s.accounts, (step s (.reverse i)).2.balance a = (s.balance a - netOf e.lines a) :=
    fun a _ => hBal a
  rw [sumOver_congr _ _ _ hcongr, sumOver_sub]

theorem trial_sum_net_aux : ∀ (accounts : List AccountId) (ls : List Line),
  accounts.Nodup → (∀ l ∈ ls, l.1 ∈ accounts) →
  sumOver accounts (fun a => netOf ls a) = lineSum ls := by
  intro accounts ls
  induction ls with
  | nil =>
    intro _ _
    unfold netOf lineSum
    simp only [sumOver_nil]
    exact helper_sum_zero accounts
  | cons p rest ih =>
    intro hnod hmem
    have hhead : p.1 ∈ accounts := hmem p (by simp)
    have htail : ∀ l ∈ rest, l.1 ∈ accounts := fun l hl => hmem l (by simp [hl])
    have hnet_cons : ∀ a, netOf (p :: rest) a = (if p.1 = a then p.2 else 0) + netOf rest a := by
      intro a
      rfl
    have hcongr : ∀ a ∈ accounts, (netOf (p :: rest) a) = ((if p.1 = a then p.2 else (0:Int)) + netOf rest a) := fun a _ => hnet_cons a
    have h1 : sumOver accounts (fun a => netOf (p :: rest) a) = sumOver accounts (fun a => (if p.1 = a then p.2 else 0) + netOf rest a) :=
      sumOver_congr _ _ _ hcongr
    rw [h1, sumOver_add]
    have h2 : sumOver accounts (fun a => (if p.1 = a then p.2 else (0:Int))) = p.2 := by
      have hc : ∀ a ∈ accounts, (if p.1 = a then p.2 else (0:Int)) = (if a = p.1 then p.2 else 0) := by
        intro a _
        by_cases h : p.1 = a
        · subst h
          rfl
        · have h2 : ¬ (a = p.1) := fun hh => h hh.symm
          simp [h, h2]
      rw [sumOver_congr _ _ _ hc]
      rw [sumOver_ite_eq hnod p.1 p.2, if_pos hhead]
    rw [h2, ih hnod htail]
    rfl

theorem wf_post_rev_subset_aux (s : State) (e : Entry) (hw : WellFormed s) :
  ∀ x ∈ s.reversed, x ∈ ids (s.journal ++ [e]) := by
  intro x hx
  have hold : x ∈ ids s.journal := hw.2.2.1 x hx
  have hids : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := by simp [ids]
  rw [hids]
  exact List.mem_append.mpr (Or.inl hold)

theorem aux_rev_congr_helper : ∀ (j : List Entry) (l : List EntryId) (i : EntryId) (a : AccountId),
  i ∉ ids j →
  (∀ e' ∈ j, (if e'.id ∈ i :: l then (0:Int) else netOf e'.lines a) = (if e'.id ∈ l then (0:Int) else netOf e'.lines a)) := by
  intro j l i a hi e' he'
  have hne : e'.id ≠ i := by
    intro heq
    apply hi
    simp [ids]
    exact ⟨e', he', heq⟩
  simp [hne]

theorem aux_active_rev_eq : ∀ (j : List Entry) (l : List EntryId) (i : EntryId) (e : Entry) (a : AccountId),
  (ids j).Nodup → i ∉ l → i ∈ ids j → findEntry j i = some e →
  sumOver j (fun e' => if e'.id ∈ (i :: l) then (0:Int) else netOf e'.lines a) =
  sumOver j (fun e' => if e'.id ∈ l then (0:Int) else netOf e'.lines a) - netOf e.lines a := by
  intro j
  induction j with
  | nil =>
    intro l i e a _ _ hm _
    simp [ids] at hm
  | cons hd tl ih =>
    intro l i e a hnod hnotl hmem hfind
    have hids_cons : ids (hd :: tl) = hd.id :: ids tl := rfl
    rw [hids_cons] at hnod hmem
    rw [List.nodup_cons] at hnod
    obtain ⟨hhd_notin, htl_nodup⟩ := hnod
    simp only [findEntry] at hfind
    by_cases heq : hd.id = i
    · subst heq
      rw [if_pos rfl] at hfind
      cases hfind
      simp only [sumOver_cons]
      have hterm1 : (if hd.id ∈ (hd.id :: l) then (0:Int) else netOf hd.lines a) = 0 := by
        simp
      have hterm2 : (if hd.id ∈ l then (0:Int) else netOf hd.lines a) = netOf hd.lines a := by
        simp [hnotl]
      rw [hterm1, hterm2]
      have hcongr : sumOver tl (fun e' => if e'.id ∈ (hd.id :: l) then (0:Int) else netOf e'.lines a) =
        sumOver tl (fun e' => if e'.id ∈ l then (0:Int) else netOf e'.lines a) := by
        apply sumOver_congr
        intro e' he'
        have hne : e'.id ≠ hd.id := by
          intro hcon
          apply hhd_notin
          simp [ids]
          exact ⟨e', he', hcon⟩
        simp [hne]
      rw [hcongr]
      omega
    · rw [if_neg heq] at hfind
      simp only [List.mem_cons] at hmem
      have hmem_tl : i ∈ ids tl := by
        cases hmem with
        | inl h => simp [h] at heq
        | inr h => exact h
      have ih_eq := ih l i e a htl_nodup hnotl hmem_tl hfind
      simp only [sumOver_cons]
      have hcongr_hd : (if hd.id ∈ (i :: l) then (0:Int) else netOf hd.lines a) =
        (if hd.id ∈ l then (0:Int) else netOf hd.lines a) := by
        simp [heq]
      rw [hcongr_hd, ih_eq]
      omega

theorem aux_active_post_full : ∀ (s : State) (e : Entry) (a : AccountId),
  e.id ∉ s.reversed →
  activeNet ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) a =
  activeNet s a + netOf e.lines a := by
  intro s e a h
  have h0 := cons_active_post s e a h
  unfold activeNet at h0 ⊢
  simp only at h0 ⊢
  exact h0

theorem aux_active_rev_full : ∀ (s : State) (i : EntryId) (e : Entry) (a : AccountId),
  (ids s.journal).Nodup → i ∉ s.reversed → i ∈ ids s.journal → findEntry s.journal i = some e →
  activeNet ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) a =
  activeNet s a - netOf e.lines a := by
  intro s i e a hnod hnotl hmem hfind
  unfold activeNet
  simp only
  exact aux_active_rev_eq s.journal s.reversed i e a hnod hnotl hmem hfind

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  obtain ⟨hne, hacc, hnz, hbal, hfreshJ, hfreshR⟩ := h
  rw [tmp_plain]
  obtain ⟨hA, hC, hD, hE, hF⟩ := probe_post_parts s e hacc hbal hfreshJ hfreshR hne
  have hB : (e.lines.all (fun l => l.2 != 0) = true) := probe_all_nz e hnz
  rw [hA, hB, hC, hD, hE, hF, probe_true_and]
  simp

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  obtain ⟨hinJ, hnotR⟩ := h
  obtain ⟨e, he⟩ := helper_findEntry_of_mem2 s.journal i hinJ
  unfold step
  simp [hinJ, hnotR, he]

theorem req_invalid_noop     : InvalidNoop step := by
  intro s c hInvalid
  cases c with
  | post e =>
    simp only [Valid] at hInvalid
    rw [tmp_plain]
    by_cases hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)
    · exfalso
      apply hInvalid
      exact ⟨helper_post_nonempty_of_ok s e hc, wf_post_accounts_of_ok s e hc, helper_post_nz_of_ok s e hc, wf_post_bal_of_ok s e hc, wf_post_freshJ_of_ok s e hc, helper_post_freshR_of_ok s e hc⟩
    · rw [if_neg hc]
  | reverse i =>
    simp only [Valid] at hInvalid
    have hplain := tmp_rev_plain2 s i
    rw [hplain]
    by_cases hc : (((ids s.journal).contains i && !(s.reversed.contains i)) = true)
    · exfalso
      apply hInvalid
      exact ⟨wf_rev_mem_of_ok s i hc, helper_rev_notR_of_ok s i hc⟩
    · rw [if_neg hc]

theorem req_post_effects : PostEffects step := by
  intro s e h
  rw [tmp_plain] at h ⊢
  by_cases hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)
  · rw [if_pos hc]
    exact ⟨rfl, rfl, rfl, rfl, fun a => rfl⟩
  · have h2 : ¬ ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true) := hc
    rw [if_neg h2] at h
    simp at h

theorem req_reverse_effects  : ReverseEffects step := req_reverse_effects2

theorem req_reverse_once : ReverseOnce step := by
  intro s i hOk
  have hplain : step s (.reverse i) = if ((ids s.journal).contains i && !(s.reversed.contains i)) then
      (match findEntry s.journal i with
      | some e => (Outcome.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a })
      | none => (Outcome.rejected, s))
    else
      (Outcome.rejected, s) := rfl
  by_cases hc : (((ids s.journal).contains i && !(s.reversed.contains i)) = true)
  · rw [if_pos hc] at hplain
    cases hF : findEntry s.journal i with
    | none =>
      rw [hF] at hplain
      have h1 : (step s (.reverse i)).1 = Outcome.rejected := by rw [hplain]
      rw [h1] at hOk
      simp at hOk
    | some e =>
      rw [hF] at hplain
      have h2eq : (step s (.reverse i)).2 = ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) := by rw [hplain]
      have hmain : step ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) (.reverse i) =
          (Outcome.rejected, ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State)) := by
        have hstep2 : step ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) (.reverse i) =
          if (((ids s.journal).contains i && !((i :: s.reversed).contains i))) then
            (match findEntry s.journal i with
            | some e2 => (Outcome.ok, { ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) with reversed := i :: (i :: s.reversed), balance := fun a => ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State).balance a - netOf e2.lines a })
            | none => (Outcome.rejected, ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State)))
          else
            (Outcome.rejected, ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State)) := rfl
        have hneg : (!((i :: s.reversed).contains i)) = false := by simp
        have hcond : ¬ ((((ids s.journal).contains i && !((i :: s.reversed).contains i))) = true) := by
          intro ht
          have h2 : (!((i :: s.reversed).contains i)) = true := (Bool.and_eq_true_iff.mp ht).2
          rw [hneg] at h2
          simp at h2
        rw [if_neg hcond] at hstep2
        exact hstep2
      rw [h2eq]
      exact hmain
  · rw [if_neg hc] at hplain
    have h1 : (step s (.reverse i)).1 = Outcome.rejected := by rw [hplain]
    rw [h1] at hOk
    simp at hOk

theorem req_roundtrip : RoundTrip step := by
  intro s e hOk
  have hcond : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true) := by
    by_cases hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)
    · exact hc
    · rw [tmp_plain, if_neg hc] at hOk
      simp at hOk
  have hfreshJ : e.id ∉ ids s.journal := wf_post_freshJ_of_ok s e hcond
  have hfreshR : e.id ∉ s.reversed := helper_post_freshR_of_ok s e hcond
  have hstep2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
    rw [tmp_plain, if_pos hcond]
  have hjour2 : (step s (.post e)).2.journal = s.journal ++ [e] := by rw [hstep2]
  have hrev2 : (step s (.post e)).2.reversed = s.reversed := by rw [hstep2]
  have hbal2 : ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a := by
    intro a; rw [hstep2]
  have hfind2 : findEntry (step s (.post e)).2.journal e.id = some e := by
    rw [hjour2]
    exact myRT_post_find s e hfreshJ
  have hmemJ2 : e.id ∈ ids (step s (.post e)).2.journal := by
    rw [hjour2]
    simp [ids]
  have hnotR2 : e.id ∉ (step s (.post e)).2.reversed := by
    rw [hrev2]; exact hfreshR
  have hValid2 : ValidReverse (step s (.post e)).2 e.id := ⟨hmemJ2, hnotR2⟩
  have hOk2 : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok :=
    req_reverse_succeeds _ _ hValid2
  refine ⟨hOk2, ?_⟩
  have hRevEff := req_reverse_effects2 (step s (.post e)).2 e.id e hOk2 hfind2
  obtain ⟨_, _, _, _, hbal3⟩ := hRevEff
  funext a
  rw [hbal3 a, hbal2 a]
  omega

theorem req_trial_balance : TrialBalance step := by
  intro s c hw hOk
  cases c with
  | post e =>
    have hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true) := by
      by_cases h : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)
      · exact h
      · rw [tmp_plain, if_neg h] at hOk
        simp at hOk
    have hEff := req_post_effects_proof2 s e hOk
    obtain ⟨hAcc, _, _, _, hBal⟩ := hEff
    rw [trial_total_post_aux2 s e hAcc hBal]
    have hbal0 : lineSum e.lines = 0 := wf_post_bal_of_ok s e hc
    have hsum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
      trial_sum_net_aux s.accounts e.lines hw.1 (wf_post_accounts_of_ok s e hc)
    rw [hsum, hbal0]
    omega
  | reverse i =>
    have hplain := tmp_rev_plain2 s i
    have hc : (((ids s.journal).contains i && !(s.reversed.contains i)) = true) := by
      by_cases h : ((((ids s.journal).contains i && !(s.reversed.contains i))) = true)
      · exact h
      · rw [hplain, if_neg h] at hOk
        simp at hOk
    have hmemJ : i ∈ ids s.journal := wf_rev_mem_of_ok s i hc
    obtain ⟨e, hFind⟩ := helper_findEntry_of_mem2 s.journal i hmemJ
    have hpos : (if ((ids s.journal).contains i && !(s.reversed.contains i)) then (match findEntry s.journal i with | some e2 => (Outcome.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e2.lines a }) | none => (Outcome.rejected, s)) else (Outcome.rejected, s)) = (match findEntry s.journal i with | some e2 => (Outcome.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e2.lines a }) | none => (Outcome.rejected, s)) := by
      rw [if_pos hc]
    have hOk2 : (step s (.reverse i)).1 = .ok := by rw [hplain, hpos, hFind]
    have hEff := req_reverse_effects2 s i e hOk2 hFind
    obtain ⟨hAcc, _, _, _, hBal⟩ := hEff
    rw [trial_total_rev_aux2 s i e hAcc hBal]
    have hem : e ∈ s.journal := cons_find_mem2 s.journal i e hFind
    have hwE := hw.2.2.2 e hem
    obtain ⟨haccE, hbalE⟩ := hwE
    have hsum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
      trial_sum_net_aux s.accounts e.lines hw.1 haccE
    rw [hsum, hbalE]
    omega

theorem req_well_formed : StaysWellFormed step := by
  intro s c hw
  cases c with
  | post e =>
    by_cases hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)
    · have hEq2 : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        rw [tmp_plain, if_pos hc]
      rw [hEq2]
      refine ⟨hw.1, wf_need1c s e hw hc, ?_, wf_need3c s e hw hc⟩
      exact wf_post_rev_subset_aux s e hw
    · have hEq2 : (step s (.post e)).2 = s := by
        rw [tmp_plain, if_neg hc]
      rw [hEq2]
      exact hw
  | reverse i =>
    have hplain := tmp_rev_plain2 s i
    by_cases hc : ((((ids s.journal).contains i && !(s.reversed.contains i))) = true)
    · have hmemJ : i ∈ ids s.journal := wf_rev_mem_of_ok s i hc
      obtain ⟨e, hFind⟩ := helper_findEntry_of_mem2 s.journal i hmemJ
      have hEq2 : (step s (.reverse i)).2 = ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) := by
        rw [hplain, if_pos hc, hFind]
      rw [hEq2]
      refine ⟨hw.1, hw.2.1, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        cases hx with
        | inl heq => subst heq; exact hmemJ
        | inr hmem => exact hw.2.2.1 x hmem
      · intro e' he'
        exact hw.2.2.2 e' he'
    · have hEq2 : (step s (.reverse i)).2 = s := by
        rw [hplain, if_neg hc]
      rw [hEq2]
      exact hw

theorem req_consistent : StaysConsistent step := by
  intro s c hw hcon
  cases c with
  | post e =>
    unfold Consistent at hcon ⊢
    by_cases hc : ((e.lines.all (fun l => s.accounts.contains l.1) && e.lines.all (fun l => l.2 != 0) && (lineSum e.lines == 0) && !((ids s.journal).contains e.id) && !(s.reversed.contains e.id) && !e.lines.isEmpty) = true)
    · have hEq : (step s (.post e)).2 = ({ s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } : State) := by
        rw [tmp_plain, if_pos hc]
      intro a
      rw [hEq]
      simp only
      have hact := aux_active_post_full s e a (helper_post_freshR_of_ok s e hc)
      rw [hact, hcon a]
      omega
    · have hEq : (step s (.post e)).2 = s := by
        rw [tmp_plain, if_neg hc]
      rw [hEq]
      exact hcon
  | reverse i =>
    unfold Consistent at hcon ⊢
    have hplain := tmp_rev_plain2 s i
    by_cases hc : ((((ids s.journal).contains i && !(s.reversed.contains i))) = true)
    · have hmemJ : i ∈ ids s.journal := wf_rev_mem_of_ok s i hc
      have hnotR : i ∉ s.reversed := helper_rev_notR_of_ok s i hc
      obtain ⟨e, hFind⟩ := helper_findEntry_of_mem2 s.journal i hmemJ
      have hEq : (step s (.reverse i)).2 = ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) := by
        rw [hplain, if_pos hc, hFind]
      intro a
      rw [hEq]
      simp only
      have hact := aux_active_rev_full s i e a hw.2.1 hnotR hmemJ hFind
      rw [hact, hcon a]
      omega
    · have hEq : (step s (.reverse i)).2 = s := by
        rw [hplain, if_neg hc]
      rw [hEq]
      exact hcon

end Reversal
