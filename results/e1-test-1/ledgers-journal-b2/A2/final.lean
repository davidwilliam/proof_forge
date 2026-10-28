import Journal.Spec
import Journal.Lemmas
namespace Journal
def acceptable (s : State) (e : Entry) : Bool :=
  decide s.accounts.Nodup && !e.lines.isEmpty && e.lines.all (fun l => s.accounts.contains l.1) &&
  e.lines.all (fun l => l.2 != 0) && decide (lineSum e.lines = 0) && !s.posted.contains e.id
def step : Impl := fun s e =>
  if acceptable s e then
    (.ok, { accounts := s.accounts,
            balance := fun a => s.balance a + netOf e.lines a,
            posted := e.id :: s.posted })
  else (.rejected, s)

theorem my_all_true (l : List Line) (p : Line → Bool) (h : ∀ x ∈ l, p x = true) : l.all p = true := by
  induction l with
  | nil => simp [List.all]
  | cons a l ih =>
    simp [List.all, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem req_effects_aux2 : Effects step := by
  intro s e hok
  cases hacc : acceptable s e with
  | true =>
    have hA : (step s e).2.accounts = s.accounts := by simp [step, hacc]
    have hB : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := by
      intro a; simp [step, hacc]
    exact ⟨hA, hB⟩
  | false =>
    unfold step at hok
    simp [hacc] at hok

theorem tmp_idem_helper (s : State) (e : Entry) :
    ((e.id :: s.posted).contains e.id) = true := by
  have heq : ((e.id :: s.posted).contains e.id) = decide (e.id ∈ (e.id :: s.posted)) :=
    List.contains_eq_mem _ _
  rw [heq]
  simp

theorem tmp_state_eq (s : State) (e : Entry) (hacc : acceptable s e = true) :
    (step s e).2.posted = e.id :: s.posted := by
  simp [step, hacc]

theorem tmp_state_mk (s : State) (e : Entry) (hacc : acceptable s e = true) :
    (step s e).2 = State.mk s.accounts (fun a => s.balance a + netOf e.lines a) (e.id :: s.posted) := by
  simp [step, hacc]

theorem tb_zero_aux (l : List AccountId) : sumOver l (fun _ : AccountId => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [sumOver_cons] at *; simp [ih]

theorem tb_flip_aux (accs : List AccountId) (x : AccountId) (c : Int) :
    (∀ a ∈ accs, (if x = a then c else (0 : Int)) = (if a = x then c else 0)) := by
  intro a _
  by_cases h : x = a
  · rw [if_pos h, if_pos h.symm]
  · have h2 : ¬ (a = x) := fun hh => h hh.symm
    rw [if_neg h, if_neg h2]

theorem tb_single_aux (accs : List AccountId) (hnd : accs.Nodup) (x : AccountId) (c : Int) :
    sumOver accs (fun a => if x = a then c else (0 : Int)) = if x ∈ accs then c else 0 := by
  have hcon : sumOver accs (fun a => if x = a then c else (0 : Int)) =
      sumOver accs (fun a => if a = x then c else (0 : Int)) :=
    sumOver_congr accs _ _ (tb_flip_aux accs x c)
  rw [hcon]
  exact sumOver_ite_eq hnd x c

theorem tb_swap_aux (accs : List AccountId) (hnd : accs.Nodup) (ls : List Line) :
    sumOver accs (fun a => netOf ls a) =
    sumOver ls (fun l => if l.1 ∈ accs then l.2 else 0) := by
  induction ls with
  | nil =>
    have h1 : (fun a : AccountId => netOf ([] : List Line) a) =
        (fun _ : AccountId => (0 : Int)) := by
      funext a; simp [netOf]
    rw [h1, tb_zero_aux]
    simp
  | cons hd tl ih =>
    have hnet : ∀ a : AccountId, netOf (hd :: tl) a =
        (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      intro a; simp [netOf]
    have hfun : (fun a : AccountId => netOf (hd :: tl) a) =
        (fun a => (if hd.1 = a then hd.2 else (0 : Int)) + netOf tl a) := by
      funext a; exact hnet a
    rw [hfun, sumOver_add, tb_single_aux accs hnd hd.1 hd.2, ih]
    simp [sumOver_cons]

theorem tb_all_mem_aux (ls : List Line) (accs : List AccountId)
    (h : ls.all (fun l => accs.contains l.1) = true) :
    ∀ l ∈ ls, (if l.1 ∈ accs then l.2 else (0 : Int)) = l.2 := by
  intro l hl
  have hall : ∀ x ∈ ls, (accs.contains x.1) = true := (List.all_eq_true).mp h
  have hm : accs.contains l.1 = true := hall l hl
  have heq : accs.contains l.1 = decide (l.1 ∈ accs) := List.contains_eq_mem _ _
  rw [heq] at hm
  have hm2 : l.1 ∈ accs := of_decide_eq_true hm
  simp [hm2]

theorem ne_bne_test (a : Int) (h : a ≠ 0) : (a != 0) = true := by
  simp [h]

theorem decide_test1 (p : Prop) [Decidable p] (h : p) : decide p = true := decide_eq_true h

theorem decide_test2 (p : Prop) [Decidable p] (h : ¬ p) : decide p = false := decide_eq_false h

theorem decide_test3 (p : Prop) [Decidable p] (h : decide p = true) : p := of_decide_eq_true h



theorem plan0_all_contains_of_forall_mem {accounts : List AccountId} {ls : List Line} (h : ∀ l ∈ ls, l.1 ∈ accounts) : ls.all (fun l => accounts.contains l.1) = true := by
  apply my_all_true
  intro x hx
  have hm := h x hx
  have heq : accounts.contains x.1 = decide (x.1 ∈ accounts) := List.contains_eq_mem _ _
  rw [heq, decide_eq_true hm]








theorem plan0_fst_step_ok_of_acceptable {s : State} {e : Entry} (h : acceptable s e = true) : (step s e).1 = Outcome.ok := by simp [step, h]


theorem plan0_isEmpty_false_of_ne_nil {ls : List Line} (h : ls ≠ []) : (!ls.isEmpty) = true := by
  cases ls with
  | nil => contradiction
  | cons hd tl => rfl

theorem plan0_contains_test {accounts : List AccountId} {ls : List Line} (h : ∀ l ∈ ls, l.1 ∈ accounts) : ls.all (fun l => accounts.contains l.1) = true := by
  apply my_all_true
  intro x hx
  have hm := h x hx
  have heq : accounts.contains x.1 = decide (x.1 ∈ accounts) := List.contains_eq_mem _ _
  rw [heq, decide_eq_true hm]

theorem plan0_all_bne_of_forall_ne_test {ls : List Line} (h : ∀ l ∈ ls, l.2 ≠ 0) : ls.all (fun l => l.2 != 0) = true := by
  apply my_all_true
  intro x hx
  exact ne_bne_test _ (h x hx)

theorem plan0_all_bne_of_forall_ne {ls : List Line} (h : ∀ l ∈ ls, l.2 ≠ 0) : ls.all (fun l => l.2 != 0) = true := by
  apply my_all_true
  intro x hx
  exact ne_bne_test _ (h x hx)

theorem plan0_not_contains_of_not_mem {posted : List EntryId} {id : EntryId} (h : id ∉ posted) : (!posted.contains id) = true := by
  have heq : posted.contains id = decide (id ∈ posted) := List.contains_eq_mem _ _
  rw [heq, decide_eq_false h, Bool.not_false]

theorem plan0_acceptable_true_of_valid {s : State} {e : Entry} (h : ValidEntry s e) : acceptable s e = true := by
  obtain ⟨hnd, hne, hmem, hnz, hsum, hfresh⟩ := h
  unfold acceptable
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact decide_eq_true hnd
  · exact plan0_isEmpty_false_of_ne_nil hne
  · exact plan0_contains_test hmem
  · exact plan0_all_bne_of_forall_ne hnz
  · exact decide_eq_true hsum
  · exact plan0_not_contains_of_not_mem hfresh

theorem inv_ne_nil_test {ls : List Line} (h : (!ls.isEmpty) = true) : ls ≠ [] := by
  cases ls with
  | nil => simp at h
  | cons hd tl => simp

theorem inv_notcontains_notmem_test3 {posted : List EntryId} {id : EntryId} (h : (!posted.contains id) = true) : id ∉ posted := by
  have heq : posted.contains id = decide (id ∈ posted) := List.contains_eq_mem _ _
  rw [heq] at h
  cases hd : decide (id ∈ posted) with
  | true => simp [hd] at h
  | false => exact of_decide_eq_false hd

theorem plan1_acceptable_valid4 {s : State} {e : Entry} (h : acceptable s e = true) : ValidEntry s e := by
  unfold acceptable at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hne : e.lines ≠ [] := by
    intro hnil
    rw [hnil] at h2
    simp at h2
  refine ⟨of_decide_eq_true h1, hne, ?_, ?_, of_decide_eq_true h5, ?_⟩
  · intro l hl
    have hall := (List.all_eq_true).mp h3 l hl
    have heq : s.accounts.contains l.1 = decide (l.1 ∈ s.accounts) := List.contains_eq_mem _ _
    rw [heq] at hall
    exact of_decide_eq_true hall
  · intro l hl
    have hall := (List.all_eq_true).mp h4 l hl
    intro hzero
    rw [hzero] at hall
    simp at hall
  · have heq : s.posted.contains e.id = decide (e.id ∈ s.posted) := List.contains_eq_mem _ _
    rw [heq] at h6
    cases hd : decide (e.id ∈ s.posted) with
    | true => simp [hd] at h6
    | false => exact of_decide_eq_false hd

theorem idem_helper_final_xyz (s : State) (e : Entry) (hacc : acceptable s e = true) :
    step (step s e).2 e = (.rejected, (step s e).2) := by
  have hs2_eq : (step s e).2 = State.mk s.accounts (fun a => s.balance a + netOf e.lines a) (e.id :: s.posted) := by
    simp [step, hacc]
  rw [hs2_eq]
  have hcontains : ((e.id :: s.posted).contains e.id) = true := by simp
  have hacc2 : acceptable (State.mk s.accounts (fun a => s.balance a + netOf e.lines a) (e.id :: s.posted)) e = false := by
    unfold acceptable
    rw [hcontains]
    simp
  simp [step, hacc2]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h
  have hacc : acceptable s e = true := plan0_acceptable_true_of_valid h
  exact plan0_fst_step_ok_of_acceptable hacc

theorem req_invalid_noop : InvalidNoop step := by
  intro s e hn
  have hacc : acceptable s e = false := by
    cases h : acceptable s e with
    | true => exact absurd (plan1_acceptable_valid4 h) hn
    | false => rfl
  simp [step, hacc]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  cases hacc : acceptable s e with
  | true =>
    unfold acceptable at hacc
    simp only [Bool.and_eq_true] at hacc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hacc
    have hall : ∀ x : Line, x ∈ e.lines → (s.accounts.contains x.1) = true := by
      have := (List.all_eq_true).mp h3
      exact this
    have hmem : s.accounts.contains l.1 = true := hall l hl
    have heq : s.accounts.contains l.1 = decide (l.1 ∈ s.accounts) :=
      List.contains_eq_mem l.1 s.accounts
    rw [heq] at hmem
    exact of_decide_eq_true hmem
  | false =>
    unfold step at hok
    simp [hacc] at hok

theorem req_balanced : Balanced step := by
  intro s e hok
  cases hacc : acceptable s e with
  | true =>
    unfold acceptable at hacc
    simp only [Bool.and_eq_true] at hacc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hacc
    exact of_decide_eq_true h5
  | false =>
    unfold step at hok
    simp [hacc] at hok

theorem req_effects : Effects step := by
  intro s e hok
  cases hacc : acceptable s e with
  | true =>
    have hA : (step s e).2.accounts = s.accounts := by simp [step, hacc]
    have hB : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := by
      intro a; simp [step, hacc]
    exact ⟨hA, hB⟩
  | false =>
    unfold step at hok
    simp [hacc] at hok

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hacc : acceptable s e = true := by
    cases h : acceptable s e with
    | true => rfl
    | false =>
      unfold step at hok
      simp [h] at hok
  have hs2_posted : (step s e).2.posted = e.id :: s.posted := by
    simp [step, hacc]
  have hmem : ∀ x, x ∈ (step s e).2.posted ↔ x = e.id ∨ x ∈ s.posted := by
    rw [hs2_posted]
    intro x
    simp
  exact ⟨hmem, idem_helper_final_xyz s e hacc⟩

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  cases hacc0 : acceptable s e with
  | false =>
    simp [step, hacc0] at hok
  | true =>
    have hacc := hacc0
    unfold acceptable at hacc
    simp only [Bool.and_eq_true] at hacc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hacc
    have hnd : s.accounts.Nodup := of_decide_eq_true h1
    have hsum : lineSum e.lines = 0 := of_decide_eq_true h5
    have hacts : (step s e).2.accounts = s.accounts := by simp [step, hacc0]
    have hbal : ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a := by
      intro a
      simp [step, hacc0]
    have htotal : total (step s e).2 = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
      unfold total
      rw [hacts]
      apply sumOver_congr
      intro a _
      exact hbal a
    rw [htotal, sumOver_add]
    have hswap := tb_swap_aux s.accounts hnd e.lines
    have hcon : sumOver e.lines (fun l => if l.1 ∈ s.accounts then l.2 else (0 : Int)) =
        sumOver e.lines (fun l : Line => l.2) :=
      sumOver_congr _ _ _ (fun l hl => tb_all_mem_aux e.lines s.accounts h3 l hl)
    have hz : sumOver s.accounts (fun a => netOf e.lines a) = 0 := by
      rw [hswap, hcon]
      exact hsum
    unfold total
    rw [hz]
    simp

end Journal
