import Journal.Spec
import Journal.Lemmas

namespace Journal

def nodupb : List AccountId → Bool
  | [] => true
  | a :: l => if a ∈ l then false else nodupb l

def allKnown : List AccountId → List Line → Bool
  | _, [] => true
  | accts, hd :: tl => if hd.1 ∈ accts then allKnown accts tl else false

def allNonZero : List Line → Bool
  | [] => true
  | hd :: tl => if hd.2 = 0 then false else allNonZero tl

def validb (s : State) (e : Entry) : Bool :=
  nodupb s.accounts && (!e.lines.isEmpty) && allKnown s.accounts e.lines && allNonZero e.lines && decide (lineSum e.lines = 0) && decide (e.id ∉ s.posted)

def step : Impl := fun s e =>
  match validb s e with
  | true => (Outcome.ok, { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted })
  | false => (Outcome.rejected, s)

theorem nodupb_true_iff (l : List AccountId) : nodupb l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupb]
  | cons a l ih =>
    have hred : nodupb (a :: l) = (if a ∈ l then false else nodupb l) := by simp [nodupb]
    rw [hred]
    by_cases hmem : a ∈ l
    · simp [hmem, List.nodup_cons]
    · simp [hmem, ih, List.nodup_cons]

theorem allKnown_true_iff' (accts : List AccountId) (ls : List Line) : allKnown accts ls = true ↔ ∀ l ∈ ls, l.1 ∈ accts := by
  induction ls with
  | nil => simp [allKnown]
  | cons hd tl ih =>
    simp only [allKnown]
    by_cases h : hd.1 ∈ accts <;> simp [h, ih]

theorem allNonZero_true_iff' (ls : List Line) : allNonZero ls = true ↔ ∀ l ∈ ls, l.2 ≠ 0 := by
  induction ls with
  | nil => simp [allNonZero]
  | cons hd tl ih =>
    simp only [allNonZero]
    by_cases h : hd.2 = 0 <;> simp [h, ih]

theorem isEmpty_eq_true_iff (ls : List Line) : ((!ls.isEmpty) = true) ↔ ls ≠ [] := by
  cases ls with
  | nil => simp
  | cons hd tl => simp

theorem validb_true_iff'' (s : State) (e : Entry) : validb s e = true ↔ ValidEntry s e := by
  unfold validb ValidEntry
  simp only [Bool.and_eq_true, nodupb_true_iff, allKnown_true_iff', allNonZero_true_iff', decide_eq_true_eq, isEmpty_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

theorem tmp_idem : Idempotent step := by
  intro s e hok
  have hb : validb s e = true := by
    cases hv : validb s e with
    | true => rfl
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by simp [step, hv]
      rw [hstep] at hok
      exact absurd hok (by decide)
  have hstep2 : (step s e).2 = { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } := by simp [step, hb]
  have hvalid_false : validb (step s e).2 e = false := by
    rw [hstep2]
    unfold validb
    have hmem : e.id ∈ e.id :: s.posted := List.mem_cons.mpr (Or.inl rfl)
    simp [hmem]
  constructor
  · intro x
    rw [hstep2]
    simp
  · generalize (step s e).2 = s' at hvalid_false ⊢
    simp [step, hvalid_false]

theorem req_idempotency_aux2 : Idempotent step := by
  intro s e hok
  have hb : validb s e = true := by
    cases hv : validb s e with
    | true => rfl
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by simp [step, hv]
      rw [hstep] at hok
      exact absurd hok (by decide)
  have hstep2 : (step s e).2 = { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } := by simp [step, hb]
  have hvalid_false : validb (step s e).2 e = false := by
    rw [hstep2]
    unfold validb
    have hmem : e.id ∈ e.id :: s.posted := List.mem_cons.mpr (Or.inl rfl)
    simp [hmem]
  constructor
  · intro x
    rw [hstep2]
    simp
  · generalize (step s e).2 = s' at hvalid_false ⊢
    simp [step, hvalid_false]

theorem sumOver_zero_tb2 (l : List AccountId) : sumOver l (fun _ => (0 : Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => exact show (0 : Int) + sumOver t _ = 0 from by rw [ih]; rfl

theorem sum_ite_swap_tb2 (accts : List AccountId) (x : AccountId) (c : Int) :
    sumOver accts (fun a => if x = a then c else (0 : Int)) =
    sumOver accts (fun a => if a = x then c else 0) := by
  apply sumOver_congr
  intro a _
  by_cases h : x = a
  · subst h; rfl
  · have h2 : ¬ (a = x) := fun hh => h hh.symm
    simp only [h, h2]

theorem sum_ite_mem_tb2 (accts : List AccountId) (hNodup : accts.Nodup) (x : AccountId) (c : Int) :
    sumOver accts (fun a => if x = a then c else (0 : Int)) =
    (if x ∈ accts then c else 0) := by
  rw [sum_ite_swap_tb2]
  exact sumOver_ite_eq hNodup x c

theorem sumNet_eq_tb3 (accts : List AccountId) (hNodup : accts.Nodup) (ls : List Line) :
    sumOver accts (fun a => netOf ls a) = sumOver ls (fun l => if l.1 ∈ accts then l.2 else 0) := by
  induction ls with
  | nil =>
    have h0 : (fun a => netOf ([] : List Line) a) = (fun _ => (0 : Int)) := by
      funext a; rfl
    rw [h0, sumOver_zero_tb2]
    rfl
  | cons hd tl ih =>
    have h1 : (fun a => netOf (hd :: tl) a) = (fun a => (if hd.1 = a then hd.2 else 0) + netOf tl a) := by
      funext a; rfl
    rw [h1, sumOver_add, ih, sum_ite_mem_tb2 accts hNodup hd.1 hd.2]
    rfl

theorem sumNet_eq_lineSum_tb3 (accts : List AccountId) (hNodup : accts.Nodup) (ls : List Line)
    (hknown : ∀ l ∈ ls, l.1 ∈ accts) :
    sumOver accts (fun a => netOf ls a) = lineSum ls := by
  rw [sumNet_eq_tb3 accts hNodup ls]
  unfold lineSum
  apply sumOver_congr
  intro l hl
  rw [if_pos (hknown l hl)]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s e h
  have hb : validb s e = true := (validb_true_iff'' s e).mpr h
  simp [step, hb]

theorem req_invalid_noop : InvalidNoop step := by
  intro s e h
  have hb : validb s e = false := by
    cases hv : validb s e with
    | true => rw [validb_true_iff''] at hv; exact absurd hv h
    | false => rfl
  show ((fun s e => match validb s e with | true => ((Outcome.ok : Outcome), ({ accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } : State)) | false => ((Outcome.rejected : Outcome), s)) s e) = _
  simp only [hb]

theorem req_known_accounts : KnownAccounts step := by
  intro s e hok l hl
  have hb : validb s e = true := by
    cases hv : validb s e with
    | true => rfl
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by simp [step, hv]
      rw [hstep] at hok
      exact absurd hok (by decide)
  rw [validb_true_iff'' ] at hb
  exact hb.2.2.1 l hl

theorem req_balanced : Balanced step := by
  intro s e hok
  have hb : validb s e = true := by
    cases hv : validb s e with
    | true => rfl
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by simp [step, hv]
      rw [hstep] at hok
      exact absurd hok (by decide)
  rw [validb_true_iff''] at hb
  exact hb.2.2.2.2.1

theorem req_effects        : Effects step := by
  intro s e hok
  have hb : validb s e = true := by
    cases hv : validb s e with
    | true => rfl
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by simp [step, hv]
      rw [hstep] at hok
      exact absurd hok (by decide)
  constructor
  · show (step s e).2.accounts = s.accounts
    simp [step, hb]
  · intro a
    show (step s e).2.balance a = s.balance a + netOf e.lines a
    simp [step, hb]

theorem req_idempotency : Idempotent step := by
  intro s e hok
  have hb : validb s e = true := by
    cases hv : validb s e with
    | true => rfl
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by simp [step, hv]
      rw [hstep] at hok
      exact absurd hok (by decide)
  have hstep2 : (step s e).2 = { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } := by simp [step, hb]
  have hvalid_false : validb (step s e).2 e = false := by
    rw [hstep2]
    unfold validb
    have hmem : e.id ∈ e.id :: s.posted := List.mem_cons.mpr (Or.inl rfl)
    simp [hmem]
  constructor
  · intro x
    rw [hstep2]
    simp
  · generalize (step s e).2 = s' at hvalid_false ⊢
    simp [step, hvalid_false]

theorem req_trial_balance : TrialBalance step := by
  intro s e hok
  have hb : validb s e = true := by
    cases hv : validb s e with
    | true => rfl
    | false =>
      have hstep : (step s e).1 = Outcome.rejected := by simp [step, hv]
      rw [hstep] at hok
      exact absurd hok (by decide)
  have hbV : ValidEntry s e := (validb_true_iff'' s e).mp hb
  obtain ⟨hNodup, _, hknown, _, hsum, _⟩ := hbV
  have h2 : (step s e).2 = { accounts := s.accounts, balance := fun a => s.balance a + netOf e.lines a, posted := e.id :: s.posted } := by
    simp [step, hb]
  have hsumNet : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines :=
    sumNet_eq_lineSum_tb3 s.accounts hNodup e.lines hknown
  have htot : total (step s e).2 = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
    rw [h2]; rfl
  rw [htot, sumOver_add, hsumNet, hsum]
  simp [total]

end Journal
