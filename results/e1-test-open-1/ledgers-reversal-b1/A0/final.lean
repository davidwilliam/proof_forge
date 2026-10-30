import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

theorem findEntry_some_mem (j : List Entry) (i : EntryId) (e : Entry) :
    findEntry j i = some e → e ∈ j ∧ e.id = i := by
  induction j with
  | nil => intro h; simp [findEntry] at h
  | cons hd tl ih =>
    intro h
    simp only [findEntry] at h
    split at h
    · next heq =>
      have h2 : some hd = some e := h
      have heq2 : hd = e := Option.some_inj.mp h2
      subst heq2
      exact ⟨List.Mem.head _, heq⟩
    · next _ => exact ⟨List.Mem.tail _ (ih h).1, (ih h).2⟩

theorem findEntry_none_iff_notMem (j : List Entry) (i : EntryId) :
    findEntry j i = none ↔ i ∉ ids j := by
  induction j with
  | nil => simp [findEntry, ids]
  | cons hd tl ih =>
    by_cases h : hd.id = i
    · simp [findEntry, ids, h]
    · have h1 : findEntry (hd :: tl) i = findEntry tl i := by simp [findEntry, h]
      have h2 : i ∈ ids (hd :: tl) ↔ i = hd.id ∨ i ∈ ids tl := by simp [ids]
      have h3 : ¬ (i = hd.id) := fun hc => h hc.symm
      rw [h1, h2]
      simp [h3, ih]

theorem ids_append_single (j : List Entry) (e : Entry) :
    ids (j ++ [e]) = ids j ++ [e.id] := by unfold ids; simp

theorem nodup_append_singleton {α} {l : List α} {x : α} (hn : l.Nodup) (hmem : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have htl : tl.Nodup := (List.nodup_cons.mp hn).2
    have h1 : hd ∉ tl := (List.nodup_cons.mp hn).1
    have hx_tl : x ∉ tl := fun h => hmem (List.Mem.tail _ h)
    have hx_hd : x ≠ hd := fun h => hmem (h ▸ List.Mem.head _)
    have ih' := ih htl hx_tl
    rw [List.nodup_cons]
    refine ⟨?_, ih'⟩
    intro hmem2
    rw [List.mem_append] at hmem2
    rcases hmem2 with h2 | h2
    · exact h1 h2
    · simp at h2; exact hx_hd h2.symm

theorem nodup_ids_append (j : List Entry) (e : Entry) (hn : (ids j).Nodup) (hni : e.id ∉ ids j) :
    (ids (j ++ [e])).Nodup := by
  rw [ids_append_single]; exact nodup_append_singleton hn hni

theorem findEntry_append_of_notMem (j : List Entry) (e : Entry) (hni : e.id ∉ ids j) :
    findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have hne : hd.id ≠ e.id := by intro heq; apply hni; unfold ids; simp [heq]
    simp only [findEntry, hne, ite_false]
    apply ih
    intro hm; apply hni; unfold ids; simp [hm]

theorem sumOver_zero' {α} (l : List α) : sumOver l (fun _ => (0:Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver_cons, ih, Int.zero_add]

theorem sumOver_swap (accts : List AccountId) (ls : List Line) :
    sumOver accts (fun a => sumOver ls (fun l => if l.1 = a then l.2 else 0))
    = sumOver ls (fun l => sumOver accts (fun a => if l.1 = a then l.2 else 0)) := by
  induction ls with
  | nil => simp only [sumOver_nil, sumOver_zero']
  | cons h2 t2 ih2 =>
    have lhs_eq : sumOver accts (fun a => sumOver (h2 :: t2) (fun l => if l.1 = a then l.2 else 0))
        = sumOver accts (fun a => ((if h2.1 = a then h2.2 else 0) + sumOver t2 (fun l => if l.1 = a then l.2 else 0))) := by
      apply sumOver_congr; intro a _; rfl
    rw [lhs_eq, sumOver_add, ih2]; rfl

theorem sumOver_accounts_netOf (accts : List AccountId) (ls : List Line)
    (hsub : ∀ l ∈ ls, l.1 ∈ accts) (hNodup : accts.Nodup) :
    sumOver accts (fun a => netOf ls a) = lineSum ls := by
  unfold netOf lineSum
  rw [sumOver_swap accts ls]
  apply sumOver_congr
  intro l hl
  have hmem : l.1 ∈ accts := hsub l hl
  have h1 : sumOver accts (fun a => if l.1 = a then l.2 else 0)
          = sumOver accts (fun a => if a = l.1 then l.2 else 0) := by
    apply sumOver_congr; intro a _; simp only [eq_comm]
  rw [h1]
  have h := sumOver_ite_eq hNodup l.1 l.2
  simp [hmem] at h
  exact h

theorem total_add_net (s : State) (ls : List Line) (hsub : ∀ l ∈ ls, l.1 ∈ s.accounts) (hNodup : s.accounts.Nodup) :
    sumOver s.accounts (fun a => s.balance a + netOf ls a) = total s + lineSum ls := by
  unfold total
  have h := sumOver_add s.accounts s.balance (fun a => netOf ls a)
  rw [h]
  have h2 := sumOver_accounts_netOf s.accounts ls hsub hNodup
  omega

theorem total_sub_net (s : State) (ls : List Line) (hsub : ∀ l ∈ ls, l.1 ∈ s.accounts) (hNodup : s.accounts.Nodup) :
    sumOver s.accounts (fun a => s.balance a - netOf ls a) = total s - lineSum ls := by
  unfold total
  have h := sumOver_sub s.accounts s.balance (fun a => netOf ls a)
  rw [h]
  have h2 := sumOver_accounts_netOf s.accounts ls hsub hNodup
  omega

theorem activeNet_append (s : State) (e : Entry) (a : AccountId) :
    activeNet { s with journal := s.journal ++ [e] } a
    = activeNet s a + if e.id ∈ s.reversed then (0 : Int) else netOf e.lines a := by
  unfold activeNet
  simp only
  rw [sumOver_append]

theorem activeNet_reverse_valid (s : State) (i : EntryId) (e : Entry) (he : findEntry s.journal i = some e) (hnot : i ∉ s.reversed) (a : AccountId) :
    activeNet { s with reversed := i :: s.reversed, journal := s.journal } a = activeNet s a - netOf e.lines a := by
  unfold activeNet
  simp only
  induction s.journal with
  | nil => simp [findEntry] at he
  | cons hd tl ih =>
    simp only [findEntry] at he
    by_cases heq : hd.id = i
    · subst heq
      simp only [ite_true] at he
      have he_hd : hd = e := Option.some_inj.mp he
      subst he_hd
      simp
    · simp only [heq, ite_false] at he
      simp only [sumOver_cons]
      by_cases hmem : hd.id ∈ s.reversed
      · have hmem2 : hd.id ∈ i :: s.reversed := by simp [hmem]
        simp [hmem, hmem2, ih he]
      · have hmem2 : hd.id ∉ i :: s.reversed := by simp [heq, hmem]
        simp only [hmem, hmem2, ih he]
        omega

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | some e =>
      if i ∈ s.reversed then (.rejected, s)
      else (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed })
    | none => (.rejected, s)

theorem step_post_eq (s : State) (e : Entry) (h : ValidPost s e) :
    step s (.post e) = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by
  unfold step; simp [h]

theorem step_post_not (s : State) (e : Entry) (h : ¬ ValidPost s e) :
    step s (.post e) = (.rejected, s) := by
  unfold step; simp [h]

theorem step_rev_some (s : State) (i : EntryId) (e : Entry) (he : findEntry s.journal i = some e) :
    step s (.reverse i) = if i ∈ s.reversed then (.rejected, s) else (.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
  unfold step; simp [he]

theorem step_rev_none (s : State) (i : EntryId) (he : findEntry s.journal i = none) :
    step s (.reverse i) = (.rejected, s) := by
  unfold step; simp [he]

theorem validPost_of_post_ok (s : State) (e : Entry) (hok : (step s (.post e)).1 = .ok) : ValidPost s e := by
  by_cases h : ValidPost s e
  · exact h
  · have hs := step_post_not s e h; rw [hs] at hok; simp at hok

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h; obtain ⟨hmem, hnot⟩ := h
  have hne : findEntry s.journal i ≠ none := by intro hnone; exact absurd hmem ((findEntry_none_iff_notMem _ _).mp hnone)
  obtain ⟨e, he⟩ := Option.ne_none_iff_isSome.mp hne |> Option.isSome_iff_exists.mp
  have hs := step_rev_some s i e he; rw [hs]; simp [hnot]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h; cases c with
  | post e =>
    have h' : ¬ ValidPost s e := h
    exact step_post_not s e h'
  | reverse i =>
    have h' : ¬ ValidReverse s i := h
    by_cases hfind : findEntry s.journal i = none
    · exact step_rev_none s i hfind
    · have hne : findEntry s.journal i ≠ none := hfind
      obtain ⟨e, he⟩ := Option.ne_none_iff_isSome.mp hne |> Option.isSome_iff_exists.mp
      have hmem : i ∈ ids s.journal := by
        have hm := findEntry_some_mem _ _ _ he; have : e ∈ s.journal := hm.1
        have : e.id ∈ ids s.journal := by unfold ids; exact List.mem_map.mpr ⟨e, ‹e ∈ s.journal›, rfl⟩
        rwa [hm.2] at this
      have hmem_rev : i ∈ s.reversed := by
        by_cases hc : i ∈ s.reversed
        · exact hc
        · exact absurd ⟨hmem, hc⟩ h'
      have hs := step_rev_some s i e he; rw [hs]; simp [hmem_rev]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  have hvp := validPost_of_post_ok s e hok
  have hs := step_post_eq s e hvp
  rw [hs] at hok ⊢
  simp

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hfind
  have hs := step_rev_some s i e hfind
  have hnot : i ∉ s.reversed := by
    by_cases hc : i ∈ s.reversed
    · have : step s (.reverse i) = (Outcome.rejected, s) := by rw [hs]; simp [hc]
      rw [this] at hok; simp at hok
    · exact hc
  have h1 : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by
    rw [hs]; simp [hnot]
  rw [h1]
  refine ⟨rfl, rfl, rfl, ?_, fun _ => rfl⟩
  intro x; simp

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  by_cases hfind : findEntry s.journal i = none
  · have hs := step_rev_none s i hfind; rw [hs] at hok; simp at hok
  · have hne : findEntry s.journal i ≠ none := hfind
    obtain ⟨e, he⟩ := Option.ne_none_iff_isSome.mp hne |> Option.isSome_iff_exists.mp
    have hs := step_rev_some s i e he; rw [hs] at hok
    by_cases hmem : i ∈ s.reversed
    · simp [hmem] at hok
    · simp [hmem] at hs hok
      have hstate_eq : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by rw [hs]
      have hfind2 : findEntry (step s (.reverse i)).2.journal i = some e := by
        rw [hstate_eq]; simp [he]
      have hmem2 : i ∈ (step s (.reverse i)).2.reversed := by rw [hstate_eq]; simp
      have hs2 := step_rev_some (step s (.reverse i)).2 i e hfind2; rw [hs2]; simp [hmem2]

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hvp := validPost_of_post_ok s e hok
  have hs_post := step_post_eq s e hvp
  have hfind : findEntry (s.journal ++ [e]) e.id = some e :=
    findEntry_append_of_notMem s.journal e hvp.2.2.2.2.1
  have hpost_state : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by rw [hs_post]
  have hfind2 : findEntry (step s (.post e)).2.journal e.id = some e := by rw [hpost_state]; exact hfind
  have hnot_rev2 : e.id ∉ (step s (.post e)).2.reversed := by rw [hpost_state]; exact hvp.2.2.2.2.2
  have hs_rev := step_rev_some (step s (.post e)).2 e.id e hfind2
  constructor
  · rw [hs_rev]; simp [hnot_rev2]
  · have hs_rev_ok : step (step s (.post e)).2 (.reverse e.id) = (Outcome.ok, { (step s (.post e)).2 with balance := fun a => (step s (.post e)).2.balance a - netOf e.lines a, reversed := e.id :: (step s (.post e)).2.reversed }) := by
      rw [hs_rev]; simp [hnot_rev2]
    have hbal : (step (step s (.post e)).2 (.reverse e.id)).2.balance = fun a => (step s (.post e)).2.balance a - netOf e.lines a := by
      rw [hs_rev_ok]
    rw [hbal]
    funext a
    rw [hpost_state]
    simp
    omega

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  cases c with
  | post e =>
    have hvp := validPost_of_post_ok s e hok
    have hs := step_post_eq s e hvp
    have hsub : ∀ l ∈ e.lines, l.1 ∈ s.accounts := hvp.2.1
    have hline : lineSum e.lines = 0 := hvp.2.2.2.1
    have htb := total_add_net s e.lines hsub hwf.1
    have h_eq : total (step s (.post e)).2 = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := by
      have h1 : (step s (.post e)).2.accounts = s.accounts := by rw [hs]
      have h2 : (step s (.post e)).2.balance = fun a => s.balance a + netOf e.lines a := by rw [hs]
      unfold total; rw [h1, h2]
    rw [h_eq, htb, hline]
    simp
  | reverse i =>
    by_cases hfind : findEntry s.journal i = none
    · have hs := step_rev_none s i hfind; rw [hs] at hok; simp at hok
    · have hne : findEntry s.journal i ≠ none := hfind
      obtain ⟨e, he⟩ := Option.ne_none_iff_isSome.mp hne |> Option.isSome_iff_exists.mp
      have hs := step_rev_some s i e he; rw [hs] at hok
      by_cases hmem : i ∈ s.reversed
      · simp [hmem] at hok
      · simp [hmem] at hs hok
        have hsub : ∀ l ∈ e.lines, l.1 ∈ s.accounts := (hwf.2.2.2 e (findEntry_some_mem _ _ _ he).1).1
        have hline : lineSum e.lines = 0 := (hwf.2.2.2 e (findEntry_some_mem _ _ _ he).1).2
        have htb := total_sub_net s e.lines hsub hwf.1
        have h_eq : total (step s (.reverse i)).2 = sumOver s.accounts (fun a => s.balance a - netOf e.lines a) := by
          have h1 : (step s (.reverse i)).2.accounts = s.accounts := by rw [hs]
          have h2 : (step s (.reverse i)).2.balance = fun a => s.balance a - netOf e.lines a := by rw [hs]
          unfold total; rw [h1, h2]
        rw [h_eq, htb, hline]
        simp

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  cases c with
  | post e =>
    by_cases hvp : ValidPost s e
    · have hs := step_post_eq s e hvp; rw [hs]
      obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩ := hwf
      refine ⟨hNodupAcc, ?_, ?_, ?_⟩
      · exact nodup_ids_append s.journal e hNodupIds hvp.2.2.2.2.1
      · intro i hi; have : i ∈ ids s.journal := hRevSub i hi; rw [ids_append_single]; exact List.mem_append.mpr (Or.inl this)
      · intro e' he'; rw [List.mem_append] at he'; rcases he' with hold | hnew
        · exact hBal e' hold
        · simp at hnew; subst hnew; exact ⟨hvp.2.1, hvp.2.2.2.1⟩
    · have hs := step_post_not s e hvp; rw [hs]; exact hwf
  | reverse i =>
    by_cases hfind : findEntry s.journal i = none
    · have hs := step_rev_none s i hfind; rw [hs]; exact hwf
    · have hne : findEntry s.journal i ≠ none := hfind
      obtain ⟨e, he⟩ := Option.ne_none_iff_isSome.mp hne |> Option.isSome_iff_exists.mp
      have hs := step_rev_some s i e he
      by_cases hmem : i ∈ s.reversed
      · have hs2 : step s (.reverse i) = (Outcome.rejected, s) := by rw [hs]; simp [hmem]
        rw [hs2]; exact hwf
      · have hst : step s (.reverse i) = (Outcome.ok, { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed }) := by rw [hs]; simp [hmem]
        rw [hst]
        obtain ⟨hNodupAcc, hNodupIds, hRevSub, hBal⟩ := hwf
        refine ⟨hNodupAcc, hNodupIds, ?_, hBal⟩
        intro x hx
        have hx' : x = i ∨ x ∈ s.reversed := by simpa using hx
        rcases hx' with rfl | hmem2
        · have hm := findEntry_some_mem _ _ _ he
          have : e ∈ s.journal := hm.1
          have : e.id ∈ ids s.journal := by unfold ids; exact List.mem_map.mpr ⟨e, ‹e ∈ s.journal›, rfl⟩
          rwa [hm.2] at this
        · exact hRevSub x hmem2

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  cases c with
  | post e =>
    by_cases hvp : ValidPost s e
    · have hs := step_post_eq s e hvp
      have hpost_state : (step s (.post e)).2 = { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] } := by rw [hs]
      rw [hpost_state]
      intro a
      have hactive1 : activeNet { s with journal := s.journal ++ [e] } a = activeNet s a + netOf e.lines a := by
        have h := activeNet_append s e a
        have hnot : e.id ∉ s.reversed := hvp.2.2.2.2.2
        simp only [hnot, ↓reduceIte] at h
        exact h
      have hactive2 : activeNet { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } a = activeNet { s with journal := s.journal ++ [e] } a := by rfl
      simp only
      rw [hactive2, hactive1]
      have hc := hcons a
      omega
    · have hs := step_post_not s e hvp; rw [hs]; exact hcons
  | reverse i =>
    by_cases hfind : findEntry s.journal i = none
    · have hs := step_rev_none s i hfind; rw [hs]; exact hcons
    · have hne : findEntry s.journal i ≠ none := hfind
      obtain ⟨e, he⟩ := Option.ne_none_iff_isSome.mp hne |> Option.isSome_iff_exists.mp
      have hs := step_rev_some s i e he
      by_cases hmem : i ∈ s.reversed
      · have hs2 : step s (.reverse i) = (Outcome.rejected, s) := by rw [hs]; simp [hmem]
        rw [hs2]; exact hcons
      · have hstate : (step s (.reverse i)).2 = { s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed } := by rw [hs]; simp [hmem]
        rw [hstate]
        intro a
        have hactive1 : activeNet { s with reversed := i :: s.reversed } a = activeNet s a - netOf e.lines a :=
          activeNet_reverse_valid s i e he hmem a
        have hactive2 : activeNet { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } a = activeNet { s with reversed := i :: s.reversed } a := by rfl
        simp only
        rw [hactive2, hactive1]
        have hc := hcons a
        omega

end Reversal
