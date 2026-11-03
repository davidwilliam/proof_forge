import Reversal.Spec
import Reversal.Lemmas
namespace Reversal
open Classical

theorem findEntry_some_mem {j : List Entry} {i : EntryId} {e : Entry}
    (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; subst h; exact List.Mem.head _
    · simp [heq] at h; exact List.Mem.tail _ (ih h)

theorem findEntry_some_id {j : List Entry} {i : EntryId} {e : Entry}
    (h : findEntry j i = some e) : e.id = i := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h; cases h; exact heq.symm
    · simp [heq] at h; exact ih h

theorem findEntry_some_mem_ids {j : List Entry} {i : EntryId} {e : Entry}
    (h : findEntry j i = some e) : i ∈ ids j := by
  have hm := findEntry_some_mem h
  have hid := findEntry_some_id h
  exact List.mem_map.mpr ⟨e, hm, by simp [ids, hid]⟩

theorem findEntry_of_mem_ids {j : List Entry} {i : EntryId}
    (h : i ∈ ids j) : ∃ e, findEntry j i = some e := by
  induction j with
  | nil => simp [ids] at h
  | cons hd tl ih =>
    simp [findEntry]
    by_cases heq : hd.id = i
    · simp [heq]
    · simp [heq]
      have : i ∈ ids tl := by simp [ids] at h; rcases h with rfl | hmem
        · exact absurd rfl heq
        · exact hmem
      exact ih this

theorem findEntry_none_of_not_mem {j : List Entry} {i : EntryId}
    (h : i ∉ ids j) : findEntry j i = none := by
  induction j with
  | nil => rfl
  | cons hd tl ih =>
    simp [findEntry]
    have hhd : hd.id ≠ i := fun heq => h (by simp [ids, heq])
    simp [hhd]
    apply ih; intro contra; apply h; simp [ids, contra]

theorem nodup_append_singleton {α : Type} {l : List α} {x : α}
    (hl : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [List.nodup_cons] at hl ⊢
    constructor
    · intro hmem; rcases List.mem_append.mp hmem with h1 | h2
      · exact hl.1 h1
      · simp at h2; subst h2; exact hl.1 (List.Mem.head _)
    · have hx2 : x ∉ tl := fun h => hx (List.Mem.tail _ h)
      exact ih hl.2 hx2

theorem sumOver_netOf_eq_lineSum_of_mem {ls : List Line} {accs : List AccountId}
    (hmem : ∀ l ∈ ls, l.1 ∈ accs) (hnodup : accs.Nodup) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil => simp [netOf, lineSum]
  | cons hd tl ih =>
    have htl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => hmem l (List.Mem.tail _ hl)
    have ih' := ih htl
    have h1 : sumOver accs (fun a => (if hd.1 = a then hd.2 else (0 : Int))) = hd.2 := by
      have hmem_hd : hd.1 ∈ accs := hmem hd (List.Mem.head _)
      have hcong : ∀ a ∈ accs, (if hd.1 = a then hd.2 else (0 : Int)) = (if a = hd.1 then hd.2 else 0) := by
        intro a _; by_cases heq : hd.1 = a
        · simp [heq]
        · simp [heq, Ne.symm heq]
      rw [sumOver_congr _ _ _ hcong, sumOver_ite_eq hnodup hd.1 hd.2]; simp [hmem_hd]
    have hcong2 : ∀ a ∈ accs, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else 0) + netOf tl a := by
      intro a _; simp [netOf]
    calc sumOver accs (fun a => netOf (hd :: tl) a)
        = sumOver accs (fun a => (if hd.1 = a then hd.2 else (0 : Int)) + netOf tl a) :=
          sumOver_congr _ _ _ hcong2
      _ = sumOver accs (fun a => (if hd.1 = a then hd.2 else (0 : Int))) +
          sumOver accs (fun a => netOf tl a) := sumOver_add _ _ _
      _ = hd.2 + lineSum tl := by rw [h1, ih']
      _ = lineSum (hd :: tl) := by simp [lineSum]

theorem netOf_sum_zero_of_balanced {ls : List Line} {accs : List AccountId}
    (hbal : lineSum ls = 0) (hmem : ∀ l ∈ ls, l.1 ∈ accs) (hnodup : accs.Nodup) :
    sumOver accs (fun a => netOf ls a) = 0 := by
  rw [sumOver_netOf_eq_lineSum_of_mem hmem hnodup, hbal]

theorem activeNet_reverse_eq {j : List Entry} {r : List EntryId} {a : AccountId}
    {i : EntryId} {e : Entry}
    (hfind : findEntry j i = some e) (hNodup : (ids j).Nodup) (hNotRev : i ∉ r) :
    sumOver j (fun e' => if e'.id ∈ (i :: r) then (0 : Int) else netOf e'.lines a) =
    sumOver j (fun e' => if e'.id ∈ r then (0 : Int) else netOf e'.lines a) - netOf e.lines a := by
  induction j generalizing e with
  | nil => simp [findEntry] at hfind
  | cons hd tl ih =>
    have hNodupTl : (ids tl).Nodup := by have : (ids (hd :: tl)).Nodup := hNodup; simp [ids] at this; exact this.2
    have hNotInTl : hd.id ∉ ids tl := by have : (ids (hd :: tl)).Nodup := hNodup; simp [ids] at this; exact this.1
    simp [findEntry] at hfind
    by_cases heq : hd.id = i
    · simp [heq] at hfind; subst hfind; simp [hNotRev]
      have hAfter : ∀ x ∈ tl, (if x.id ∈ (i :: r) then (0 : Int) else netOf x.lines a) =
          (if x.id ∈ r then (0 : Int) else netOf x.lines a) := by
        intro x hx; have hne : x.id ≠ i := fun heq2 => hNotInTl (List.mem_map.mpr ⟨x, hx, by simp [heq2]⟩)
        simp [hne]
      have hc := sumOver_congr tl _ _ hAfter; simp [hc]
    · simp [heq] at hfind
      have ih' := ih (e:=e) hfind hNodupTl
      have h1 : (if hd.id ∈ (i :: r) then (0 : Int) else netOf hd.lines a) =
          (if hd.id ∈ r then (0 : Int) else netOf hd.lines a) := by simp [heq]
      simp only [sumOver_cons]; rw [h1, ih']; omega

noncomputable def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { accounts := s.accounts, opening := s.opening,
              balance := fun a => s.balance a + netOf e.lines a,
              journal := s.journal ++ [e], reversed := s.reversed })
    else (.rejected, s)
  | .reverse i =>
    match h : findEntry s.journal i with
    | none => (.rejected, s)
    | some e => if i ∈ s.reversed then (.rejected, s) else
        (.ok, { accounts := s.accounts, opening := s.opening,
                balance := fun a => s.balance a - netOf e.lines a,
                journal := s.journal, reversed := i :: s.reversed })

theorem req_post_succeeds : PostSucceeds step := by intro s e h; simp [step, h]
theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h; obtain ⟨hmem, hnot⟩ := h; obtain ⟨e, he⟩ := findEntry_of_mem_ids hmem; simp [step, he, hnot]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h; cases c with
  | post e => simp [Valid] at h; simp [step, h]
  | reverse i =>
    simp [Valid, ValidReverse] at h
    by_cases hmem : i ∈ ids s.journal
    · have hrev : i ∈ s.reversed := by by_contra hnot; exact h ⟨hmem, hnot⟩
      obtain ⟨e, he⟩ := findEntry_of_mem_ids hmem; simp [step, he, hrev]
    · have hnone : findEntry s.journal i = none := findEntry_none_of_not_mem hmem; simp [step, hnone]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  have hvalid : ValidPost s e := by
    by_contra hnv; have : step s (.post e) = (.rejected, s) := by simp [step, hnv]; rw [this] at hok; simp at hok
  have hEq : step s (.post e) = (.ok, ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => s.balance a + netOf e.lines a,
               journal := s.journal ++ [e], reversed := s.reversed } : State)) := by simp [step, hvalid]
  have hSnd : (step s (.post e)).2 = ({ accounts := s.accounts, opening := s.opening,
         balance := fun a => s.balance a + netOf e.lines a,
         journal := s.journal ++ [e], reversed := s.reversed } : State) := by simp [hEq]
  simp only [hSnd, and_self, implies_true, forall_const]

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hfind
  have hnot : i ∉ s.reversed := by
    by_contra hc; have : step s (.reverse i) = (.rejected, s) := by simp [step, hfind, hc]; rw [this] at hok; simp at hok
  have hEq : step s (.reverse i) = (.ok, ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => s.balance a - netOf e.lines a,
               journal := s.journal, reversed := i :: s.reversed } : State)) := by simp [step, hfind, hnot]
  have hSnd : (step s (.reverse i)).2 = ({ accounts := s.accounts, opening := s.opening,
         balance := fun a => s.balance a - netOf e.lines a,
         journal := s.journal, reversed := i :: s.reversed } : State) := by simp [hEq]
  simp only [hSnd, and_self, implies_true, forall_const]

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  by_cases hnone : findEntry s.journal i = none
  · have h1 : step s (.reverse i) = (.rejected, s) := by simp [step, hnone]
    rw [h1] at hok; simp at hok
  · simp at hnone; obtain ⟨e, he⟩ := hnone; by_cases hmem : i ∈ s.reversed
    · have h1 : step s (.reverse i) = (.rejected, s) := by simp [step, he, hmem]
      rw [h1] at hok; simp at hok
    · have hstep : step s (.reverse i) = (.ok, ({ accounts := s.accounts, opening := s.opening,
                   balance := fun a => s.balance a - netOf e.lines a,
                   journal := s.journal, reversed := i :: s.reversed } : State)) := by simp [step, he, hmem]
      have hSnd : (step s (.reverse i)).2 = ({ accounts := s.accounts, opening := s.opening,
             balance := fun a => s.balance a - netOf e.lines a,
             journal := s.journal, reversed := i :: s.reversed } : State) := by simp [hstep]
      rw [hSnd]
      have hfind2 : findEntry (({ accounts := s.accounts, opening := s.opening,
                   balance := fun a => s.balance a - netOf e.lines a,
                   journal := s.journal, reversed := i :: s.reversed } : State).journal) i = some e := by simp [he]
      simp [step, hfind2]

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hvalid : ValidPost s e := by
    by_contra hnv; have : step s (.post e) = (.rejected, s) := by simp [step, hnv]; rw [this] at hok; simp at hok
  have hEq : step s (.post e) = (.ok, ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => s.balance a + netOf e.lines a,
               journal := s.journal ++ [e], reversed := s.reversed } : State)) := by simp [step, hvalid]
  have hpost2 : (step s (.post e)).2 = ({ accounts := s.accounts, opening := s.opening,
         balance := fun a => s.balance a + netOf e.lines a,
         journal := s.journal ++ [e], reversed := s.reversed } : State) := by simp [hEq]
  have hnotJ : e.id ∉ ids s.journal := hvalid.2.2.2.2.1
  have hfind : findEntry (s.journal ++ [e]) e.id = some e := by
    induction s.journal with
    | nil => simp [findEntry]
    | cons hd tl ih => simp [findEntry]
      have hne : hd.id ≠ e.id := fun heq => hnotJ (by simp [ids, heq]); simp [hne]
      exact ih (fun contra => hnotJ (by simp [ids, contra]))
  have hstep2 : step ({ accounts := s.accounts, opening := s.opening,
         balance := fun a => s.balance a + netOf e.lines a,
         journal := s.journal ++ [e], reversed := s.reversed } : State) (.reverse e.id) =
      (.ok, ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => (s.balance a + netOf e.lines a) - netOf e.lines a,
               journal := s.journal ++ [e], reversed := e.id :: s.reversed } : State)) := by simp [step, hfind]
  constructor; · simp [hpost2, hstep2]; · simp [hpost2, hstep2]

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  revert hok
  cases c with
  | post e =>
    intro hok
    by_cases hvalid : ValidPost s e
    · have hEq : step s (Command.post e) = (.ok, ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => s.balance a + netOf e.lines a,
               journal := s.journal ++ [e], reversed := s.reversed } : State)) := by simp [step, hvalid]
      have : total (step s (Command.post e)).snd = total s := by
        rw [hEq]; simp only [total]
        have h : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) =
            sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := sumOver_add _ _ _
        rw [h]
        have hzero : sumOver s.accounts (fun a => netOf e.lines a) = 0 :=
          netOf_sum_zero_of_balanced hvalid.2.2.2.1 hvalid.2.1 hwf.1
        omega
      exact this
    · have hEq : step s (Command.post e) = (.rejected, s) := by simp [step, hvalid]
      rw [hEq]; simp
  | reverse i =>
    intro hok
    by_cases hnone : findEntry s.journal i = none
    · have hEq : step s (Command.reverse i) = (.rejected, s) := by simp [step, hnone]
      rw [hEq] at hok; simp at hok
    · simp at hnone; obtain ⟨e, he⟩ := hnone; by_cases hmem : i ∈ s.reversed
      · have hEq : step s (Command.reverse i) = (.rejected, s) := by simp [step, he, hmem]
        rw [hEq] at hok; simp at hok
      · have hEq : step s (Command.reverse i) = (.ok, ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => s.balance a - netOf e.lines a,
               journal := s.journal, reversed := i :: s.reversed } : State)) := by simp [step, he, hmem]
        have : total (step s (Command.reverse i)).snd = total s := by
          rw [hEq]; simp only [total]
          have h : sumOver s.accounts (fun a => s.balance a - netOf e.lines a) =
              sumOver s.accounts s.balance - sumOver s.accounts (fun a => netOf e.lines a) := sumOver_sub _ _ _
          rw [h]; have he_mem : e ∈ s.journal := findEntry_some_mem he
          have hwf_e := hwf.2.2.2 e he_mem
          have hzero : sumOver s.accounts (fun a => netOf e.lines a) = 0 :=
            netOf_sum_zero_of_balanced hwf_e.2 hwf_e.1 hwf.1; omega
        exact this

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  cases c with
  | post e =>
    by_cases hvalid : ValidPost s e
    · have hEq : step s (.post e) = (.ok, ({ accounts := s.accounts, opening := s.opening,
                   balance := fun a => s.balance a + netOf e.lines a,
                   journal := s.journal ++ [e], reversed := s.reversed } : State)) := by simp [step, hvalid]
      have hSnd : (step s (Command.post e)).2 = ({ accounts := s.accounts, opening := s.opening,
             balance := fun a => s.balance a + netOf e.lines a,
             journal := s.journal ++ [e], reversed := s.reversed } : State) := by simp [hEq]
      rw [hSnd]; rcases hvalid with ⟨_hne, hmemAcc, _hnz, hbal, hnotJ, _hnotR⟩
      have hids_eq : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := by simp [ids]
      have hnodup : (ids (s.journal ++ [e])).Nodup := by rw [hids_eq]; exact nodup_append_singleton hwf.2.1 hnotJ
      exact ⟨hwf.1, hnodup, fun i hi => by have : i ∈ ids s.journal := hwf.2.2.1 i hi; rw [hids_eq]; exact List.mem_append.mpr (Or.inl this),
        fun e' he' => by simp at he'; rcases he' with he'_in_j | rfl; exact hwf.2.2.2 _ he'_in_j; exact ⟨hmemAcc, hbal⟩⟩
    · have hEq : step s (.post e) = (.rejected, s) := by simp [step, hvalid]
      have hSnd : (step s (Command.post e)).2 = s := by simp [hEq]; rw [hSnd]; exact hwf
  | reverse i =>
    by_cases hnone : findEntry s.journal i = none
    · have hEq : step s (.reverse i) = (.rejected, s) := by simp [step, hnone]
      have hSnd : (step s (Command.reverse i)).2 = s := by simp [hEq]; rw [hSnd]; exact hwf
    · simp at hnone; obtain ⟨e, he⟩ := hnone; by_cases hmem : i ∈ s.reversed
      · have hEq : step s (.reverse i) = (.rejected, s) := by simp [step, he, hmem]
        have hSnd : (step s (Command.reverse i)).2 = s := by simp [hEq]; rw [hSnd]; exact hwf
      · have hEq : step s (.reverse i) = (.ok, ({ accounts := s.accounts, opening := s.opening,
                     balance := fun a => s.balance a - netOf e.lines a,
                     journal := s.journal, reversed := i :: s.reversed } : State)) := by simp [step, he, hmem]
        have hSnd : (step s (Command.reverse i)).2 = ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => s.balance a - netOf e.lines a,
               journal := s.journal, reversed := i :: s.reversed } : State) := by simp [hEq]
        rw [hSnd]; exact ⟨hwf.1, hwf.2.1, fun j hj => by rcases List.mem_cons.mp hj with rfl | hj; exact findEntry_some_mem_ids he; exact hwf.2.2.1 _ hj, fun e' he' => hwf.2.2.2 e' he'⟩

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  cases c with
  | post e =>
    by_cases hvalid : ValidPost s e
    · have hStep : step s (Command.post e) = (.ok, ({ accounts := s.accounts, opening := s.opening,
                   balance := fun a => s.balance a + netOf e.lines a,
                   journal := s.journal ++ [e], reversed := s.reversed } : State)) := by simp [step, hvalid]
      have hSnd : (step s (Command.post e)).2 = ({ accounts := s.accounts, opening := s.opening,
             balance := fun a => s.balance a + netOf e.lines a,
             journal := s.journal ++ [e], reversed := s.reversed } : State) := by simp [hStep]
      have hnotR : e.id ∉ s.reversed := hvalid.2.2.2.2.2
      have hActive : ∀ a, activeNet ({ accounts := s.accounts, opening := s.opening,
             balance := fun a => s.balance a + netOf e.lines a,
             journal := s.journal ++ [e], reversed := s.reversed } : State) a = activeNet s a + netOf e.lines a := by
        intro a; simp [activeNet, sumOver_append, hnotR]
      have hGoal : Consistent ({ accounts := s.accounts, opening := s.opening,
             balance := fun a => s.balance a + netOf e.lines a,
             journal := s.journal ++ [e], reversed := s.reversed } : State) := by intro a; simp only [hActive a, hcons a]; omega
      rw [← hSnd] at hGoal; exact hGoal
    · have hEq : step s (Command.post e) = (.rejected, s) := by simp [step, hvalid]
      have hSnd : (step s (Command.post e)).2 = s := by simp [hEq]; rw [hSnd]; exact hcons
  | reverse i =>
    by_cases hnone : findEntry s.journal i = none
    · have hEq : step s (.reverse i) = (.rejected, s) := by simp [step, hnone]
      have hSnd : (step s (Command.reverse i)).2 = s := by simp [hEq]; rw [hSnd]; exact hcons
    · simp at hnone; obtain ⟨e, he⟩ := hnone; by_cases hmem : i ∈ s.reversed
      · have hEq : step s (.reverse i) = (.rejected, s) := by simp [step, he, hmem]
        have hSnd : (step s (Command.reverse i)).2 = s := by simp [hEq]; rw [hSnd]; exact hcons
      · have hStep : step s (Command.reverse i) = (.ok, ({ accounts := s.accounts, opening := s.opening,
                     balance := fun a => s.balance a - netOf e.lines a,
                     journal := s.journal, reversed := i :: s.reversed } : State)) := by simp [step, he, hmem]
        have hSnd : (step s (Command.reverse i)).2 = ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => s.balance a - netOf e.lines a,
               journal := s.journal, reversed := i :: s.reversed } : State) := by simp [hStep]
        have hActive : ∀ a, activeNet ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => s.balance a - netOf e.lines a,
               journal := s.journal, reversed := i :: s.reversed } : State) a = activeNet s a - netOf e.lines a := by
          intro a; have h1 : activeNet ({ accounts := s.accounts, opening := s.opening,
                 balance := fun a => s.balance a - netOf e.lines a,
                 journal := s.journal, reversed := i :: s.reversed } : State) a =
              sumOver s.journal (fun e' => if e'.id ∈ (i :: s.reversed) then (0 : Int) else netOf e'.lines a) := by simp [activeNet]
          rw [h1]; change sumOver s.journal (fun e' => if e'.id ∈ (i :: s.reversed) then (0 : Int) else netOf e'.lines a) = _; exact activeNet_reverse_eq he hwf.2.1 hmem
        have hGoal : Consistent ({ accounts := s.accounts, opening := s.opening,
               balance := fun a => s.balance a - netOf e.lines a,
               journal := s.journal, reversed := i :: s.reversed } : State) := by intro a; simp only [hActive a, hcons a]; omega
        rw [← hSnd] at hGoal; exact hGoal
end Reversal
