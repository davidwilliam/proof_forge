import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | none => (.rejected, s)
    | some e =>
      if i ∈ s.reversed then (.rejected, s)
      else (.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a })

theorem findEntry_none_of_not_mem (j : List Entry) (i : EntryId) (h : i ∉ ids j) : findEntry j i = none := by
  induction j with
  | nil => rfl
  | cons hd tl ih =>
    simp only [findEntry]
    have h1 : hd.id ≠ i := by
      intro heq
      apply h
      simp [ids, heq]
    simp [h1]
    apply ih
    intro hm
    apply h
    simp [ids, hm]

theorem findEntry_isSome_of_mem (j : List Entry) (i : EntryId) (h : i ∈ ids j) : (findEntry j i).isSome = true := by
  induction j with
  | nil => simp [ids] at h
  | cons hd tl ih =>
    simp only [findEntry]
    by_cases heq : hd.id = i
    · simp [heq]
    · simp [heq]
      exact ih (by simp [ids, heq] at h ⊢; exact h)

theorem findEntry_mem_journal {j i e} (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih =>
    simp only [findEntry] at h
    by_cases heq : hd.id = i
    · simp [heq] at h
      rw [h]
      simp
    · simp [heq] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem findEntry_append_of_not_mem {j : List Entry} {e : Entry} (h : e.id ∉ ids j) :
    findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have h1 : hd.id ≠ e.id := by intro heq; exact h (by simp [ids, heq])
    have h2 : e.id ∉ ids tl := by intro hm; exact h (by simp [ids, hm])
    simp [findEntry, h1, ih h2]

theorem sumOver_zero (l : List AccountId) : sumOver l (fun _ : AccountId => (0:Int)) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [sumOver_cons, ih]

theorem sumOver_accounts_netOf (accs : List AccountId) (ls : List Line)
    (hnodup : accs.Nodup) (h : ∀ l ∈ ls, l.1 ∈ accs) :
    sumOver accs (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil =>
    have hc : ∀ a ∈ accs, netOf ([] : List Line) a = 0 := by intro a _; rfl
    calc sumOver accs (fun a => netOf [] a) = sumOver accs (fun _ => (0:Int)) := sumOver_congr accs _ _ hc
      _ = 0 := sumOver_zero accs
      _ = lineSum [] := by rfl
  | cons hd tl ih =>
    have hhd : hd.1 ∈ accs := h hd (by simp)
    have htl : ∀ l ∈ tl, l.1 ∈ accs := fun l hl => h l (List.mem_cons_of_mem _ hl)
    have ih' := ih htl
    have h1 : ∀ a ∈ accs, netOf (hd :: tl) a = netOf tl a + if hd.1 = a then hd.2 else 0 := by
      intro a _; simp [netOf, sumOver_cons]
    have heq1 : sumOver accs (fun a => netOf (hd :: tl) a) = sumOver accs (fun a => netOf tl a + if hd.1 = a then hd.2 else 0) :=
      sumOver_congr accs _ _ h1
    rw [heq1, sumOver_add, ih']
    have heq2 : (fun a : AccountId => if hd.1 = a then hd.2 else (0:Int)) = (fun a => if a = hd.1 then hd.2 else 0) := by
      funext a
      by_cases heq : hd.1 = a
      · rw [heq]; simp [heq]
      · have hne : ¬ (a = hd.1) := fun hh => heq hh.symm
        simp [heq, hne]
    have hsingle : sumOver accs (fun a => if hd.1 = a then hd.2 else (0:Int)) = hd.2 := by
      rw [heq2, sumOver_ite_eq hnodup _ _, if_pos hhd]
    rw [hsingle]
    simp [lineSum, sumOver_cons]

theorem total_add_netOf {s : State} {e : Entry}
    (hwf : WellFormed s) (hvalid : ValidPost s e) :
    sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = total s := by
  unfold total
  rw [sumOver_add]
  have hsum := sumOver_accounts_netOf s.accounts e.lines hwf.1 hvalid.2.1
  rw [hsum, hvalid.2.2.2.1]
  omega

theorem total_sub_netOf {s : State} {e : Entry}
    (hwf : WellFormed s) (he : e ∈ s.journal) :
    sumOver s.accounts (fun a => s.balance a - netOf e.lines a) = total s := by
  unfold total
  rw [sumOver_sub]
  have hsum := sumOver_accounts_netOf s.accounts e.lines hwf.1 (hwf.2.2.2 e he).1
  rw [hsum, (hwf.2.2.2 e he).2]
  omega

theorem activeNet_post {s : State} {e : Entry} {a : AccountId}
    (h : e.id ∉ s.reversed) :
    activeNet { s with journal := s.journal ++ [e] } a = activeNet s a + netOf e.lines a := by
  unfold activeNet
  rw [sumOver_append]
  simp [h]

theorem activeNet_rev {s : State} {e : Entry} {i : EntryId} {a : AccountId}
    (hwf : WellFormed s) (hfind : findEntry s.journal i = some e) (hnotrev : i ∉ s.reversed) :
    sumOver s.journal (fun ent => if ent.id ∈ i :: s.reversed then (0:Int) else netOf ent.lines a)
      = activeNet s a - netOf e.lines a := by
  unfold activeNet
  have hnodup : (ids s.journal).Nodup := hwf.2.1
  have key : ∀ ent ∈ s.journal, (if ent.id ∈ i :: s.reversed then (0:Int) else netOf ent.lines a)
        = (if ent.id ∈ s.reversed then (0:Int) else netOf ent.lines a) - if ent.id = i then netOf ent.lines a else 0 := by
    intro ent _
    by_cases heq : ent.id = i
    · subst heq; simp [hnotrev]
    · by_cases hin : ent.id ∈ s.reversed
      · simp [hin, heq]
      · simp [hin, heq]
  rw [sumOver_congr s.journal _ _ key, sumOver_sub]
  congr 1
  induction s.journal with
  | nil => simp [findEntry] at hfind
  | cons hd tl ih =>
    simp only [findEntry] at hfind
    by_cases heq : hd.id = i
    · simp [heq] at hfind
      rw [← hfind]
      simp only [sumOver_cons, heq]
      have htlZero : sumOver tl (fun ent => if ent.id = i then netOf ent.lines a else (0:Int)) = 0 := by
        apply sumOver_congr
        intro ent hmem
        have hne : ent.id ≠ i := by
          intro heq2
          have hdup : hd.id ∈ ids tl := List.mem_map_of_mem (a:=ent) hmem rfl
          have hnd : hd.id ∉ ids tl := (List.nodup_cons.mp hnodup).1
          rw [← heq2, ← heq] at hdup
          exact hnd hdup
        simp [hne]
      simp [htlZero]
    · simp [heq] at hfind
      simp [heq]
      have hnodupTl : (ids tl).Nodup := (List.nodup_cons.mp hnodup).2
      exact ih hnodupTl hfind

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h
  simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h
  have hfind : (findEntry s.journal i).isSome = true := findEntry_isSome_of_mem s.journal i h.1
  cases hc : findEntry s.journal i with
  | none => simp [hc] at hfind
  | some _ => simp [step, hc, h.2]

theorem req_invalid_noop : InvalidNoop step := by
  intro s c hn
  cases c with
  | post e =>
    simp [Valid] at hn
    simp [step, hn]
  | reverse i =>
    simp [Valid, ValidReverse] at hn
    by_cases hmem : i ∈ ids s.journal
    · have hrev : i ∈ s.reversed := hn hmem
      have hfind : (findEntry s.journal i).isSome = true := findEntry_isSome_of_mem _ _ hmem
      cases hc : findEntry s.journal i with
      | none => simp [hc] at hfind
      | some _ => simp [step, hc, hrev]
    · simp [step, findEntry_none_of_not_mem _ _ hmem]

theorem req_post_effects : PostEffects step := by
  intro s e hok
  have hvalid : ValidPost s e := by
    by_cases hv : ValidPost s e
    · exact hv
    · simp [step, hv] at hok
  simp [step, hvalid]

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hfind
  have hmem : i ∉ s.reversed := by
    by_cases hm : i ∈ s.reversed
    · simp [step, hfind, hm] at hok
    · exact hm
  simp [step, hfind, hmem]
  exact ⟨rfl, rfl, rfl, by intro x; simp, fun _ => rfl⟩

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  cases hfe : findEntry s.journal i with
  | none => simp [step, hfe] at hok
  | some e =>
    have hnr : i ∉ s.reversed := by
      intro hc
      simp [step, hfe, hc] at hok
    have hstep : step s (.reverse i) = (.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a }) := by
      simp [step, hfe, hnr]
    have h2_eq : (step s (.reverse i)).2 = ({ s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a } : State) := by
      rw [hstep]
    let s2 : State := { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf e.lines a }
    have hfe2 : findEntry s2.journal i = some e := by
      show findEntry s.journal i = some e
      exact hfe
    have hmem2 : i ∈ s2.reversed := by
      show i ∈ i :: s.reversed
      simp
    have hsecond : step s2 (.reverse i) = (.rejected, s2) := by
      simp [step, hfe2, hmem2]
    calc step (step s (.reverse i)).2 (.reverse i)
        = step s2 (.reverse i) := by rw [h2_eq]
      _ = (.rejected, s2) := hsecond
      _ = (.rejected, (step s (.reverse i)).2) := by rw [h2_eq]

theorem req_roundtrip : RoundTrip step := by
  intro s e hok
  have hvalid : ValidPost s e := by
    by_cases hv : ValidPost s e
    · exact hv
    · simp [step, hv] at hok
  have h1 : step s (.post e) = (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
    simp [step, hvalid]
  have h2 : (step s (.post e)).2 = ({ accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed } : State) := by
    simp [h1]
  have hfind : findEntry (s.journal ++ [e]) e.id = some e := findEntry_append_of_not_mem hvalid.2.2.2.2.1
  rw [h2]
  constructor
  · simp [step, hfind, hvalid.2.2.2.2.2]
  · simp [step, hfind, hvalid.2.2.2.2.2]

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok
  cases c with
  | post e =>
    have hvalid : ValidPost s e := by
      by_cases hv : ValidPost s e
      · exact hv
      · simp [step, hv] at hok
    have h1 : step s (.post e) = (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
      simp [step, hvalid]
    calc total (step s (.post e)).2
        = total { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } := by rw [h1]
      _ = sumOver s.accounts (fun a => s.balance a + netOf e.lines a) := rfl
      _ = total s := total_add_netOf hwf hvalid
  | reverse i =>
    cases hfe : findEntry s.journal i with
    | none => simp [step, hfe] at hok
    | some ee =>
      by_cases hmem : i ∈ s.reversed
      · simp [step, hfe, hmem] at hok
      · have hst : step s (.reverse i) = (.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf ee.lines a }) := by
          simp [step, hfe, hmem]
        have heMem : ee ∈ s.journal := findEntry_mem_journal hfe
        calc total (step s (.reverse i)).2
            = total { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf ee.lines a } := by rw [hst]
          _ = sumOver s.accounts (fun a => s.balance a - netOf ee.lines a) := rfl
          _ = total s := total_sub_netOf hwf heMem

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  cases c with
  | post e =>
    by_cases hvalid : ValidPost s e
    · have h1 : step s (.post e) = (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
        simp [step, hvalid]
      have h_eq : (step s (.post e)).2 = { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a } := by
        rw [h1]
      rw [h_eq]
      have hIdsEq : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := by simp [ids]
      have hNodup : (ids (s.journal ++ [e])).Nodup := by
        rw [hIdsEq, List.nodup_append]
        refine ⟨by simpa using hwf.2.1, by simp, ?_⟩
        intro a ha1 ha2
        simp at ha2
        subst ha2
        exact hvalid.2.2.2.2.1 ha1
      have hSub : ∀ i ∈ s.reversed, i ∈ ids (s.journal ++ [e]) := by
        intro i hi
        have hiOld := hwf.2.2.1 i hi
        rw [hIdsEq]
        exact List.mem_append_left _ hiOld
      have hBal : ∀ ee ∈ s.journal ++ [e], (∀ l ∈ ee.lines, l.1 ∈ s.accounts) ∧ lineSum ee.lines = 0 := by
        intro ee hee
        rw [List.mem_append] at hee
        rcases hee with h1m | h2m
        · exact hwf.2.2.2 ee h1m
        · simp at h2m
          subst h2m
          exact ⟨hvalid.2.1, hvalid.2.2.2.1⟩
      exact ⟨hwf.1, hNodup, hSub, hBal⟩
    · simp [step, hvalid]
      exact hwf
  | reverse i =>
    cases hfe : findEntry s.journal i with
    | none =>
      simp [step, hfe]
      exact hwf
    | some ee =>
      by_cases hmem : i ∈ s.reversed
      · simp [step, hfe, hmem]
        exact hwf
      · have hst : step s (.reverse i) = (.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf ee.lines a }) := by
          simp [step, hfe, hmem]
        rw [hst]
        have hfindId : ee.id = i := by
          induction s.journal with
          | nil => simp [findEntry] at hfe
          | cons hd tl ih =>
            simp [findEntry] at hfe
            by_cases heq : hd.id = i
            · simp [heq] at hfe
              rw [← hfe] at heq
              exact heq
            · simp [heq] at hfe
              exact ih hfe
        refine ⟨hwf.1, hwf.2.1, ?_, hwf.2.2.2⟩
        intro j hj
        simp at hj
        rcases hj with rfl | hj
        · have hm : ee ∈ s.journal := findEntry_mem_journal hfe
          have hmemIds : ee.id ∈ ids s.journal := List.mem_map.mpr ⟨ee, hm, rfl⟩
          rw [hfindId] at hmemIds
          exact hmemIds
        · exact hwf.2.2.1 j hj

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  cases c with
  | post e =>
    by_cases hvalid : ValidPost s e
    · have h1 : step s (.post e) = (.ok, { s with journal := s.journal ++ [e], balance := fun a => s.balance a + netOf e.lines a }) := by
        simp [step, hvalid]
      rw [h1]
      intro a
      show s.balance a + netOf e.lines a = s.opening a + activeNet { s with journal := s.journal ++ [e] } a
      rw [activeNet_post (a:=a) hvalid.2.2.2.2.2, hcons a]
      omega
    · simp [step, hvalid]
      exact hcons
  | reverse i =>
    cases hfe : findEntry s.journal i with
    | none =>
      simp [step, hfe]
      exact hcons
    | some ee =>
      by_cases hmem : i ∈ s.reversed
      · simp [step, hfe, hmem]
        exact hcons
      · have hst : step s (.reverse i) = (.ok, { s with reversed := i :: s.reversed, balance := fun a => s.balance a - netOf ee.lines a }) := by
          simp [step, hfe, hmem]
        rw [hst]
        intro a
        have hact := activeNet_rev (a:=a) hwf hfe hmem
        show s.balance a - netOf ee.lines a = s.opening a + activeNet { s with reversed := i :: s.reversed } a
        have : activeNet { s with reversed := i :: s.reversed } a = sumOver s.journal (fun ent => if ent.id ∈ i :: s.reversed then (0:Int) else netOf ent.lines a) := rfl
        rw [this, hact, hcons a]
        omega
end Reversal
