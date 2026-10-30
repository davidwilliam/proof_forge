import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance instDecidableValidPost (s : State) (e : Entry) : Decidable (ValidPost s e) := by unfold ValidPost; infer_instance

theorem findEntry_none_iff {j : List Entry} {i : EntryId} : findEntry j i = none ↔ i ∉ ids j := by
  induction j with
  | nil => simp [findEntry, ids]
  | cons hd tl ih => simp only [findEntry, ids]; by_cases he : hd.id = i <;> simp [he, ih]

theorem mem_ids_of_some {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : i ∈ ids j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih => by_cases heq : hd.id = i
    · simp [ids, heq]
    · simp [findEntry, heq] at h; simp [ids, heq, ih h]

theorem mem_of_some {j : List Entry} {i : EntryId} {e : Entry} (h : findEntry j i = some e) : e ∈ j := by
  induction j with
  | nil => simp [findEntry] at h
  | cons hd tl ih => by_cases heq : hd.id = i
    · simp [findEntry, heq] at h; rw [h]; simp
    · simp [findEntry, heq] at h; exact List.mem_cons_of_mem hd (ih h)

theorem findEntry_append_new {j : List Entry} {e : Entry} (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by
  induction j with
  | nil => simp [findEntry]
  | cons hd tl ih =>
    have hhd : hd.id ≠ e.id := fun heq => h (by simp [ids, heq])
    have h2 : e.id ∉ ids tl := fun hm => h (by simp [ids, hm])
    simp [findEntry, Ne.symm hhd, ih h2]

theorem nodup_append_singleton {l : List Nat} {a : Nat} (hl : l.Nodup) (ha : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have h1 : ¬ hd ∈ tl := (List.nodup_cons.mp hl).1
    have h2 : tl.Nodup := (List.nodup_cons.mp hl).2
    have ha' : a ∉ tl := fun hm => ha (List.mem_cons_of_mem hd hm)
    have ih' := ih h2 ha'
    have h3 : ¬ hd ∈ tl ++ [a] := by intro hm; rw [List.mem_append] at hm; cases hm with
      | inl h => exact h1 h
      | inr h => simp at h; rw [h] at ha; exact ha (List.mem_cons_self hd tl)
    exact List.nodup_cons.mpr ⟨h3, ih'⟩

theorem sumZero {α : Type} (l : List α) : sumOver l (fun _ => (0:Int)) = 0 := by induction l with | nil => rfl | cons _ _ ih => simp [sumOver_cons, ih]

theorem netSumZero (acc : List AccountId) (hnodup : acc.Nodup) (ls : List Line) (hcover : ∀ l ∈ ls, l.1 ∈ acc) : sumOver acc (fun a => netOf ls a) = lineSum ls := by
  induction ls with
  | nil => simp [netOf, lineSum, sumZero]
  | cons hd tl ih =>
    have hc_tl : ∀ l ∈ tl, l.1 ∈ acc := fun l hm => hcover l (List.mem_cons_of_mem hd hm)
    have ih' := ih hc_tl
    have h1 : ∀ a, netOf (hd :: tl) a = (if hd.1 = a then hd.2 else (0:Int)) + netOf tl a := fun a => rfl
    have h2 : sumOver acc (fun a => netOf (hd :: tl) a) = sumOver acc (fun a => (if hd.1 = a then hd.2 else (0:Int)) + netOf tl a) := sumOver_congr _ _ (fun a _ => h1 a)
    rw [h2, sumOver_add, ih']
    have hswap : ∀ a, (if hd.1 = a then (hd.2:Int) else 0) = (if a = hd.1 then hd.2 else 0) := by intro a; by_cases ha : a = hd.1 <;> by_cases hb : hd.1 = a <;> simp_all
    have h4 : sumOver acc (fun a => if hd.1 = a then hd.2 else (0:Int)) = sumOver acc (fun a => if a = hd.1 then hd.2 else (0:Int)) := sumOver_congr _ _ (fun a _ => hswap a)
    rw [h4, sumOver_ite_eq hnodup hd.1 hd.2]
    have hm : hd.1 ∈ acc := hcover hd (by simp)
    simp [hm, lineSum, sumOver_cons]

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed })
    else (.rejected, s)
  | .reverse i =>
    match findEntry s.journal i with
    | none => (.rejected, s)
    | some e => if i ∈ s.reversed then (.rejected, s) else (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] })

private theorem post_ok_valid {s : State} {e : Entry} (h : (step s (.post e)).1 = .ok) : ValidPost s e := by unfold step at h; by_cases hv : ValidPost s e <;> simp [hv] at h ⊢; exact hv
private theorem rev_ok_not_rev {s : State} {i : EntryId} {e : Entry} (hfind : findEntry s.journal i = some e) (h : (step s (.reverse i)).1 = .ok) : i ∉ s.reversed := by unfold step at h; simp [hfind] at h; intro hm; simp [hm] at h

theorem req_post_succeeds : PostSucceeds step := by intro s e h; simp [step, h]
theorem req_reverse_succeeds : ReverseSucceeds step := by intro s i h; unfold step; have hne : findEntry s.journal i ≠ none := by intro hnone; have : i ∉ ids s.journal := findEntry_none_iff.mp hnone; exact h.2 this; cases he : findEntry s.journal i with | none => contradiction | some e => simp [he, h.2]
theorem req_invalid_noop : InvalidNoop step := by
  intro s c h; cases c with
  | post e => have hn : ¬ValidPost s e := fun hp => h hp; simp [step, hn]
  | reverse i =>
    simp only [Valid] at h; show step s (.reverse i) = (Outcome.rejected, s)
    cases he : findEntry s.journal i with
    | none => simp [step, he]
    | some e => simp [step, he]; by_cases hi : i ∈ s.reversed
      · simp [hi]
      · have hmem : i ∈ ids s.journal := mem_ids_of_some he; exfalso; apply h; exact ⟨hmem, hi⟩

theorem req_post_effects : PostEffects step := by
  intro s e hok; have hv : ValidPost s e := post_ok_valid hok
  have hstep : step s (.post e) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed }) := by simp [step, hv]
  exact ⟨by rw [hstep], by rw [hstep], by rw [hstep], by rw [hstep], by intro a; rw [hstep]⟩

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok hfind; have hi : i ∉ s.reversed := rev_ok_not_rev hfind hok
  have hstep : step s (.reverse i) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] }) := by simp [step, hfind, hi]
  exact ⟨by rw [hstep], by rw [hstep], by rw [hstep], by intro x; rw [hstep]; simp [List.mem_append, or_comm], by intro a; rw [hstep]⟩

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok
  have h_none : findEntry s.journal i ≠ none := by intro hc; have hst : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, hc]; rw [hst] at hok; simp at hok
  obtain ⟨e, he⟩ : ∃ e, findEntry s.journal i = some e := by cases hc : findEntry s.journal i with | none => exact absurd hc h_none | some e => exact ⟨e, rfl⟩
  have hi : i ∉ s.reversed := by by_contra hmem; have hst : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, he, hmem]; rw [hst] at hok; simp at hok
  have h1 : step s (.reverse i) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] }) := by simp [step, he, hi]
  rw [h1]; have hmem2 : i ∈ s.reversed ++ [i] := by simp; simp [step, he, hmem2]

theorem req_roundtrip : RoundTrip step := by
  intro s e hok; have hv : ValidPost s e := post_ok_valid hok; have hfind : findEntry (s.journal ++ [e]) e.id = some e := findEntry_append_new hv.2.2.2.2.1
  have hs1 : step s (.post e) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed }) := by simp [step, hv]
  have hs1_snd : (step s (.post e)).2 = { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed } := by rw [hs1]
  have hstep2 : step (step s (.post e)).2 (.reverse e.id) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a - netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed ++ [e.id] }) := by rw [hs1_snd]; simp [step, hfind, hv.2.2.2.2.2]
  constructor; · rw [hstep2] ; · have hbal : (step (step s (.post e)).2 (.reverse e.id)).2.balance = fun a => s.balance a + netOf e.lines a - netOf e.lines a := by rw [hstep2]; rfl; rw [hbal]; funext a; omega

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok; cases c with
  | post e =>
    have hv : ValidPost s e := post_ok_valid hok; have hstep : step s (.post e) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed }) := by simp [step, hv]
    have heq : (step s (.post e)).2 = { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed } := by rw [hstep]
    rw [heq]; show total { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed } = total s
    unfold total; have hadd : sumOver s.accounts (fun a => s.balance a + netOf e.lines a) = sumOver s.accounts s.balance + sumOver s.accounts (fun a => netOf e.lines a) := by rw [← sumOver_add]
    have hsum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := netSumZero s.accounts hwf.1 e.lines hv.2.1
    rw [hadd, hsum, hv.2.2.2.1, Int.add_zero]
  | reverse i =>
    cases he : findEntry s.journal i with
    | none => have hst : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, he]; have : (step s (.reverse i)).1 = Outcome.rejected := by rw [hst]; rw [this] at hok; simp at hok
    | some e =>
      by_cases hi : i ∈ s.reversed
      · have hst : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, he, hi]; have : (step s (.reverse i)).1 = Outcome.rejected := by rw [hst]; rw [this] at hok; simp at hok
      · have hstep : step s (.reverse i) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] }) := by simp [step, he, hi]
        have heq : (step s (.reverse i)).2 = { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] } := by rw [hstep]
        rw [heq]; show total { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] } = total s
        unfold total; have he_mem : e ∈ s.journal := mem_of_some he; have hprop := hwf.2.2.2 e he_mem
        have hsub : sumOver s.accounts (fun a => s.balance a - netOf e.lines a) = sumOver s.accounts s.balance - sumOver s.accounts (fun a => netOf e.lines a) := by rw [← sumOver_sub]
        have hsum : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := netSumZero s.accounts hwf.1 e.lines hprop.1
        rw [hsub, hsum, hprop.2, Int.sub_zero]

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf; cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hstep : step s (.post e) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed }) := by simp [step, hv]
      have heq : (step s (.post e)).2 = { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed } := by rw [hstep]
      rw [heq]; have hids : ids (s.journal ++ [e]) = ids s.journal ++ [e.id] := by simp [ids]
      refine ⟨hwf.1, ?_, ?_, ?_⟩
      · rw [hids]; exact nodup_append_singleton hwf.2.1 hv.2.2.2.2.1
      · intro i hi; have hmem : i ∈ ids s.journal := hwf.2.2.1 i hi; rw [hids]; exact List.mem_append_left _ hmem
      · intro e' he'; rw [List.mem_append] at he'; rcases he' with hm | hm
        · exact hwf.2.2.2 e' hm
        · simp at hm; rw [hm]; exact ⟨hv.2.1, hv.2.2.2.1⟩
    · have hstep : step s (.post e) = (.rejected, s) := by simp [step, hv]
      have heq : (step s (.post e)).2 = s := by rw [hstep]
      rw [heq]; exact hwf
  | reverse i =>
    cases he : findEntry s.journal i with
    | none => have hstep : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, he]; have heq : (step s (.reverse i)).2 = s := by rw [hstep]; rw [heq]; exact hwf
    | some e => by_cases hi : i ∈ s.reversed
      · have hstep : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, he, hi]; have heq : (step s (.reverse i)).2 = s := by rw [hstep]; rw [heq]; exact hwf
      · have hstep : step s (.reverse i) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] }) := by simp [step, he, hi]
        have heq : (step s (.reverse i)).2 = { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] } := by rw [hstep]
        rw [heq]; refine ⟨hwf.1, hwf.2.1, ?_, fun e' he' => hwf.2.2.2 e' he'⟩
        intro j hj; rw [List.mem_append] at hj; cases hj with | inl h => exact hwf.2.2.1 j h | inr h => simp at h; rw [h]; exact mem_ids_of_some he

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons; intro a; cases c with
  | post e =>
    by_cases hv : ValidPost s e
    · have hstep : step s (.post e) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed }) := by simp [step, hv]
      have heq : (step s (.post e)).2 = { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed } := by rw [hstep]
      rw [heq]
      have hactive : activeNet { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e], reversed := s.reversed } a = activeNet s a + netOf e.lines a := by unfold activeNet; rw [sumOver_append]; simp [sumOver_cons, hv.2.2.2.2.2]
      change (fun a => s.balance a + netOf e.lines a) a = _ + _; simp only [hactive]; have := hcons a; omega
    · have hstep : step s (.post e) = (.rejected, s) := by simp [step, hv]
      have heq : (step s (.post e)).2 = s := by rw [hstep]
      rw [heq]; exact hcons a
  | reverse i =>
    cases he : findEntry s.journal i with
    | none => have hstep : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, he]; have heq : (step s (.reverse i)).2 = s := by rw [hstep]; rw [heq]; exact hcons a
    | some e => by_cases hi : i ∈ s.reversed
      · have hstep : step s (.reverse i) = (Outcome.rejected, s) := by simp [step, he, hi]; have heq : (step s (.reverse i)).2 = s := by rw [hstep]; rw [heq]; exact hcons a
      · have hstep : step s (.reverse i) = (.ok, { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] }) := by simp [step, he, hi]
        have heq : (step s (.reverse i)).2 = { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] } := by rw [hstep]
        rw [heq]
        have hactive : activeNet { accounts := s.accounts, opening := s.opening, balance := fun a => s.balance a - netOf e.lines a, journal := s.journal, reversed := s.reversed ++ [i] } a = activeNet s a - netOf e.lines a := by
          unfold activeNet; induction s.journal generalizing i e with
          | nil => simp [findEntry] at he
          | cons hd tl ih =>
            simp only [sumOver_cons]
            by_cases heq : hd.id = i
            · simp [findEntry, heq] at he; have he_eq : hd = e := by cases he; rfl; subst he_eq; simp [hi]
              have hnd : (ids (e :: tl)).Nodup := hwf.2.1; rw [List.nodup_cons] at hnd; have hnot_tl : i ∉ ids tl := hnd.1
              have htl_eq : sumOver tl (fun e' => if e'.id ∈ s.reversed ++ [i] then (0:Int) else netOf e'.lines a) = sumOver tl (fun e' => if e'.id ∈ s.reversed then (0:Int) else netOf e'.lines a) := by
                apply sumOver_congr; intro e' he'; have hid : e'.id ≠ i := by intro heq2; have : e'.id ∈ ids tl := by induction tl with | nil => simp at he' | cons hd2 tl2 ih2 => simp [ids] at he' ⊢; rcases he' with rfl | hmem; · exact Or.inl rfl; · exact Or.inr (ih2 hmem); rw [heq2] at this; exact hnot_tl this; simp [hid]
              rw [htl_eq]
            · simp [findEntry, heq] at he; have hwf_tl : WellFormed { accounts := s.accounts, opening := s.opening, balance := s.balance, journal := tl, reversed := s.reversed } := ⟨hwf.1, (List.nodup_cons.mp hwf.2.1).2, fun j hj => hwf.2.2.1 j (List.mem_cons_of_mem hd hj), fun e' he' => hwf.2.2.2 e' (List.mem_cons_of_mem hd he')⟩
              have ih' := ih hwf_tl he; have h1 : (if hd.id ∈ s.reversed ++ [i] then (0:Int) else netOf hd.lines a) = (if hd.id ∈ s.reversed then (0:Int) else netOf hd.lines a) := by simp [List.mem_append, heq]
              rw [h1, ih']; omega
        change (fun a => s.balance a - netOf e.lines a) a = _ + _; simp only [hactive]; have := hcons a; omega

end Reversal
