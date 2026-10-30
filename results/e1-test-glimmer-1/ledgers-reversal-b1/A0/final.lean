import Reversal.Spec
import Reversal.Lemmas
namespace Reversal

instance (s : State) (e : Entry) : Decidable (ValidPost s e) := by
  unfold ValidPost; infer_instance
instance (s : State) (i : EntryId) : Decidable (ValidReverse s i) := by
  unfold ValidReverse; infer_instance

def step : Impl := fun s c =>
  match c with
  | .post e =>
    if ValidPost s e then
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a,
                     journal := s.journal ++ [e] })
    else (.rejected, s)
  | .reverse i =>
    if ValidReverse s i then
      match findEntry s.journal i with
      | some e => (.ok, { s with balance := fun a => s.balance a - netOf e.lines a,
                             reversed := i :: s.reversed })
      | none => (.rejected, s)
    else (.rejected, s)

theorem req_post_succeeds : PostSucceeds step := by
  intro s e h; simp [step, h]

theorem req_reverse_succeeds : ReverseSucceeds step := by
  intro s i h; simp [step, h]; cases findEntry s.journal i <;> simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s c h
  cases c
  case post e =>
    simp [step, Valid] at h ⊢
    by_cases hv : ValidPost s e <;> simp [hv] at h ⊢; [exact h hv | rfl]
  case reverse i =>
    simp [step, Valid] at h ⊢
    by_cases hv : ValidReverse s i
    · cases findEntry s.journal i <;> simp at h ⊢; [exact h hv | rfl]
    · simp [hv]

theorem req_post_effects : PostEffects step := by
  intro s e hok; simp [step] at hok
  by_cases hv : ValidPost s e
  · simp [hv] at hok; exact ⟨rfl,rfl,rfl,rfl,fun a=>rfl⟩
  · simp [hv] at hok

theorem req_reverse_effects : ReverseEffects step := by
  intro s i e hok heq; simp [step] at hok
  by_cases hv : ValidReverse s i
  · cases h : findEntry s.journal i
    · contradiction
    · simp at hok; subst heq; exact ⟨rfl,rfl,rfl,by intro x; simp [List.mem_cons]; tauto,fun a=>rfl⟩
  · simp [hv] at hok

theorem req_reverse_once : ReverseOnce step := by
  intro s i hok; simp [step] at hok
  by_cases hv : ValidReverse s i
  · cases h : findEntry s.journal i
    · contradiction
    · have hnot : ¬ ValidReverse {s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed} i := by
        intro h'; exact List.mem_cons_self i s.reversed h'.2
      simp [step, hnot]
  · simp [hv] at hok

theorem req_roundtrip : RoundTrip step := by
  intro s e hpost; simp [step] at hpost
  by_cases hv : ValidPost s e
  · simp [hv] at hpost
    have hrev : ValidReverse {s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e]} e.id := by
      constructor; simp [ids, List.mem_append]
    have hfind : findEntry (s.journal ++ [e]) e.id = some e := by simp [findEntry]
    simp [step, hrev, hfind]
    constructor; rfl; ext a; simp; ring
  · simp [hv] at hpost

theorem req_trial_balance : TrialBalance step := by
  intro s c hwf hok; rcases hwf with ⟨hacc,hids,hrev,hj⟩
  cases c
  case post e =>
    simp [step] at hok
    by_cases hv : ValidPost s e
    · rcases hv with ⟨_,haccL,_,hsum,_,_⟩
      have hsum' : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := by
        induction e.lines with
        | nil => simp [netOf,lineSum]
        | cons l ls ih =>
          simp [netOf,lineSum,sumOver_cons]
          have hmem : l.1 ∈ s.accounts := haccL l (by simp)
          have h1 : sumOver s.accounts (fun a => if l.1 = a then l.2 else 0) = l.2 := by
            rw [sumOver_ite_eq hacc l.1 l.2]; simp [hmem]
          rw [h1,sumOver_add,ih (fun x hx => haccL x (by simp [List.mem_cons] at hx; exact hx.2))]; simp [sumOver_add]
      simp [total,hsum',hsum]
    · simp [hv] at hok
  case reverse i =>
    simp [step] at hok
    by_cases hv : ValidReverse s i
    · cases h : findEntry s.journal i
      · contradiction
      · have hmem : e ∈ s.journal := by
          induction s.journal with
          | nil => simp [findEntry] at h
          | cons e' es ih => simp [findEntry] at h; by_cases he : e'.id = i; [subst he; injection h with h'; subst h'; left; rfl | simp [he] at h; exact List.mem_cons_of_mem_right (ih h) e]
        rcases hj e hmem with ⟨_,hsumE⟩
        have hsum' : sumOver s.accounts (fun a => netOf e.lines a) = lineSum e.lines := by
          induction e.lines with
          | nil => simp [netOf,lineSum]
          | cons l ls ih =>
            simp [netOf,lineSum,sumOver_cons]
            have h1 : sumOver s.accounts (fun a => if l.1 = a then l.2 else 0) = l.2 := by
              rw [sumOver_ite_eq hacc l.1 l.2]; have : l.1 ∈ s.accounts := by have := hj e hmem; rcases this with ⟨haccE,_⟩; exact haccE l (by simp); simp [this]
            rw [h1,sumOver_add,ih]; simp [sumOver_add]
        simp [total,sumOver_sub,hsum',hsumE]
    · simp [hv] at hok

theorem req_well_formed : StaysWellFormed step := by
  intro s c hwf
  rcases hwf with ⟨hacc,hids,hrev,hj⟩
  cases c
  case post e =>
    simp [step]; by_cases hv : ValidPost s e
    · rcases hv with ⟨_,haccL,_,hsum,hid,_⟩
      constructor; simp
      constructor
      · simp [ids]; rw [List.nodup_append_iff]; exact ⟨hids, by intro h'; exact hid (List.mem_of_mem_singleton h')⟩
      constructor
      · intro i hi; simp [List.mem_append] at hi; rcases hi with h|h; [exact hrev i h | subst h; simp]
      · intro e' he'; simp [List.mem_append] at he'; rcases he' with h|h; [exact hj e' h | subst h; exact ⟨haccL,hsum⟩]
    · exact hwf
  case reverse i =>
    simp [step]; by_cases hv : ValidReverse s i
    · cases h : findEntry s.journal i
      · simp
      · simp [h]; constructor; simp; constructor; simp; constructor
        · intro j hj; simp [List.mem_cons] at hj; rcases hj with rfl|h; [exact hv.1 | exact hrev j h]
        · intro e' he'; exact hj e' he'
    · exact hwf

theorem req_consistent : StaysConsistent step := by
  intro s c hwf hcons
  rcases hwf with ⟨hacc,hids,hrev,hj⟩
  cases c
  case post e =>
    simp [step]; by_cases hv : ValidPost s e
    · simp [hv]
      intro a
      have : activeNet {s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e]} a = activeNet s a + netOf e.lines a := by
        simp [activeNet,sumOver_append]
        rcases hv with ⟨_,_,_,_,hid,_⟩
        simp [hid]
      rw [hcons a,this]; rfl
    · simp [hv]; exact hcons
  case reverse i =>
    simp [step]; by_cases hv : ValidReverse s i
    · cases h : findEntry s.journal i
      · simp; exact hcons
      · simp [h]
        intro a
        have hmem : e ∈ s.journal := by
          induction s.journal with
          | nil => simp [findEntry] at h
          | cons e' es ih => simp [findEntry] at h; by_cases he : e'.id = i; [subst he; injection h with h'; subst h'; left; rfl | simp [he] at h; exact List.mem_cons_of_mem_right (ih h) e]
        have hsumE : lineSum e.lines = 0 := (hj e hmem).2
        simp [Consistent,activeNet]
        rw [hcons a]
        have : activeNet {s with balance := fun a => s.balance a - netOf e.lines a, reversed := i :: s.reversed} a = activeNet s a - netOf e.lines a := by
          simp [activeNet]
          have : (fun e' => if e'.id ∈ i :: s.reversed then 0 else netOf e'.lines a) = (fun e' => if e'.id ∈ s.reversed then 0 else netOf e'.lines a - if e'.id = i then netOf e.lines a else 0) := by
            funext e'; by_cases hi : e'.id = i; [simp [hi]; simp [List.mem_cons]; tauto | simp [hi]; simp [List.mem_cons]; tauto]
          rw [this,sumOver_add]; simp [sumOver_sub]
        rw [this]; ring
    · simp [hv]; exact hcons

end Reversal
