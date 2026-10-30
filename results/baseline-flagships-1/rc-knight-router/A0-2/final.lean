import OrderRouter.Spec
import OrderRouter.Lemmas

namespace OrderRouter

def step : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    (⟨s.nParents + 1, upd s.parents s.nParents ⟨q, f, 0, 0⟩, s.nChildren, s.children⟩, [])
  | .route id liq =>
    if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      (⟨s.nParents,
        upd s.parents id ⟨(s.parents id).qty, (s.parents id).flag, (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent), (s.parents id).cum⟩,
        s.nChildren + 1,
        upd s.children s.nChildren ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩⟩,
       [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩])
    else (s, [])
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      (⟨s.nParents,
        upd s.parents (s.children k).parent ⟨((s.parents (s.children k).parent).qty), ((s.parents (s.children k).parent).flag), ((s.parents (s.children k).parent).sent), ((s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done))⟩,
        s.nChildren,
        upd s.children k ⟨(s.children k).parent, (s.children k).qty, (s.children k).done + min q ((s.children k).qty - (s.children k).done)⟩⟩, [])
    else (s, [])

theorem upd_same_thm {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by
  unfold upd
  simp

theorem upd_other_thm {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) : upd f k v j = f j := by
  unfold upd
  simp [h]

theorem record_nil_thm (t : Truth) : t.record ([] : List Child) = t := by
  cases t with
  | mk nOrders qty kids =>
    simp [Truth.record]

theorem sentFor_zero_of_all_ne_thm (l : List Kid) (pid : Nat) (h : ∀ c ∈ l, c.parent ≠ pid) :
    sentFor l pid = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : a.parent ≠ pid := h a List.mem_cons_self
    have ihh := ih (fun c hc => h c (List.mem_cons_of_mem a hc))
    simp only [sentFor_cons, ha, ite_false, ihh, Nat.add_zero]

theorem execFor_zero_of_all_ne_thm (l : List Kid) (pid : Nat) (h : ∀ c ∈ l, c.parent ≠ pid) :
    execFor l pid = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : a.parent ≠ pid := h a List.mem_cons_self
    have ihh := ih (fun c hc => h c (List.mem_cons_of_mem a hc))
    simp only [execFor_cons, ha, ite_false, ihh, Nat.add_zero]

theorem sentFor_fresh_thm (l : List Kid) (n : Nat) (h : ∀ c ∈ l, c.parent < n) :
    sentFor l n = 0 := by
  apply sentFor_zero_of_all_ne_thm
  intro c hc
  have hh := h c hc
  omega

theorem execFor_fresh_thm (l : List Kid) (n : Nat) (h : ∀ c ∈ l, c.parent < n) :
    execFor l n = 0 := by
  apply execFor_zero_of_all_ne_thm
  intro c hc
  have hh := h c hc
  omega

theorem get_some_lt_thm (l : List Kid) (j : Nat) (c : Kid) (h : l[j]? = some c) : j < l.length := by
  induction l generalizing j with
  | nil =>
    cases j <;> simp_all
  | cons b bs ih =>
    cases j with
    | zero => simp
    | succ j =>
      have h2 : bs[j]? = some c := by simpa using h
      have hh := ih j h2
      simp only [List.length_cons]
      omega

theorem append_get_lt_thm (l : List Kid) (a : Kid) (j : Nat) (hj : j < l.length) :
    (l ++ [a])[j]? = l[j]? := by
  induction l generalizing j with
  | nil =>
    simp only [List.length_nil] at hj
    omega
  | cons b bs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj2 : j < bs.length := by simp only [List.length_cons] at hj; omega
      simp only [List.getElem?_cons_succ]
      exact ih j hj2

theorem get_append_single_eq_thm (l : List Kid) (a : Kid) : (l ++ [a])[l.length]? = some a := by
  simp

theorem set_get_ne_eq_thm (l : List Kid) (k j : Nat) (a : Kid) (hne : j ≠ k) :
    (l.set k a)[j]? = l[j]? := by
  induction l generalizing k j with
  | nil =>
    cases k <;> cases j <;> simp_all
  | cons b bs ih =>
    cases k with
    | zero =>
      cases j with
      | zero => contradiction
      | succ j => rfl
    | succ k =>
      cases j with
      | zero => rfl
      | succ j =>
        have hne2 : j ≠ k := by omega
        simp only [List.getElem?_cons_succ, List.set_cons_succ]
        exact ih k j hne2

theorem get_set_eq_proof_thm (l : List Kid) (k : Nat) (a : Kid) (hk : k < l.length) :
    (l.set k a)[k]? = some a := by
  induction l generalizing k with
  | nil =>
    simp only [List.length_nil] at hk
    omega
  | cons b bs ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk2 : k < bs.length := by simp only [List.length_cons] at hk; omega
      simp only [List.set_cons_succ, List.getElem?_cons_succ]
      exact ih k hk2

theorem mem_set_of_mem_helper_thm (l : List Kid) (k : Nat) (a : Kid) (c : Kid) (h : c ∈ l.set k a) :
    c = a ∨ c ∈ l := by
  induction l generalizing k with
  | nil =>
    simp at h
  | cons b bs ih =>
    cases k with
    | zero =>
      simp at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    | succ k =>
      simp at h
      rcases h with rfl | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · have hh := ih k h
        rcases hh with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons.mpr (Or.inr hm))

theorem exists_of_lt_thm (l : List Kid) (kk : Nat) (h : kk < l.length) : ∃ c, l[kk]? = some c := by
  induction l generalizing kk with
  | nil =>
    simp only [List.length_nil] at h
    omega
  | cons a as ih =>
    cases kk with
    | zero => exact ⟨a, rfl⟩
    | succ kk =>
      have h2 : kk < as.length := by simp only [List.length_cons] at h; omega
      obtain ⟨c, hc⟩ := ih kk h2
      exact ⟨c, by simpa using hc⟩

theorem get_none_of_le_thm (l : List Kid) (kk : Nat) (h : l.length ≤ kk) : l[kk]? = none := by
  induction l generalizing kk with
  | nil => simp
  | cons a as ih =>
    cases kk with
    | zero =>
      simp only [List.length_cons] at h
      omega
    | succ kk =>
      have h2 : as.length ≤ kk := by simp only [List.length_cons] at h; omega
      simp only [List.getElem?_cons_succ]
      exact ih kk h2

theorem set_length_thm (l : List Kid) (k : Nat) (a : Kid) : (l.set k a).length = l.length := by
  induction l generalizing k with
  | nil =>
    cases k with
    | zero => simp
    | succ k => simp
  | cons b bs ih =>
    cases k with
    | zero => simp
    | succ k => simp [ih k]

theorem step_route_snd_thm (b : Build) (s : State) (id liq : Nat) :
    (step b s (Event.route id liq)).2 =
      if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)
      then [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else [] := by
  unfold step
  by_cases h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)
  · simp [h]
  · simp [h]

theorem step_parent_snd_thm (b : Build) (s : State) (q : Nat) (f : Bool) :
    (step b s (Event.parent q f)).2 = ([] : List Child) := by
  unfold step
  simp

theorem step_ack_snd_thm (b : Build) (s : State) (n : Nat) :
    (step b s (Event.ack n)).2 = ([] : List Child) := by
  unfold step
  simp

theorem step_fill_snd_thm (b : Build) (s : State) (k q : Nat) :
    (step b s (Event.fill k q)).2 = ([] : List Child) := by
  unfold step
  by_cases h : k < s.nChildren <;> simp [h]

def Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ pid, pid < x.tr.nOrders → (x.st.parents pid).qty = x.tr.qty pid) ∧
  (∀ pid, (x.st.parents pid).sent = x.tr.sent pid) ∧
  (∀ pid, (x.st.parents pid).cum = x.tr.exec pid) ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ k c, x.tr.kids[k]? = some c → x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
  (∀ c ∈ x.tr.kids, c.parent < x.tr.nOrders) ∧
  (∀ pid, pid < x.st.nParents → (x.st.parents pid).sent ≤ (x.st.parents pid).qty)

theorem inv_start_thm : Inv start := by
  refine And.intro rfl (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro rfl (And.intro ?_ (And.intro ?_ ?_))))))
  · intro pid h
    simp [start, Truth.empty] at h
  · intro pid
    simp [start, Truth.empty, Truth.sent, init]
  · intro pid
    simp [start, Truth.empty, Truth.exec, init]
  · intro k c h
    simp [start, Truth.empty] at h
  · intro c h
    simp [start, Truth.empty] at h
  · intro pid h
    simp [start, init] at h

theorem inv_step_thm (b : Build) (x : Sys) (e : Event) (h : Inv x) : Inv (advance step b x e) := by
  obtain ⟨hNP, hQty, hSent, hCum, hNC, hChild, hLt, hLe⟩ := h
  cases e with
  | parent q f =>
    have hStepParent : step b x.st (Event.parent q f) =
        (⟨x.st.nParents + 1, upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩, x.st.nChildren, x.st.children⟩, []) := by
      unfold step; simp
    have hObsParent : x.tr.observe (Event.parent q f) =
        ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩ := rfl
    have hEq : advance step b x (Event.parent q f) =
        ⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents ⟨q, f, 0, 0⟩, x.st.nChildren, x.st.children⟩,
         ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ := by
      simp only [advance, hStepParent, hObsParent, record_nil_thm]
    rw [hEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · intro pid hid
      by_cases heq : pid = x.tr.nOrders
      · have hEqP : pid = x.st.nParents := by omega
        have e1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).qty = q := by
          rw [hEqP, upd_same_thm]
        have e2 : (upd x.tr.qty x.tr.nOrders q pid) = q := by rw [heq, upd_same_thm]
        have g1 : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).qty = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).qty := rfl
        have g2 : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).tr.qty pid) = (upd x.tr.qty x.tr.nOrders q pid) := rfl
        rw [g1, g2, e1, e2]
      · have hlt : pid < x.tr.nOrders := by omega
        have hne : pid ≠ x.st.nParents := by omega
        have e1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).qty = (x.st.parents pid).qty := by
          rw [upd_other_thm _ _ _ _ hne]
        have e2 : (upd x.tr.qty x.tr.nOrders q pid) = x.tr.qty pid := by
          rw [upd_other_thm _ _ _ _ heq]
        have g1 : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).qty = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).qty := rfl
        have g2 : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).tr.qty pid) = (upd x.tr.qty x.tr.nOrders q pid) := rfl
        rw [g1, g2, e1, e2]
        exact hQty pid hlt
    · intro pid
      by_cases heq : pid = x.st.nParents
      · have e1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).sent = (0 : Nat) := by
          rw [heq, upd_same_thm]
        have hzero : sentFor x.tr.kids pid = 0 := by
          rw [heq, ← hNP]
          exact sentFor_fresh_thm x.tr.kids x.st.nParents (fun c hc => by have := hLt c hc; omega)
        have g : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).sent = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).sent := rfl
        have g2 : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).tr.sent pid) = sentFor x.tr.kids pid := rfl
        rw [g, g2, e1, hzero]
      · have e1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).sent = (x.st.parents pid).sent := by
          rw [upd_other_thm _ _ _ _ heq]
        have g : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).sent = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).sent := rfl
        have g2 : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).tr.sent pid) = sentFor x.tr.kids pid := rfl
        rw [g, g2, e1]
        exact hSent pid
    · intro pid
      by_cases heq : pid = x.st.nParents
      · have e1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).cum = (0 : Nat) := by
          rw [heq, upd_same_thm]
        have hzero : execFor x.tr.kids pid = 0 := by
          rw [heq, ← hNP]
          exact execFor_fresh_thm x.tr.kids x.st.nParents (fun c hc => by have := hLt c hc; omega)
        have g : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).cum = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).cum := rfl
        have g2 : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).tr.exec pid) = execFor x.tr.kids pid := rfl
        rw [g, g2, e1, hzero]
      · have e1 : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).cum = (x.st.parents pid).cum := by
          rw [upd_other_thm _ _ _ _ heq]
        have g : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).cum = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).cum := rfl
        have g2 : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).tr.exec pid) = execFor x.tr.kids pid := rfl
        rw [g, g2, e1]
        exact hCum pid
    · exact hNC
    · intro kk cc hjj
      exact hChild kk cc hjj
    · intro c hc
      have hh := hLt c hc
      omega
    · intro pid hid
      by_cases heq : pid = x.st.nParents
      · have eS : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).sent = (0 : Nat) := by
          rw [heq, upd_same_thm]
        have eQ : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).qty = q := by
          rw [heq, upd_same_thm]
        have gS : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).sent = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).sent := rfl
        have gQ : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).qty = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).qty := rfl
        rw [gS, gQ, eS, eQ]
        omega
      · have e : (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid) = x.st.parents pid := by
          rw [upd_other_thm _ _ _ _ heq]
        have gS : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).sent = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).sent := rfl
        have gQ : ((⟨⟨x.st.nParents + 1, upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec), x.st.nChildren, x.st.children⟩, ⟨x.tr.nOrders + 1, upd x.tr.qty x.tr.nOrders q, x.tr.kids⟩⟩ : Sys).st.parents pid).qty = (upd x.st.parents x.st.nParents (⟨q, f, 0, 0⟩ : ParentRec) pid).qty := rfl
        rw [gS, gQ, e]
        exact hLe pid (by omega)
  | route rid rliq =>
    by_cases hcond : rid < x.st.nParents ∧ 0 < min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent)
    · have hidSt : rid < x.st.nParents := hcond.1
      have hidTr : rid < x.tr.nOrders := by omega
      have hq : (x.st.parents rid).qty = x.tr.qty rid := hQty rid hidTr
      have hStepRoute : step b x.st (Event.route rid rliq) =
          (⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩,
              x.st.nChildren + 1,
              upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩,
           [⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent)⟩]) := by
        unfold step; simp [hcond]
      have hObsRoute : x.tr.observe (Event.route rid rliq) = x.tr := rfl
      have hEq : advance step b x (Event.route rid rliq) =
          ⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩,
              x.st.nChildren + 1,
              upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩,
           ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ := by
        simp only [advance, hStepRoute, hObsRoute, Truth.record, List.map_cons, List.map_nil]
      rw [hEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hNP
      · intro j hj
        by_cases heq : j = rid
        · have e1 : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).qty = (x.st.parents rid).qty := by
            rw [heq, upd_same_thm]
          have g1 : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).st.parents j).qty = (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).qty := rfl
          have g2 : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).tr.qty j) = x.tr.qty j := rfl
          rw [g1, g2, e1, heq]
          exact hq
        · have e1 : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).qty = (x.st.parents j).qty := by
            rw [upd_other_thm _ _ _ _ heq]
          have g1 : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).st.parents j).qty = (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).qty := rfl
          have g2 : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).tr.qty j) = x.tr.qty j := rfl
          rw [g1, g2, e1]
          exact hQty j hj
      · intro j
        have hOld : (x.st.parents j).sent = sentFor x.tr.kids j := hSent j
        by_cases heq : j = rid
        · have hUpd : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).sent = (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent) := by
            rw [heq, upd_same_thm]
          have hApp : sentFor (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]) j = sentFor x.tr.kids j + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent) := by
            subst heq
            simp
          have hOld2 : (x.st.parents rid).sent = sentFor x.tr.kids rid := hSent rid
          have hChain : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).sent = sentFor (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]) j := by
            rw [hUpd, hApp, heq, hOld2]
          exact hChain
        · have hUpd : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).sent = (x.st.parents j).sent := by
            rw [upd_other_thm _ _ _ _ heq]
          have hApp : sentFor (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]) j = sentFor x.tr.kids j := by
            simp [show rid ≠ j from fun h => heq h.symm]
          have hChain : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).sent = sentFor (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]) j := by
            rw [hUpd, hApp, hOld]
          exact hChain
      · intro j
        by_cases heq : j = rid
        · have hUpd : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).cum = (x.st.parents rid).cum := by
            rw [heq, upd_same_thm]
          have hOld : (x.st.parents rid).cum = execFor x.tr.kids rid := hCum rid
          have hApp : execFor x.tr.kids rid = execFor (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]) rid := by
            simp
          have hChain : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).cum = execFor (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]) j := by
            rw [hUpd, heq, hOld, hApp]
          exact hChain
        · have hUpdRec : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j) = x.st.parents j := by
            rw [upd_other_thm _ _ _ _ heq]
          have hUpd : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).cum = (x.st.parents j).cum := by
            rw [hUpdRec]
          have hOld : (x.st.parents j).cum = execFor x.tr.kids j := hCum j
          have hApp : execFor x.tr.kids j = execFor (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]) j := by
            simp [show rid ≠ j from fun h => heq h.symm]
          have hChain : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).cum = execFor (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]) j := by
            rw [hUpd, hOld, hApp]
          exact hChain
      · simp [hNC]
      · intro jj cc hjj
        by_cases hlt : jj < x.tr.kids.length
        · have hget : (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)])[jj]? = x.tr.kids[jj]? :=
            append_get_lt_thm _ _ _ hlt
          have hjj2 : x.tr.kids[jj]? = some cc := by rw [← hget]; exact hjj
          have hch := hChild jj cc hjj2
          have hne : jj ≠ x.st.nChildren := by omega
          have hUpd : (upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec) jj) = x.st.children jj := by
            rw [upd_other_thm _ _ _ _ hne]
          have g : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).st.children jj) = (upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec) jj) := rfl
          rw [g, hUpd, hch]
        · have hlenLt : jj < (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]).length :=
            get_some_lt_thm _ _ _ hjj
          have hlenEq : (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]).length = x.tr.kids.length + 1 := by simp
          have heqK : jj = x.tr.kids.length := by omega
          have hSing : (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)])[x.tr.kids.length]? = some (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid) :=
            get_append_single_eq_thm _ _
          have hjj2 : (x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)])[x.tr.kids.length]? = some cc := by
            rw [← heqK]; exact hjj
          have hEqOpt : (some cc : Option Kid) = some (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid) :=
            hjj2.symm.trans hSing
          have hcc : cc = (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid) := by
            cases hEqOpt; rfl
          have hJJ : jj = x.st.nChildren := by omega
          have hUpd : (upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec) jj) = (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec) := by
            rw [hJJ, upd_same_thm]
          have g : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).st.children jj) = (upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec) jj) := rfl
          rw [g, hUpd, hcc]
      · intro c hc
        simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | hc
        · exact hLt c hc
        · rw [hc]; exact hidTr
      · intro j hj
        by_cases heq : j = rid
        · have eS : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).sent = (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent) := by
            rw [heq, upd_same_thm]
          have eQ : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).qty = (x.st.parents rid).qty := by
            rw [heq, upd_same_thm]
          have gS : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).st.parents j).sent = (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).sent := rfl
          have gQ : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).st.parents j).qty = (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).qty := rfl
          rw [gS, gQ, eS, eQ]
          have hleOld := hLe rid hidSt
          have hcle : min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent) ≤ (x.st.parents rid).qty - (x.st.parents rid).sent :=
            Nat.min_le_right _ _
          omega
        · have eRec : (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j) = x.st.parents j := by
            rw [upd_other_thm _ _ _ _ heq]
          have gS : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).st.parents j).sent = (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).sent := rfl
          have gQ : ((⟨⟨x.st.nParents, upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩, x.st.nChildren + 1, upd x.st.children x.st.nChildren (⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : ChildRec)⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids ++ [(⟨rid, min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), 0⟩ : Kid)]⟩⟩ : Sys).st.parents j).qty = (upd x.st.parents rid ⟨(x.st.parents rid).qty, (x.st.parents rid).flag, (x.st.parents rid).sent + min rliq ((x.st.parents rid).qty - (x.st.parents rid).sent), (x.st.parents rid).cum⟩ j).qty := rfl
          rw [gS, gQ, eRec]
          exact hLe j hj
    · have hStepRouteNeg : step b x.st (Event.route rid rliq) = (x.st, []) := by
        unfold step; simp [hcond]
      have hObsRouteNeg : x.tr.observe (Event.route rid rliq) = x.tr := rfl
      have hAdv : advance step b x (Event.route rid rliq) = Sys.mk x.st x.tr := by
        simp only [advance, hStepRouteNeg, hObsRouteNeg, record_nil_thm]
      rw [hAdv]
      exact ⟨hNP, hQty, hSent, hCum, hNC, hChild, hLt, hLe⟩
  | ack n =>
    have hStepAck : step b x.st (Event.ack n) = (x.st, []) := by
      unfold step; simp
    have hObsAck : x.tr.observe (Event.ack n) = x.tr := rfl
    have hAdv : advance step b x (Event.ack n) = Sys.mk x.st x.tr := by
      simp only [advance, hStepAck, hObsAck, record_nil_thm]
    rw [hAdv]
    exact ⟨hNP, hQty, hSent, hCum, hNC, hChild, hLt, hLe⟩
  | fill k q =>
    by_cases hcond : k < x.st.nChildren
    · have hLen : k < x.tr.kids.length := by omega
      obtain ⟨ctruth, hctruth⟩ := exists_of_lt_thm x.tr.kids k hLen
      have hchEq := hChild k ctruth hctruth
      have hStateChild : x.st.children k = (⟨ctruth.parent, ctruth.qty, ctruth.done⟩ : ChildRec) := hchEq
      have hStepFill : step b x.st (Event.fill k q) =
          (⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩,
              x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, []) := by
        unfold step; simp [hcond, hStateChild]
      have hObsFill : x.tr.observe (Event.fill k q) =
          ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩ := by
        simp [Truth.observe, hctruth]
      have hEq : advance step b x (Event.fill k q) =
          ⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩,
              x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩,
           ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ := by
        simp only [advance, hStepFill, hObsFill, record_nil_thm]
      rw [hEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hNP
      · intro j hj
        have hjOld : j < x.tr.nOrders := hj
        by_cases heq : j = ctruth.parent
        · have e0 : (upd x.st.parents ctruth.parent (⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ : ParentRec) j).qty = (x.st.parents ctruth.parent).qty := by
            rw [heq, upd_same_thm]
          have g1 : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).st.parents j).qty = (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ j).qty := rfl
          have g2 : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).tr.qty j) = x.tr.qty j := rfl
          rw [g1, g2, e0, heq]
          exact hQty _ (hLt ctruth (List.mem_of_getElem? hctruth))
        · have eQ : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ j).qty = (x.st.parents j).qty := by
            rw [upd_other_thm _ _ _ _ heq]
          have g1 : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).st.parents j).qty = (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ j).qty := rfl
          have g2 : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).tr.qty j) = x.tr.qty j := rfl
          rw [g1, g2, eQ]
          exact hQty j hjOld
      · intro j
        have hSetSent : sentFor (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }) j = sentFor x.tr.kids j :=
          sentFor_set_done _ _ _ _ hctruth _
        have eSt : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ j).sent = (x.st.parents j).sent := by
          by_cases heq2 : j = ctruth.parent
          · rw [heq2, upd_same_thm]
          · rw [upd_other_thm _ _ _ _ heq2]
        have hNewOld : (x.st.parents j).sent = sentFor (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }) j := by
          rw [hSetSent]
          exact hSent j
        have hChain : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ j).sent = sentFor (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }) j :=
          eSt.trans hNewOld
        exact hChain
      · intro j
        by_cases heq : j = ctruth.parent
        · subst heq
          have hExecSet : execFor (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }) ctruth.parent
              = execFor x.tr.kids ctruth.parent + min q (ctruth.qty - ctruth.done) := by
            have h0 := execFor_set_done x.tr.kids k ctruth (min q (ctruth.qty - ctruth.done)) hctruth ctruth.parent
            simpa using h0
          have h1 : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ ctruth.parent).cum
              = (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done) := by
            rw [upd_same_thm]
          have hcm := hCum ctruth.parent
          have hrfl : x.tr.exec ctruth.parent = execFor x.tr.kids ctruth.parent := rfl
          have hChain : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ ctruth.parent).cum = execFor (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }) ctruth.parent := by
            rw [h1, hExecSet, hcm, hrfl]
          exact hChain
        · have hExecSet : execFor (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }) j
              = execFor x.tr.kids j := by
            have h0 := execFor_set_done x.tr.kids k ctruth (min q (ctruth.qty - ctruth.done)) hctruth j
            rw [if_neg (fun hh => heq hh.symm), Nat.add_zero] at h0
            exact h0
          have hupdRec : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩) j = x.st.parents j := by
            rw [upd_other_thm _ _ _ _ heq]
          have e1 : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ j).cum = (x.st.parents j).cum := by
            rw [hupdRec]
          have hOld : (x.st.parents j).cum = execFor x.tr.kids j := hCum j
          have hChain : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ j).cum = execFor (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }) j := by
            rw [e1, hOld, hExecSet]
          exact hChain
      · rw [set_length_thm, hNC]
      · intro jj cc hjj
        by_cases heq : jj = k
        · have hget : (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) })[k]? =
              some { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) } :=
            get_set_eq_proof_thm _ _ _ hLen
          have hget2 : (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) })[jj]? =
              some { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) } := by
            rw [heq]; exact hget
          have hjj2 : (some { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) } : Option Kid) = some cc := by
            rw [← hget2, hjj]
          have hccEq : ({ ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) } : Kid) = cc := by
            cases hjj2; rfl
          have hupd_eq : (upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩ jj) =
              (upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩ k) := by
            rw [heq]
          have hsame : (upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩ k) =
              ⟨ctruth.parent, ctruth.qty, ctruth.done + min q (ctruth.qty - ctruth.done)⟩ := by
            rw [upd_same_thm, hStateChild]
          have g : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).st.children jj) = (upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩ jj) := rfl
          rw [g, hupd_eq, hsame, ← hccEq]
        · have hEqq : (x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) })[jj]? = x.tr.kids[jj]? :=
            set_get_ne_eq_thm _ _ _ _ heq
          have hjj2 : x.tr.kids[jj]? = some cc := by rw [← hEqq]; exact hjj
          have hch := hChild jj cc hjj2
          have hUpd : (upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩ jj) = x.st.children jj := by
            rw [upd_other_thm _ _ _ _ heq]
          have g : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).st.children jj) = (upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩ jj) := rfl
          rw [g, hUpd, hch]
      · intro c hc
        show c.parent < x.tr.nOrders
        have hmem : c = { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) } ∨ c ∈ x.tr.kids :=
          mem_set_of_mem_helper_thm x.tr.kids k _ c hc
        rcases hmem with rfl | hm
        · exact hLt ctruth (List.mem_of_getElem? hctruth)
        · exact hLt c hm
      · intro jj hjj
        have hjjOld : jj < x.st.nParents := hjj
        by_cases heq : jj = ctruth.parent
        · have hle : (x.st.parents ctruth.parent).sent ≤ (x.st.parents ctruth.parent).qty :=
            hLe _ (by rw [← heq]; exact hjjOld)
          have eS : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ jj).sent = (x.st.parents ctruth.parent).sent := by
            rw [heq, upd_same_thm]
          have eQ : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ jj).qty = (x.st.parents ctruth.parent).qty := by
            rw [heq, upd_same_thm]
          have gS : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).st.parents jj).sent = (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ jj).sent := rfl
          have gQ : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).st.parents jj).qty = (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ jj).qty := rfl
          rw [gS, gQ, eS, eQ]
          exact hle
        · have eRec : (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ jj) = x.st.parents jj := by
            rw [upd_other_thm _ _ _ _ heq]
          have gS : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).st.parents jj).sent = (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ jj).sent := rfl
          have gQ : ((⟨⟨x.st.nParents, upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩, x.st.nChildren, upd x.st.children k ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done + min q (ctruth.qty - ctruth.done)⟩⟩, ⟨x.tr.nOrders, x.tr.qty, x.tr.kids.set k { ctruth with done := ctruth.done + min q (ctruth.qty - ctruth.done) }⟩⟩ : Sys).st.parents jj).qty = (upd x.st.parents ctruth.parent ⟨(x.st.parents ctruth.parent).qty, (x.st.parents ctruth.parent).flag, (x.st.parents ctruth.parent).sent, (x.st.parents ctruth.parent).cum + min q (ctruth.qty - ctruth.done)⟩ jj).qty := rfl
          rw [gS, gQ, eRec]
          exact hLe jj hjjOld
    · have hStepFillNeg : step b x.st (Event.fill k q) = (x.st, []) := by
        unfold step; simp [hcond]
      have hLenGe : x.tr.kids.length ≤ k := by omega
      have hNone : x.tr.kids[k]? = none := get_none_of_le_thm x.tr.kids k hLenGe
      have hObsFillNeg : x.tr.observe (Event.fill k q) = x.tr := by
        simp [Truth.observe, hNone]
      have hAdv : advance step b x (Event.fill k q) = Sys.mk x.st x.tr := by
        simp only [advance, hStepFillNeg, hObsFillNeg, record_nil_thm]
      rw [hAdv]
      exact ⟨hNP, hQty, hSent, hCum, hNC, hChild, hLt, hLe⟩

theorem inv_all_thm (b : Build) (evs : List Event) : Inv (run step b evs) := by
  apply run_induction step b Inv inv_start_thm (fun x e hx => inv_step_thm b x e hx) evs

theorem req_routes_available : RoutesAvailable step := by
  intro b evs pid liq
  have hInv := inv_all_thm b evs
  obtain ⟨hNP, hQty, hSent, hCum, hNC, hChild, hLt, hLe⟩ := hInv
  have hSnd := step_route_snd_thm b (run step b evs).st pid liq
  by_cases hid : pid < (run step b evs).tr.nOrders
  · have hq : ((run step b evs).st.parents pid).qty = (run step b evs).tr.qty pid := hQty pid hid
    have hs : ((run step b evs).st.parents pid).sent = (run step b evs).tr.sent pid := hSent pid
    rw [hSnd]
    unfold expectedRoute
    rw [hq, hs, hNP]
  · have hSt : ¬ pid < (run step b evs).st.nParents := by omega
    rw [hSnd]
    unfold expectedRoute
    simp [hSt, hid]

theorem req_never_overroute : NeverOverroute step := by
  intro b evs pid
  have hInv := inv_all_thm b evs
  obtain ⟨hNP, hQty, hSent, hCum, hNC, hChild, hLt, hLe⟩ := hInv
  by_cases hid : pid < (run step b evs).tr.nOrders
  · have hidSt : pid < (run step b evs).st.nParents := by omega
    have hle := hLe pid hidSt
    have hs := hSent pid
    have hq := hQty pid hid
    calc (run step b evs).tr.sent pid = ((run step b evs).st.parents pid).sent := hs.symm
      _ ≤ ((run step b evs).st.parents pid).qty := hle
      _ = (run step b evs).tr.qty pid := hq
  · have hzero : sentFor (run step b evs).tr.kids pid = 0 := by
      apply sentFor_zero_of_all_ne_thm
      intro c hc
      have hh := hLt c hc
      omega
    calc (run step b evs).tr.sent pid = sentFor (run step b evs).tr.kids pid := rfl
      _ = 0 := hzero
      _ ≤ (run step b evs).tr.qty pid := Nat.zero_le _

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs pid
  exact Nat.le_trans (exec_le_sent step b evs pid) (req_never_overroute b evs pid)

theorem req_fill_accounting : FillAccounting step := by
  intro b evs pid hid
  have hInv := inv_all_thm b evs
  obtain ⟨hNP, hQty, hSent, hCum, hNC, hChild, hLt, hLe⟩ := hInv
  exact hCum pid

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e pid hexec c hc
  have hexecLe := exec_le_sent step b evs pid
  have hNever := req_never_overroute b evs pid
  have hsentEq : (run step b evs).tr.sent pid = (run step b evs).tr.qty pid := by omega
  cases e with
  | parent q f =>
    rw [step_parent_snd_thm] at hc
    simp at hc
  | route j liq =>
    have hOut := step_route_snd_thm b (run step b evs).st j liq
    rw [hOut] at hc
    by_cases hcond : j < (run step b evs).st.nParents ∧ 0 < min liq (((run step b evs).st.parents j).qty - ((run step b evs).st.parents j).sent)
    · simp [hcond] at hc
      obtain rfl := hc
      simp
      intro hcontra
      have hInv2 := inv_all_thm b evs
      obtain ⟨hNP2, hQty2, hSent2, hCum2, hNC2, hChild2, hLt2, hLe2⟩ := hInv2
      have hEqPid : (run step b evs).tr.sent j = (run step b evs).tr.qty j := by
        rw [hcontra]; exact hsentEq
      by_cases hid : j < (run step b evs).tr.nOrders
      · have hq : ((run step b evs).st.parents j).qty = (run step b evs).tr.qty j := hQty2 j hid
        have hs : ((run step b evs).st.parents j).sent = (run step b evs).tr.sent j := hSent2 j
        have hEqZero : ((run step b evs).st.parents j).qty - ((run step b evs).st.parents j).sent = 0 := by
          rw [hq, hs, hEqPid, Nat.sub_self]
        omega
      · have hSt : ¬ j < (run step b evs).st.nParents := by omega
        omega
    · simp [hcond] at hc
  | ack n =>
    rw [step_ack_snd_thm] at hc
    simp at hc
  | fill k q =>
    rw [step_fill_snd_thm] at hc
    simp at hc

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> decide

end OrderRouter
