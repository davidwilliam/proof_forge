import OrderRouter.Spec
import OrderRouter.Lemmas
namespace OrderRouter

def step : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    ({ nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩, nChildren := s.nChildren, children := s.children }, [])
  | .route r l =>
    if r < s.nParents ∧ 0 < min l ((s.parents r).qty - (s.parents r).sent) then
      ({ nParents := s.nParents,
         parents := upd s.parents r ⟨(s.parents r).qty, (s.parents r).flag, (s.parents r).sent + min l ((s.parents r).qty - (s.parents r).sent), (s.parents r).cum⟩,
         nChildren := s.nChildren + 1,
         children := upd s.children s.nChildren (⟨r, min l ((s.parents r).qty - (s.parents r).sent), 0⟩ : ChildRec) },
       [⟨r, min l ((s.parents r).qty - (s.parents r).sent)⟩])
    else (s, [])
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      ({ nParents := s.nParents,
         parents := upd s.parents (s.children k).parent ⟨(s.parents (s.children k).parent).qty, (s.parents (s.children k).parent).flag, (s.parents (s.children k).parent).sent, (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done)⟩,
         nChildren := s.nChildren,
         children := upd s.children k ⟨(s.children k).parent, (s.children k).qty, (s.children k).done + min q ((s.children k).qty - (s.children k).done)⟩ },
       [])
    else (s, [])

theorem aux_sent_zero (l : List Kid) (pid : Nat) (h : ∀ kid ∈ l, kid.parent ≠ pid) : sentFor l pid = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : a.parent ≠ pid := h a (by simp)
    have ihp := ih (fun k hk => h k (by simp [hk]))
    simp [ha, ihp]

theorem aux_exec_zero (l : List Kid) (pid : Nat) (h : ∀ kid ∈ l, kid.parent ≠ pid) : execFor l pid = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : a.parent ≠ pid := h a (by simp)
    have ihp := ih (fun k hk => h k (by simp [hk]))
    simp [ha, ihp]

theorem aux_get_none_of_ge {α : Type} (l : List α) (k : Nat) (h : l.length ≤ k) : l[k]? = none := by
  induction l generalizing k with
  | nil => rfl
  | cons _ as ih =>
    cases k with
    | zero => simp at h
    | succ k => exact ih k (by simp at h ⊢; omega)

theorem aux_append_get_left {α : Type} (lone ltwo : List α) (k : Nat) (h : k < lone.length) : (lone ++ ltwo)[k]? = lone[k]? := by
  induction lone generalizing k with
  | nil => simp at h
  | cons _ as ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hk : k < as.length := by simp at h ⊢; omega
      exact ih k hk

theorem aux_set_get_same {α : Type} (l : List α) (k : Nat) (v : α) (h : k < l.length) : (l.set k v)[k]? = some v := by
  induction l generalizing k with
  | nil => simp at h
  | cons _ as ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hk : k < as.length := by simp at h ⊢; omega
      exact ih k hk

theorem aux_set_get_other {α : Type} (l : List α) (k j : Nat) (v : α) (h : j ≠ k) : (l.set k v)[j]? = l[j]? := by
  induction l generalizing k j with
  | nil =>
    have eone : ([] : List α).set k v = [] := by cases k <;> rfl
    rw [eone]
  | cons _ as ih =>
    cases k with
    | zero =>
      cases j with
      | zero => simp at h
      | succ _ => rfl
    | succ k =>
      cases j with
      | zero => rfl
      | succ j =>
        have htwo : j ≠ k := by omega
        exact ih k j htwo

theorem aux_exists_get {α : Type} (l : List α) (k : Nat) (h : k < l.length) : ∃ c, l[k]? = some c := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => exact ⟨a, rfl⟩
    | succ k =>
      simp at h ⊢
      have hk : k < as.length := by omega
      obtain ⟨c, hc⟩ := ih k hk
      exact ⟨c, hc⟩

theorem aux_append_get_eq {α : Type} (l : List α) (x : α) : (l ++ [x])[l.length]? = some x := by
  induction l with
  | nil => rfl
  | cons _ as ih => simp [ih]

theorem step_parent_snd (b : Build) (s : State) (q : Nat) (f : Bool) : (step b s (.parent q f)).2 = ([] : List Child) := by
  simp [step]

theorem step_ack_snd (b : Build) (s : State) (k : Nat) : (step b s (.ack k)).2 = ([] : List Child) := by
  simp [step]

theorem step_fill_snd (b : Build) (s : State) (k q : Nat) : (step b s (.fill k q)).2 = ([] : List Child) := by
  simp [step]
  split <;> rfl

theorem step_route_snd (b : Build) (s : State) (r l : Nat) : (step b s (.route r l)).2 = (if r < s.nParents ∧ 0 < min l ((s.parents r).qty - (s.parents r).sent) then [⟨r, min l ((s.parents r).qty - (s.parents r).sent)⟩] else []) := by
  simp [step]
  split <;> rfl

theorem step_ack_fst (b : Build) (s : State) (k : Nat) : (step b s (.ack k)).1 = s := by
  simp [step]

def Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ pid, (x.st.parents pid).qty = x.tr.qty pid) ∧
  (∀ pid, (x.st.parents pid).sent = x.tr.sent pid) ∧
  (∀ pid, (x.st.parents pid).cum = x.tr.exec pid) ∧
  (∀ k c, x.tr.kids[k]? = some c → x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec)) ∧
  (∀ kid ∈ x.tr.kids, kid.parent < x.tr.nOrders) ∧
  (∀ pid, (x.st.parents pid).sent ≤ (x.st.parents pid).qty)

theorem inv_start : Inv start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pid; rfl
  · intro pid; rfl
  · intro pid; rfl
  · intro k c h; simp [start, Truth.empty] at h
  · intro kid h; simp [start, Truth.empty] at h
  · intro pid; exact Nat.zero_le _

theorem inv_parent (b : Build) (x : Sys) (hx : Inv x) (qq : Nat) (fl : Bool) : Inv (advance step b x (.parent qq fl)) := by
  obtain ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩ := hx
  have e2 : (step b x.st (.parent qq fl)).2 = ([] : List Child) := step_parent_snd b x.st qq fl
  have hstep1 : (step b x.st (.parent qq fl)).1 = { nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨qq, fl, 0, 0⟩, nChildren := x.st.nChildren, children := x.st.children } := by simp [step]
  have hAdv : advance step b x (.parent qq fl) = ⟨{ nParents := x.st.nParents + 1, parents := upd x.st.parents x.st.nParents ⟨qq, fl, 0, 0⟩, nChildren := x.st.nChildren, children := x.st.children }, { x.tr with nOrders := x.tr.nOrders + 1, qty := upd x.tr.qty x.tr.nOrders qq }⟩ := by
    simp [advance, Truth.observe, Truth.record, hstep1, e2]
  rw [hAdv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h_np]
  · simp [h_nc]
  · intro pid
    show ((upd x.st.parents x.st.nParents ⟨qq, fl, 0, 0⟩) pid).qty = (upd x.tr.qty x.tr.nOrders qq pid)
    by_cases heq : pid = x.tr.nOrders
    · rw [heq]; simp [upd, h_np]
    · have hne : pid ≠ x.st.nParents := by omega
      simp [upd, heq, hne, h_qty pid]
  · intro pid
    have hT : Truth.sent { x.tr with nOrders := x.tr.nOrders + 1, qty := upd x.tr.qty x.tr.nOrders qq } pid = sentFor x.tr.kids pid := by simp [Truth.sent]
    rw [hT]
    by_cases heq : pid = x.st.nParents
    · subst heq
      simp [upd]
      have s0 : sentFor x.tr.kids x.st.nParents = 0 := by
        apply aux_sent_zero
        intro kid hk heq2; have hv := h_valid kid hk; omega
      exact s0.symm
    · simp [upd, heq]
      have hh := h_sent pid; simp [Truth.sent] at hh; exact hh
  · intro pid
    have hT : Truth.exec { x.tr with nOrders := x.tr.nOrders + 1, qty := upd x.tr.qty x.tr.nOrders qq } pid = execFor x.tr.kids pid := by simp [Truth.exec]
    rw [hT]
    by_cases heq : pid = x.st.nParents
    · subst heq
      simp [upd]
      have s0 : execFor x.tr.kids x.st.nParents = 0 := by
        apply aux_exec_zero
        intro kid hk heq2; have hv := h_valid kid hk; omega
      exact s0.symm
    · simp [upd, heq]
      have hc := h_cum pid; simp [Truth.exec] at hc; exact hc
  · intro k c hk
    exact h_child k c hk
  · intro kid hk
    simp at hk ⊢
    exact Nat.lt_succ_of_lt (h_valid kid hk)
  · intro pid
    by_cases heq : pid = x.st.nParents
    · subst heq; simp [upd]
    · simp [upd, heq, h_le pid]

theorem inv_ack (b : Build) (x : Sys) (hx : Inv x) (kk : Nat) : Inv (advance step b x (.ack kk)) := by
  obtain ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩ := hx
  have hstep1 : (step b x.st (.ack kk)).1 = x.st := step_ack_fst b x.st kk
  have e2 : (step b x.st (.ack kk)).2 = ([] : List Child) := step_ack_snd b x.st kk
  have hAdv : advance step b x (.ack kk) = ⟨x.st, x.tr⟩ := by
    simp [advance, Truth.observe, Truth.record, hstep1, e2]
  rw [hAdv]
  exact ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩

theorem inv_route (b : Build) (x : Sys) (hx : Inv x) (rId liq : Nat) : Inv (advance step b x (.route rId liq)) := by
  obtain ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩ := hx
  by_cases hcond : rId < x.st.nParents ∧ 0 < min liq ((x.st.parents rId).qty - (x.st.parents rId).sent)
  · have hstep1 : (step b x.st (.route rId liq)).1 = { nParents := x.st.nParents, parents := upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩, nChildren := x.st.nChildren + 1, children := upd x.st.children x.st.nChildren (⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : ChildRec) } := by
      simp [step, hcond]
    have hstep2 : (step b x.st (.route rId liq)).2 = [⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent)⟩] := by
      have h := step_route_snd b x.st rId liq
      rw [if_pos hcond] at h; exact h
    have obs_id : x.tr.observe (.route rId liq) = x.tr := rfl
    have hAdv : advance step b x (.route rId liq) = ⟨{ nParents := x.st.nParents, parents := upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩, nChildren := x.st.nChildren + 1, children := upd x.st.children x.st.nChildren (⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : ChildRec) }, { x.tr with kids := x.tr.kids ++ [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)] }⟩ := by
      simp [advance, Truth.record, hstep1, hstep2, obs_id]
    rw [hAdv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h_np]
    · simp [h_nc]
    · intro pid
      have hR : (({ x.tr with kids := x.tr.kids ++ [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)]} : Truth).qty pid) = x.tr.qty pid := by simp
      rw [hR]
      by_cases heq : pid = rId
      · rw [heq]; simp [upd, h_qty]
      · simp [upd, heq, h_qty pid]
    · intro pid
      by_cases heq : pid = rId
      · have heqr : rId = pid := heq.symm
        have hh : (x.st.parents rId).sent = sentFor x.tr.kids rId := by
          have h := h_sent rId; simp [Truth.sent] at h; exact h
        have e1 : ((upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩) pid).sent = (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent) := by
          simp [upd, heq]
        have e2 : Truth.sent ({ x.tr with kids := x.tr.kids ++ [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)]} : Truth) pid = sentFor x.tr.kids rId + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent) := by
          rw [heqr]; simp [Truth.sent, sentFor_append, hh]
        rw [e1, e2, hh]
      · have hne : rId ≠ pid := fun h => heq h.symm
        have gz : sentFor [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)] pid = 0 := by simp [hne]
        have hh : (x.st.parents pid).sent = sentFor x.tr.kids pid := by
          have h := h_sent pid; simp [Truth.sent] at h; exact h
        have e1 : ((upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩) pid).sent = (x.st.parents pid).sent := by
          simp [upd, heq]
        have e2 : Truth.sent ({ x.tr with kids := x.tr.kids ++ [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)]} : Truth) pid = sentFor x.tr.kids pid := by
          simp [Truth.sent, sentFor_append, gz]
        rw [e1, e2, hh]
    · intro pid
      by_cases heq : pid = rId
      · have heqr : rId = pid := heq.symm
        have e1 : ((upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩) pid).cum = (x.st.parents rId).cum := by
          simp [upd, heq]
        have hcR : (x.st.parents rId).cum = execFor x.tr.kids rId := by
          have h := h_cum rId; simp [Truth.exec] at h; exact h
        have e2 : Truth.exec ({ x.tr with kids := x.tr.kids ++ [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)]} : Truth) pid = execFor x.tr.kids rId := by
          rw [heqr]; simp [Truth.exec, execFor_append]
        rw [e1, e2, hcR]
      · have e1 : ((upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩) pid).cum = (x.st.parents pid).cum := by
          simp [upd, heq]
        have e2 : Truth.exec ({ x.tr with kids := x.tr.kids ++ [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)]} : Truth) pid = execFor x.tr.kids pid := by
          simp [Truth.exec, execFor_append]
        have hcP : (x.st.parents pid).cum = execFor x.tr.kids pid := by
          have h := h_cum pid; simp [Truth.exec] at h; exact h
        rw [e1, e2, hcP]
    · intro k c hk
      by_cases hlt : k < x.tr.kids.length
      · have hleft : (x.tr.kids ++ [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)])[k]? = x.tr.kids[k]? := aux_append_get_left _ _ _ hlt
        rw [hleft] at hk
        have hc0 := h_child k c hk
        have hne : k ≠ x.st.nChildren := by omega
        simp [upd, hne, hc0]
      · by_cases heq2 : k = x.tr.kids.length
        · rw [heq2] at hk ⊢
          have hget : (x.tr.kids ++ [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)])[x.tr.kids.length]? = some (⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid) := aux_append_get_eq _ _
          have hcc : c = (⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid) := Option.some_inj.mp (hk.symm.trans hget)
          rw [hcc]
          have hkk : x.tr.kids.length = x.st.nChildren := h_nc.symm
          rw [hkk]
          simp [upd]
        · have hnone2 : (x.tr.kids ++ [(⟨rId, min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), 0⟩ : Kid)])[k]? = none := aux_get_none_of_ge _ _ (by simp; omega)
          rw [hnone2] at hk
          simp at hk
    · intro kid hk2
      simp only [List.mem_append, List.mem_singleton] at hk2
      rcases hk2 with hk2 | hk2
      · exact h_valid kid hk2
      · rw [hk2]; simp only; omega
    · intro pid
      by_cases heq : pid = rId
      · have e1 : ((upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩) pid).sent = (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent) := by
          simp [upd, heq]
        have e2 : ((upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩) pid).qty = (x.st.parents rId).qty := by
          simp [upd, heq]
        rw [e1, e2]
        have hcap : min liq ((x.st.parents rId).qty - (x.st.parents rId).sent) ≤ (x.st.parents rId).qty - (x.st.parents rId).sent := Nat.min_le_right _ _
        have hlej := h_le rId
        omega
      · have e1 : ((upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩) pid).sent = (x.st.parents pid).sent := by
          simp [upd, heq]
        have e2 : ((upd x.st.parents rId ⟨(x.st.parents rId).qty, (x.st.parents rId).flag, (x.st.parents rId).sent + min liq ((x.st.parents rId).qty - (x.st.parents rId).sent), (x.st.parents rId).cum⟩) pid).qty = (x.st.parents pid).qty := by
          simp [upd, heq]
        rw [e1, e2]
        exact h_le pid
  · have hstep1 : (step b x.st (.route rId liq)).1 = x.st := by simp [step, hcond]
    have hstep2 : (step b x.st (.route rId liq)).2 = ([] : List Child) := by
      have h := step_route_snd b x.st rId liq
      rw [if_neg hcond] at h; exact h
    have obs_id : x.tr.observe (.route rId liq) = x.tr := rfl
    have hAdv : advance step b x (.route rId liq) = ⟨x.st, x.tr⟩ := by
      simp [advance, Truth.record, hstep1, hstep2, obs_id]
    rw [hAdv]
    exact ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩

theorem inv_fill (b : Build) (x : Sys) (hx : Inv x) (m n : Nat) : Inv (advance step b x (.fill m n)) := by
  obtain ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩ := hx
  by_cases hk : m < x.st.nChildren
  · have hkT : m < x.tr.kids.length := by omega
    obtain ⟨ck, hck⟩ := aux_exists_get x.tr.kids m hkT
    have hch := h_child m ck hck
    have hpar_eq : (x.st.children m).parent = ck.parent := by rw [hch]
    have hqty_eq : (x.st.children m).qty = ck.qty := by rw [hch]
    have hdone_eq : (x.st.children m).done = ck.done := by rw [hch]
    have hstep1 : (step b x.st (.fill m n)).1 = { nParents := x.st.nParents, parents := upd x.st.parents ck.parent ⟨(x.st.parents ck.parent).qty, (x.st.parents ck.parent).flag, (x.st.parents ck.parent).sent, (x.st.parents ck.parent).cum + min n (ck.qty - ck.done)⟩, nChildren := x.st.nChildren, children := upd x.st.children m (⟨ck.parent, ck.qty, ck.done + min n (ck.qty - ck.done)⟩ : ChildRec) } := by
      simp [step, hk, hpar_eq, hqty_eq, hdone_eq]
    have hstep2 : (step b x.st (.fill m n)).2 = ([] : List Child) := step_fill_snd b x.st m n
    have hobs : x.tr.observe (.fill m n) = { x.tr with kids := x.tr.kids.set m { ck with done := ck.done + min n (ck.qty - ck.done) } } := by
      simp [Truth.observe, hck]
    have hAdv : advance step b x (.fill m n) = ⟨{ nParents := x.st.nParents, parents := upd x.st.parents ck.parent ⟨(x.st.parents ck.parent).qty, (x.st.parents ck.parent).flag, (x.st.parents ck.parent).sent, (x.st.parents ck.parent).cum + min n (ck.qty - ck.done)⟩, nChildren := x.st.nChildren, children := upd x.st.children m (⟨ck.parent, ck.qty, ck.done + min n (ck.qty - ck.done)⟩ : ChildRec) }, { x.tr with kids := x.tr.kids.set m { ck with done := ck.done + min n (ck.qty - ck.done) } }⟩ := by
      simp [advance, Truth.record, hstep1, hstep2, hobs]
    rw [hAdv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h_np]
    · simp [h_nc]
    · intro pid
      have hR : (({ x.tr with kids := x.tr.kids.set m { ck with done := ck.done + min n (ck.qty - ck.done) } } : Truth).qty pid = x.tr.qty pid) := by simp
      rw [hR]
      by_cases heq : pid = ck.parent
      · rw [heq]; simp [upd, h_qty]
      · simp [upd, heq, h_qty pid]
    · intro pid
      have hs : sentFor (x.tr.kids.set m { ck with done := ck.done + min n (ck.qty - ck.done) }) pid = sentFor x.tr.kids pid := sentFor_set_done _ _ _ _ hck pid
      have hT : Truth.sent { x.tr with kids := x.tr.kids.set m { ck with done := ck.done + min n (ck.qty - ck.done) } } pid = sentFor x.tr.kids pid := by simp [Truth.sent, hs]
      rw [hT]
      have hold : (x.st.parents pid).sent = sentFor x.tr.kids pid := by
        have h := h_sent pid; simp [Truth.sent] at h; exact h
      by_cases heq : pid = ck.parent
      · have e1 : ((upd x.st.parents ck.parent ⟨(x.st.parents ck.parent).qty, (x.st.parents ck.parent).flag, (x.st.parents ck.parent).sent, (x.st.parents ck.parent).cum + min n (ck.qty - ck.done)⟩) pid).sent = (x.st.parents ck.parent).sent := by
          simp [upd, heq]
        rw [e1]
        have heqr : ck.parent = pid := heq.symm
        rw [heqr]
        exact hold
      · have e1 : ((upd x.st.parents ck.parent ⟨(x.st.parents ck.parent).qty, (x.st.parents ck.parent).flag, (x.st.parents ck.parent).sent, (x.st.parents ck.parent).cum + min n (ck.qty - ck.done)⟩) pid).sent = (x.st.parents pid).sent := by
          simp [upd, heq]
        rw [e1, hold]
    · intro pid
      have hset := execFor_set_done x.tr.kids m ck (min n (ck.qty - ck.done)) hck pid
      have hTe : Truth.exec { x.tr with kids := x.tr.kids.set m { ck with done := ck.done + min n (ck.qty - ck.done) } } pid = execFor x.tr.kids pid + (if ck.parent = pid then min n (ck.qty - ck.done) else 0) := by
        simp [Truth.exec, hset]
      rw [hTe]
      by_cases htwo : pid = ck.parent
      · subst htwo
        have hcumeq : (x.st.parents ck.parent).cum = execFor x.tr.kids ck.parent := by
          have h := h_cum ck.parent; simp [Truth.exec] at h; exact h
        simp [upd, hcumeq]
      · have hne : ck.parent ≠ pid := fun h => htwo h.symm
        have hcum : (x.st.parents pid).cum = execFor x.tr.kids pid := by
          have h := h_cum pid; simp [Truth.exec] at h; exact h
        have e1 : ((upd x.st.parents ck.parent ⟨(x.st.parents ck.parent).qty, (x.st.parents ck.parent).flag, (x.st.parents ck.parent).sent, (x.st.parents ck.parent).cum + min n (ck.qty - ck.done)⟩) pid).cum = (x.st.parents pid).cum := by
          simp [upd, htwo]
        rw [e1, hcum]
        simp [hne]
    · intro wq dq hj
      by_cases heq : wq = m
      · rw [heq] at hj ⊢
        have hs2 := aux_set_get_same (x.tr.kids) m ({ ck with done := ck.done + min n (ck.qty - ck.done) }) hkT
        rw [hs2] at hj
        have hdd : dq = { ck with done := ck.done + min n (ck.qty - ck.done) } := by simpa using hj.symm
        rw [hdd]
        simp [upd]
      · have hotherw : ((x.tr.kids.set m { ck with done := ck.done + min n (ck.qty - ck.done) })[wq]?) = x.tr.kids[wq]? := aux_set_get_other _ _ _ _ heq
        rw [hotherw] at hj
        have hc2 := h_child wq dq hj
        simp [upd, heq, hc2]
    · intro kid hm
      have hmem := List.mem_or_eq_of_mem_set hm
      rcases hmem with hmem | hmem
      · exact h_valid kid hmem
      · rw [hmem]
        exact h_valid ck (List.mem_of_getElem? hck)
    · intro pid
      by_cases heq : pid = ck.parent
      · have e1 : ((upd x.st.parents ck.parent ⟨(x.st.parents ck.parent).qty, (x.st.parents ck.parent).flag, (x.st.parents ck.parent).sent, (x.st.parents ck.parent).cum + min n (ck.qty - ck.done)⟩) pid).sent ≤ ((upd x.st.parents ck.parent ⟨(x.st.parents ck.parent).qty, (x.st.parents ck.parent).flag, (x.st.parents ck.parent).sent, (x.st.parents ck.parent).cum + min n (ck.qty - ck.done)⟩) pid).qty := by
          simp [upd, heq, h_le]
        exact e1
      · have e1 : ((upd x.st.parents ck.parent ⟨(x.st.parents ck.parent).qty, (x.st.parents ck.parent).flag, (x.st.parents ck.parent).sent, (x.st.parents ck.parent).cum + min n (ck.qty - ck.done)⟩) pid).sent = (x.st.parents pid).sent := by
          simp [upd, heq]
        have e2 : ((upd x.st.parents ck.parent ⟨(x.st.parents ck.parent).qty, (x.st.parents ck.parent).flag, (x.st.parents ck.parent).sent, (x.st.parents ck.parent).cum + min n (ck.qty - ck.done)⟩) pid).qty = (x.st.parents pid).qty := by
          simp [upd, heq]
        rw [e1, e2]
        exact h_le pid
  · have hstep1 : (step b x.st (.fill m n)).1 = x.st := by simp [step, hk]
    have hstep2 : (step b x.st (.fill m n)).2 = ([] : List Child) := step_fill_snd b x.st m n
    have hnone : x.tr.kids[m]? = none := aux_get_none_of_ge _ _ (by omega)
    have hobs : x.tr.observe (.fill m n) = x.tr := by simp [Truth.observe, hnone]
    have hAdv : advance step b x (.fill m n) = ⟨x.st, x.tr⟩ := by
      simp [advance, Truth.record, hstep1, hstep2, hobs]
    rw [hAdv]
    exact ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩

theorem inv_all (b : Build) (evs : List Event) : Inv (run step b evs) := by
  apply run_induction step b Inv inv_start _ evs
  intro x e hx
  cases e with
  | parent qq fl => exact inv_parent b x hx qq fl
  | route rId liq => exact inv_route b x hx rId liq
  | ack kk => exact inv_ack b x hx kk
  | fill m n => exact inv_fill b x hx m n

theorem req_routes_available : RoutesAvailable step := by
  intro b evs rr ll
  have hx := inv_all b evs
  obtain ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩ := hx
  have hone := step_route_snd b (run step b evs).st rr ll
  have hcond_iff : (rr < (run step b evs).st.nParents ∧ 0 < min ll (((run step b evs).st.parents rr).qty - ((run step b evs).st.parents rr).sent)) ↔ (rr < (run step b evs).tr.nOrders ∧ 0 < min ll ((run step b evs).tr.qty rr - (run step b evs).tr.sent rr)) := by
    rw [h_np, h_qty rr, h_sent rr]
  have hval_eq : min ll (((run step b evs).st.parents rr).qty - ((run step b evs).st.parents rr).sent) = min ll ((run step b evs).tr.qty rr - (run step b evs).tr.sent rr) := by
    rw [h_qty rr, h_sent rr]
  have hexp : expectedRoute (run step b evs).tr rr ll = (if rr < (run step b evs).tr.nOrders ∧ 0 < min ll ((run step b evs).tr.qty rr - (run step b evs).tr.sent rr) then [⟨rr, min ll ((run step b evs).tr.qty rr - (run step b evs).tr.sent rr)⟩] else []) := by
    simp [expectedRoute]
  rw [hone, hexp]
  by_cases h : rr < (run step b evs).st.nParents ∧ 0 < min ll (((run step b evs).st.parents rr).qty - ((run step b evs).st.parents rr).sent)
  · have htwo := hcond_iff.mp h
    rw [if_pos h, if_pos htwo, hval_eq]
  · have htwo : ¬ (rr < (run step b evs).tr.nOrders ∧ 0 < min ll ((run step b evs).tr.qty rr - (run step b evs).tr.sent rr)) := fun hh => h (hcond_iff.mpr hh)
    rw [if_neg h, if_neg htwo]

theorem req_never_overroute : NeverOverroute step := by
  intro b evs pid
  have hx := inv_all b evs
  obtain ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩ := hx
  have eone : (run step b evs).tr.sent pid = ((run step b evs).st.parents pid).sent := (h_sent pid).symm
  have etwo : (run step b evs).tr.qty pid = ((run step b evs).st.parents pid).qty := (h_qty pid).symm
  rw [eone, etwo]
  exact h_le pid

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs pid
  have hone := exec_le_sent step b evs pid
  have htwo := req_never_overroute b evs pid
  omega

theorem req_fill_accounting : FillAccounting step := by
  intro b evs pid _
  have hx := inv_all b evs
  obtain ⟨h_np, h_nc, h_qty, h_sent, h_cum, h_child, h_valid, h_le⟩ := hx
  exact h_cum pid

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e tout hfill c hc
  cases e with
  | parent qq fl =>
    have htwo := step_parent_snd b (run step b evs).st qq fl
    rw [htwo] at hc
    simp at hc
  | route rr ll =>
    have hstep : (step b (run step b evs).st (Event.route rr ll)).2 = expectedRoute (run step b evs).tr rr ll := req_routes_available b evs rr ll
    rw [hstep] at hc
    have hexp : expectedRoute (run step b evs).tr rr ll = (if rr < (run step b evs).tr.nOrders ∧ 0 < min ll ((run step b evs).tr.qty rr - (run step b evs).tr.sent rr) then [⟨rr, min ll ((run step b evs).tr.qty rr - (run step b evs).tr.sent rr)⟩] else []) := by simp [expectedRoute]
    rw [hexp] at hc
    by_cases hcc : rr < (run step b evs).tr.nOrders ∧ 0 < min ll ((run step b evs).tr.qty rr - (run step b evs).tr.sent rr)
    · rw [if_pos hcc, List.mem_singleton] at hc
      rw [hc]
      intro heq
      have hrr : rr = tout := heq
      have hcc2 : tout < (run step b evs).tr.nOrders ∧ 0 < min ll ((run step b evs).tr.qty tout - (run step b evs).tr.sent tout) := hrr ▸ hcc
      have hsent_le : (run step b evs).tr.sent tout ≤ (run step b evs).tr.qty tout := req_never_overroute b evs tout
      have hex_le : (run step b evs).tr.exec tout ≤ (run step b evs).tr.sent tout := exec_le_sent step b evs tout
      have hle2 : (run step b evs).tr.qty tout ≤ (run step b evs).tr.sent tout := hfill ▸ hex_le
      have heq_sent : (run step b evs).tr.sent tout = (run step b evs).tr.qty tout := Nat.le_antisymm hsent_le hle2
      have hpos : 0 < min ll ((run step b evs).tr.qty tout - (run step b evs).tr.sent tout) := hcc2.2
      rw [heq_sent, Nat.sub_self] at hpos
      simp at hpos
    · rw [if_neg hcc] at hc
      simp at hc
  | ack kk =>
    have htwo := step_ack_snd b (run step b evs).st kk
    rw [htwo] at hc
    simp at hc
  | fill m n =>
    have htwo := step_fill_snd b (run step b evs).st m n
    rw [htwo] at hc
    simp at hc

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> decide

end OrderRouter
