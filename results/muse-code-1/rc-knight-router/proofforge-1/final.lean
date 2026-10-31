import OrderRouter.Spec
import OrderRouter.Lemmas

namespace OrderRouter

/-- Send the available liquidity capped at the shares not yet sent. -/
def routeBySent (s : State) (id liq : Nat) : State × List Child :=
  if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
    ({ s with parents := upd s.parents id { (s.parents id) with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
              nChildren := s.nChildren + 1,
              children := upd s.children s.nChildren ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ },
     [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩])
  else (s, [])

def step : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route id liq => routeBySent s id liq
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      ({ s with parents := upd s.parents (s.children k).parent { (s.parents (s.children k).parent) with cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) },
                children := upd s.children k { (s.children k) with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } }, [])
    else (s, [])

theorem upd_self' {α : Type} (f : Nat → α) (k : Nat) (v : α) :
    upd f k v k = v := by simp [upd]

theorem upd_ne' {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) :
    upd f k v j = f j := by simp [upd, h]

theorem sentFor_fresh (l : List Kid) (N : Nat) (h : ∀ k ∈ l, k.parent < N) (id : Nat) (hle : N ≤ id) :
    sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent < N := h a (by simp)
    have hr : ∀ k ∈ as, k.parent < N := fun k hk => h k (by simp [hk])
    rw [ih hr]
    simp
    omega

theorem execFor_fresh (l : List Kid) (N : Nat) (h : ∀ k ∈ l, k.parent < N) (id : Nat) (hle : N ≤ id) :
    execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent < N := h a (by simp)
    have hr : ∀ k ∈ as, k.parent < N := fun k hk => h k (by simp [hk])
    rw [ih hr]
    simp
    omega

theorem sent_append_single (l : List Kid) (pid c : Nat) (id : Nat) :
    sentFor (l ++ [(⟨pid, c, 0⟩ : Kid)]) id = sentFor l id + (if pid = id then c else 0) := by
  simp

theorem exec_append_single (l : List Kid) (pid c : Nat) (id : Nat) :
    execFor (l ++ [(⟨pid, c, 0⟩ : Kid)]) id = execFor l id := by
  simp

theorem length_append_single (l : List Kid) (pid c : Nat) :
    (l ++ [(⟨pid, c, 0⟩ : Kid)]).length = l.length + 1 := by
  simp

/-- Master invariant: router state matches ground truth. -/
def Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ id, id < x.st.nParents → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ id, id < x.st.nParents → (x.st.parents id).sent = x.tr.sent id) ∧
  (∀ id, id < x.st.nParents → (x.st.parents id).cum = x.tr.exec id) ∧
  (∀ id, id < x.st.nParents → (x.st.parents id).sent ≤ (x.st.parents id).qty) ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ k, k < x.st.nChildren → ∃ c, x.tr.kids[k]? = some c ∧ x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec)) ∧
  (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders)

theorem inv_start : Inv start := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro id h; simp [start, init] at h
  · intro k h; simp [start, init] at h
  · intro k h; simp [start, Truth.empty] at h

theorem inv_parent (b : Build) (x : Sys) (q : Nat) (f : Bool) (h : Inv x) :
    Inv (advance step b x (.parent q f)) := by
  obtain ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩ := h
  have hmem' : ∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders + 1 :=
    fun k hk => Nat.lt_succ_of_lt (hmem k hk)
  have hsentFresh : sentFor x.tr.kids x.tr.nOrders = 0 :=
    sentFor_fresh x.tr.kids x.tr.nOrders hmem _ (Nat.le_refl _)
  have hexecFresh : execFor x.tr.kids x.tr.nOrders = 0 :=
    execFor_fresh x.tr.kids x.tr.nOrders hmem _ (Nat.le_refl _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [advance, step, Truth.observe, Truth.record, hnP]
  · intro id hid
    simp only [advance, step] at hid ⊢
    by_cases heq : id = x.st.nParents
    · subst heq
      simp [upd_self', Truth.observe, Truth.record]
      rw [← hnP, upd_self']
    · have hid' : id < x.st.nParents := by omega
      rw [upd_ne' _ _ _ _ heq]
      rw [hqty id hid']
      simp [Truth.observe, Truth.record]
      by_cases hid2 : id = x.tr.nOrders
      · omega
      · rw [upd_ne' _ _ _ _ hid2]
  · intro id hid
    simp only [advance, step] at hid ⊢
    by_cases heq : id = x.st.nParents
    · subst heq
      simp [upd_self']
      simp [Truth.sent, Truth.record, Truth.observe]
      rw [hnP]
      exact hsentFresh.symm
    · have hid' : id < x.st.nParents := by omega
      rw [upd_ne' _ _ _ _ heq]
      rw [hsent id hid']
      simp [Truth.sent, Truth.record, Truth.observe]
  · intro id hid
    simp only [advance, step] at hid ⊢
    by_cases heq : id = x.st.nParents
    · subst heq
      simp [upd_self']
      simp [Truth.exec, Truth.record, Truth.observe]
      rw [hnP]
      exact hexecFresh.symm
    · have hid' : id < x.st.nParents := by omega
      rw [upd_ne' _ _ _ _ heq]
      rw [hcum id hid']
      simp [Truth.exec, Truth.record, Truth.observe]
  · intro id hid
    simp only [advance, step] at hid ⊢
    by_cases heq : id = x.st.nParents
    · subst heq
      simp [upd_self']
    · have hid' : id < x.st.nParents := by omega
      rw [upd_ne' _ _ _ _ heq]
      exact hle id hid'
  · simp [advance, step, Truth.observe, Truth.record, hnC]
  · intro k hk
    simp only [advance, step] at hk ⊢
    simp [Truth.record, Truth.observe]
    obtain ⟨c, hc1, hc2⟩ := hch k hk
    exact ⟨c, hc1, hc2⟩
  · intro k hk
    simp [advance, step, Truth.record, Truth.observe] at hk ⊢
    exact Nat.lt_succ_of_lt (hmem k hk)

theorem inv_ack (b : Build) (x : Sys) (k : Nat) (h : Inv x) :
    Inv (advance step b x (.ack k)) := by
  obtain ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩ := h
  simp [advance, step, Truth.observe, Truth.record]
  exact ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩

theorem routeBySent_snd (s : State) (id liq : Nat) :
    (routeBySent s id liq).2 =
      (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
        [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else []) := by
  unfold routeBySent
  by_cases h : id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent)
  · simp [h]
  · simp [h]

theorem route_output_eq (x : Sys) (id liq : Nat)
    (hnP : x.st.nParents = x.tr.nOrders)
    (hqty : ∀ id, id < x.st.nParents → (x.st.parents id).qty = x.tr.qty id)
    (hsent : ∀ id, id < x.st.nParents → (x.st.parents id).sent = x.tr.sent id) :
    (routeBySent x.st id liq).2 = expectedRoute x.tr id liq := by
  rw [routeBySent_snd]
  unfold expectedRoute
  by_cases hid : id < x.st.nParents
  · have hq := hqty id hid
    have hs := hsent id hid
    have hval : min liq ((x.st.parents id).qty - (x.st.parents id).sent)
        = min liq (x.tr.qty id - x.tr.sent id) := by
      rw [hq, hs]
    rw [hval]
    have hidT : id < x.tr.nOrders := by omega
    by_cases hc : 0 < min liq (x.tr.qty id - x.tr.sent id)
    · simp [hid, hidT, hc]
    · simp [hid, hidT, hc]
  · have hidT : ¬ id < x.tr.nOrders := by omega
    simp [hid, hidT]

theorem inv_route (b : Build) (x : Sys) (id liq : Nat) (h : Inv x) :
    Inv (advance step b x (.route id liq)) := by
  obtain ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩ := h
  have hout := route_output_eq x id liq hnP hqty hsent
  by_cases hid : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
  · have hid1 : id < x.st.nParents := hid.1
    have hid2 : 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent) := hid.2
    have hq := hqty id hid1
    have hs := hsent id hid1
    have hc0 := hcum id hid1
    have hle0 := hle id hid1
    have htr : id < x.tr.nOrders := by omega
    have hmin_eq : min liq ((x.st.parents id).qty - (x.st.parents id).sent) = min liq (x.tr.qty id - x.tr.sent id) := by
      rw [hq, hs]
    have htrCond : id < x.tr.nOrders ∧ 0 < min liq (x.tr.qty id - x.tr.sent id) := by
      rw [hnP] at hid1; rw [← hmin_eq]; exact ⟨hid1, hid2⟩
    have c_le : min liq (x.tr.qty id - x.tr.sent id) ≤ x.tr.qty id - x.tr.sent id := Nat.min_le_right _ _
    have sent_le : x.tr.sent id ≤ x.tr.qty id := by
      rw [← hs, ← hq]; exact hle0
    -- unfold advance with the taken branch
    have hstep1 : (routeBySent x.st id liq).1 =
        { x.st with parents := upd x.st.parents id { (x.st.parents id) with sent := (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent) },
                    nChildren := x.st.nChildren + 1,
                    children := upd x.st.children x.st.nChildren ⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent), 0⟩ } := by
      unfold routeBySent; simp [hid]
    have hstep2 : (routeBySent x.st id liq).2 = [⟨id, min liq ((x.st.parents id).qty - (x.st.parents id).sent)⟩] := by
      unfold routeBySent; simp [hid]
    have hadv : advance step b x (.route id liq) =
        ⟨(routeBySent x.st id liq).1, (x.tr.observe (.route id liq)).record (routeBySent x.st id liq).2⟩ := by
      simp [advance, step]
    rw [hadv, hstep1, hstep2]
    simp [Truth.observe, Truth.record]
    rw [hmin_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hnP]
    · intro j hj
      simp at hj ⊢
      by_cases heqQ : j = id
      · subst j
        simp [upd_self', hqty _ (by omega)]
      · simp [upd_ne' _ _ _ _ heqQ, hqty j (by omega)]
    · intro j hj
      simp at hj ⊢
      by_cases heqS : j = id
      · subst j
        simp [upd_self', Truth.sent, hs]
      · simp [upd_ne' _ _ _ _ heqS, hsent j (by omega), Truth.sent, Ne.symm heqS]
    · intro j hj
      simp at hj ⊢
      by_cases heqC : j = id
      · subst j
        simp [upd_self', hcum _ (by omega), Truth.exec]
      · simp [upd_ne' _ _ _ _ heqC, hcum j (by omega), Truth.exec]
    · intro j hj
      simp at hj ⊢
      by_cases heq : j = id
      · subst j
        simp [upd_self']
        simp [Truth.sent] at hq hs ⊢
        rw [hmin_eq] at hid2
        rw [hs, hq]
        rw [hs, hq] at hle0
        omega
      · rw [upd_ne' _ _ _ _ heq]
        exact hle j (by omega)
    · simp [hnC]
    · intro kk hkk
      simp at hkk
      have hlen : (x.tr.kids ++ [(⟨id, min liq (x.tr.qty id - x.tr.sent id), 0⟩ : Kid)]).length = x.tr.kids.length + 1 := by simp
      by_cases heq : kk = x.tr.kids.length
      · subst heq
        have hget : ((x.tr.kids ++ [(⟨id, min liq (x.tr.qty id - x.tr.sent id), 0⟩ : Kid)])[x.tr.kids.length]?) = some ⟨id, min liq (x.tr.qty id - x.tr.sent id), 0⟩ := by simp
        refine ⟨⟨id, min liq (x.tr.qty id - x.tr.sent id), 0⟩, hget, ?_⟩
        simp [upd_self', hnC]
      · have hkk' : kk < x.tr.kids.length := by omega
        have hkkC : kk < x.st.nChildren := by omega
        obtain ⟨cc, hc1, hc2⟩ := hch kk hkkC
        have hget : ((x.tr.kids ++ [(⟨id, min liq (x.tr.qty id - x.tr.sent id), 0⟩ : Kid)])[kk]?) = x.tr.kids[kk]? :=
          List.getElem?_append_left hkk'
        rw [hget]
        refine ⟨cc, hc1, ?_⟩
        dsimp only
        rw [upd_ne' _ _ _ _ (by omega : kk ≠ x.st.nChildren)]
        exact hc2
    · intro kk hkk
      simp at hkk
      rcases hkk with hkk | ⟨_, _, rfl⟩
      · exact hmem kk hkk
      · exact htr
  · -- route sends nothing
    have hstep : routeBySent x.st id liq = (x.st, []) := by
      unfold routeBySent; simp [hid]
    have h1 : step b x.st (.route id liq) = (x.st, []) := hstep
    have hadv : advance step b x (.route id liq) = ⟨x.st, x.tr⟩ := by
      simp [advance, h1, Truth.observe, Truth.record, List.append_nil]
    rw [hadv]
    exact ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩

theorem inv_fill (b : Build) (x : Sys) (k q : Nat) (h : Inv x) :
    Inv (advance step b x (.fill k q)) := by
  obtain ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩ := h
  by_cases hk : k < x.st.nChildren
  · obtain ⟨ck, hck1, hck2⟩ := hch k hk
    have hklen : k < x.tr.kids.length := by omega
    have hckQty : (x.st.children k).qty = ck.qty := by rw [hck2]
    have hckDone : (x.st.children k).done = ck.done := by rw [hck2]
    have hckPar : (x.st.children k).parent = ck.parent := by rw [hck2]
    have hckParLt : ck.parent < x.tr.nOrders := by
      have := hmem ck (List.mem_of_getElem? hck1); exact this
    have hckParLtS : (x.st.children k).parent < x.st.nParents := by omega
    have hparQty := hqty _ hckParLtS
    have hparSent := hsent _ hckParLtS
    have hparCum := hcum _ hckParLtS
    have hparLe := hle _ hckParLtS
    have hxx_eq : min q ((x.st.children k).qty - (x.st.children k).done) = min q (ck.qty - ck.done) := by
      rw [hckQty, hckDone]
    have hstep : (step b x.st (.fill k q)).1 =
        { x.st with parents := upd x.st.parents (x.st.children k).parent { (x.st.parents (x.st.children k).parent) with cum := (x.st.parents (x.st.children k).parent).cum + min q ((x.st.children k).qty - (x.st.children k).done) },
                    children := upd x.st.children k { (x.st.children k) with done := (x.st.children k).done + min q ((x.st.children k).qty - (x.st.children k).done) } } := by
      simp [step, hk]
    have hout : (step b x.st (.fill k q)).2 = ([] : List Child) := by
      simp [step, hk]
    have hadv : advance step b x (.fill k q) =
        ⟨(step b x.st (.fill k q)).1, (x.tr.observe (.fill k q)).record (step b x.st (.fill k q)).2⟩ := rfl
    -- truth observe computes the same increment
    have hobs : x.tr.observe (.fill k q) = { x.tr with kids := x.tr.kids.set k { ck with done := ck.done + min q (ck.qty - ck.done) } } := by
      simp [Truth.observe, hck1]
    rw [hadv, hstep, hout, hobs]
    simp [Truth.record]
    rw [hxx_eq, hckPar]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hnP]
    · intro j hj
      simp at hj ⊢
      by_cases heqQ : j = ck.parent
      · subst heqQ
        simp [upd_self']
        rw [hqty _ (by omega)]
      · rw [upd_ne' _ _ _ _ heqQ]
        rw [hqty j (by omega)]
    · intro j hj
      simp at hj ⊢
      by_cases heqS : j = ck.parent
      · subst heqS
        simp [upd_self', Truth.sent]
        have h1 : (x.st.parents ck.parent).sent = sentFor x.tr.kids ck.parent := hsent _ (by omega)
        rw [h1]
        have h2 := sentFor_set_done x.tr.kids k ck (ck.done + min q (ck.qty - ck.done)) hck1 ck.parent
        exact h2.symm
      · rw [upd_ne' _ _ _ _ heqS]
        rw [hsent j (by omega)]
        simp [Truth.sent]
        have h2 := sentFor_set_done x.tr.kids k ck (ck.done + min q (ck.qty - ck.done)) hck1 j
        exact h2.symm
    · intro j hj
      simp at hj ⊢
      by_cases heq : j = ck.parent
      · subst heq
        have hparCum2 : (x.st.parents ck.parent).cum = execFor x.tr.kids ck.parent := by
          have := hcum ck.parent (by omega); simp [Truth.exec] at this ⊢; exact this
        simp [upd_self']
        simp [Truth.exec]
        have hset := execFor_set_done x.tr.kids k ck (min q (ck.qty - ck.done)) hck1 ck.parent
        simp at hset
        omega
      · rw [upd_ne' _ _ _ _ heq]
        rw [hcum j (by omega)]
        simp [Truth.exec]
        have hset := execFor_set_done x.tr.kids k ck (min q (ck.qty - ck.done)) hck1 j
        simp [Ne.symm heq] at hset
        exact hset.symm
    · intro j hj
      simp at hj ⊢
      by_cases heq2 : j = ck.parent
      · subst heq2
        simp [upd_self']
        exact hle _ (by omega)
      · rw [upd_ne' _ _ _ _ heq2]
        exact hle j (by omega)
    · simp [hnC]
    · intro j hj
      simp at hj ⊢
      have hjlen0 : j < x.tr.kids.length := by omega
      by_cases heq : j = k
      · have hget : ((x.tr.kids.set k { ck with done := ck.done + min q (ck.qty - ck.done) })[j]?) = some { ck with done := ck.done + min q (ck.qty - ck.done) } := by
          rw [heq]; exact List.getElem?_set_self hklen
        refine ⟨{ ck with done := ck.done + min q (ck.qty - ck.done) }, hget, ?_⟩
        rw [heq, upd_self']
        rw [hck2]
      · have hget : ((x.tr.kids.set k { ck with done := ck.done + min q (ck.qty - ck.done) })[j]?) = x.tr.kids[j]? :=
          List.getElem?_set_ne (Ne.symm heq)
        obtain ⟨cc, hc1, hc2⟩ := hch j (by omega)
        refine ⟨cc, by rw [hget, hc1], ?_⟩
        rw [upd_ne' _ _ _ _ heq]
        exact hc2
    · intro kk hkk
      simp at hkk
      -- membership preserved: set preserves parents
      have : ∀ a ∈ x.tr.kids.set k { ck with done := ck.done + min q (ck.qty - ck.done) }, a.parent < x.tr.nOrders := by
        intro a ha
        rcases List.mem_or_eq_of_mem_set ha with ha | ha
        · exact hmem a ha
        · subst ha
          simp
          exact hckParLt
      exact this kk hkk
  · have hstep : step b x.st (.fill k q) = (x.st, []) := by
      simp [step, hk]
    have hle2 : x.tr.kids.length ≤ k := by omega
    have hget : x.tr.kids[k]? = none := by simp_all
    have hobs : x.tr.observe (.fill k q) = x.tr := by
      simp [Truth.observe, hget]
    have hadv : advance step b x (.fill k q) = ⟨x.st, x.tr⟩ := by
      simp [advance, hstep, hobs, Truth.record]
    rw [hadv]
    exact ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩

theorem inv_preserve (b : Build) (x : Sys) (e : Event) (h : Inv x) : Inv (advance step b x e) := by
  cases e with
  | parent q f => exact inv_parent b x q f h
  | route id liq => exact inv_route b x id liq h
  | ack k => exact inv_ack b x k h
  | fill k q => exact inv_fill b x k q h

theorem inv_all (b : Build) (evs : List Event) : Inv (run step b evs) :=
  run_induction step b Inv inv_start (fun x e h => inv_preserve b x e h) evs

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  have h := inv_all b evs
  obtain ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩ := h
  have e : step b (run step b evs).st (.route id liq)
      = routeBySent (run step b evs).st id liq := rfl
  rw [e]
  exact route_output_eq _ id liq hnP hqty hsent

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id hid
  have h := inv_all b evs
  obtain ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩ := h
  have hid2 : id < (run step b evs).st.nParents := by omega
  exact hcum id hid2

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  have h := inv_all b evs
  obtain ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩ := h
  by_cases hid : id < (run step b evs).st.nParents
  · rw [← hsent id hid, ← hqty id hid]
    exact hle id hid
  · have hN : (run step b evs).tr.nOrders ≤ id := by omega
    have hz : (run step b evs).tr.sent id = 0 :=
      sentFor_fresh _ _ hmem id hN
    rw [hz]
    exact Nat.zero_le _

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  have h1 := exec_le_sent step b evs id
  have h2 := req_never_overroute b evs id
  omega

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hfill c hc
  cases e with
  | parent q f => simp [step] at hc
  | route j liq =>
    have h := inv_all b evs
    obtain ⟨hnP, hqty, hsent, hcum, hle, hnC, hch, hmem⟩ := h
    have e2 : step b (run step b evs).st (.route j liq)
        = routeBySent (run step b evs).st j liq := rfl
    rw [e2, route_output_eq _ j liq hnP hqty hsent] at hc
    unfold expectedRoute at hc
    by_cases hC : (j < (run step b evs).tr.nOrders
      ∧ 0 < min liq ((run step b evs).tr.qty j - (run step b evs).tr.sent j))
    · simp [hC] at hc
      subst hc
      simp
      intro hji
      subst j
      have hsent_eq : (run step b evs).tr.sent id = (run step b evs).tr.qty id := by
        have h1 := exec_le_sent step b evs id
        have hN : (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id := by
          by_cases hid : id < (run step b evs).st.nParents
          · rw [← hsent id hid, ← hqty id hid]
            exact hle id hid
          · have hNN : (run step b evs).tr.nOrders ≤ id := by omega
            have hz : (run step b evs).tr.sent id = 0 :=
              sentFor_fresh _ _ hmem id hNN
            rw [hz]
            exact Nat.zero_le _
        omega
      rw [hsent_eq] at hC
      simp at hC
    · simp [hC] at hc
  | ack k => simp [step] at hc
  | fill k q =>
    simp only [step] at hc
    by_cases hk : k < (run step b evs).st.nChildren
    · simp [hk] at hc
    · simp [hk] at hc

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  have hkids : (run step b (normalOrder flag)).tr.kids
      = [⟨0, 100, 100⟩, ⟨0, 100, 100⟩, ⟨0, 100, 100⟩] := by
    simp [normalOrder, run, advance, step, routeBySent, Truth.observe, Truth.record,
      start, init, Truth.empty, upd_self', List.getElem_cons_zero,
      List.getElem_cons_succ, List.set_cons_zero, List.set_cons_succ]
  constructor
  · exact hkids
  · simp only [Truth.exec]
    rw [hkids]
    decide

end OrderRouter
