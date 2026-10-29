import OrderRouter.Spec
import OrderRouter.Lemmas
namespace OrderRouter

def step : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route rid liq =>
    if rid < s.nParents ∧ 0 < min liq ((s.parents rid).qty - (s.parents rid).sent) then
      ({ s with parents := upd s.parents rid { (s.parents rid) with sent := (s.parents rid).sent + min liq ((s.parents rid).qty - (s.parents rid).sent) },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren (⟨rid, min liq ((s.parents rid).qty - (s.parents rid).sent), 0⟩ : ChildRec) },
       [(⟨rid, min liq ((s.parents rid).qty - (s.parents rid).sent)⟩ : Child)])
    else (s, [])
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      ({ s with parents := upd s.parents (s.children k).parent { (s.parents (s.children k).parent) with cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) },
                children := upd s.children k { (s.children k) with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } }, [])
    else (s, [])

theorem upd_same {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by simp [upd]
theorem upd_ne {α : Type} (f : Nat → α) (k j : Nat) (v : α) (h : j ≠ k) : upd f k v j = f j := by simp [upd, h]

def Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ rid, rid < x.st.nParents → (x.st.parents rid).qty = x.tr.qty rid) ∧
  (∀ rid, rid < x.st.nParents → (x.st.parents rid).sent = x.tr.sent rid) ∧
  (∀ rid, rid < x.st.nParents → (x.st.parents rid).cum = x.tr.exec rid) ∧
  (∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → x.st.children k = (⟨c.parent, c.qty, c.done⟩ : ChildRec)) ∧
  (∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → c.parent < x.tr.nOrders) ∧
  (∀ rid, rid < x.st.nParents → (x.st.parents rid).sent ≤ (x.st.parents rid).qty)

theorem inv_start : Inv start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rid h; simp [start, init] at h
  · intro rid h; simp [start, init] at h
  · intro rid h; simp [start, init] at h
  · intro k c h; simp [start, Truth.empty] at h
  · intro k c h; simp [start, Truth.empty] at h
  · intro rid h; simp [start, init] at h

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> exact ⟨rfl, rfl⟩

theorem req_routes_available : RoutesAvailable step := sorry

theorem req_never_overroute : NeverOverroute step := sorry

theorem req_stop_when_filled : StopWhenFilled step := sorry

theorem req_no_excess_execution : NoExcessExecution step := sorry

theorem req_fill_accounting : FillAccounting step := sorry

end OrderRouter
