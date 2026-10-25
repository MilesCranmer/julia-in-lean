import JuliaLean.IOBuffers.Inv

/-! Monad and arithmetic lemmas for the write proofs. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

theorem bind_ok {α β} {x : M α} {f : α → M β} {s s' : IOBuf} {a : α} (h : x.run s = .ok a s') :
    (x >>= f).run s = (f a).run s' := by
  show EStateM.bind x f s = _
  simp only [EStateM.bind]
  rw [show x s = _ from h]; rfl

theorem bind_err {α β} {x : M α} {f : α → M β} {s s' : IOBuf} {e : IOErr} (h : x.run s = .error e s') :
    (x >>= f).run s = .error e s' := by
  show EStateM.bind x f s = _
  simp only [EStateM.bind]
  rw [show x s = _ from h]

theorem run_get (s : IOBuf) : (get : M IOBuf).run s = .ok s s := rfl
theorem run_set (s t : IOBuf) : (set t : M PUnit).run s = .ok () t := rfl
theorem run_pure {α} (a : α) (s : IOBuf) : (pure a : M α).run s = .ok a s := rfl
theorem run_throw {α} (e : IOErr) (s : IOBuf) : (throw e : M α).run s = .error e s := rfl
theorem run_modify (f : IOBuf → IOBuf) (s : IOBuf) : (modify f : M PUnit).run s = .ok () (f s) := rfl
theorem run_lift_ok {α} (a : α) (s : IOBuf) : (lift (.ok a) : M α).run s = .ok a s := rfl
theorem run_lift_err {α} (e : IOErr) (s : IOBuf) : (lift (.error e) : M α).run s = .error e s := rfl

theorem get_bind {β} (f : IOBuf → M β) (s : IOBuf) : ((get : M IOBuf) >>= f).run s = (f s).run s :=
  bind_ok (run_get s)
theorem set_bind {β} (t : IOBuf) (f : PUnit → M β) (s : IOBuf) :
    ((set t : M PUnit) >>= f).run s = (f ()).run t := bind_ok (run_set s t)
theorem pure_bind' {α β} (a : α) (f : α → M β) (s : IOBuf) : ((pure a : M α) >>= f).run s = (f a).run s :=
  bind_ok (run_pure a s)
theorem lift_ok_bind {α β} (a : α) (f : α → M β) (s : IOBuf) :
    ((lift (.ok a) : M α) >>= f).run s = (f a).run s := bind_ok (run_lift_ok a s)
theorem lift_err_bind {α β} (e : IOErr) (f : α → M β) (s : IOBuf) :
    ((lift (.error e) : M α) >>= f).run s = .error e s := bind_err (run_lift_err e s)
theorem throw_bind {α β} (e : IOErr) (f : α → M β) (s : IOBuf) :
    ((throw e : M α) >>= f).run s = .error e s := bind_err (run_throw e s)

theorem wr (x : Int) (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) : wrapInt .i64 x = x :=
  wrapInt_of_inRange .i64 x ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩

theorem wru (x : Int) (h1 : 0 ≤ x) (h2 : x ≤ 2 ^ 64 - 1) : wrapInt .u64 x = x :=
  wrapInt_of_inRange .u64 x ⟨by simp [IntTy.min, IntTy.signed]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩

theorem sub_val (a b : I) : (a - b).val = wrapInt .i64 (a.val - b.val) := rfl
theorem add_val (a b : I) : (a + b).val = wrapInt .i64 (a.val + b.val) := rfl
theorem neg_val (a : I) : (-a).val = wrapInt .i64 (-a.val) := rfl
theorem i_val (x : Int) : (i x).val = wrapInt .i64 x := rfl
theorem u_val (x : Int) : (u x).val = wrapInt .u64 x := rfl
theorem rem_i64_val (x : U) : (JInt.rem .i64 x).val = wrapInt .i64 x.val := rfl
theorem rem_u64_val (x : I) : (JInt.rem .u64 x).val = wrapInt .u64 x.val := rfl

theorem imax_val (a b : I) : (imax a b).val = max a.val b.val := by
  unfold imax; split <;> omega
theorem imin_val (a b : I) : (imin a b).val = min a.val b.val := by
  unfold imin; split <;> omega
theorem uminU_val (a b : U) : (uminU a b).val = min a.val b.val := by
  unfold uminU; split <;> omega

theorem i0 : (i 0).val = 0 := rfl
theorem i1 : (i 1).val = 1 := rfl

theorem off_val (io : IOBuf) : (getOffset io).val = max 0 io.oc.val := by
  rw [getOffset, imax_val, i0]

theorem I.ge (a : I) : -2 ^ 63 ≤ a.val := by
  have := a.property.1; simp [IntTy.min, IntTy.signed, IntTy.bits] at this; omega
theorem I.le (a : I) : a.val ≤ 2 ^ 63 - 1 := by
  have := a.property.2; simp [IntTy.max, IntTy.signed, IntTy.bits] at this; omega

/-- Remove every in-range wrap in the goal and hypotheses. -/
macro "wrs" : tactic => `(tactic| simp (disch := omega) only [sub_val, add_val, neg_val, i_val, u_val,
  rem_i64_val, rem_u64_val, imax_val, imin_val, uminU_val, off_val, wr, wru] at *)

/-- Remove every in-range wrap in the goal. -/
macro "wrg" : tactic => `(tactic| simp (disch := omega) only [sub_val, add_val, neg_val, i_val, u_val,
  rem_i64_val, rem_u64_val, imax_val, imin_val, uminU_val, off_val, wr, wru])

end WriteP
end JuliaLean.IOBuffers
