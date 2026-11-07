import JuliaLean.Proofs.base.reduce.Contracts

/-!
Proofs of the `Val`-level properties: widened `sum` with `init`.
-/

namespace JuliaLean.Reduce

/-! ### Wrapping arithmetic -/

theorem wrapInt_emod (t : IntTy) (x : Int) : wrapInt t x = wrapInt t (x % 2 ^ t.bits) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_emod_self (t : IntTy) (x : Int) : wrapInt t x % 2 ^ t.bits = x % 2 ^ t.bits := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_wrapInt (t : IntTy) (x : Int) : wrapInt t (wrapInt t x) = wrapInt t x :=
  wrapInt_of_inRange t _ (wrapInt_bounds t x)

theorem wrapInt_add (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a + wrapInt t b) = wrapInt t (a + b) := by
  rw [wrapInt_emod t (wrapInt t a + wrapInt t b), Int.add_emod, wrapInt_emod_self,
    wrapInt_emod_self, ← Int.add_emod, ← wrapInt_emod]

theorem wrapInt_mul (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a * wrapInt t b) = wrapInt t (a * b) := by
  rw [wrapInt_emod t (wrapInt t a * wrapInt t b), Int.mul_emod, wrapInt_emod_self,
    wrapInt_emod_self, ← Int.mul_emod, ← wrapInt_emod]

theorem rem_wrap_add {t : IntTy} (w : IntTy) (p : Int) (y : JInt t) :
    JInt.rem w (JInt.wrap w p) + JInt.rem w y = JInt.wrap w (p + y.val) :=
  Subtype.ext (by
    show wrapInt w (wrapInt w (wrapInt w p) + wrapInt w y.val) = wrapInt w (p + y.val)
    rw [wrapInt_wrapInt, wrapInt_add])

theorem rem_wrap_mul {t : IntTy} (w : IntTy) (p : Int) (y : JInt t) :
    JInt.rem w (JInt.wrap w p) * JInt.rem w y = JInt.wrap w (p * y.val) :=
  Subtype.ext (by
    show wrapInt w (wrapInt w (wrapInt w p) * wrapInt w y.val) = wrapInt w (p * y.val)
    rw [wrapInt_wrapInt, wrapInt_mul])

/-! ### `sum` with `init` -/

theorem addSum_wide {w t : IntTy} (hw : w = .i64 ∨ w = .u64) (ht : smallTy t = true)
    (a : JInt w) (y : JInt t) :
    Val.addSum (.int w a) (.int t y) = .int w (JInt.rem w a + JInt.rem w y) := by
  rcases hw with rfl | rfl <;> cases t <;> first | exact absurd ht (by decide) | rfl

theorem sum_fold {w t : IntTy} (hw : w = .i64 ∨ w = .u64) (ht : smallTy t = true) (p : Int)
    (xs : List (JInt t)) :
    (xs.map (Val.int t)).foldl Val.addSum (.int w (JInt.wrap w p)) =
      .int w (JInt.wrap w (p + (xs.map (·.val)).sum)) := by
  induction xs generalizing p with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [addSum_wide hw ht, rem_wrap_add, ih]
    simp [List.sum_cons, Int.add_assoc]

theorem lit_zero_val (s : IntTy) : (JInt.lit s 0).val = 0 := by
  cases s <;> simp [JInt.lit, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]

theorem sumInitWidened_proven : SumInitWidened := by
  intro t s v ht hs hne _
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hs' : Val.smallOrBool (.int s (JInt.lit s 0)) = true := hs
  have ht' : Val.smallOrBool (.int t x) = true := ht
  have key : ∀ w, (w = .i64 ∨ w = .u64) →
      Val.addSum (.int s (JInt.lit s 0)) (.int t x) = .int w (JInt.wrap w x.val) →
      Vec.sumInit (.int s (JInt.lit s 0)) (ints t (x :: rest)) =
        .int w (JInt.wrap w ((x :: rest).map (·.val)).sum) := by
    intro w hw h1
    show List.foldl Val.addSum _ (List.map (Val.int t) (x :: rest)) = _
    rw [List.map_cons, List.foldl_cons, h1, sum_fold hw ht]
    simp [List.sum_cons]
  by_cases hu : (Val.smallUnsigned s && Val.smallUnsigned t) = true
  · refine ⟨.u64, .inr rfl, key _ (.inr rfl) ?_⟩
    simp only [Val.addSum]
    simp only [hu, ↓reduceIte, Val.intVal, lit_zero_val, Int.zero_add]
  · refine ⟨.i64, .inl rfl, key _ (.inl rfl) ?_⟩
    simp only [Val.addSum]
    have hb : (Val.smallOrBool (.int s (JInt.lit s 0)) && Val.smallOrBool (.int t x)) = true := by
      simp [hs', ht']
    simp only [hu, hb, Bool.false_eq_true, ↓reduceIte, Val.intVal, lit_zero_val, Int.zero_add]

end JuliaLean.Reduce
